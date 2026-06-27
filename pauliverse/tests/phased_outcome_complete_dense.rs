//! Dense statevector validation of `PhasedOutcomeCompleteSimulation`.
//!
//! For random circuits (Clifford gates, Pauli exponentials, Paulis, controlled-Paulis, conditional
//! Paulis and Pauli measurements) this test enumerates every random-bit assignment `r`, materialises
//! the simulator's claimed output state `i^⟨p,r⟩ (-1)^⟨Br+s,r⟩ R|Ar⟩`, and compares it — *exactly,
//! including the global phase* — against a brute-force dense statevector simulation whose
//! measurement outcomes are forced to the branch selected by `r`.

#![allow(
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::too_many_lines
)]

use binar::vec::AlignedBitVec;
use binar::{Bitwise, BitwiseMut};
use paulimer::clifford::{Clifford, PhasedCliffordUnitary};
use paulimer::pauli::{Pauli, commutes_with};
use paulimer::{DensePauli, SparsePauli, UnitaryOp};
use pauliverse::{PhasedOutcomeCompleteSimulation, Simulation};
use rand::RngExt;

#[derive(Clone, Copy, PartialEq, Debug)]
struct C {
    re: f64,
    im: f64,
}

impl C {
    const ZERO: C = C { re: 0.0, im: 0.0 };
    fn new(re: f64, im: f64) -> C {
        C { re, im }
    }
    fn add(self, o: C) -> C {
        C::new(self.re + o.re, self.im + o.im)
    }
    fn mul(self, o: C) -> C {
        C::new(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)
    }
    fn scale(self, s: f64) -> C {
        C::new(self.re * s, self.im * s)
    }
    fn abs2(self) -> f64 {
        self.re * self.re + self.im * self.im
    }
}

fn zeta8(k: i64) -> C {
    let a = std::f64::consts::FRAC_PI_4 * (k.rem_euclid(8)) as f64;
    C::new(a.cos(), a.sin())
}

const ROOT_HALF: f64 = std::f64::consts::FRAC_1_SQRT_2;

struct Dense {
    n: usize,
    amp: Vec<C>,
}

impl Dense {
    fn zero(n: usize) -> Dense {
        let mut amp = vec![C::ZERO; 1 << n];
        amp[0] = C::new(1.0, 0.0);
        Dense { n, amp }
    }
    fn apply1(&mut self, q: usize, m: [[C; 2]; 2]) {
        let bit = 1usize << (self.n - 1 - q);
        for base in 0..(1 << self.n) {
            if base & bit == 0 {
                let a0 = self.amp[base];
                let a1 = self.amp[base | bit];
                self.amp[base] = m[0][0].mul(a0).add(m[0][1].mul(a1));
                self.amp[base | bit] = m[1][0].mul(a0).add(m[1][1].mul(a1));
            }
        }
    }
    fn apply_cx(&mut self, c: usize, t: usize) {
        let cb = 1usize << (self.n - 1 - c);
        let tb = 1usize << (self.n - 1 - t);
        let mut out = self.amp.clone();
        for base in 0..(1 << self.n) {
            let src = if base & cb != 0 { base ^ tb } else { base };
            out[base] = self.amp[src];
        }
        self.amp = out;
    }
    fn apply_cz(&mut self, a: usize, b: usize) {
        let ab = 1usize << (self.n - 1 - a);
        let bb = 1usize << (self.n - 1 - b);
        for base in 0..(1 << self.n) {
            if base & ab != 0 && base & bb != 0 {
                self.amp[base] = self.amp[base].scale(-1.0);
            }
        }
    }
    fn apply_swap(&mut self, a: usize, b: usize) {
        let ab = 1usize << (self.n - 1 - a);
        let bb = 1usize << (self.n - 1 - b);
        let mut out = self.amp.clone();
        for base in 0..(1 << self.n) {
            let bit_a = usize::from(base & ab != 0);
            let bit_b = usize::from(base & bb != 0);
            let mut src = base & !ab & !bb;
            if bit_b != 0 {
                src |= ab;
            }
            if bit_a != 0 {
                src |= bb;
            }
            out[base] = self.amp[src];
        }
        self.amp = out;
    }
    fn pauli_applied(&self, x: &[bool], z: &[bool], phase: i64) -> Vec<C> {
        let mut out = vec![C::ZERO; self.amp.len()];
        let xmask: usize = (0..self.n).filter(|&q| x[q]).map(|q| 1usize << (self.n - 1 - q)).sum();
        for base in 0..(1 << self.n) {
            let target = base ^ xmask;
            let mut sign_parity = 0i64;
            for q in 0..self.n {
                if z[q] && (base >> (self.n - 1 - q)) & 1 == 1 {
                    sign_parity ^= 1;
                }
            }
            let coeff = zeta8(2 * phase + 4 * sign_parity);
            out[target] = out[target].add(self.amp[base].mul(coeff));
        }
        out
    }
    fn apply_pauli(&mut self, x: &[bool], z: &[bool], phase: i64) {
        self.amp = self.pauli_applied(x, z, phase);
    }
    fn apply_pauli_exp(&mut self, x: &[bool], z: &[bool], phase: i64) {
        let p_applied = self.pauli_applied(x, z, phase);
        for base in 0..self.amp.len() {
            self.amp[base] = self.amp[base].add(p_applied[base].mul(C::new(0.0, 1.0))).scale(ROOT_HALF);
        }
    }
    fn apply_controlled_pauli(&mut self, p1: &(Vec<bool>, Vec<bool>, i64), p2: &(Vec<bool>, Vec<bool>, i64)) {
        // Lambda(P1, P2) = (I + P1)/2 + (I - P1)/2 * P2
        let p1v = self.pauli_applied(&p1.0, &p1.1, p1.2);
        let plus: Vec<C> = (0..self.amp.len())
            .map(|i| self.amp[i].add(p1v[i]).scale(0.5))
            .collect();
        let minus = Dense {
            n: self.n,
            amp: (0..self.amp.len())
                .map(|i| self.amp[i].add(p1v[i].scale(-1.0)).scale(0.5))
                .collect(),
        };
        let p2_minus = minus.pauli_applied(&p2.0, &p2.1, p2.2);
        for i in 0..self.amp.len() {
            self.amp[i] = plus[i].add(p2_minus[i]);
        }
    }
    fn project(&mut self, x: &[bool], z: &[bool], phase: i64, outcome: bool) {
        let pv = self.pauli_applied(x, z, phase);
        let sign = if outcome { -1.0 } else { 1.0 };
        for i in 0..self.amp.len() {
            self.amp[i] = self.amp[i].add(pv[i].scale(sign)).scale(0.5);
        }
        normalize(&mut self.amp);
    }
}

fn normalize(amp: &mut [C]) {
    let norm = amp.iter().map(|a| a.abs2()).sum::<f64>().sqrt();
    assert!(norm > 1e-9, "attempted to normalize a vanishing state");
    let inv = 1.0 / norm;
    for a in amp.iter_mut() {
        *a = a.scale(inv);
    }
}

fn gate_matrix(op: UnitaryOp) -> [[C; 2]; 2] {
    let rh = ROOT_HALF;
    match op {
        UnitaryOp::Hadamard => [[C::new(rh, 0.0), C::new(rh, 0.0)], [C::new(rh, 0.0), C::new(-rh, 0.0)]],
        UnitaryOp::X => [[C::ZERO, C::new(1.0, 0.0)], [C::new(1.0, 0.0), C::ZERO]],
        UnitaryOp::Y => [[C::ZERO, C::new(0.0, -1.0)], [C::new(0.0, 1.0), C::ZERO]],
        UnitaryOp::Z => [[C::new(1.0, 0.0), C::ZERO], [C::ZERO, C::new(-1.0, 0.0)]],
        UnitaryOp::SqrtZ => [[C::new(1.0, 0.0), C::ZERO], [C::ZERO, C::new(0.0, 1.0)]],
        UnitaryOp::SqrtZInv => [[C::new(1.0, 0.0), C::ZERO], [C::ZERO, C::new(0.0, -1.0)]],
        UnitaryOp::SqrtX => [
            [zeta8(1).scale(rh), zeta8(7).scale(rh)],
            [zeta8(7).scale(rh), zeta8(1).scale(rh)],
        ],
        UnitaryOp::SqrtXInv => [
            [zeta8(7).scale(rh), zeta8(1).scale(rh)],
            [zeta8(1).scale(rh), zeta8(7).scale(rh)],
        ],
        UnitaryOp::SqrtY => [
            [zeta8(1).scale(rh), zeta8(5).scale(rh)],
            [zeta8(1).scale(rh), zeta8(1).scale(rh)],
        ],
        UnitaryOp::SqrtYInv => [
            [zeta8(7).scale(rh), zeta8(7).scale(rh)],
            [zeta8(3).scale(rh), zeta8(7).scale(rh)],
        ],
        other => panic!("gate_matrix called on multi-qubit op {other:?}"),
    }
}

fn statevector(phased: &PhasedCliffordUnitary) -> Vec<C> {
    use binar::matrix::AlignedBitMatrix;
    use binar::{BitMatrix, BitwiseMut};
    let n = phased.num_qubits();
    let mut matrix = AlignedBitMatrix::zeros(n, n);
    for generator in 0..n {
        let image: DensePauli = phased.clifford().image_z(generator);
        for qubit in image.x_bits().support() {
            matrix.row_mut(generator).assign_index(qubit, true);
        }
    }
    let rank = BitMatrix::from_aligned(matrix).rank();
    let mag = (0.5f64).powf(rank as f64 / 2.0);
    let mut out = vec![C::ZERO; 1 << n];
    for idx in 0..(1usize << n) {
        let mut value = 0usize;
        for q in 0..n {
            if (idx >> (n - 1 - q)) & 1 == 1 {
                value |= 1usize << q;
            }
        }
        if let Some(exp) = phased.state_amplitude_phase_exponent_usize(value) {
            out[idx] = zeta8(i64::from(exp)).scale(mag);
        }
    }
    out
}

fn pauli_arrays(pauli: &DensePauli, n: usize) -> (Vec<bool>, Vec<bool>, i64) {
    let mut x = vec![false; n];
    let mut z = vec![false; n];
    for q in pauli.x_bits().support() {
        x[q] = true;
    }
    for q in pauli.z_bits().support() {
        z[q] = true;
    }
    (x, z, i64::from(pauli.xz_phase_exponent()))
}

#[derive(Clone)]
enum Op {
    Gate(UnitaryOp, Vec<usize>),
    Pauli(String),
    PauliExp(String),
    ControlledPauli(String, String),
    ConditionalPauli(String, Vec<usize>, bool),
    Measure(String),
}

fn random_hermitian_pauli(rng: &mut impl RngExt, n: usize) -> String {
    loop {
        let mut letters = String::new();
        let mut any = false;
        for _ in 0..n {
            match rng.random_range(0..4) {
                0 => letters.push('I'),
                1 => {
                    letters.push('X');
                    any = true;
                }
                2 => {
                    letters.push('Z');
                    any = true;
                }
                _ => {
                    letters.push('Y');
                    any = true;
                }
            }
        }
        if !any {
            continue;
        }
        let sign = if rng.random_range(0..2) == 0 { "-" } else { "" };
        return format!("{sign}{letters}");
    }
}

fn two_distinct(rng: &mut impl RngExt, n: usize) -> (usize, usize) {
    let a = rng.random_range(0..n);
    let mut b = rng.random_range(0..n);
    while b == a {
        b = rng.random_range(0..n);
    }
    (a, b)
}

fn random_circuit(rng: &mut impl RngExt, n: usize) -> Vec<Op> {
    let single = [
        UnitaryOp::Hadamard,
        UnitaryOp::X,
        UnitaryOp::Y,
        UnitaryOp::Z,
        UnitaryOp::SqrtZ,
        UnitaryOp::SqrtZInv,
        UnitaryOp::SqrtX,
        UnitaryOp::SqrtXInv,
        UnitaryOp::SqrtY,
        UnitaryOp::SqrtYInv,
    ];
    let two = [UnitaryOp::ControlledX, UnitaryOp::ControlledZ, UnitaryOp::Swap];
    let mut ops = Vec::new();
    let mut measurement_count = 0usize;
    let op_count = rng.random_range(6..14);
    for _ in 0..op_count {
        match rng.random_range(0..7) {
            0 => {
                let q = rng.random_range(0..n);
                ops.push(Op::Gate(single[rng.random_range(0..single.len())], vec![q]));
            }
            1 => {
                let (a, b) = two_distinct(rng, n);
                ops.push(Op::Gate(two[rng.random_range(0..two.len())], vec![a, b]));
            }
            2 => ops.push(Op::Pauli(random_hermitian_pauli(rng, n))),
            3 => ops.push(Op::PauliExp(random_hermitian_pauli(rng, n))),
            4 => {
                let p1 = random_hermitian_pauli(rng, n);
                let mut p2 = random_hermitian_pauli(rng, n);
                let mut guard = 0;
                loop {
                    let sp1: SparsePauli = p1.parse().unwrap();
                    let sp2: SparsePauli = p2.parse().unwrap();
                    if commutes_with(&sp1, &sp2) {
                        break;
                    }
                    p2 = random_hermitian_pauli(rng, n);
                    guard += 1;
                    if guard > 32 {
                        break;
                    }
                }
                let sp1: SparsePauli = p1.parse().unwrap();
                let sp2: SparsePauli = p2.parse().unwrap();
                if commutes_with(&sp1, &sp2) {
                    ops.push(Op::ControlledPauli(p1, p2));
                }
            }
            5 => {
                if measurement_count > 0 && rng.random_range(0..2) == 0 {
                    let mut outcomes = Vec::new();
                    for o in 0..measurement_count {
                        if rng.random_range(0..2) == 0 {
                            outcomes.push(o);
                        }
                    }
                    if !outcomes.is_empty() {
                        ops.push(Op::ConditionalPauli(
                            random_hermitian_pauli(rng, n),
                            outcomes,
                            rng.random_range(0..2) == 1,
                        ));
                    }
                }
            }
            _ => {
                if measurement_count < 5 {
                    ops.push(Op::Measure(random_hermitian_pauli(rng, n)));
                    measurement_count += 1;
                }
            }
        }
    }
    ops
}

fn run_simulation(ops: &[Op], n: usize) -> PhasedOutcomeCompleteSimulation {
    let mut sim = PhasedOutcomeCompleteSimulation::new(n);
    for op in ops {
        match op {
            Op::Gate(u, support) => sim.unitary_op(*u, support),
            Op::Pauli(p) => sim.pauli(&p.parse().unwrap()),
            Op::PauliExp(p) => sim.pauli_exp(&p.parse().unwrap()),
            Op::ControlledPauli(p1, p2) => sim.controlled_pauli(&p1.parse().unwrap(), &p2.parse().unwrap()),
            Op::ConditionalPauli(p, outcomes, parity) => {
                sim.conditional_pauli(&p.parse().unwrap(), outcomes, *parity);
            }
            Op::Measure(p) => {
                sim.measure(&p.parse().unwrap());
            }
        }
    }
    sim
}

fn dense_reference(ops: &[Op], outcome_vector: &[bool], n: usize) -> Vec<C> {
    let mut dense = Dense::zero(n);
    let mut measurement_index = 0usize;
    for op in ops {
        match op {
            Op::Gate(u, support) => match u {
                UnitaryOp::ControlledX => dense.apply_cx(support[0], support[1]),
                UnitaryOp::ControlledZ => dense.apply_cz(support[0], support[1]),
                UnitaryOp::Swap => dense.apply_swap(support[0], support[1]),
                other => dense.apply1(support[0], gate_matrix(*other)),
            },
            Op::Pauli(p) => {
                let (x, z, phase) = pauli_arrays(&p.parse::<DensePauli>().unwrap(), n);
                dense.apply_pauli(&x, &z, phase);
            }
            Op::PauliExp(p) => {
                let (x, z, phase) = pauli_arrays(&p.parse::<DensePauli>().unwrap(), n);
                dense.apply_pauli_exp(&x, &z, phase);
            }
            Op::ControlledPauli(p1, p2) => {
                let a = pauli_arrays(&p1.parse::<DensePauli>().unwrap(), n);
                let b = pauli_arrays(&p2.parse::<DensePauli>().unwrap(), n);
                dense.apply_controlled_pauli(&a, &b);
            }
            Op::ConditionalPauli(p, outcomes, parity) => {
                let condition = outcomes.iter().fold(false, |acc, &o| acc ^ outcome_vector[o]);
                if condition == *parity {
                    let (x, z, phase) = pauli_arrays(&p.parse::<DensePauli>().unwrap(), n);
                    dense.apply_pauli(&x, &z, phase);
                }
            }
            Op::Measure(p) => {
                let (x, z, phase) = pauli_arrays(&p.parse::<DensePauli>().unwrap(), n);
                dense.project(&x, &z, phase, outcome_vector[measurement_index]);
                measurement_index += 1;
            }
        }
    }
    dense.amp
}

fn claimed_state(sim: &PhasedOutcomeCompleteSimulation, random_bits: &[bool], n: usize) -> Vec<C> {
    let encoder = sim.phased_state_encoder();
    let base = statevector(&encoder);

    let sign_matrix = sim.aligned_sign_matrix();
    let n_random = sim.random_outcome_count();
    let mut register = AlignedBitVec::zeros(n);
    for qubit in 0..n {
        let mut bit = false;
        for column in 0..n_random {
            if random_bits[column] && sign_matrix.row(qubit).index(column) {
                bit = !bit;
            }
        }
        register.assign_index(qubit, bit);
    }

    let image = encoder.clifford().image_x_bits(&register);
    let (x, z, phase) = pauli_arrays(&image, n);
    let mut dense = Dense { n, amp: base };
    dense.apply_pauli(&x, &z, phase);

    let exponent = i64::from(sim.output_phase_exponent(random_bits));
    for amplitude in &mut dense.amp {
        *amplitude = amplitude.mul(zeta8(exponent));
    }
    let mut amp = dense.amp;
    normalize(&mut amp);
    amp
}

fn outcome_vector(sim: &PhasedOutcomeCompleteSimulation, random_bits: &[bool]) -> Vec<bool> {
    let outcome_matrix = sim.aligned_outcome_matrix();
    let shift = sim.aligned_outcome_shift();
    let n_random = sim.random_outcome_count();
    (0..sim.outcome_count())
        .map(|row| {
            let mut bit = shift.index(row);
            for column in 0..n_random {
                if random_bits[column] && outcome_matrix.row(row).index(column) {
                    bit = !bit;
                }
            }
            bit
        })
        .collect()
}

fn describe(ops: &[Op]) -> String {
    ops.iter()
        .map(|op| match op {
            Op::Gate(u, s) => format!("Gate({u:?},{s:?})"),
            Op::Pauli(p) => format!("Pauli({p})"),
            Op::PauliExp(p) => format!("PauliExp({p})"),
            Op::ControlledPauli(a, b) => format!("CPauli({a},{b})"),
            Op::ConditionalPauli(p, o, parity) => format!("CondPauli({p},{o:?},{parity})"),
            Op::Measure(p) => format!("Measure({p})"),
        })
        .collect::<Vec<_>>()
        .join(" | ")
}

fn close(a: &[C], b: &[C]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.add(y.scale(-1.0)).abs2() < 1e-6)
}

fn verify(ops: &[Op], n: usize) {
    let sim = run_simulation(ops, n);
    let n_random = sim.random_outcome_count();
    assert!(n_random <= 12, "too many random bits to enumerate");
    for assignment in 0..(1usize << n_random) {
        let random_bits: Vec<bool> = (0..n_random).map(|bit| (assignment >> bit) & 1 == 1).collect();
        let outcomes = outcome_vector(&sim, &random_bits);
        let reference = dense_reference(ops, &outcomes, n);
        let claimed = claimed_state(&sim, &random_bits, n);
        assert!(
            close(&claimed, &reference),
            "mismatch: ops=[{}] random_bits={random_bits:?}",
            describe(ops)
        );
    }
}

#[test]
fn single_pauli_measurement() {
    verify(&[Op::Measure("X".into())], 1);
    verify(&[Op::Measure("Y".into())], 1);
    verify(&[Op::Measure("-X".into())], 1);
    verify(&[Op::Measure("-Y".into())], 1);
}

#[test]
fn two_pauli_measurements() {
    verify(&[Op::Measure("X".into()), Op::Measure("Y".into())], 1);
    verify(&[Op::Measure("Y".into()), Op::Measure("X".into())], 1);
    verify(&[Op::Measure("X".into()), Op::Measure("Z".into())], 1);
    verify(&[Op::Measure("-X".into()), Op::Measure("-Y".into())], 1);
}

#[test]
fn measurement_then_conditional() {
    verify(
        &[Op::Measure("X".into()), Op::ConditionalPauli("Z".into(), vec![0], false)],
        1,
    );
    verify(
        &[Op::Measure("Y".into()), Op::ConditionalPauli("X".into(), vec![0], true)],
        1,
    );
}

#[test]
fn controlled_pauli_no_randomness() {
    verify(&[Op::Gate(UnitaryOp::Hadamard, vec![0]), Op::ControlledPauli("ZI".into(), "IX".into())], 2);
    verify(&[Op::Gate(UnitaryOp::Hadamard, vec![0]), Op::ControlledPauli("ZZ".into(), "XX".into())], 2);
    verify(&[Op::Gate(UnitaryOp::SqrtX, vec![0]), Op::ControlledPauli("YI".into(), "IY".into())], 2);
}

#[test]
fn entangling_then_two_measurements() {
    verify(
        &[
            Op::Gate(UnitaryOp::Hadamard, vec![0]),
            Op::Gate(UnitaryOp::ControlledX, vec![0, 1]),
            Op::Measure("XX".into()),
            Op::Measure("ZI".into()),
        ],
        2,
    );
    verify(
        &[Op::Measure("X".into()), Op::Gate(UnitaryOp::SqrtX, vec![0]), Op::Measure("X".into())],
        1,
    );
}

#[test]
fn shrink_a() {
    verify(
        &[
            Op::Gate(UnitaryOp::Swap, vec![2, 0]),
            Op::Measure("-ZIX".into()),
            Op::Gate(UnitaryOp::ControlledX, vec![2, 1]),
            Op::Gate(UnitaryOp::SqrtX, vec![0]),
            Op::ConditionalPauli("-ZXI".into(), vec![0], false),
            Op::Gate(UnitaryOp::ControlledZ, vec![2, 1]),
            Op::Measure("XIY".into()),
        ],
        3,
    );
}

#[test]
fn shrink_b_no_conditional() {
    verify(
        &[
            Op::Gate(UnitaryOp::Swap, vec![2, 0]),
            Op::Measure("-ZIX".into()),
            Op::Gate(UnitaryOp::ControlledX, vec![2, 1]),
            Op::Gate(UnitaryOp::SqrtX, vec![0]),
            Op::Gate(UnitaryOp::ControlledZ, vec![2, 1]),
            Op::Measure("XIY".into()),
        ],
        3,
    );
}

#[test]
fn shrink_c_conditional_between() {
    verify(
        &[
            Op::Measure("-ZIX".into()),
            Op::ConditionalPauli("-ZXI".into(), vec![0], false),
            Op::Measure("XIY".into()),
        ],
        3,
    );
}

#[test]
fn shrink_d_two_meas_gate() {
    verify(
        &[
            Op::Measure("ZIX".into()),
            Op::Gate(UnitaryOp::SqrtX, vec![0]),
            Op::Measure("XIY".into()),
        ],
        3,
    );
}

#[test]
fn captured_regression_one() {
    verify(
        &[
            Op::Gate(UnitaryOp::Swap, vec![2, 0]),
            Op::Measure("-ZIX".into()),
            Op::Gate(UnitaryOp::ControlledX, vec![2, 1]),
            Op::Gate(UnitaryOp::SqrtX, vec![0]),
            Op::ConditionalPauli("-ZXI".into(), vec![0], false),
            Op::Gate(UnitaryOp::ControlledZ, vec![2, 1]),
            Op::Measure("XIY".into()),
            Op::Gate(UnitaryOp::SqrtY, vec![1]),
            Op::Gate(UnitaryOp::ControlledX, vec![1, 2]),
            Op::Gate(UnitaryOp::Y, vec![2]),
        ],
        3,
    );
}

#[test]
fn phased_outcome_complete_tracks_dense_statevector() {
    let mut rng = rand::rng();
    for _trial in 0..600 {
        let n = 3usize;
        let ops = random_circuit(&mut rng, n);
        let sim = run_simulation(&ops, n);
        let n_random = sim.random_outcome_count();
        if n_random > 8 {
            continue;
        }
        for assignment in 0..(1usize << n_random) {
            let random_bits: Vec<bool> = (0..n_random).map(|bit| (assignment >> bit) & 1 == 1).collect();
            let outcomes = outcome_vector(&sim, &random_bits);
            let reference = dense_reference(&ops, &outcomes, n);
            let claimed = claimed_state(&sim, &random_bits, n);
            assert!(
                close(&claimed, &reference),
                "mismatch: ops=[{}] random_bits={random_bits:?}",
                describe(&ops)
            );
        }
    }
}
