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
    let angle = std::f64::consts::FRAC_PI_4 * (k.rem_euclid(8)) as f64;
    C::new(angle.cos(), angle.sin())
}

const ROOT_HALF: f64 = std::f64::consts::FRAC_1_SQRT_2;

struct Dense {
    qubit_count: usize,
    amp: Vec<C>,
}

impl Dense {
    fn zero(qubit_count: usize) -> Dense {
        let mut amp = vec![C::ZERO; 1 << qubit_count];
        amp[0] = C::new(1.0, 0.0);
        Dense { qubit_count, amp }
    }
    fn apply1(&mut self, qubit: usize, matrix: [[C; 2]; 2]) {
        let bit = 1usize << (self.qubit_count - 1 - qubit);
        for base in 0..(1 << self.qubit_count) {
            if base & bit == 0 {
                let amplitude_0 = self.amp[base];
                let amplitude_1 = self.amp[base | bit];
                self.amp[base] = matrix[0][0].mul(amplitude_0).add(matrix[0][1].mul(amplitude_1));
                self.amp[base | bit] = matrix[1][0].mul(amplitude_0).add(matrix[1][1].mul(amplitude_1));
            }
        }
    }
    fn apply_cx(&mut self, control: usize, target: usize) {
        let control_bit = 1usize << (self.qubit_count - 1 - control);
        let target_bit = 1usize << (self.qubit_count - 1 - target);
        let mut out = self.amp.clone();
        for base in 0..(1 << self.qubit_count) {
            let src = if base & control_bit != 0 {
                base ^ target_bit
            } else {
                base
            };
            out[base] = self.amp[src];
        }
        self.amp = out;
    }
    fn apply_cz(&mut self, first_qubit: usize, second_qubit: usize) {
        let first_bit = 1usize << (self.qubit_count - 1 - first_qubit);
        let second_bit = 1usize << (self.qubit_count - 1 - second_qubit);
        for base in 0..(1 << self.qubit_count) {
            if base & first_bit != 0 && base & second_bit != 0 {
                self.amp[base] = self.amp[base].scale(-1.0);
            }
        }
    }
    fn apply_swap(&mut self, first_qubit: usize, second_qubit: usize) {
        let first_bit = 1usize << (self.qubit_count - 1 - first_qubit);
        let second_bit = 1usize << (self.qubit_count - 1 - second_qubit);
        let mut out = self.amp.clone();
        for base in 0..(1 << self.qubit_count) {
            let bit_first = usize::from(base & first_bit != 0);
            let bit_second = usize::from(base & second_bit != 0);
            let mut src = base & !first_bit & !second_bit;
            if bit_second != 0 {
                src |= first_bit;
            }
            if bit_first != 0 {
                src |= second_bit;
            }
            out[base] = self.amp[src];
        }
        self.amp = out;
    }
    fn pauli_applied(&self, x_bits: &[bool], z_bits: &[bool], phase: i64) -> Vec<C> {
        let mut out = vec![C::ZERO; self.amp.len()];
        let x_mask: usize = (0..self.qubit_count)
            .filter(|&qubit| x_bits[qubit])
            .map(|qubit| 1usize << (self.qubit_count - 1 - qubit))
            .sum();
        for base in 0..(1 << self.qubit_count) {
            let target = base ^ x_mask;
            let mut sign_parity = 0i64;
            for qubit in 0..self.qubit_count {
                if z_bits[qubit] && (base >> (self.qubit_count - 1 - qubit)) & 1 == 1 {
                    sign_parity ^= 1;
                }
            }
            let coeff = zeta8(2 * phase + 4 * sign_parity);
            out[target] = out[target].add(self.amp[base].mul(coeff));
        }
        out
    }
    fn apply_pauli(&mut self, x_bits: &[bool], z_bits: &[bool], phase: i64) {
        self.amp = self.pauli_applied(x_bits, z_bits, phase);
    }
    fn apply_pauli_exp(&mut self, x_bits: &[bool], z_bits: &[bool], phase: i64) {
        let pauli_applied = self.pauli_applied(x_bits, z_bits, phase);
        for base in 0..self.amp.len() {
            self.amp[base] = self.amp[base]
                .add(pauli_applied[base].mul(C::new(0.0, 1.0)))
                .scale(ROOT_HALF);
        }
    }
    fn apply_controlled_pauli(
        &mut self,
        first_pauli: &(Vec<bool>, Vec<bool>, i64),
        second_pauli: &(Vec<bool>, Vec<bool>, i64),
    ) {
        // controlled_pauli(first, second) = (I + first)/2 + (I - first)/2 * second
        let first_pauli_applied = self.pauli_applied(&first_pauli.0, &first_pauli.1, first_pauli.2);
        let plus: Vec<C> = (0..self.amp.len())
            .map(|index| self.amp[index].add(first_pauli_applied[index]).scale(0.5))
            .collect();
        let minus = Dense {
            qubit_count: self.qubit_count,
            amp: (0..self.amp.len())
                .map(|index| self.amp[index].add(first_pauli_applied[index].scale(-1.0)).scale(0.5))
                .collect(),
        };
        let second_pauli_applied_to_minus = minus.pauli_applied(&second_pauli.0, &second_pauli.1, second_pauli.2);
        for index in 0..self.amp.len() {
            self.amp[index] = plus[index].add(second_pauli_applied_to_minus[index]);
        }
    }
    fn project(&mut self, x_bits: &[bool], z_bits: &[bool], phase: i64, outcome: bool) {
        let pauli_applied = self.pauli_applied(x_bits, z_bits, phase);
        let sign = if outcome { -1.0 } else { 1.0 };
        for index in 0..self.amp.len() {
            self.amp[index] = self.amp[index].add(pauli_applied[index].scale(sign)).scale(0.5);
        }
        normalize(&mut self.amp);
    }
}

fn normalize(amp: &mut [C]) {
    let norm = amp.iter().map(|amplitude| amplitude.abs2()).sum::<f64>().sqrt();
    assert!(norm > 1e-9, "attempted to normalize a vanishing state");
    let inv = 1.0 / norm;
    for amplitude in amp.iter_mut() {
        *amplitude = amplitude.scale(inv);
    }
}

fn gate_matrix(op: UnitaryOp) -> [[C; 2]; 2] {
    let root_half = ROOT_HALF;
    match op {
        UnitaryOp::Hadamard => [
            [C::new(root_half, 0.0), C::new(root_half, 0.0)],
            [C::new(root_half, 0.0), C::new(-root_half, 0.0)],
        ],
        UnitaryOp::X => [[C::ZERO, C::new(1.0, 0.0)], [C::new(1.0, 0.0), C::ZERO]],
        UnitaryOp::Y => [[C::ZERO, C::new(0.0, -1.0)], [C::new(0.0, 1.0), C::ZERO]],
        UnitaryOp::Z => [[C::new(1.0, 0.0), C::ZERO], [C::ZERO, C::new(-1.0, 0.0)]],
        UnitaryOp::SqrtZ => [[C::new(1.0, 0.0), C::ZERO], [C::ZERO, C::new(0.0, 1.0)]],
        UnitaryOp::SqrtZInv => [[C::new(1.0, 0.0), C::ZERO], [C::ZERO, C::new(0.0, -1.0)]],
        UnitaryOp::SqrtX => [
            [zeta8(1).scale(root_half), zeta8(7).scale(root_half)],
            [zeta8(7).scale(root_half), zeta8(1).scale(root_half)],
        ],
        UnitaryOp::SqrtXInv => [
            [zeta8(7).scale(root_half), zeta8(1).scale(root_half)],
            [zeta8(1).scale(root_half), zeta8(7).scale(root_half)],
        ],
        UnitaryOp::SqrtY => [
            [zeta8(1).scale(root_half), zeta8(5).scale(root_half)],
            [zeta8(1).scale(root_half), zeta8(1).scale(root_half)],
        ],
        UnitaryOp::SqrtYInv => [
            [zeta8(7).scale(root_half), zeta8(7).scale(root_half)],
            [zeta8(3).scale(root_half), zeta8(7).scale(root_half)],
        ],
        other => panic!("gate_matrix called on multi-qubit op {other:?}"),
    }
}

fn statevector(phased: &PhasedCliffordUnitary) -> Vec<C> {
    use binar::matrix::AlignedBitMatrix;
    use binar::{BitMatrix, BitwiseMut};
    let qubit_count = phased.num_qubits();
    let mut matrix = AlignedBitMatrix::zeros(qubit_count, qubit_count);
    for generator in 0..qubit_count {
        let image: DensePauli = phased.clifford().image_z(generator);
        for qubit in image.x_bits().support() {
            matrix.row_mut(generator).assign_index(qubit, true);
        }
    }
    let rank = BitMatrix::from_aligned(matrix).rank();
    let mag = (0.5f64).powf(rank as f64 / 2.0);
    let mut out = vec![C::ZERO; 1 << qubit_count];
    for idx in 0..(1usize << qubit_count) {
        let mut value = 0usize;
        for qubit in 0..qubit_count {
            if (idx >> (qubit_count - 1 - qubit)) & 1 == 1 {
                value |= 1usize << qubit;
            }
        }
        if let Some(exp) = phased.state_amplitude_phase_exponent_usize(value) {
            out[idx] = zeta8(i64::from(exp)).scale(mag);
        }
    }
    out
}

fn pauli_arrays(pauli: &DensePauli, qubit_count: usize) -> (Vec<bool>, Vec<bool>, i64) {
    let mut x_bits = vec![false; qubit_count];
    let mut z_bits = vec![false; qubit_count];
    for qubit in pauli.x_bits().support() {
        x_bits[qubit] = true;
    }
    for qubit in pauli.z_bits().support() {
        z_bits[qubit] = true;
    }
    (x_bits, z_bits, i64::from(pauli.xz_phase_exponent()))
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

fn random_hermitian_pauli(rng: &mut impl RngExt, qubit_count: usize) -> String {
    loop {
        let mut letters = String::new();
        let mut any = false;
        for _ in 0..qubit_count {
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

fn two_distinct(rng: &mut impl RngExt, qubit_count: usize) -> (usize, usize) {
    let first = rng.random_range(0..qubit_count);
    let mut second = rng.random_range(0..qubit_count);
    while second == first {
        second = rng.random_range(0..qubit_count);
    }
    (first, second)
}

fn random_circuit(rng: &mut impl RngExt, qubit_count: usize) -> Vec<Op> {
    let single_qubit_gates = [
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
    let two_qubit_gates = [UnitaryOp::ControlledX, UnitaryOp::ControlledZ, UnitaryOp::Swap];
    let mut ops = Vec::new();
    let mut measurement_count = 0usize;
    let op_count = rng.random_range(6..14);
    for _ in 0..op_count {
        match rng.random_range(0..7) {
            0 => {
                let qubit = rng.random_range(0..qubit_count);
                ops.push(Op::Gate(
                    single_qubit_gates[rng.random_range(0..single_qubit_gates.len())],
                    vec![qubit],
                ));
            }
            1 => {
                let (first_qubit, second_qubit) = two_distinct(rng, qubit_count);
                ops.push(Op::Gate(
                    two_qubit_gates[rng.random_range(0..two_qubit_gates.len())],
                    vec![first_qubit, second_qubit],
                ));
            }
            2 => ops.push(Op::Pauli(random_hermitian_pauli(rng, qubit_count))),
            3 => ops.push(Op::PauliExp(random_hermitian_pauli(rng, qubit_count))),
            4 => {
                let first_pauli_string = random_hermitian_pauli(rng, qubit_count);
                let mut second_pauli_string = random_hermitian_pauli(rng, qubit_count);
                let mut guard = 0;
                loop {
                    let first_sparse_pauli: SparsePauli = first_pauli_string.parse().unwrap();
                    let second_sparse_pauli: SparsePauli = second_pauli_string.parse().unwrap();
                    if commutes_with(&first_sparse_pauli, &second_sparse_pauli) {
                        break;
                    }
                    second_pauli_string = random_hermitian_pauli(rng, qubit_count);
                    guard += 1;
                    if guard > 32 {
                        break;
                    }
                }
                let first_sparse_pauli: SparsePauli = first_pauli_string.parse().unwrap();
                let second_sparse_pauli: SparsePauli = second_pauli_string.parse().unwrap();
                if commutes_with(&first_sparse_pauli, &second_sparse_pauli) {
                    ops.push(Op::ControlledPauli(first_pauli_string, second_pauli_string));
                }
            }
            5 => {
                if measurement_count > 0 && rng.random_range(0..2) == 0 {
                    let mut outcomes = Vec::new();
                    for outcome_index in 0..measurement_count {
                        if rng.random_range(0..2) == 0 {
                            outcomes.push(outcome_index);
                        }
                    }
                    if !outcomes.is_empty() {
                        ops.push(Op::ConditionalPauli(
                            random_hermitian_pauli(rng, qubit_count),
                            outcomes,
                            rng.random_range(0..2) == 1,
                        ));
                    }
                }
            }
            _ => {
                if measurement_count < 5 {
                    ops.push(Op::Measure(random_hermitian_pauli(rng, qubit_count)));
                    measurement_count += 1;
                }
            }
        }
    }
    ops
}

fn run_simulation(ops: &[Op], qubit_count: usize) -> PhasedOutcomeCompleteSimulation {
    let mut sim = PhasedOutcomeCompleteSimulation::new(qubit_count);
    for op in ops {
        match op {
            Op::Gate(gate, support) => sim.unitary_op(*gate, support),
            Op::Pauli(pauli) => sim.pauli(&pauli.parse().unwrap()),
            Op::PauliExp(pauli) => sim.pauli_exp(&pauli.parse().unwrap()),
            Op::ControlledPauli(first_pauli, second_pauli) => {
                sim.controlled_pauli(&first_pauli.parse().unwrap(), &second_pauli.parse().unwrap());
            }
            Op::ConditionalPauli(pauli, outcomes, parity) => {
                sim.conditional_pauli(&pauli.parse().unwrap(), outcomes, *parity);
            }
            Op::Measure(pauli) => {
                sim.measure(&pauli.parse().unwrap());
            }
        }
    }
    sim
}

fn dense_reference(ops: &[Op], outcome_bits: &[bool], qubit_count: usize) -> Vec<C> {
    let mut dense = Dense::zero(qubit_count);
    let mut measurement_index = 0usize;
    for op in ops {
        match op {
            Op::Gate(gate, support) => match gate {
                UnitaryOp::ControlledX => dense.apply_cx(support[0], support[1]),
                UnitaryOp::ControlledZ => dense.apply_cz(support[0], support[1]),
                UnitaryOp::Swap => dense.apply_swap(support[0], support[1]),
                other => dense.apply1(support[0], gate_matrix(*other)),
            },
            Op::Pauli(pauli) => {
                let (x_bits, z_bits, phase) = pauli_arrays(&pauli.parse::<DensePauli>().unwrap(), qubit_count);
                dense.apply_pauli(&x_bits, &z_bits, phase);
            }
            Op::PauliExp(pauli) => {
                let (x_bits, z_bits, phase) = pauli_arrays(&pauli.parse::<DensePauli>().unwrap(), qubit_count);
                dense.apply_pauli_exp(&x_bits, &z_bits, phase);
            }
            Op::ControlledPauli(first_pauli, second_pauli) => {
                let first_arrays = pauli_arrays(&first_pauli.parse::<DensePauli>().unwrap(), qubit_count);
                let second_arrays = pauli_arrays(&second_pauli.parse::<DensePauli>().unwrap(), qubit_count);
                dense.apply_controlled_pauli(&first_arrays, &second_arrays);
            }
            Op::ConditionalPauli(pauli, outcomes, parity) => {
                let condition = outcomes
                    .iter()
                    .fold(false, |acc, &outcome_index| acc ^ outcome_bits[outcome_index]);
                if condition == *parity {
                    let (x_bits, z_bits, phase) = pauli_arrays(&pauli.parse::<DensePauli>().unwrap(), qubit_count);
                    dense.apply_pauli(&x_bits, &z_bits, phase);
                }
            }
            Op::Measure(pauli) => {
                let (x_bits, z_bits, phase) = pauli_arrays(&pauli.parse::<DensePauli>().unwrap(), qubit_count);
                dense.project(&x_bits, &z_bits, phase, outcome_bits[measurement_index]);
                measurement_index += 1;
            }
        }
    }
    dense.amp
}

fn claimed_state(sim: &PhasedOutcomeCompleteSimulation, random_bits: &[bool], qubit_count: usize) -> Vec<C> {
    let encoder = sim.phased_state_encoder();
    let base = statevector(&encoder);

    let sign_matrix = sim.aligned_sign_matrix();
    let random_outcome_count = sim.random_outcome_count();
    let mut register = AlignedBitVec::zeros(qubit_count);
    for qubit in 0..qubit_count {
        let mut bit = false;
        for column in 0..random_outcome_count {
            if random_bits[column] && sign_matrix.row(qubit).index(column) {
                bit = !bit;
            }
        }
        register.assign_index(qubit, bit);
    }

    let image = encoder.clifford().image_x_bits(&register);
    let (x_bits, z_bits, phase) = pauli_arrays(&image, qubit_count);
    let mut dense = Dense { qubit_count, amp: base };
    dense.apply_pauli(&x_bits, &z_bits, phase);

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
    let random_outcome_count = sim.random_outcome_count();
    (0..sim.outcome_count())
        .map(|row| {
            let mut bit = shift.index(row);
            for column in 0..random_outcome_count {
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
            Op::Gate(gate, support) => format!("Gate({gate:?},{support:?})"),
            Op::Pauli(pauli) => format!("Pauli({pauli})"),
            Op::PauliExp(pauli) => format!("PauliExp({pauli})"),
            Op::ControlledPauli(first_pauli, second_pauli) => format!("CPauli({first_pauli},{second_pauli})"),
            Op::ConditionalPauli(pauli, outcomes, parity) => format!("CondPauli({pauli},{outcomes:?},{parity})"),
            Op::Measure(pauli) => format!("Measure({pauli})"),
        })
        .collect::<Vec<_>>()
        .join(" | ")
}

fn close(left: &[C], right: &[C]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left_value, right_value)| left_value.add(right_value.scale(-1.0)).abs2() < 1e-6)
}

fn verify(ops: &[Op], qubit_count: usize) {
    let sim = run_simulation(ops, qubit_count);
    let random_outcome_count = sim.random_outcome_count();
    assert!(random_outcome_count <= 12, "too many random bits to enumerate");
    for assignment in 0..(1usize << random_outcome_count) {
        let random_bits: Vec<bool> = (0..random_outcome_count)
            .map(|bit| (assignment >> bit) & 1 == 1)
            .collect();
        let outcomes = outcome_vector(&sim, &random_bits);
        let reference = dense_reference(ops, &outcomes, qubit_count);
        let claimed = claimed_state(&sim, &random_bits, qubit_count);
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
        &[
            Op::Measure("X".into()),
            Op::ConditionalPauli("Z".into(), vec![0], false),
        ],
        1,
    );
    verify(
        &[Op::Measure("Y".into()), Op::ConditionalPauli("X".into(), vec![0], true)],
        1,
    );
}

#[test]
fn controlled_pauli_no_randomness() {
    verify(
        &[
            Op::Gate(UnitaryOp::Hadamard, vec![0]),
            Op::ControlledPauli("ZI".into(), "IX".into()),
        ],
        2,
    );
    verify(
        &[
            Op::Gate(UnitaryOp::Hadamard, vec![0]),
            Op::ControlledPauli("ZZ".into(), "XX".into()),
        ],
        2,
    );
    verify(
        &[
            Op::Gate(UnitaryOp::SqrtX, vec![0]),
            Op::ControlledPauli("YI".into(), "IY".into()),
        ],
        2,
    );
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
        &[
            Op::Measure("X".into()),
            Op::Gate(UnitaryOp::SqrtX, vec![0]),
            Op::Measure("X".into()),
        ],
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
        let qubit_count = 3usize;
        let ops = random_circuit(&mut rng, qubit_count);
        let sim = run_simulation(&ops, qubit_count);
        let random_outcome_count = sim.random_outcome_count();
        if random_outcome_count > 8 {
            continue;
        }
        for assignment in 0..(1usize << random_outcome_count) {
            let random_bits: Vec<bool> = (0..random_outcome_count)
                .map(|bit| (assignment >> bit) & 1 == 1)
                .collect();
            let outcomes = outcome_vector(&sim, &random_bits);
            let reference = dense_reference(&ops, &outcomes, qubit_count);
            let claimed = claimed_state(&sim, &random_bits, qubit_count);
            assert!(
                close(&claimed, &reference),
                "mismatch: ops=[{}] random_bits={random_bits:?}",
                describe(&ops)
            );
        }
    }
}
