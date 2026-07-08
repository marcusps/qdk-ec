#![allow(
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::too_many_lines
)]

use paulimer::DensePauli;
use paulimer::clifford::PhasedCliffordUnitary;

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
            let src = if base & control_bit != 0 { base ^ target_bit } else { base };
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
    fn apply_pauli(&mut self, x_bits: &[bool], z_bits: &[bool], phase: i64) {
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
        self.amp = out;
    }
    fn apply_pauli_exp(&mut self, x_bits: &[bool], z_bits: &[bool], phase: i64) {
        let mut pauli_applied = self.amp.clone();
        let saved = std::mem::replace(&mut self.amp, pauli_applied.clone());
        self.apply_pauli(x_bits, z_bits, phase);
        pauli_applied = std::mem::replace(&mut self.amp, saved);
        for base in 0..self.amp.len() {
            self.amp[base] = self.amp[base].add(pauli_applied[base].mul(C::new(0.0, 1.0))).scale(ROOT_HALF);
        }
    }
}

fn h_mat() -> [[C; 2]; 2] {
    [[C::new(ROOT_HALF, 0.0), C::new(ROOT_HALF, 0.0)], [C::new(ROOT_HALF, 0.0), C::new(-ROOT_HALF, 0.0)]]
}
fn x_mat() -> [[C; 2]; 2] {
    [[C::ZERO, C::new(1.0, 0.0)], [C::new(1.0, 0.0), C::ZERO]]
}
fn y_mat() -> [[C; 2]; 2] {
    [[C::ZERO, C::new(0.0, -1.0)], [C::new(0.0, 1.0), C::ZERO]]
}
fn z_mat() -> [[C; 2]; 2] {
    [[C::new(1.0, 0.0), C::ZERO], [C::ZERO, C::new(-1.0, 0.0)]]
}
fn s_mat() -> [[C; 2]; 2] {
    [[C::new(1.0, 0.0), C::ZERO], [C::ZERO, C::new(0.0, 1.0)]]
}
fn sdg_mat() -> [[C; 2]; 2] {
    [[C::new(1.0, 0.0), C::ZERO], [C::ZERO, C::new(0.0, -1.0)]]
}
fn rt_x() -> [[C; 2]; 2] {
    [[zeta8(1).scale(ROOT_HALF), zeta8(7).scale(ROOT_HALF)], [zeta8(7).scale(ROOT_HALF), zeta8(1).scale(ROOT_HALF)]]
}
fn rt_x_inv() -> [[C; 2]; 2] {
    [[zeta8(7).scale(ROOT_HALF), zeta8(1).scale(ROOT_HALF)], [zeta8(1).scale(ROOT_HALF), zeta8(7).scale(ROOT_HALF)]]
}
fn rt_y() -> [[C; 2]; 2] {
    [[zeta8(1).scale(ROOT_HALF), zeta8(5).scale(ROOT_HALF)], [zeta8(1).scale(ROOT_HALF), zeta8(1).scale(ROOT_HALF)]]
}
fn rt_y_inv() -> [[C; 2]; 2] {
    [[zeta8(7).scale(ROOT_HALF), zeta8(7).scale(ROOT_HALF)], [zeta8(3).scale(ROOT_HALF), zeta8(7).scale(ROOT_HALF)]]
}

fn statevector(phased: &PhasedCliffordUnitary) -> Vec<C> {
    let qubit_count = phased.num_qubits();
    let rank = stabilizer_rank(phased);
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

fn stabilizer_rank(phased: &PhasedCliffordUnitary) -> usize {
    use binar::matrix::AlignedBitMatrix;
    use binar::{BitMatrix, Bitwise, BitwiseMut};
    use paulimer::clifford::Clifford;
    use paulimer::pauli::Pauli;
    let qubit_count = phased.num_qubits();
    let mut matrix = AlignedBitMatrix::zeros(qubit_count, qubit_count);
    for generator in 0..qubit_count {
        let image: DensePauli = phased.clifford().image_z(generator);
        for qubit in image.x_bits().support() {
            matrix.row_mut(generator).assign_index(qubit, true);
        }
    }
    BitMatrix::from_aligned(matrix).rank()
}

fn close(left: &[C], right: &[C]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left_value, right_value)| left_value.add(right_value.scale(-1.0)).abs2() < 1e-6)
}

#[test]
fn phased_clifford_tracks_dense_statevector() {
    use rand::RngExt;
    let mut rng = rand::rng();
    for _trial in 0..400 {
        let qubit_count = 4usize;
        let mut dense = Dense::zero(qubit_count);
        let mut phased = PhasedCliffordUnitary::identity(qubit_count);
        let mut log: Vec<String> = Vec::new();
        for _gate in 0..40 {
            let pick = rng.random_range(0..16);
            match pick {
                0 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("H {qubit}"));
                    dense.apply1(qubit, h_mat());
                    phased.left_mul_hadamard(qubit);
                }
                1 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("X {qubit}"));
                    dense.apply1(qubit, x_mat());
                    phased.left_mul_x(qubit);
                }
                2 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("Y {qubit}"));
                    dense.apply1(qubit, y_mat());
                    phased.left_mul_y(qubit);
                }
                3 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("Z {qubit}"));
                    dense.apply1(qubit, z_mat());
                    phased.left_mul_z(qubit);
                }
                4 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("S {qubit}"));
                    dense.apply1(qubit, s_mat());
                    phased.left_mul_root_z(qubit);
                }
                5 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("Sdg {qubit}"));
                    dense.apply1(qubit, sdg_mat());
                    phased.left_mul_root_z_inverse(qubit);
                }
                6 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("RX {qubit}"));
                    dense.apply1(qubit, rt_x());
                    phased.left_mul_root_x(qubit);
                }
                7 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("RXi {qubit}"));
                    dense.apply1(qubit, rt_x_inv());
                    phased.left_mul_root_x_inverse(qubit);
                }
                8 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("RY {qubit}"));
                    dense.apply1(qubit, rt_y());
                    phased.left_mul_root_y(qubit);
                }
                9 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("RYi {qubit}"));
                    dense.apply1(qubit, rt_y_inv());
                    phased.left_mul_root_y_inverse(qubit);
                }
                10 => {
                    let (first_qubit, second_qubit) = two_distinct(&mut rng, qubit_count);
                    log.push(format!("CX {first_qubit} {second_qubit}"));
                    dense.apply_cx(first_qubit, second_qubit);
                    phased.left_mul_cx(first_qubit, second_qubit);
                }
                11 => {
                    let (first_qubit, second_qubit) = two_distinct(&mut rng, qubit_count);
                    log.push(format!("CZ {first_qubit} {second_qubit}"));
                    dense.apply_cz(first_qubit, second_qubit);
                    phased.left_mul_cz(first_qubit, second_qubit);
                }
                12 => {
                    let (first_qubit, second_qubit) = two_distinct(&mut rng, qubit_count);
                    log.push(format!("SWAP {first_qubit} {second_qubit}"));
                    dense.apply_swap(first_qubit, second_qubit);
                    phased.left_mul_swap(first_qubit, second_qubit);
                }
                13 => {
                    let pauli_string = random_pauli_string(&mut rng, qubit_count);
                    log.push(format!("P {pauli_string}"));
                    let pauli: DensePauli = pauli_string.parse().unwrap();
                    let (x_bits, z_bits, phase) = pauli_arrays(&pauli, qubit_count);
                    dense.apply_pauli(&x_bits, &z_bits, phase);
                    phased.left_mul_pauli(&pauli);
                }
                14 => {
                    let pauli_string = random_hermitian_pauli_string(&mut rng, qubit_count);
                    log.push(format!("PEXP {pauli_string}"));
                    let pauli: DensePauli = pauli_string.parse().unwrap();
                    let (x_bits, z_bits, phase) = pauli_arrays(&pauli, qubit_count);
                    dense.apply_pauli_exp(&x_bits, &z_bits, phase);
                    phased.left_mul_pauli_exp(&pauli);
                }
                _ => {
                    let (first_qubit, second_qubit) = two_distinct(&mut rng, qubit_count);
                    log.push(format!("BELL {first_qubit} {second_qubit}"));
                    dense.apply1(first_qubit, h_mat());
                    dense.apply_cx(first_qubit, second_qubit);
                    phased.left_mul_prepare_bell(first_qubit, second_qubit);
                }
            }
        }
        let tracked_statevector = statevector(&phased);
        assert!(
            close(&tracked_statevector, &dense.amp),
            "mismatch log={log:?}\n tracker={tracked_statevector:?}\n dense={:?}",
            dense.amp
        );
    }
}

fn two_distinct(rng: &mut impl rand::RngExt, qubit_count: usize) -> (usize, usize) {
    let first = rng.random_range(0..qubit_count);
    let mut second = rng.random_range(0..qubit_count);
    while second == first {
        second = rng.random_range(0..qubit_count);
    }
    (first, second)
}

fn random_pauli_string(rng: &mut impl rand::RngExt, qubit_count: usize) -> String {
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
        let phase: i64 = rng.random_range(0..4);
        let prefix = match phase {
            0 => "",
            1 => "i",
            2 => "-",
            _ => "-i",
        };
        return format!("{prefix}{letters}");
    }
}

fn random_hermitian_pauli_string(rng: &mut impl rand::RngExt, qubit_count: usize) -> String {
    let inner = random_pauli_string(rng, qubit_count);
    let body = inner.trim_start_matches(['-', 'i']);
    if rng.random_range(0..2) == 0 {
        format!("-{body}")
    } else {
        body.to_string()
    }
}

fn pauli_arrays(pauli: &DensePauli, qubit_count: usize) -> (Vec<bool>, Vec<bool>, i64) {
    use binar::Bitwise;
    use paulimer::pauli::Pauli;
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

