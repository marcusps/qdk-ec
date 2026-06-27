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
    fn apply_pauli(&mut self, x: &[bool], z: &[bool], phase: i64) {
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
        self.amp = out;
    }
    fn apply_pauli_exp(&mut self, x: &[bool], z: &[bool], phase: i64) {
        let mut p_applied = self.amp.clone();
        let saved = std::mem::replace(&mut self.amp, p_applied.clone());
        self.apply_pauli(x, z, phase);
        p_applied = std::mem::replace(&mut self.amp, saved);
        for base in 0..self.amp.len() {
            self.amp[base] = self.amp[base].add(p_applied[base].mul(C::new(0.0, 1.0))).scale(ROOT_HALF);
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
    let n = phased.num_qubits();
    let rank = stabilizer_rank(phased);
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

fn stabilizer_rank(phased: &PhasedCliffordUnitary) -> usize {
    use binar::matrix::AlignedBitMatrix;
    use binar::{BitMatrix, Bitwise, BitwiseMut};
    use paulimer::clifford::Clifford;
    use paulimer::pauli::Pauli;
    let n = phased.num_qubits();
    let mut matrix = AlignedBitMatrix::zeros(n, n);
    for generator in 0..n {
        let image: DensePauli = phased.clifford().image_z(generator);
        for qubit in image.x_bits().support() {
            matrix.row_mut(generator).assign_index(qubit, true);
        }
    }
    BitMatrix::from_aligned(matrix).rank()
}

fn close(a: &[C], b: &[C]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.add(y.scale(-1.0)).abs2() < 1e-6)
}

#[test]
fn phased_clifford_tracks_dense_statevector() {
    use rand::RngExt;
    let mut rng = rand::rng();
    for _trial in 0..400 {
        let n = 4usize;
        let mut dense = Dense::zero(n);
        let mut phased = PhasedCliffordUnitary::identity(n);
        let mut log: Vec<String> = Vec::new();
        for _gate in 0..40 {
            let pick = rng.random_range(0..16);
            match pick {
                0 => {
                    let q = rng.random_range(0..n);
                    log.push(format!("H {q}"));
                    dense.apply1(q, h_mat());
                    phased.left_mul_hadamard(q);
                }
                1 => {
                    let q = rng.random_range(0..n);
                    log.push(format!("X {q}"));
                    dense.apply1(q, x_mat());
                    phased.left_mul_x(q);
                }
                2 => {
                    let q = rng.random_range(0..n);
                    log.push(format!("Y {q}"));
                    dense.apply1(q, y_mat());
                    phased.left_mul_y(q);
                }
                3 => {
                    let q = rng.random_range(0..n);
                    log.push(format!("Z {q}"));
                    dense.apply1(q, z_mat());
                    phased.left_mul_z(q);
                }
                4 => {
                    let q = rng.random_range(0..n);
                    log.push(format!("S {q}"));
                    dense.apply1(q, s_mat());
                    phased.left_mul_root_z(q);
                }
                5 => {
                    let q = rng.random_range(0..n);
                    log.push(format!("Sdg {q}"));
                    dense.apply1(q, sdg_mat());
                    phased.left_mul_root_z_inverse(q);
                }
                6 => {
                    let q = rng.random_range(0..n);
                    log.push(format!("RX {q}"));
                    dense.apply1(q, rt_x());
                    phased.left_mul_root_x(q);
                }
                7 => {
                    let q = rng.random_range(0..n);
                    log.push(format!("RXi {q}"));
                    dense.apply1(q, rt_x_inv());
                    phased.left_mul_root_x_inverse(q);
                }
                8 => {
                    let q = rng.random_range(0..n);
                    log.push(format!("RY {q}"));
                    dense.apply1(q, rt_y());
                    phased.left_mul_root_y(q);
                }
                9 => {
                    let q = rng.random_range(0..n);
                    log.push(format!("RYi {q}"));
                    dense.apply1(q, rt_y_inv());
                    phased.left_mul_root_y_inverse(q);
                }
                10 => {
                    let (a, b) = two_distinct(&mut rng, n);
                    log.push(format!("CX {a} {b}"));
                    dense.apply_cx(a, b);
                    phased.left_mul_cx(a, b);
                }
                11 => {
                    let (a, b) = two_distinct(&mut rng, n);
                    log.push(format!("CZ {a} {b}"));
                    dense.apply_cz(a, b);
                    phased.left_mul_cz(a, b);
                }
                12 => {
                    let (a, b) = two_distinct(&mut rng, n);
                    log.push(format!("SWAP {a} {b}"));
                    dense.apply_swap(a, b);
                    phased.left_mul_swap(a, b);
                }
                13 => {
                    let p = random_pauli_string(&mut rng, n);
                    log.push(format!("P {p}"));
                    let dp: DensePauli = p.parse().unwrap();
                    let (x, z, phase) = pauli_arrays(&dp, n);
                    dense.apply_pauli(&x, &z, phase);
                    phased.left_mul_pauli(&dp);
                }
                14 => {
                    let p = random_hermitian_pauli_string(&mut rng, n);
                    log.push(format!("PEXP {p}"));
                    let dp: DensePauli = p.parse().unwrap();
                    let (x, z, phase) = pauli_arrays(&dp, n);
                    dense.apply_pauli_exp(&x, &z, phase);
                    phased.left_mul_pauli_exp(&dp);
                }
                _ => {
                    let (a, b) = two_distinct(&mut rng, n);
                    log.push(format!("BELL {a} {b}"));
                    dense.apply1(a, h_mat());
                    dense.apply_cx(a, b);
                    phased.left_mul_prepare_bell(a, b);
                }
            }
        }
        let sv = statevector(&phased);
        assert!(close(&sv, &dense.amp), "mismatch log={log:?}\n tracker={sv:?}\n dense={:?}", dense.amp);
    }
}

fn two_distinct(rng: &mut impl rand::RngExt, n: usize) -> (usize, usize) {
    let a = rng.random_range(0..n);
    let mut b = rng.random_range(0..n);
    while b == a {
        b = rng.random_range(0..n);
    }
    (a, b)
}

fn random_pauli_string(rng: &mut impl rand::RngExt, n: usize) -> String {
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

fn random_hermitian_pauli_string(rng: &mut impl rand::RngExt, n: usize) -> String {
    let inner = random_pauli_string(rng, n);
    let body = inner.trim_start_matches(['-', 'i']);
    if rng.random_range(0..2) == 0 {
        format!("-{body}")
    } else {
        body.to_string()
    }
}

fn pauli_arrays(pauli: &DensePauli, n: usize) -> (Vec<bool>, Vec<bool>, i64) {
    use binar::Bitwise;
    use paulimer::pauli::Pauli;
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

