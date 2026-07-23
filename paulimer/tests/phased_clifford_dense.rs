#![allow(
    clippy::cast_precision_loss,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::too_many_lines
)]

use paulimer::clifford::PhasedCliffordUnitary;
use paulimer::{DensePauli, UnitaryOp};

use dense_oracle::{Dense, close, gate_matrix, pauli_arrays, statevector};

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
                    dense.apply1(qubit, gate_matrix(UnitaryOp::Hadamard));
                    phased.left_mul_hadamard(qubit);
                }
                1 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("X {qubit}"));
                    dense.apply1(qubit, gate_matrix(UnitaryOp::X));
                    phased.left_mul_x(qubit);
                }
                2 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("Y {qubit}"));
                    dense.apply1(qubit, gate_matrix(UnitaryOp::Y));
                    phased.left_mul_y(qubit);
                }
                3 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("Z {qubit}"));
                    dense.apply1(qubit, gate_matrix(UnitaryOp::Z));
                    phased.left_mul_z(qubit);
                }
                4 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("S {qubit}"));
                    dense.apply1(qubit, gate_matrix(UnitaryOp::SqrtZ));
                    phased.left_mul_root_z(qubit);
                }
                5 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("Sdg {qubit}"));
                    dense.apply1(qubit, gate_matrix(UnitaryOp::SqrtZInv));
                    phased.left_mul_root_z_inverse(qubit);
                }
                6 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("RX {qubit}"));
                    dense.apply1(qubit, gate_matrix(UnitaryOp::SqrtX));
                    phased.left_mul_root_x(qubit);
                }
                7 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("RXi {qubit}"));
                    dense.apply1(qubit, gate_matrix(UnitaryOp::SqrtXInv));
                    phased.left_mul_root_x_inverse(qubit);
                }
                8 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("RY {qubit}"));
                    dense.apply1(qubit, gate_matrix(UnitaryOp::SqrtY));
                    phased.left_mul_root_y(qubit);
                }
                9 => {
                    let qubit = rng.random_range(0..qubit_count);
                    log.push(format!("RYi {qubit}"));
                    dense.apply1(qubit, gate_matrix(UnitaryOp::SqrtYInv));
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
                    dense.apply1(first_qubit, gate_matrix(UnitaryOp::Hadamard));
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
