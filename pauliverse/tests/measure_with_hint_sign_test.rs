//! Sign-correctness of hinted Pauli measurements (`measure_with_hint`).
//!
//! Defining property of a projective measurement: once `P` has been measured, `P` is a stabilizer of
//! the post-measurement state whose sign equals the reported outcome. In particular, this must hold
//! no matter which anti-commuting `hint` is supplied — including hints carrying a negative sign,
//! which drive the `(-1)^alpha` branch of case 5 of Algorithm 4.2.

use paulimer::UnitaryOp;
use paulimer::clifford::{Clifford, PhasedCliffordUnitary};
use paulimer::pauli::{SparsePauli, as_sparse};
use pauliverse::{PhasedOutcomeCompleteSimulation, Simulation};
use proptest::prelude::*;
use rand::{RngExt, SeedableRng};

/// Builds a random Clifford state-preparation on `qubit_count` qubits from `seed`, applying the same
/// gates to a [`PhasedOutcomeCompleteSimulation`] and to a mirror [`PhasedCliffordUnitary`] so a
/// genuine stabilizer of the prepared state can be extracted from the mirror.
fn prepare_random_state(
    qubit_count: usize,
    seed: u64,
    gate_count: usize,
) -> (PhasedOutcomeCompleteSimulation, PhasedCliffordUnitary) {
    let mut sim = PhasedOutcomeCompleteSimulation::new(qubit_count);
    let mut mirror = PhasedCliffordUnitary::identity(qubit_count);
    let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
    for _ in 0..gate_count {
        match rng.random_range(0..4) {
            0 => apply(
                &mut sim,
                &mut mirror,
                UnitaryOp::Hadamard,
                &[rng.random_range(0..qubit_count)],
            ),
            1 => apply(
                &mut sim,
                &mut mirror,
                UnitaryOp::SqrtZ,
                &[rng.random_range(0..qubit_count)],
            ),
            2 => apply(
                &mut sim,
                &mut mirror,
                UnitaryOp::SqrtX,
                &[rng.random_range(0..qubit_count)],
            ),
            _ if qubit_count >= 2 => {
                let control = rng.random_range(0..qubit_count);
                let mut target = rng.random_range(0..qubit_count);
                while target == control {
                    target = rng.random_range(0..qubit_count);
                }
                apply(&mut sim, &mut mirror, UnitaryOp::ControlledX, &[control, target]);
            }
            _ => apply(
                &mut sim,
                &mut mirror,
                UnitaryOp::Hadamard,
                &[rng.random_range(0..qubit_count)],
            ),
        }
    }
    (sim, mirror)
}

fn apply(
    sim: &mut PhasedOutcomeCompleteSimulation,
    mirror: &mut PhasedCliffordUnitary,
    op: UnitaryOp,
    support: &[usize],
) {
    sim.unitary_op(op, support);
    mirror.left_mul(op, support);
}

proptest! {
    /// For a random stabilizer state, measuring the destabilizer `X`-image of qubit `q` while hinting
    /// with the (optionally negated) stabilizer `Z`-image of `q` must leave the observable a
    /// stabilizer whose conditional sign matches the reported outcome.
    #[test]
    fn measure_with_hint_outcome_sign_is_correct(
        qubit_count in 1usize..4,
        seed in any::<u64>(),
        gate_count in 0usize..12,
        negate_hint in any::<bool>(),
        target_selector in 0usize..4,
    ) {
        let (mut sim, mirror) = prepare_random_state(qubit_count, seed, gate_count);
        let target = target_selector % qubit_count;

        // `image_z(target)` is a stabilizer of the prepared state; `image_x(target)` anti-commutes
        // with it, so measuring the latter is a genuine (random) case-5 measurement.
        let stabilizer: SparsePauli = as_sparse(&mirror.clifford().image_z(target));
        let observable: SparsePauli = as_sparse(&mirror.clifford().image_x(target));
        let hint = if negate_hint { -stabilizer } else { stabilizer };

        let outcome = sim.measure_with_hint(&observable, &hint);

        prop_assert!(
            sim.is_stabilizer_with_conditional_sign(&observable, &[outcome]),
            "measured observable {observable} is not a stabilizer with the reported outcome sign \
             (qubit_count={qubit_count}, seed={seed}, gate_count={gate_count}, \
             negate_hint={negate_hint}, target={target})"
        );
    }
}
