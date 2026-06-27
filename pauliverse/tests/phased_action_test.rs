use paulimer::core::z;
use paulimer::pauli::SparsePauli;
use paulimer::{PositionedPauliObservable, UnitaryOp};
use pauliverse::action::{ActionsInequivalenceReason, phased_action_from_simulation, phased_action_of};
use pauliverse::phased_outcome_complete_simulation::PhasedOutcomeCompleteSimulation;
use pauliverse::{Circuit, CircuitBuilder, QubitId, Simulation};

fn build_circuit(build: impl FnOnce(&mut CircuitBuilder)) -> Circuit {
    let mut builder = CircuitBuilder::new();
    build(&mut builder);
    builder.into()
}

fn sparse(observable: &[PositionedPauliObservable]) -> SparsePauli {
    observable.into()
}

/// `exp(iα Z₀Z₁)` represented as a symbolic rotation gadget: allocate a random branch bit, then
/// conditionally apply `Z₀Z₁` on the odd branch.
fn zz_rotation() -> (Circuit, Vec<QubitId>, Vec<QubitId>) {
    let circuit = build_circuit(|builder| {
        let branch = builder.allocate_random_bit();
        builder.conditional_pauli(&sparse(&[z(0), z(1)]), &[branch], true);
    });
    (circuit, vec![0, 1], vec![0, 1])
}

/// `CNOT₀₁ · exp(iα Z₁) · CNOT₀₁`, which should equal `exp(iα Z₀Z₁)` as a channel.
fn cnot_conjugated_z_rotation() -> (Circuit, Vec<QubitId>, Vec<QubitId>) {
    let circuit = build_circuit(|builder| {
        builder.unitary_op(UnitaryOp::ControlledX, &[0, 1]);
        let branch = builder.allocate_random_bit();
        builder.conditional_pauli(&sparse(&[z(1)]), &[branch], true);
        builder.unitary_op(UnitaryOp::ControlledX, &[0, 1]);
    });
    (circuit, vec![0, 1], vec![0, 1])
}

/// `exp(iα Z₁)` on its own, which differs from `exp(iα Z₀Z₁)` in symplectic action.
fn z_rotation() -> (Circuit, Vec<QubitId>, Vec<QubitId>) {
    let circuit = build_circuit(|builder| {
        let branch = builder.allocate_random_bit();
        builder.conditional_pauli(&sparse(&[z(1)]), &[branch], true);
    });
    (circuit, vec![0, 1], vec![0, 1])
}

/// Conditional `±Z₀` gadget: the two signs share the same symplectic action but differ only in the
/// branch phase of the odd branch.
fn signed_z_rotation(negate: bool) -> (Circuit, Vec<QubitId>, Vec<QubitId>) {
    let circuit = build_circuit(|builder| {
        let branch = builder.allocate_random_bit();
        let observable = if negate { -sparse(&[z(0)]) } else { sparse(&[z(0)]) };
        builder.conditional_pauli(&observable, &[branch], true);
    });
    (circuit, vec![0], vec![0])
}

#[test]
fn zz_rotation_equals_cnot_conjugated_z_rotation() {
    let (direct, direct_input, direct_output) = zz_rotation();
    let (conjugated, conjugated_input, conjugated_output) = cnot_conjugated_z_rotation();

    let direct_action = phased_action_of(&direct, &direct_input, &direct_output).expect("direct action");
    let conjugated_action =
        phased_action_of(&conjugated, &conjugated_input, &conjugated_output).expect("conjugated action");

    direct_action
        .is_equivalent(&conjugated_action)
        .expect("symbolic rotations must agree including branch phase");
    conjugated_action
        .is_equivalent(&direct_action)
        .expect("equivalence must be symmetric");
}

#[test]
fn zz_rotation_differs_from_z_rotation() {
    let (zz, zz_input, zz_output) = zz_rotation();
    let (single, single_input, single_output) = z_rotation();

    let zz_action = phased_action_of(&zz, &zz_input, &zz_output).expect("zz action");
    let single_action = phased_action_of(&single, &single_input, &single_output).expect("z action");

    let reasons = zz_action
        .is_equivalent(&single_action)
        .expect_err("rotations with different supports must differ");
    assert!(!reasons.is_empty());
}

#[test]
fn opposite_sign_rotations_differ_only_in_relative_phase() {
    let (positive, positive_input, positive_output) = signed_z_rotation(false);
    let (negative, negative_input, negative_output) = signed_z_rotation(true);

    let positive_action = phased_action_of(&positive, &positive_input, &positive_output).expect("positive action");
    let negative_action = phased_action_of(&negative, &negative_input, &negative_output).expect("negative action");

    positive_action
        .is_equivalent_up_to_signs(&negative_action)
        .expect("phaseless actions must be identical");

    let reasons = positive_action
        .is_equivalent(&negative_action)
        .expect_err("opposite signs must be distinguished by the phased action");
    assert_eq!(reasons, vec![ActionsInequivalenceReason::RelativePhase]);
}

#[test]
fn rotation_equals_itself() {
    let (zz, zz_input, zz_output) = zz_rotation();
    let action = phased_action_of(&zz, &zz_input, &zz_output).expect("action");
    action
        .is_equivalent(&action)
        .expect("a rotation must be equivalent to itself");
}

/// Builds the Choi state of a single-system-qubit gadget directly in a phased simulation, mirroring
/// the simulator-native idiom used by the Python bindings: Bell-pair every system qubit `q` in
/// `0..n` with its reference `q + n`, allocate one random branch bit, then apply `build_gadget`.
fn choi_simulation(
    system_qubit_count: usize,
    build_gadget: impl FnOnce(&mut PhasedOutcomeCompleteSimulation, usize),
) -> PhasedOutcomeCompleteSimulation {
    let mut simulation = PhasedOutcomeCompleteSimulation::new(2 * system_qubit_count);
    for system_qubit in 0..system_qubit_count {
        simulation.unitary_op(UnitaryOp::PrepareBell, &[system_qubit, system_qubit + system_qubit_count]);
    }
    let branch = simulation.allocate_random_bit();
    build_gadget(&mut simulation, branch);
    simulation
}

#[test]
fn simulator_native_action_matches_circuit_action() {
    let (zz, zz_input, zz_output) = zz_rotation();
    let circuit_action = phased_action_of(&zz, &zz_input, &zz_output).expect("circuit action");

    let simulation = choi_simulation(2, |simulation, branch| {
        simulation.conditional_pauli(&sparse(&[z(0), z(1)]), &[branch], true);
    });
    let simulation_action = phased_action_from_simulation(&simulation, &[0, 1], &[0, 1]).expect("simulation action");

    simulation_action
        .is_equivalent(&circuit_action)
        .expect("simulator-native action must match the circuit action");
}

#[test]
fn simulator_native_distinguishes_opposite_signs() {
    let positive = choi_simulation(1, |simulation, branch| {
        simulation.conditional_pauli(&sparse(&[z(0)]), &[branch], true);
    });
    let negative = choi_simulation(1, |simulation, branch| {
        simulation.conditional_pauli(&-sparse(&[z(0)]), &[branch], true);
    });

    let positive_action = phased_action_from_simulation(&positive, &[0], &[0]).expect("positive action");
    let negative_action = phased_action_from_simulation(&negative, &[0], &[0]).expect("negative action");

    positive_action
        .is_equivalent_up_to_signs(&negative_action)
        .expect("phaseless actions must be identical");
    let reasons = positive_action
        .is_equivalent(&negative_action)
        .expect_err("opposite signs differ only in relative phase");
    assert_eq!(reasons, vec![ActionsInequivalenceReason::RelativePhase]);
}
