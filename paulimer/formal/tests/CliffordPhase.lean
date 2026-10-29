import PaulimerFormal.CliffordPhase

open PaulimerFormal PaulimerFormal.Pauli CliffordAction CliffordMatrix

example {m : ℕ} (action : CliffordAction m) :
    ∃! phase : ℂ, ‖phase‖ = 1 ∧
      CliffordMatrix.realize action = phase • CliffordMatrix.realize action :=
  realization_phase_unique action (realization_spec action).1 (realization_spec action).2.1

example :
    ∃! phase : ℂ, ‖phase‖ = 1 ∧
      matrix (ofProjective (0 : ProjectivePauli 0) 1) = phase • (1 : OperatorMatrix 0) := by
  apply unitary_phase_unique (Matrix.unitaryGroup _ _).one_mem (matrix_unitary _)
  intro pauli
  simp [matrix_scalar, Matrix.conjTranspose_smul, smul_smul]

example :
    matrix (ofProjective (0 : ProjectivePauli 0) 1) = Complex.I • (1 : OperatorMatrix 0) := by
  simp [matrix_scalar]

example : matrix (1 : Pauli 1) ≠ matrix (-1 : Pauli 1) := by
  intro equal
  have impossible := matrix_injective equal
  have phases := congrArg Pauli.phase impossible
  exact (by decide : (0 : PauliPhase) ≠ 2) phases

example :
    ∃! phase : ℂ, ‖phase‖ = 1 ∧
      CliffordMatrix.realize (quarterTurn oneQubitX (by apply Pauli.ext <;> decide)) *
        CliffordMatrix.realize (quarterTurn oneQubitZ (by apply Pauli.ext <;> decide)) =
      phase • CliffordMatrix.realize
        (quarterTurn oneQubitX (by apply Pauli.ext <;> decide) *
          quarterTurn oneQubitZ (by apply Pauli.ext <;> decide)) :=
  composition_phase_unique _ _
