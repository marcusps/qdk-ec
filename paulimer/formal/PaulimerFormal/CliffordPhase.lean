import PaulimerFormal.CliffordMatrix

/-! Uniqueness of concrete Clifford realizations up to a unit-modulus scalar. -/

namespace PaulimerFormal.CliffordMatrix

open Pauli CliffordAction

variable {m : ℕ}

theorem scalar_of_commutes_paulis (operator : OperatorMatrix m)
    (commutes : ∀ pauli, operator * matrix pauli = matrix pauli * operator) :
    operator = operator 0 0 • 1 := by
  have off_diagonal (row column : ComputationalBasis m) (different : row ≠ column) :
      operator row column = 0 := by
    by_contra nonzero
    have coordinates (index : Fin m) : row index = column index := by
      have entry := congrFun (congrFun (commutes ⟨⟨0, Pi.single index 1⟩, 0⟩) row) column
      have phases : operator row column * phaseScalar (parityPhase (column index)) =
          phaseScalar (parityPhase (row index)) * operator row column := by
        simpa [matrix, Matrix.mul_apply, eq_comm] using entry
      rw [mul_comm _ (operator row column)] at phases
      exact (parityPhase_injective
        (phaseScalar_injective (mul_left_cancel₀ nonzero phases))).symm
    exact different (funext coordinates)
  have diagonal (row : ComputationalBasis m) : operator row row = operator 0 0 := by
    have entry := congrFun (congrFun (commutes ⟨⟨row, 0⟩, 0⟩) row) 0
    simpa [matrix, Matrix.mul_apply, eq_comm] using entry
  ext row column
  by_cases equal : row = column
  · subst column
    simpa using diagonal row
  · simp [equal, off_diagonal row column equal]

theorem unitary_phase_unique {left right : OperatorMatrix m}
    (left_unitary : left ∈ Matrix.unitaryGroup (ComputationalBasis m) ℂ)
    (right_unitary : right ∈ Matrix.unitaryGroup (ComputationalBasis m) ℂ)
    (same_action : ∀ pauli, left * matrix pauli * left.conjTranspose =
      right * matrix pauli * right.conjTranspose) :
    ∃! phase : ℂ, ‖phase‖ = 1 ∧ right = phase • left := by
  have left_inverse := Matrix.mem_unitaryGroup_iff'.mp left_unitary
  have left_inverse' := Matrix.mem_unitaryGroup_iff.mp left_unitary
  have right_inverse := Matrix.mem_unitaryGroup_iff'.mp right_unitary
  change left.conjTranspose * left = 1 at left_inverse
  change left * left.conjTranspose = 1 at left_inverse'
  change right.conjTranspose * right = 1 at right_inverse
  let difference := left.conjTranspose * right
  let phase := difference 0 0
  have scalar : difference = phase • 1 := by
    apply scalar_of_commutes_paulis
    intro pauli
    calc
      difference * matrix pauli =
          left.conjTranspose *
            (right * matrix pauli * right.conjTranspose) * right := by
        simp only [difference, Matrix.mul_assoc, right_inverse, mul_one]
      _ = left.conjTranspose *
            (left * matrix pauli * left.conjTranspose) * right := by
        rw [← same_action]
      _ = matrix pauli * difference := by
        simp only [difference, ← Matrix.mul_assoc, left_inverse, one_mul]
  have reconstructed : right = phase • left := by
    calc
      right = left * difference := by
        simp only [difference, ← Matrix.mul_assoc, left_inverse', one_mul]
      _ = phase • left := by rw [scalar, Matrix.mul_smul, mul_one]
  have difference_unitary : difference.conjTranspose * difference = 1 := by
    simp only [difference, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      (right.conjTranspose * left) * (left.conjTranspose * right) =
          right.conjTranspose * (left * left.conjTranspose) * right := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [left_inverse', mul_one, right_inverse]
  have phase_unitary : star phase * phase = 1 := by
    rw [scalar, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul] at difference_unitary
    simpa using congrFun (congrFun difference_unitary 0) 0
  have phase_norm : ‖phase‖ = 1 := by
    have norms := congrArg norm phase_unitary
    simp only [norm_mul, norm_star, norm_one] at norms
    nlinarith [norm_nonneg phase]
  refine ⟨phase, ⟨phase_norm, reconstructed⟩, ?_⟩
  intro other specification
  have entry := congrArg (fun operator => (left.conjTranspose * operator) 0 0) specification.2
  have equal : phase = other := by
    simpa [Matrix.mul_smul, left_inverse, phase, difference] using entry
  exact equal.symm

theorem realization_phase_unique (action : CliffordAction m) {unitary : OperatorMatrix m}
    (is_unitary : unitary ∈ Matrix.unitaryGroup (ComputationalBasis m) ℂ)
    (represented : Represents unitary action) :
    ∃! phase : ℂ, ‖phase‖ = 1 ∧ unitary = phase • realize action := by
  apply unitary_phase_unique (realization_spec action).1 is_unitary
  intro pauli
  rw [(realization_spec action).2.1, represented]

theorem composition_phase_unique (first second : CliffordAction m) :
    ∃! phase : ℂ, ‖phase‖ = 1 ∧
      realize first * realize second = phase • realize (first * second) :=
  realization_phase_unique (first * second)
    ((Matrix.unitaryGroup _ _).mul_mem
      (realization_spec first).1 (realization_spec second).1)
    (represents_mul (realization_spec first).2.1 (realization_spec second).2.1)

end PaulimerFormal.CliffordMatrix
