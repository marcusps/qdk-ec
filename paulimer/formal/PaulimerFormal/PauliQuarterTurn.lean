import PaulimerFormal.PauliMatrix
import PaulimerFormal.Clifford

/-! Concrete normalized quarter turns implementing the signed Pauli automorphism. -/

namespace PaulimerFormal.Pauli

variable {m : ℕ}

noncomputable def quarterScale : ℂ := (Real.sqrt 2 : ℂ)⁻¹

@[simp]
theorem quarterScale_star : star quarterScale = quarterScale := by
  simp [quarterScale]

theorem quarterScale_square : quarterScale * quarterScale = (2 : ℂ)⁻¹ := by
  have square : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [quarterScale, ← mul_inv, square]

noncomputable def quarterMatrix (exponent : Pauli m) : OperatorMatrix m :=
  quarterScale • (1 + Complex.I • matrix exponent)

theorem matrix_addPhase (pauli : Pauli m) (phase : PauliPhase) :
    matrix (pauli.addPhase phase) = phaseScalar phase • matrix pauli := by
  rw [← CliffordAction.scalar_mul, matrix_mul, matrix_scalar, smul_mul_assoc, one_mul]

theorem quarterMatrix_adjoint (exponent : Pauli m) (hermitian : exponent.IsOrderTwo) :
    (quarterMatrix exponent).conjTranspose = quarterScale • (1 - Complex.I • matrix exponent) := by
  have adjoint := (matrix_hermitian_iff exponent).mpr hermitian
  simp [quarterMatrix, Matrix.conjTranspose_smul, adjoint.eq, sub_eq_add_neg]

theorem quarterMatrix_unitary (exponent : Pauli m) (hermitian : exponent.IsOrderTwo) :
    quarterMatrix exponent ∈ Matrix.unitaryGroup (ComputationalBasis m) ℂ := by
  have square : matrix exponent * matrix exponent = 1 := by rw [← matrix_mul, hermitian, matrix_one]
  rw [Matrix.mem_unitaryGroup_iff]
  change quarterMatrix exponent * (quarterMatrix exponent).conjTranspose = 1
  rw [quarterMatrix_adjoint exponent hermitian, quarterMatrix, smul_mul_smul, quarterScale_square]
  simp only [mul_sub, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_smul, Complex.I_mul_I, square, neg_one_smul]
  have cancel : (1 : OperatorMatrix m) + Complex.I • matrix exponent -
      (Complex.I • matrix exponent + -1) = 1 + 1 := by abel
  rw [cancel, smul_add, ← add_smul]
  norm_num

theorem quarterMatrix_intertwines (target exponent : Pauli m) (hermitian : exponent.IsOrderTwo) :
    quarterMatrix exponent * matrix target = matrix (exponentAction target exponent) * quarterMatrix exponent := by
  have square : matrix exponent * matrix exponent = 1 := by rw [← matrix_mul, hermitian, matrix_one]
  by_cases commutes : ProjectivePauli.commutationPairing target.projective exponent.projective = 0
  · have swapped : matrix target * matrix exponent = matrix exponent * matrix target := by
      rw [← matrix_mul, ← matrix_mul, (mul_comm_iff_commutationPairing_eq_zero target exponent).mpr commutes]
    simp [exponentAction, commutes, quarterMatrix, add_mul, mul_add, swapped]
  · have paired := (f2_eq_zero_or_one
      (ProjectivePauli.commutationPairing target.projective exponent.projective)).resolve_left commutes
    have swapped : matrix target * matrix exponent = -(matrix exponent * matrix target) := by
      rw [← matrix_mul, ← matrix_mul, ← matrix_neg]
      exact congrArg matrix ((mul_eq_neg_mul_iff_commutationPairing_eq_one target exponent).mpr paired)
    have sandwich : matrix exponent * matrix target * matrix exponent = -matrix target := by
      rw [Matrix.mul_assoc, swapped, _root_.mul_neg, ← Matrix.mul_assoc, square, one_mul]
    simp only [exponentAction, ite_eq_right commutes, matrix_addPhase, phaseScalar_one, matrix_mul,
      quarterMatrix, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [sandwich]
    simp only [Complex.I_mul_I, neg_smul, smul_neg]
    module

theorem quarterMatrix_conjugation (target exponent : Pauli m) (hermitian : exponent.IsOrderTwo) :
    quarterMatrix exponent * matrix target * (quarterMatrix exponent).conjTranspose =
      matrix (exponentAction target exponent) := by
  have unitary := (Matrix.mem_unitaryGroup_iff.mp (quarterMatrix_unitary exponent hermitian))
  change quarterMatrix exponent * (quarterMatrix exponent).conjTranspose = 1 at unitary
  rw [quarterMatrix_intertwines target exponent hermitian, Matrix.mul_assoc, unitary, mul_one]

theorem quarterMatrix_spec (exponent : Pauli m) (hermitian : exponent.IsOrderTwo) :
    quarterMatrix exponent ∈ Matrix.unitaryGroup (ComputationalBasis m) ℂ ∧
      ∀ target : Pauli m,
        quarterMatrix exponent * matrix target * (quarterMatrix exponent).conjTranspose =
          matrix (exponentAction target exponent) :=
  ⟨quarterMatrix_unitary exponent hermitian, fun target => quarterMatrix_conjugation target exponent hermitian⟩

end PaulimerFormal.Pauli
