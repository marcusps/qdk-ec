import PaulimerFormal.Pauli
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-! Faithful bitstring-indexed complex matrices in the `i^p X^x Z^z` convention. -/

namespace PaulimerFormal.Pauli

open scoped BigOperators

abbrev ComputationalBasis (m : ℕ) := Fin m → F2
abbrev OperatorMatrix (m : ℕ) := Matrix (ComputationalBasis m) (ComputationalBasis m) ℂ

variable {m : ℕ}

noncomputable def matrix (pauli : Pauli m) : OperatorMatrix m :=
  fun row column =>
    if row = column + pauli.x then phaseScalar (pauli.phase + parityPhase (pauli.z ⬝ᵥ column)) else 0

theorem phaseScalar_ne_zero (phase : PauliPhase) : phaseScalar phase ≠ 0 := by
  have product := phaseScalar_add phase (-phase)
  rw [add_neg_cancel, phaseScalar_zero] at product
  exact left_ne_zero_of_mul_eq_one product.symm

theorem phaseScalar_injective : Function.Injective phaseScalar := by
  intro left right equal
  change Complex.I ^ left.val = Complex.I ^ right.val at equal
  fin_cases left <;> fin_cases right <;>
    first | rfl | norm_num [ZMod.val, pow_succ, Complex.ext_iff] at equal

@[simp]
theorem phaseScalar_star (phase : PauliPhase) : star (phaseScalar phase) = phaseScalar (-phase) := by
  fin_cases phase
  · change star (Complex.I ^ 0) = Complex.I ^ 0
    simp
  · change star (Complex.I ^ 1) = Complex.I ^ 3
    norm_num [pow_succ]
  · change star (Complex.I ^ 2) = Complex.I ^ 2
    norm_num [pow_succ]
  · change star (Complex.I ^ 3) = Complex.I ^ 1
    norm_num [pow_succ]

@[simp]
theorem matrix_one : matrix (1 : Pauli m) = 1 := by
  ext row column
  change (if row = column + 0 then phaseScalar (0 + parityPhase (0 ⬝ᵥ column)) else 0) = _
  simp [Matrix.one_apply]

theorem matrix_mul (left right : Pauli m) : matrix (left * right) = matrix left * matrix right := by
  ext row column
  change (if row = column + (left.x + right.x) then
    phaseScalar (left.phase + right.phase + parityPhase (left.z ⬝ᵥ right.x) +
      parityPhase ((left.z + right.z) ⬝ᵥ column)) else 0) = _
  simp only [Matrix.mul_apply, matrix, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  have coordinates : column + (left.x + right.x) = column + right.x + left.x := by abel
  rw [coordinates]
  split
  · rw [← phaseScalar_add]
    congr 1
    simp only [dotProduct_add, add_dotProduct, parityPhase_add]
    abel
  · simp_all

theorem matrix_star_mul (pauli : Pauli m) : (matrix pauli).conjTranspose * matrix pauli = 1 := by
  ext row column
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, matrix, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases equal : row = column
  · subst column
    simp only [ite_true, Matrix.one_apply_eq]
    rw [phaseScalar_star, ← phaseScalar_add, neg_add_cancel, phaseScalar_zero]
  · have different : column + pauli.x ≠ row + pauli.x := by
      intro same
      exact equal (add_right_cancel same).symm
    simp [different, equal]

@[simp]
theorem matrix_inv (pauli : Pauli m) : matrix pauli⁻¹ = (matrix pauli).conjTranspose := by
  have product : matrix pauli * matrix pauli⁻¹ = 1 := by rw [← matrix_mul, mul_inv_cancel, matrix_one]
  calc
    matrix pauli⁻¹ = ((matrix pauli).conjTranspose * matrix pauli) * matrix pauli⁻¹ := by
      rw [matrix_star_mul, one_mul]
    _ = (matrix pauli).conjTranspose := by rw [Matrix.mul_assoc, product, mul_one]

theorem matrix_unitary (pauli : Pauli m) : matrix pauli ∈ Matrix.unitaryGroup (ComputationalBasis m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  exact matrix_star_mul pauli

theorem matrix_injective : Function.Injective (@matrix m) := by
  intro left right same
  have at_zero := congrFun (congrFun same left.x) 0
  have x_equal : left.x = right.x := by
    by_contra different
    have impossible : phaseScalar left.phase = 0 := by simpa [matrix, different] using at_zero
    exact phaseScalar_ne_zero _ impossible
  have phase_equal : left.phase = right.phase := by
    apply phaseScalar_injective
    simpa [matrix, x_equal] using at_zero
  have z_equal : left.z = right.z := by
    funext index
    have evaluated := congrFun (congrFun same (Pi.single index 1 + left.x)) (Pi.single index 1)
    have phases : phaseScalar (left.phase + parityPhase (left.z index)) =
        phaseScalar (right.phase + parityPhase (right.z index)) := by
      simpa [matrix, x_equal] using evaluated
    exact parityPhase_injective (add_left_cancel (phase_equal ▸ phaseScalar_injective phases))
  exact Pauli.ext x_equal z_equal phase_equal

theorem matrix_hermitian_iff (pauli : Pauli m) :
    (matrix pauli).IsHermitian ↔ pauli.IsOrderTwo := by
  rw [Matrix.IsHermitian, ← matrix_inv, matrix_injective.eq_iff,
    ← isHermitian_iff_isOrderTwo]
  rfl

noncomputable def matrixHom : Pauli m →* OperatorMatrix m where
  toFun := matrix
  map_one' := matrix_one
  map_mul' := matrix_mul

theorem matrix_scalar (phase : PauliPhase) :
    matrix (ofProjective (0 : ProjectivePauli m) phase) = phaseScalar phase • 1 := by
  ext row column
  simp [matrix, ofProjective, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]

@[simp]
theorem matrix_neg (pauli : Pauli m) : matrix (-pauli) = -matrix pauli := by
  ext row column
  change (if row = column + pauli.x then
    phaseScalar (pauli.phase + 2 + parityPhase (pauli.z ⬝ᵥ column)) else 0) = _
  by_cases shifted : row = column + pauli.x <;> simp [matrix, phaseScalar_add, shifted]

theorem matrix_oneQubit (pauli : Pauli 1) :
    (matrix pauli).submatrix (fun index : Fin 2 => fun _ : Fin 1 => (index.val : F2))
      (fun index : Fin 2 => fun _ : Fin 1 => (index.val : F2)) = oneQubitMatrix pauli := by
  rcases f2_eq_zero_or_one (pauli.x 0) with x_value | x_value <;>
    rcases f2_eq_zero_or_one (pauli.z 0) with z_value | z_value <;>
    ext row column <;> fin_cases row <;> fin_cases column <;>
    norm_num [matrix, Matrix.submatrix_apply, oneQubitMatrix, oneQubitProjectiveMatrix,
      phaseScalar_add, projective, dotProduct, funext_iff, Fin.forall_fin_one,
      PauliMatrix.pauliMatrix, Matrix.mul_apply, Matrix.one_apply, x_value, z_value]

theorem matrix_spec :
    Function.Injective (@matrix m) ∧ matrix (1 : Pauli m) = 1 ∧
      (∀ left right : Pauli m, matrix (left * right) = matrix left * matrix right) ∧
      (∀ pauli : Pauli m, matrix pauli⁻¹ = (matrix pauli).conjTranspose) ∧
      (∀ pauli : Pauli m, matrix pauli ∈ Matrix.unitaryGroup (ComputationalBasis m) ℂ) ∧
      (∀ pauli : Pauli m, (matrix pauli).IsHermitian ↔ pauli.IsOrderTwo) ∧
      (∀ pauli : Pauli 1,
        (matrix pauli).submatrix (fun index : Fin 2 => fun _ : Fin 1 => (index.val : F2))
          (fun index : Fin 2 => fun _ : Fin 1 => (index.val : F2)) = oneQubitMatrix pauli) := by
  exact ⟨matrix_injective, matrix_one, matrix_mul, matrix_inv, matrix_unitary,
    matrix_hermitian_iff, matrix_oneQubit⟩

end PaulimerFormal.Pauli
