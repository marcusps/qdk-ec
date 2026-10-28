import PaulimerFormal.ResidueExtraction
import BinarFormal.Solve

/-! The trailing echelon-transform rows form a basis of the left kernel. -/

namespace PaulimerFormal.IntersectionKernel

open BinarFormal.Packed BinarFormal.Echelon

variable {rows columns : ℕ}

def dependencyIndex (matrix : PackedMatrix rows columns)
    (index : Fin (rows - (EchelonForm.new matrix).pivots.length)) : Fin rows :=
  ⟨(EchelonForm.new matrix).pivots.length + index.val, by
    have bound := EchelonForm.new_pivots_length_le matrix
    omega⟩

def dependencyRows (matrix : PackedMatrix rows columns) :
    PackedMatrix (rows - (EchelonForm.new matrix).pivots.length) rows where
  rows index := (EchelonForm.new matrix).transform.rows (dependencyIndex matrix index)

theorem transform_independent (matrix : PackedMatrix rows columns) :
    LinearIndependent F2 (EchelonForm.new matrix).transform.decode := by
  change LinearIndependent BinarFormal.Packed.F2
    (fun row => ((EchelonForm.new matrix).transform.rows row).decode)
  rw [Fintype.linearIndependent_iff]
  intro coefficients zero index
  have combination : Matrix.vecMul coefficients (EchelonForm.new matrix).transform.decode = 0 := by
    funext column
    simpa only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      PackedMatrix.decode, Matrix.of_apply] using
      congrFun zero column
  have recovered := congrArg
    (fun vector => Matrix.vecMul vector (EchelonForm.new matrix).transformInvT.decode.transpose) combination
  rw [Matrix.vecMul_vecMul, EchelonForm.new_transform_mul_inv, Matrix.vecMul_one, Matrix.zero_vecMul] at recovered
  exact congrFun recovered index

theorem dependencyRows_independent (matrix : PackedMatrix rows columns) :
    LinearIndependent F2 (dependencyRows matrix).decode := by
  apply (transform_independent matrix).comp (dependencyIndex matrix)
  intro first second equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  dsimp only [dependencyIndex] at values
  omega

theorem dependencyRows_mem_ker (matrix : PackedMatrix rows columns)
    (index : Fin (rows - (EchelonForm.new matrix).pivots.length)) :
    (dependencyRows matrix).decode index ∈ LinearMap.ker matrix.decode.transpose.mulVecLin := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext column
  have transformed := congrFun (congrFun (EchelonForm.new_transform_mul_eq matrix)
    (dependencyIndex matrix index)) column
  have zero : (EchelonForm.new matrix).matrix.decode (dependencyIndex matrix index) column = 0 := by
    rw [PackedMatrix.decode_get, EchelonForm.new_rows_zero matrix _ (by simp [dependencyIndex]) _ column.isLt]
    rfl
  rw [zero] at transformed
  simpa only [Matrix.mul_apply, Matrix.mulVec, Matrix.transpose_apply, dotProduct, mul_comm,
    dependencyRows, PackedMatrix.decode, Matrix.of_apply, Pi.zero_apply] using transformed

theorem dependencyRows_span (matrix : PackedMatrix rows columns) :
    Submodule.span F2 (Set.range (dependencyRows matrix).decode) =
      LinearMap.ker matrix.decode.transpose.mulVecLin := by
  have included : Submodule.span F2 (Set.range (dependencyRows matrix).decode) ≤
      LinearMap.ker matrix.decode.transpose.mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    exact dependencyRows_mem_ker matrix index
  have dimension := finrank_span_eq_card (dependencyRows_independent matrix)
  rw [Fintype.card_fin] at dimension
  have rank_nullity := LinearMap.finrank_range_add_finrank_ker matrix.decode.transpose.mulVecLin
  rw [Module.finrank_pi, Fintype.card_fin] at rank_nullity
  change matrix.decode.transpose.rank + Module.finrank F2 (LinearMap.ker matrix.decode.transpose.mulVecLin) = rows
    at rank_nullity
  rw [Matrix.rank_transpose, ← EchelonForm.new_pivots_length_eq_rank matrix] at rank_nullity
  apply Submodule.eq_of_le_of_finrank_eq included
  rw [dimension]
  omega

theorem kernel_spec (matrix : PackedMatrix rows columns) :
    LinearIndependent F2 (dependencyRows matrix).decode ∧
      Submodule.span F2 (Set.range (dependencyRows matrix).decode) =
        LinearMap.ker matrix.decode.transpose.mulVecLin :=
  ⟨dependencyRows_independent matrix, dependencyRows_span matrix⟩

end PaulimerFormal.IntersectionKernel
