import PaulimerFormal.IntersectionKernel

/-! Stacked dependencies, alpha projection, and final row-space intersection extraction. -/

namespace PaulimerFormal.IntersectionExtraction

open BinarFormal.Packed BinarFormal.Echelon BinarBridge

variable {firstRows secondRows columns : ℕ}

def stacked (first : PackedMatrix firstRows columns) (second : PackedMatrix secondRows columns) :
    PackedMatrix (firstRows + secondRows) columns where
  rows := Fin.addCases first.rows second.rows

def leftProjection : (Fin (firstRows + secondRows) → F2) →ₗ[F2] (Fin firstRows → F2) where
  toFun vector index := vector (Fin.castAdd secondRows index)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def alphaMap (first : PackedMatrix firstRows columns) :
    (Fin (firstRows + secondRows) → F2) →ₗ[F2] (Fin columns → F2) :=
  first.decode.vecMulLinear.comp leftProjection

theorem span_rows_eq_range (matrix : PackedMatrix firstRows columns) :
    Submodule.span F2 (Set.range matrix.decode) = LinearMap.range matrix.decode.vecMulLinear := by
  simpa only [Matrix.row_def] using (range_vecMulLinear matrix.decode).symm

theorem stacked_vecMul (first : PackedMatrix firstRows columns) (second : PackedMatrix secondRows columns)
    (coefficients : Fin (firstRows + secondRows) → F2) :
    Matrix.vecMul coefficients (stacked first second).decode =
      Matrix.vecMul (coefficients ∘ Fin.castAdd secondRows) first.decode +
        Matrix.vecMul (coefficients ∘ Fin.natAdd firstRows) second.decode := by
  funext column
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_add, stacked, PackedMatrix.decode, Function.comp_def]

theorem kernel_image (first : PackedMatrix firstRows columns) (second : PackedMatrix secondRows columns) :
    Submodule.map (alphaMap first)
      (LinearMap.ker (stacked first second).decode.transpose.mulVecLin) =
        Submodule.span F2 (Set.range first.decode) ⊓ Submodule.span F2 (Set.range second.decode) := by
  rw [span_rows_eq_range, span_rows_eq_range]
  apply le_antisymm
  · rintro vector ⟨coefficients, kernel_member, rfl⟩
    change (stacked first second).decode.transpose.mulVec coefficients = 0 at kernel_member
    rw [Matrix.mulVec_transpose, stacked_vecMul] at kernel_member
    have same : Matrix.vecMul (coefficients ∘ Fin.castAdd secondRows) first.decode =
        Matrix.vecMul (coefficients ∘ Fin.natAdd firstRows) second.decode := by
      have cancelled := congrArg
        (fun vector => vector + Matrix.vecMul (coefficients ∘ Fin.natAdd firstRows) second.decode) kernel_member
      simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using cancelled
    exact ⟨⟨coefficients ∘ Fin.castAdd secondRows, rfl⟩,
      ⟨coefficients ∘ Fin.natAdd firstRows, same.symm⟩⟩
  · rintro vector ⟨⟨left, left_eq⟩, ⟨right, right_eq⟩⟩
    refine ⟨Fin.addCases left right, ?_, ?_⟩
    · change (stacked first second).decode.transpose.mulVec (Fin.addCases left right) = 0
      rw [Matrix.mulVec_transpose, stacked_vecMul]
      simp only [Function.comp_def, Fin.addCases_left, Fin.addCases_right,
        ← Matrix.vecMulLinear_apply, left_eq, right_eq, ZModModule.add_self]
    · simpa only [alphaMap, LinearMap.comp_apply, leftProjection, LinearMap.coe_mk, AddHom.coe_mk,
        Fin.addCases_left] using left_eq

def alphas (first : PackedMatrix firstRows columns) (second : PackedMatrix secondRows columns) :
    PackedMatrix
      (firstRows + secondRows - (EchelonForm.new (stacked first second)).pivots.length) firstRows where
  rows index := packVector fun column =>
    (IntersectionKernel.dependencyRows (stacked first second)).decode index (Fin.castAdd secondRows column)

def candidates (first : PackedMatrix firstRows columns) (second : PackedMatrix secondRows columns) :=
  ((alphas first second).materialize.m4riMul first).materialize

theorem candidates_decode (first : PackedMatrix firstRows columns) (second : PackedMatrix secondRows columns) :
    (candidates first second).decode =
      fun index => alphaMap first ((IntersectionKernel.dependencyRows (stacked first second)).decode index) := by
  simp only [candidates, PackedMatrix.materialize_eq, PackedMatrix.decode_m4riMul]
  funext index column
  simp [Matrix.mul_apply, alphaMap, leftProjection, Matrix.vecMul,
    dotProduct, alphas, PackedMatrix.decode]

theorem candidates_span (first : PackedMatrix firstRows columns) (second : PackedMatrix secondRows columns) :
    Submodule.span F2 (Set.range (candidates first second).decode) =
      Submodule.span F2 (Set.range first.decode) ⊓ Submodule.span F2 (Set.range second.decode) := by
  rw [candidates_decode]
  change Submodule.span F2 (Set.range (alphaMap first ∘
    fun index => ((IntersectionKernel.dependencyRows (stacked first second)).rows index).decode)) = _
  rw [Set.range_comp, Submodule.span_image]
  change Submodule.map (alphaMap first)
    (Submodule.span F2 (Set.range (IntersectionKernel.dependencyRows (stacked first second)).decode)) = _
  rw [IntersectionKernel.dependencyRows_span, kernel_image]

def basis (first : PackedMatrix firstRows columns) (second : PackedMatrix secondRows columns) :
    PackedMatrix (EchelonForm.new (candidates first second)).pivots.length columns :=
  let form := EchelonForm.new (candidates first second)
  { rows := fun index => form.matrix.rows
      ⟨index.val, index.isLt.trans_le (EchelonForm.new_pivots_length_le (candidates first second))⟩ }

theorem basis_independent (first : PackedMatrix firstRows columns) (second : PackedMatrix secondRows columns) :
    LinearIndependent F2 (basis first second).decode :=
  ResidueExtraction.pivotRows_independent (candidates first second)

theorem basis_span (first : PackedMatrix firstRows columns) (second : PackedMatrix secondRows columns) :
    Submodule.span F2 (Set.range (basis first second).decode) =
      Submodule.span F2 (Set.range first.decode) ⊓ Submodule.span F2 (Set.range second.decode) :=
  (ResidueExtraction.pivotRows_span (candidates first second)).trans (candidates_span first second)

theorem extraction_spec (first : PackedMatrix firstRows columns) (second : PackedMatrix secondRows columns) :
    LinearIndependent F2 (basis first second).decode ∧
      Submodule.span F2 (Set.range (basis first second).decode) =
        Submodule.span F2 (Set.range first.decode) ⊓ Submodule.span F2 (Set.range second.decode) :=
  ⟨basis_independent first second, basis_span first second⟩

end PaulimerFormal.IntersectionExtraction
