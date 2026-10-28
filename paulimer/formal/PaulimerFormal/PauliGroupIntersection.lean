import PaulimerFormal.IntersectionExtraction
import PaulimerFormal.PauliIntersectionLoop

/-! Complete fixed-width phase-aware intersection, including projective-basis extraction. -/

namespace PaulimerFormal.PauliIntersection

open BinarFormal.Packed BinarBridge

variable {size rows : ℕ}

def fromRow (vector : Fin (size + size) → F2) : Pauli size :=
  Pauli.ofProjective (ProjectivePauli.ofPhaseVector (ofFinVector vector)) 0

@[simp]
theorem fromRow_projectiveRow (vector : Fin (size + size) → F2) :
    (fromRow vector).projectiveRow = vector := by
  simp [fromRow, Pauli.projectiveRow]

def matrixPaulis (matrix : PackedMatrix rows (size + size)) : List (Pauli size) :=
  List.ofFn fun index => fromRow (matrix.decode index)

theorem matrixPaulis_range (matrix : PackedMatrix rows (size + size)) :
    Set.range (fun index : Fin (matrixPaulis matrix).length => (matrixPaulis matrix)[index].projectiveRow) =
      Set.range matrix.decode := by
  change Set.range (Pauli.projectiveRow ∘ (matrixPaulis matrix).get) = _
  rw [Set.range_comp, Set.range_list_get]
  ext vector
  simp [matrixPaulis]
  rfl

theorem rowImage_generated (generators : List (DensePauli size)) :
    rowImage (generatedPauliGroup generators) = projectiveSpan generators := by
  apply le_antisymm
  · rintro vector ⟨pauli, member, rfl⟩
    exact generatedPauliGroup_projectiveRow_mem generators member
  · intro vector member
    exact exists_mem_subgroup_projectiveRow_eq (generatedPauliGroup generators)
      (fun index : Fin generators.length => generators[index].decode.projectiveRow)
      (fun index => ⟨generators[index].decode, DensePauli.decode_mem_generatedPauliGroup generators index, rfl⟩)
      member

def projectiveBasis (first second : List (DensePauli size)) : List (Pauli size) :=
  matrixPaulis (IntersectionExtraction.basis (bitMatrixFromPaulis first) (bitMatrixFromPaulis second))

theorem projectiveBasis_valid (first second : List (DensePauli size)) :
    ValidBasis first second (projectiveBasis first second) := by
  unfold ValidBasis projectiveBasis
  rw [matrixPaulis_range, IntersectionExtraction.basis_span,
    bitMatrixFromPaulis_rowSpace, bitMatrixFromPaulis_rowSpace, rowImage_generated, rowImage_generated]

def intersect (first second : List (DensePauli size)) : Option (List (Pauli size)) :=
  intersectionFromBasis first second (projectiveBasis first second)

theorem full_intersection_spec (first second : List (DensePauli size)) :
    (intersect first second).isSome = true ∧
      ∀ output, intersect first second = some output →
        listGroup output = generatedPauliGroup first ⊓ generatedPauliGroup second :=
  traversal_spec first second (projectiveBasis first second) (projectiveBasis_valid first second)

end PaulimerFormal.PauliIntersection
