import PaulimerFormal.BinarBridge
import PaulimerFormal.Pauli
import PaulimerFormal.TriangularKeys

/-!
# Complete projective fixed space

Compute the left kernel of `I + F` through Binar's transpose and kernel basis.
The output Paulis use positive Hermitian representatives, not signed-centralizer
semantics.
-/

namespace PaulimerFormal.CliffordFixedSpace

open BinarFormal.Packed BinarFormal.Echelon BinarFormal.Solve BinarBridge
open scoped Matrix

def packedDifference {m : ℕ} (action : ActionMatrix m) : PackedActionMatrix m :=
  Triangularization.packedRows fun row column =>
    (1 + action) ((phaseIndexEquiv m).symm row) ((phaseIndexEquiv m).symm column)

@[simp]
theorem decode_packedDifference {m : ℕ} (action : ActionMatrix m) :
    (packedDifference action).decode = fun row column =>
      (1 + action) ((phaseIndexEquiv m).symm row) ((phaseIndexEquiv m).symm column) :=
  Triangularization.decode_packedRows _

abbrev dimension {m : ℕ} (action : ActionMatrix m) : ℕ :=
  (freeColumns (EchelonForm.new (packedDifference action).transpose).pivots (m + m)).length

def vectors {m : ℕ} (action : ActionMatrix m) : Fin (dimension action) → PhaseVector m :=
  fun row => ofFinVector (((packedDifference action).transpose.kernelBasis.rows row).decode)

theorem vectors_independent {m : ℕ} (action : ActionMatrix m) :
    LinearIndependent F2 (vectors action) := by
  let reindex := LinearEquiv.funCongrLeft F2 F2 (phaseIndexEquiv m)
  exact (kernelBasis_linearIndependent (packedDifference action).transpose).map'
    reindex.toLinearMap (LinearMap.ker_eq_bot.mpr reindex.injective)

theorem kernel_apply {m : ℕ} (action : ActionMatrix m) (vector : Fin (m + m) → F2) :
    ofFinVector ((packedDifference action).transpose.decode.mulVec vector) =
      rowAction (ofFinVector vector) (1 + action) := by
  funext column
  simp only [ofFinVector, Function.comp_apply, PackedMatrix.decode_transpose,
    decode_packedDifference, Matrix.mulVec, Matrix.transpose, Matrix.of_apply, dotProduct,
    rowAction, Matrix.vecMul, Equiv.symm_apply_apply]
  simpa only [Equiv.symm_apply_apply, mul_comm] using
    ((phaseIndexEquiv m).sum_comp (fun row =>
      vector row * (1 + action) ((phaseIndexEquiv m).symm row) column)).symm

theorem kernel_mem_iff {m : ℕ} (action : ActionMatrix m) (vector : Fin (m + m) → F2) :
    vector ∈ LinearMap.ker (packedDifference action).transpose.decode.mulVecLin ↔
      ofFinVector vector ∈ fixedSpace action := by
  change (packedDifference action).transpose.decode.mulVec vector = 0 ↔
    rowAction (ofFinVector vector) (1 + action) = 0
  constructor
  · intro zero
    rw [← kernel_apply, zero]
    rfl
  · intro zero
    apply (LinearEquiv.funCongrLeft F2 F2 (phaseIndexEquiv m)).injective
    change ofFinVector ((packedDifference action).transpose.decode.mulVec vector) = ofFinVector 0
    rw [kernel_apply, zero]
    rfl

theorem vectors_span {m : ℕ} (action : ActionMatrix m) :
    Submodule.span F2 (Set.range (vectors action)) = fixedSpace action := by
  let reindex := LinearEquiv.funCongrLeft F2 F2 (phaseIndexEquiv m)
  change Submodule.span F2 (Set.range (reindex.toLinearMap ∘
    (fun row => ((packedDifference action).transpose.kernelBasis.rows row).decode))) = _
  rw [Set.range_comp, Submodule.span_image, kernelBasis_span_eq_ker]
  ext vector
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨preimage, member, rfl⟩
    exact (kernel_mem_iff action preimage).mp member
  · intro member
    refine ⟨toFinVector vector, ?_, ofFinVector_toFinVector vector⟩
    apply (kernel_mem_iff action _).mpr
    simpa only [ofFinVector_toFinVector] using member

theorem dimension_eq {m : ℕ} (action : ActionMatrix m) :
    dimension action = 2 * m - residueRank action := by
  have dimension := finrank_span_eq_card (vectors_independent action)
  rw [vectors_span, Fintype.card_fin] at dimension
  have total := residueRank_add_finrank_fixedSpace action
  omega

def paulis {m : ℕ} (action : ActionMatrix m) : Fin (dimension action) → Pauli m :=
  fun row => Pauli.positiveRepresentative (ProjectivePauli.ofPhaseVector (vectors action row))

@[simp]
theorem paulis_projective {m : ℕ} (action : ActionMatrix m) (row : Fin (dimension action)) :
    (paulis action row).projective.toPhaseVector = vectors action row := by
  simp [paulis]

theorem paulis_positive {m : ℕ} (action : ActionMatrix m) (row : Fin (dimension action)) :
    (paulis action row).xyzPhase = 0 ∧ (paulis action row).IsHermitian := by
  refine ⟨Pauli.xyzPhase_positiveRepresentative _, ?_⟩
  exact (Pauli.isHermitian_iff_isOrderTwo _).mpr (Pauli.positiveRepresentative_isOrderTwo _)

theorem paulis_fixed {m : ℕ} (action : ActionMatrix m) (row : Fin (dimension action)) :
    rowAction (paulis action row).projective.toPhaseVector action =
      (paulis action row).projective.toPhaseVector := by
  rw [paulis_projective, ← mem_fixedSpace_iff, ← vectors_span]
  exact Submodule.subset_span (Set.mem_range_self row)

theorem fixedSpace_spec {m : ℕ} (action : ActionMatrix m) :
    LinearIndependent F2 (fun row => (paulis action row).projective.toPhaseVector) ∧
    Submodule.span F2 (Set.range (fun row => (paulis action row).projective.toPhaseVector)) =
      fixedSpace action ∧
    dimension action = 2 * m - residueRank action ∧
    ∀ row, (paulis action row).xyzPhase = 0 ∧ (paulis action row).IsHermitian ∧
      rowAction (paulis action row).projective.toPhaseVector action =
        (paulis action row).projective.toPhaseVector := by
  refine ⟨?_, ?_, dimension_eq action, ?_⟩
  · simpa only [paulis_projective] using vectors_independent action
  · simpa only [paulis_projective] using vectors_span action
  · intro row
    exact ⟨(paulis_positive action row).1, (paulis_positive action row).2, paulis_fixed action row⟩

end PaulimerFormal.CliffordFixedSpace
