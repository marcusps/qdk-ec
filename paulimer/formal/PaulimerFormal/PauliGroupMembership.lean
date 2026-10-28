import PaulimerFormal.PauliGroup
import PaulimerFormal.PackedEncoding
import BinarFormal.Solve

/-! Executable phase-aware membership using the verified transpose solver. -/

namespace PaulimerFormal

deriving instance DecidableEq for ProjectivePauli
deriving instance DecidableEq for Pauli

namespace PauliGroupMembership

open BinarFormal.Packed BinarFormal.Echelon BinarBridge

variable {size : ℕ}

def phases (generators : List (DensePauli size)) : List PauliPhase := by
  letI : Decidable (HasOddRelation generators) := by
    unfold HasOddRelation
    infer_instance
  letI : Decidable (HasNegativeStandardTrigger generators) := by
    unfold HasNegativeStandardTrigger HasPhaseTwoRelation HasPivotNegativeTrigger
      Pauli.IsOrderTwo Commute SemiconjBy
    infer_instance
  exact if HasOddRelation generators then [0, 1, 2, 3]
    else if HasNegativeStandardTrigger generators then [0, 2] else [0]

theorem phases_eq (generators : List (DensePauli size)) :
    phases generators = standardPhaseRepresentatives generators := by
  classical
  unfold phases standardPhaseRepresentatives
  split_ifs <;> rfl

theorem mem_phases_iff (generators : List (DensePauli size)) (phase : PauliPhase) :
    phase ∈ phases generators ↔ phase ∈ scalarPhases (generatedPauliGroup generators) := by
  rw [phases_eq, standardPhaseRepresentatives_eq_phaseRepresentatives, mem_phaseRepresentatives_iff]

def binarySolve (generators : List (DensePauli size)) (target : DensePauli size) :
    Option (PackedVec generators.length) :=
  (EchelonForm.new (bitMatrixFromPaulis generators)).transposeSolve target.phaseBits

theorem binarySolve_some (generators : List (DensePauli size)) (target : DensePauli size)
    (coefficients : PackedVec generators.length) (returned : binarySolve generators target = some coefficients) :
    (selectedPauliProduct generators coefficients.decode).projectiveRow = target.decode.projectiveRow := by
  have solved := ((BinarFormal.Solve.EchelonForm.transposeSolve_eq_some_iff _ _ _).mp returned).1
  rw [Matrix.mulVec_transpose, DensePauli.decode_phaseBits] at solved
  rw [selectedPauliProduct_projectiveRow]
  exact solved

theorem binarySolve_none (generators : List (DensePauli size)) (target : DensePauli size)
    (returned : binarySolve generators target = none) : target.decode ∉ generatedPauliGroup generators := by
  intro member
  have impossible := (BinarFormal.Solve.EchelonForm.transposeSolve_eq_none_iff _ _).mp returned
  have in_span := generatedPauliGroup_projectiveRow_mem generators member
  obtain ⟨coefficients, combined⟩ := (Submodule.mem_span_range_iff_exists_fun F2).mp in_span
  apply impossible
  refine ⟨packVector coefficients, ?_⟩
  rw [decode_packVector, Matrix.mulVec_transpose, DensePauli.decode_phaseBits]
  funext column
  have entry := congrFun combined column
  simpa only [Matrix.vecMul, dotProduct, decode_bitMatrixFromPaulis_row,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using entry

theorem correction_eq (first target : Pauli size) (same : first.projectiveRow = target.projectiveRow) :
    first * Pauli.scalar (target.phase - first.phase) = target := by
  have projective : (first * Pauli.scalar (target.phase - first.phase)).projective = target.projective := by
    simpa using Pauli.projective_eq_of_projectiveRow_eq same
  apply Pauli.ext
  · exact congrArg ProjectivePauli.x projective
  · exact congrArg ProjectivePauli.z projective
  · simp [Pauli.phase_mul, ProjectivePauli.xzCross, dotProduct]

theorem correction_mem_iff (group : Subgroup (Pauli size)) (first target : Pauli size)
    (first_mem : first ∈ group) (same : first.projectiveRow = target.projectiveRow) :
    target ∈ group ↔ target.phase - first.phase ∈ scalarPhases group := by
  have replay := correction_eq first target same
  have scalar_eq : Pauli.scalar (target.phase - first.phase) = first⁻¹ * target := by
    rw [← replay]
    simp
  constructor
  · intro member
    change Pauli.scalar (target.phase - first.phase) ∈ group
    rw [scalar_eq]
    exact group.mul_mem (group.inv_mem first_mem) member
  · intro member
    rw [← replay]
    exact group.mul_mem first_mem member

def factorization (generators : List (DensePauli size)) (target : DensePauli size) :
    Option (PackedVec generators.length × PauliPhase) := do
  let coefficients ← binarySolve generators target
  let remaining := target.decode.phase - (selectedPauliProduct generators coefficients.decode).phase
  if remaining ∈ phases generators then some (coefficients, remaining) else none

theorem factorization_some (generators : List (DensePauli size)) (target : DensePauli size)
    (coefficients : PackedVec generators.length) (phase : PauliPhase)
    (returned : factorization generators target = some (coefficients, phase)) :
    selectedPauliProduct generators coefficients.decode * Pauli.scalar phase = target.decode ∧
      phase ∈ scalarPhases (generatedPauliGroup generators) := by
  cases solved : binarySolve generators target with
  | none => simp [factorization, solved] at returned
  | some found =>
      dsimp only [factorization] at returned
      rw [solved] at returned
      dsimp at returned
      split_ifs at returned with accepted
      cases returned
      exact ⟨correction_eq _ _ (binarySolve_some generators target coefficients solved),
        (mem_phases_iff generators _).mp accepted⟩

theorem factorization_isSome_iff (generators : List (DensePauli size)) (target : DensePauli size) :
    (factorization generators target).isSome = true ↔ target.decode ∈ generatedPauliGroup generators := by
  cases solved : binarySolve generators target with
  | none => simp [factorization, solved, binarySolve_none generators target solved]
  | some coefficients =>
      have member := correction_mem_iff (generatedPauliGroup generators)
        (selectedPauliProduct generators coefficients.decode) target.decode
        (selectedPauliProduct_mem_generatedPauliGroup generators coefficients.decode)
        (binarySolve_some generators target coefficients solved)
      simp [factorization, solved, member, mem_phases_iff]

theorem membership_spec (generators : List (DensePauli size)) (target : DensePauli size) :
    ((factorization generators target).isSome = true ↔ target.decode ∈ generatedPauliGroup generators) ∧
    ∀ coefficients phase, factorization generators target = some (coefficients, phase) →
      selectedPauliProduct generators coefficients.decode * Pauli.scalar phase = target.decode ∧
      phase ∈ scalarPhases (generatedPauliGroup generators) :=
  ⟨factorization_isSome_iff generators target, factorization_some generators target⟩

end PauliGroupMembership
end PaulimerFormal
