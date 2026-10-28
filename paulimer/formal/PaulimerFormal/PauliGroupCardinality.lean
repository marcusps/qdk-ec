import PaulimerFormal.PauliGroup
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Index

/-! Actual subgroup cardinality from the binary image and scalar kernel. -/

namespace PaulimerFormal

variable {size : ℕ}

def groupProjectiveMap (generators : List (DensePauli size)) :
    generatedPauliGroup generators →* Multiplicative (projectiveSpan generators) where
  toFun pauli := Multiplicative.ofAdd
    ⟨pauli.val.projectiveRow, generatedPauliGroup_projectiveRow_mem generators pauli.property⟩
  map_one' := by
    apply Subtype.ext
    exact Pauli.projectiveRow_one
  map_mul' first second := by
    apply Subtype.ext
    exact Pauli.projectiveRow_mul first.val second.val

theorem groupProjectiveMap_surjective (generators : List (DensePauli size)) :
    Function.Surjective (groupProjectiveMap generators) := by
  intro vector
  obtain ⟨pauli, member, same⟩ := exists_mem_subgroup_projectiveRow_eq
    (generatedPauliGroup generators) (fun index : Fin generators.length => generators[index].decode.projectiveRow)
    (fun index => ⟨generators[index].decode, DensePauli.decode_mem_generatedPauliGroup generators index, rfl⟩)
    (Multiplicative.toAdd vector).property
  exact ⟨⟨pauli, member⟩, Subtype.ext same⟩

theorem groupProjectiveMap_kernel_scalar (generators : List (DensePauli size))
    (pauli : (groupProjectiveMap generators).ker) :
    pauli.val.val = Pauli.scalar pauli.val.val.phase := by
  have accepted : groupProjectiveMap generators pauli.val = 1 := pauli.property
  have zero : pauli.val.val.projectiveRow = 0 :=
    congrArg (fun vector : Multiplicative (projectiveSpan generators) =>
      (Multiplicative.toAdd vector).val) accepted
  apply Pauli.eq_scalar_phase_of_projective_eq_zero
  exact Pauli.projective_eq_of_projectiveRow_eq (right := 1) (by simpa using zero)

def scalarKernelEquiv (generators : List (DensePauli size)) :
    scalarPhases (generatedPauliGroup generators) ≃ (groupProjectiveMap generators).ker where
  toFun phase := ⟨⟨Pauli.scalar phase.val, phase.property⟩, by
    change groupProjectiveMap generators ⟨Pauli.scalar phase.val, phase.property⟩ = 1
    apply Subtype.ext
    exact Pauli.projectiveRow_scalar phase.val⟩
  invFun pauli := ⟨pauli.val.val.phase, by
    change Pauli.scalar pauli.val.val.phase ∈ generatedPauliGroup generators
    rw [← groupProjectiveMap_kernel_scalar generators pauli]
    exact pauli.val.property⟩
  left_inv phase := rfl
  right_inv pauli := by
    apply Subtype.ext
    apply Subtype.ext
    exact (groupProjectiveMap_kernel_scalar generators pauli).symm

theorem phaseRepresentatives_nodup (phases : AddSubgroup PauliPhase) :
    (phaseRepresentatives phases).Nodup := by
  classical
  unfold phaseRepresentatives
  split_ifs <;> decide

theorem scalarPhases_card (phases : AddSubgroup PauliPhase) :
    Nat.card phases = 2 ^ scalarPhaseRank phases := by
  classical
  have membership : ∀ phase, phase ∈ (phaseRepresentatives phases).toFinset ↔ phase ∈ phases := by
    intro phase
    simp only [List.mem_toFinset, mem_phaseRepresentatives_iff]
  rw [Nat.card_eq_fintype_card, Fintype.card_of_subtype _ membership,
    List.toFinset_card_of_nodup (phaseRepresentatives_nodup phases), phaseRepresentatives_length]

theorem generatedPauliGroup_card (generators : List (DensePauli size)) :
    Nat.card (generatedPauliGroup generators) = 2 ^ standardLog2Size generators := by
  rw [← (groupProjectiveMap generators).ker.card_mul_index, Subgroup.index_ker,
    (groupProjectiveMap generators).range_eq_top.mpr (groupProjectiveMap_surjective generators),
    Subgroup.card_top, ← Nat.card_congr (scalarKernelEquiv generators), scalarPhases_card]
  change 2 ^ scalarPhaseRank (scalarPhases (generatedPauliGroup generators)) *
    Nat.card (projectiveSpan generators) = _
  rw [Module.natCard_eq_pow_finrank (K := F2), Nat.card_zmod, standardLog2Size_eq_semantic_ranks, pow_add]
  exact Nat.mul_comm _ _

end PaulimerFormal
