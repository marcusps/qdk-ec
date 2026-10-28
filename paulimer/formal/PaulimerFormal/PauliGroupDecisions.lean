import PaulimerFormal.PauliGroupMembership
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Data.List.Pairwise

/-! Complete abelian and stabilizer decisions for phase-aware Pauli groups. -/

namespace PaulimerFormal.PauliGroupDecisions

open scoped IsMulCommutative
open PauliGroupMembership

variable {size : ℕ}

def IsAbelian (group : Subgroup (Pauli size)) : Prop :=
  ∀ first ∈ group, ∀ second ∈ group, Commute first second

def IsStabilizer (group : Subgroup (Pauli size)) : Prop :=
  IsAbelian group ∧ -(1 : Pauli size) ∉ group

theorem abelian_iff (generators : List (DensePauli size)) :
    areMutuallyCommuting generators = true ↔ IsAbelian (generatedPauliGroup generators) := by
  constructor
  · intro accepted
    have pairs : (generators.map DensePauli.decode).Pairwise Commute := by
      simpa only [List.pairwise_map, Pauli.commute_iff_commutationPairing_eq_zero] using
        (areMutuallyCommuting_eq_true_iff generators).mp accepted
    have : IsMulCommutative (generatedPauliGroup generators) := by
      apply Subgroup.isMulCommutative_closure
      rintro first ⟨first_index, rfl⟩ second ⟨second_index, rfl⟩ different
      apply pairs.forall ?_ ?_ different
      · exact List.mem_map.mpr ⟨_, by simp, rfl⟩
      · exact List.mem_map.mpr ⟨_, by simp, rfl⟩
    intro first first_mem second second_mem
    exact congrArg Subtype.val
      (mul_comm (⟨first, first_mem⟩ : generatedPauliGroup generators) ⟨second, second_mem⟩)
  · intro abelian
    have group_mem (pauli : DensePauli size) (member : pauli ∈ generators) :
        pauli.decode ∈ generatedPauliGroup generators := by
      obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
      exact DensePauli.decode_mem_generatedPauliGroup generators index
    apply (areMutuallyCommuting_eq_true_iff generators).mpr
    apply List.pairwise_of_forall_mem_list
    intro first first_mem second second_mem
    exact (Pauli.commute_iff_commutationPairing_eq_zero _ _).mp
      (abelian _ (group_mem first first_mem) _ (group_mem second second_mem))

def isStabilizer (generators : List (DensePauli size)) : Bool :=
  areMutuallyCommuting generators && !(phases generators).contains 2

theorem stabilizer_iff (generators : List (DensePauli size)) :
    isStabilizer generators = true ↔ IsStabilizer (generatedPauliGroup generators) := by
  simp [isStabilizer, IsStabilizer, abelian_iff, mem_phases_iff,
    scalarPhases, Pauli.neg_one_eq_scalar_two]
  intro _
  rfl

theorem stabilizer_hermitian (group : Subgroup (Pauli size)) (stabilizer : IsStabilizer group)
    (pauli : Pauli size) (member : pauli ∈ group) : Pauli.IsHermitian pauli := by
  apply (Pauli.isHermitian_iff_isOrderTwo pauli).mpr
  rcases Pauli.square_eq_one_or_scalar_two pauli with identity | negative
  · exact identity
  · exfalso
    apply stabilizer.2
    rw [Pauli.neg_one_eq_scalar_two, ← negative]
    exact group.mul_mem member member

theorem decisions_spec (generators : List (DensePauli size)) :
    (areMutuallyCommuting generators = true ↔ IsAbelian (generatedPauliGroup generators)) ∧
    (isStabilizer generators = true ↔ IsStabilizer (generatedPauliGroup generators)) ∧
    (isStabilizer generators = true →
      ∀ pauli ∈ generatedPauliGroup generators, Pauli.IsHermitian pauli) :=
  ⟨abelian_iff generators, stabilizer_iff generators, fun accepted =>
    stabilizer_hermitian _ ((stabilizer_iff generators).mp accepted)⟩

end PaulimerFormal.PauliGroupDecisions
