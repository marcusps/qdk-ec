import PaulimerFormal.PauliGroupIntersection
import PaulimerFormal.PauliGroupCardinality

/-! Generator concatenation and the phase-count/binary-rank partial comparison. -/

namespace PaulimerFormal.PauliGroupOrder

open PauliGroupMembership PauliIntersection

variable {size : ℕ}

theorem generated_eq_listGroup (generators : List (DensePauli size)) :
    generatedPauliGroup generators = listGroup (generators.map DensePauli.decode) := by
  unfold generatedPauliGroup
  change Subgroup.closure (Set.range (DensePauli.decode ∘ generators.get)) = _
  rw [Set.range_comp, Set.range_list_get]
  congr 1
  ext pauli
  simp

theorem join_spec (first second : List (DensePauli size)) :
    generatedPauliGroup (first ++ second) = generatedPauliGroup first ⊔ generatedPauliGroup second := by
  simp only [generated_eq_listGroup, List.map_append, listGroup, List.mem_append,
    Set.ofPred_or, Subgroup.closure_union]

def ranks (generators : List (DensePauli size)) : ℕ × ℕ :=
  ((phases generators).length, standardBinaryRank generators)

theorem phase_count_eq (generators : List (DensePauli size)) :
    (phases generators).length = Nat.card (scalarPhases (generatedPauliGroup generators)) := by
  rw [phases_eq, standardPhaseRepresentatives_eq_phaseRepresentatives,
    phaseRepresentatives_length, scalarPhases_card]

theorem ranks_semantic (generators : List (DensePauli size)) :
    ranks generators = (Nat.card (scalarPhases (generatedPauliGroup generators)),
      Module.finrank F2 (rowImage (generatedPauliGroup generators))) := by
  rw [ranks, phase_count_eq, standardBinaryRank_eq_finrank_projectiveSpan, rowImage_generated]

theorem ranks_congr (first second : List (DensePauli size))
    (same : generatedPauliGroup first = generatedPauliGroup second) : ranks first = ranks second := by
  rw [ranks_semantic, ranks_semantic, same]

theorem ranks_mono (first second : List (DensePauli size))
    (included : generatedPauliGroup first ≤ generatedPauliGroup second) :
    (ranks first).1 ≤ (ranks second).1 ∧ (ranks first).2 ≤ (ranks second).2 := by
  rw [ranks_semantic, ranks_semantic]
  constructor
  · exact AddSubgroup.card_le_of_le (fun _ member => included member)
  · apply Submodule.finrank_mono
    rintro vector ⟨pauli, member, rfl⟩
    exact ⟨pauli, included member, rfl⟩

theorem card_eq (generators : List (DensePauli size)) :
    Nat.card (generatedPauliGroup generators) = (ranks generators).1 * 2 ^ (ranks generators).2 := by
  simp only [ranks, phases_eq, standardPhaseRepresentatives_eq_phaseRepresentatives,
    phaseRepresentatives_length, generatedPauliGroup_card, standardLog2Size,
    standardScalarPhaseRank_eq_scalarPhaseRank, pow_add]
  exact Nat.mul_comm _ _

theorem ranks_eq_iff_eq_of_le (first second : List (DensePauli size))
    (included : generatedPauliGroup first ≤ generatedPauliGroup second) :
    ranks first = ranks second ↔ generatedPauliGroup first = generatedPauliGroup second := by
  constructor
  · intro same
    have : Finite (generatedPauliGroup second) :=
      Nat.finite_of_card_ne_zero (by rw [generatedPauliGroup_card]; exact pow_ne_zero _ (by decide))
    apply Subgroup.eq_of_le_of_card_ge included
    rw [card_eq, card_eq, same]
  · exact ranks_congr first second

theorem left_join_eq_iff (first second : List (DensePauli size)) :
    ranks first = ranks (first ++ second) ↔ generatedPauliGroup second ≤ generatedPauliGroup first := by
  rw [ranks_eq_iff_eq_of_le first (first ++ second) (by rw [join_spec]; exact le_sup_left), join_spec]
  exact eq_comm.trans sup_eq_left

theorem right_join_eq_iff (first second : List (DensePauli size)) :
    ranks second = ranks (first ++ second) ↔ generatedPauliGroup first ≤ generatedPauliGroup second := by
  rw [ranks_eq_iff_eq_of_le second (first ++ second) (by rw [join_spec]; exact le_sup_right), join_spec]
  exact eq_comm.trans sup_eq_right

theorem equal_test_iff (first second : List (DensePauli size)) :
    (ranks first = ranks second ∧ ranks first = ranks (first ++ second)) ↔
      generatedPauliGroup first = generatedPauliGroup second := by
  constructor
  · rintro ⟨same, joined⟩
    exact le_antisymm ((right_join_eq_iff first second).mp (same.symm.trans joined))
      ((left_join_eq_iff first second).mp joined)
  · intro same
    exact ⟨ranks_congr first second same, (left_join_eq_iff first second).mpr same.ge⟩

theorem less_test_iff (first second : List (DensePauli size)) :
    ((ranks first).1 ≤ (ranks second).1 ∧ (ranks first).2 ≤ (ranks second).2 ∧
      ranks second = ranks (first ++ second)) ↔
      generatedPauliGroup first ≤ generatedPauliGroup second := by
  constructor
  · exact fun accepted => (right_join_eq_iff first second).mp accepted.2.2
  · intro included
    exact ⟨(ranks_mono first second included).1, (ranks_mono first second included).2,
      (right_join_eq_iff first second).mpr included⟩

def partialCmp (first second : List (DensePauli size)) : Option Ordering :=
  let firstRanks := ranks first
  let secondRanks := ranks second
  let joinedRanks := ranks (first ++ second)
  if firstRanks = secondRanks ∧ firstRanks = joinedRanks then some .eq
  else if firstRanks.1 ≤ secondRanks.1 ∧ firstRanks.2 ≤ secondRanks.2 ∧ secondRanks = joinedRanks then some .lt
  else if firstRanks = joinedRanks then some .gt
  else none

theorem partialCmp_eq (first second : List (DensePauli size)) :
    partialCmp first second =
      (by classical exact
        if generatedPauliGroup first = generatedPauliGroup second then some .eq
        else if generatedPauliGroup first ≤ generatedPauliGroup second then some .lt
        else if generatedPauliGroup second ≤ generatedPauliGroup first then some .gt
        else none) := by
  classical
  dsimp only [partialCmp]
  simp only [equal_test_iff, less_test_iff]
  simp only [left_join_eq_iff]

theorem compare_equal_iff (first second : List (DensePauli size)) :
    partialCmp first second = some .eq ↔ generatedPauliGroup first = generatedPauliGroup second := by
  classical
  rw [partialCmp_eq]
  split_ifs <;> simp_all

theorem compare_less_iff (first second : List (DensePauli size)) :
    partialCmp first second = some .lt ↔ generatedPauliGroup first < generatedPauliGroup second := by
  classical
  rw [partialCmp_eq]
  split_ifs <;> simp_all [lt_iff_le_and_ne]

theorem compare_greater_iff (first second : List (DensePauli size)) :
    partialCmp first second = some .gt ↔ generatedPauliGroup second < generatedPauliGroup first := by
  classical
  rw [partialCmp_eq]
  split_ifs <;> simp_all [lt_iff_le_and_ne, ne_comm]
  exact fun reverse => False.elim (‹generatedPauliGroup first ≠ generatedPauliGroup second›
    (le_antisymm ‹generatedPauliGroup first ≤ generatedPauliGroup second› reverse))

theorem compare_none_iff (first second : List (DensePauli size)) :
    partialCmp first second = none ↔
      ¬ generatedPauliGroup first ≤ generatedPauliGroup second ∧
      ¬ generatedPauliGroup second ≤ generatedPauliGroup first := by
  classical
  rw [partialCmp_eq]
  split_ifs <;> simp_all

def intersect (first second : List (DensePauli size)) : Option (List (Pauli size)) :=
  match partialCmp first second with
  | some .gt => some (second.map DensePauli.decode)
  | some .lt | some .eq => some (first.map DensePauli.decode)
  | none => PauliIntersection.intersect first second

theorem intersection_spec (first second : List (DensePauli size)) :
    (intersect first second).isSome = true ∧
      ∀ output, intersect first second = some output →
        listGroup output = generatedPauliGroup first ⊓ generatedPauliGroup second := by
  cases comparison : partialCmp first second with
  | none => simpa only [intersect, comparison] using full_intersection_spec first second
  | some ordering =>
      cases ordering with
      | lt =>
          simp [intersect, comparison, ← generated_eq_listGroup,
            inf_eq_left.mpr ((compare_less_iff first second).mp comparison).le]
      | eq =>
          simp [intersect, comparison, ← generated_eq_listGroup,
            (compare_equal_iff first second).mp comparison]
      | gt =>
          simp [intersect, comparison, ← generated_eq_listGroup,
            inf_eq_right.mpr ((compare_greater_iff first second).mp comparison).le]

theorem operations_spec (first second : List (DensePauli size)) :
    (generatedPauliGroup (first ++ second) = generatedPauliGroup first ⊔ generatedPauliGroup second) ∧
    (partialCmp first second = some .eq ↔ generatedPauliGroup first = generatedPauliGroup second) ∧
    (partialCmp first second = some .lt ↔ generatedPauliGroup first < generatedPauliGroup second) ∧
    (partialCmp first second = some .gt ↔ generatedPauliGroup second < generatedPauliGroup first) ∧
    (partialCmp first second = none ↔
      ¬ generatedPauliGroup first ≤ generatedPauliGroup second ∧
      ¬ generatedPauliGroup second ≤ generatedPauliGroup first) ∧
    (intersect first second).isSome = true ∧
    (∀ output, intersect first second = some output →
      listGroup output = generatedPauliGroup first ⊓ generatedPauliGroup second) :=
  ⟨join_spec first second, compare_equal_iff first second, compare_less_iff first second,
    compare_greater_iff first second, compare_none_iff first second, intersection_spec first second⟩

end PaulimerFormal.PauliGroupOrder
