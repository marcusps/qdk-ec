import PaulimerFormal.PauliGroupMembership
import PaulimerFormal.PauliGroupCardinality
import PaulimerFormal.ResidueExtraction
import PaulimerFormal.Algorithm

/-! Complete duplicate-free enumeration by normalized pivot subsets and scalar phases. -/

namespace PaulimerFormal.PauliGroupEnumeration

open PauliGroupMembership

variable {size : ℕ}

def pivot (generators : List (DensePauli size)) (index : EchelonPivotIndex generators) : Pauli size :=
  if (1 : PauliPhase) ∈ phases generators then
    Pauli.ofProjective (pivotPauliProduct generators index).projective 0
  else if (2 : PauliPhase) ∈ phases generators then
    (pivotPauliProduct generators index).parityNormalize
  else pivotPauliProduct generators index

theorem pivot_eq (generators : List (DensePauli size)) (index : EchelonPivotIndex generators) :
    pivot generators index = normalizedPivotPauliProduct generators index := by
  classical
  unfold pivot normalizedPivotPauliProduct
  simp only [mem_phases_iff, one_mem_scalarPhases_iff_hasOddRelation,
    two_mem_scalarPhases_iff_standard_classification]
  split_ifs <;> simp_all

theorem pivot_row (generators : List (DensePauli size)) (index : EchelonPivotIndex generators) :
    (pivot generators index).projectiveRow = (pivotPauliProduct generators index).projectiveRow := by
  rw [pivot_eq]
  exact congrArg (fun pauli : ProjectivePauli size => BinarBridge.toFinVector pauli.toPhaseVector)
    (normalizedPivotPauliProduct_projective generators index)

def product (generators : List (DensePauli size)) (coefficients : EchelonPivotIndex generators → F2) :
    Pauli size :=
  (List.ofFn fun index => if coefficients index = 0 then 1 else pivot generators index).prod

theorem product_mem (generators : List (DensePauli size)) (coefficients : EchelonPivotIndex generators → F2) :
    product generators coefficients ∈ generatedPauliGroup generators := by
  apply Subgroup.list_prod_mem
  rw [List.forall_mem_ofFn_iff]
  intro index
  split_ifs
  · exact Subgroup.one_mem _
  · rw [pivot_eq]
    exact normalizedPivotPauliProduct_mem_generatedPauliGroup generators index

theorem product_row (generators : List (DensePauli size)) (coefficients : EchelonPivotIndex generators → F2) :
    (product generators coefficients).projectiveRow =
      ∑ index, coefficients index • (pivotPauliProduct generators index).projectiveRow := by
  rw [product, Pauli.projectiveRow_list_prod, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro index _
  rcases Pauli.f2_eq_zero_or_one (coefficients index) with zero | one
  · simp [zero]
  · simp [one, pivot_row]

theorem pivot_span (generators : List (DensePauli size)) :
    Submodule.span F2 (Set.range fun index : EchelonPivotIndex generators =>
      (pivotPauliProduct generators index).projectiveRow) = projectiveSpan generators := by
  simp only [pivotPauliProduct_projectiveRow]
  rw [ResidueExtraction.pivotRows_span, bitMatrixFromPaulis_rowSpace]

def elements (generators : List (DensePauli size)) : List (Pauli size) :=
  (allFinFunctions f2Values (standardBinaryRank generators)).flatMap fun coefficients =>
    (phases generators).map fun phase => product generators coefficients * Pauli.scalar phase

theorem mem_elements_iff (generators : List (DensePauli size)) (pauli : Pauli size) :
    pauli ∈ elements generators ↔ pauli ∈ generatedPauliGroup generators := by
  constructor
  · intro member
    obtain ⟨coefficients, _, member⟩ := List.mem_flatMap.mp member
    obtain ⟨phase, allowed, rfl⟩ := List.mem_map.mp member
    exact (generatedPauliGroup generators).mul_mem (product_mem generators coefficients)
      ((mem_phases_iff generators phase).mp allowed)
  · intro member
    have in_span := generatedPauliGroup_projectiveRow_mem generators member
    rw [← pivot_span generators] at in_span
    obtain ⟨coefficients, same⟩ := (Submodule.mem_span_range_iff_exists_fun F2).mp in_span
    have row : (product generators coefficients).projectiveRow = pauli.projectiveRow :=
      (product_row generators coefficients).trans same
    have allowed := (correction_mem_iff (generatedPauliGroup generators) _ pauli
      (product_mem generators coefficients) row).mp member
    apply List.mem_flatMap.mpr
    refine ⟨coefficients, mem_allFinFunctions f2Values mem_f2Values coefficients, ?_⟩
    apply List.mem_map.mpr
    exact ⟨_, (mem_phases_iff generators _).mpr allowed, correction_eq _ _ row⟩

theorem allFinFunctions_length (values : List α) (count : ℕ) :
    (allFinFunctions values count).length = values.length ^ count := by
  induction count with
  | zero => simp [allFinFunctions]
  | succ count induction => simp [allFinFunctions, List.length_flatMap, induction, pow_succ, Nat.mul_comm]

theorem elements_length (generators : List (DensePauli size)) :
    (elements generators).length = 2 ^ standardLog2Size generators := by
  rw [elements]
  unfold standardBinaryRank
  rw [List.length_flatMap]
  simp only [List.length_map]
  rw [phases_eq, standardPhaseRepresentatives_eq_phaseRepresentatives, phaseRepresentatives_length,
    standardLog2Size, standardScalarPhaseRank_eq_scalarPhaseRank, pow_add]
  simp [allFinFunctions_length, f2Values, standardBinaryRank]

theorem elements_nodup (generators : List (DensePauli size)) : (elements generators).Nodup := by
  let equivalence : {pauli // pauli ∈ (elements generators).toFinset} ≃ generatedPauliGroup generators :=
    Equiv.subtypeEquivRight fun pauli => by
      rw [List.mem_toFinset, mem_elements_iff]
  have cardinality := Nat.card_congr equivalence
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at cardinality
  apply Multiset.coe_nodup.mp
  apply Multiset.toFinset_card_eq_card_iff_nodup.mp
  change (elements generators).toFinset.card = (elements generators).length
  rw [cardinality, generatedPauliGroup_card, elements_length]

theorem enumeration_spec (generators : List (DensePauli size)) :
    (elements generators).Nodup ∧
    (∀ pauli, pauli ∈ elements generators ↔ pauli ∈ generatedPauliGroup generators) ∧
    (elements generators).length = Nat.card (generatedPauliGroup generators) :=
  ⟨elements_nodup generators, mem_elements_iff generators,
    (elements_length generators).trans (generatedPauliGroup_card generators).symm⟩

end PaulimerFormal.PauliGroupEnumeration
