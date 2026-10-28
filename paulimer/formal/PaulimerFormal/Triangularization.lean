import PaulimerFormal.Bilinear
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Congruence-triangularizer search

Algorithmic invariants for the pivot/complement search in PR #217,
`2ce895eda84473762d7db36bf6c3561460992858`.
-/

namespace PaulimerFormal.Triangularization

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module F2 V]

abbrev familySpan {n : ℕ} (basis : Fin n → V) : Submodule F2 V :=
  Submodule.span F2 (Set.range basis)

theorem member_familySpan {n : ℕ} (basis : Fin n → V) (index : Fin n) :
    basis index ∈ familySpan basis :=
  Submodule.subset_span (Set.mem_range_self index)

/-- Rust's complement loop, retaining the original order except for the
deleted coupling pivot. Multiplication by a bit is conditional XOR. -/
def complementVectors {n : ℕ} (coupling : V →ₗ[F2] F2)
    (basis : Fin (n + 1) → V) (pivot : Fin (n + 1)) : Fin n → V :=
  fun index =>
    basis (pivot.succAbove index) +
      coupling (basis (pivot.succAbove index)) • basis pivot

theorem exists_coupling_pivot {n : ℕ} (coupling : V →ₗ[F2] F2)
    (basis : Fin n → V) (pick : V)
    (pick_mem : pick ∈ familySpan basis) (pick_coupling : coupling pick = 1) :
    ∃ pivot, coupling (basis pivot) = 1 := by
  by_contra none
  have zero_on_basis : ∀ index, coupling (basis index) = 0 := by
    intro index
    by_contra nonzero
    exact none ⟨index, f2_eq_one_of_ne_zero _ nonzero⟩
  have contained : familySpan basis ≤ LinearMap.ker coupling := by
    apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    exact zero_on_basis index
  have pick_zero : coupling pick = 0 := contained pick_mem
  rw [pick_coupling] at pick_zero
  exact one_ne_zero pick_zero

theorem complement_sum {n : ℕ} (coupling : V →ₗ[F2] F2)
    (basis : Fin (n + 1) → V) (pivot : Fin (n + 1))
    (coefficients : Fin n → F2) :
    (∑ index, coefficients index • complementVectors coupling basis pivot index) =
      (∑ index, coefficients index • basis (pivot.succAbove index)) +
        (∑ index, coefficients index * coupling (basis (pivot.succAbove index))) •
          basis pivot := by
  simp [complementVectors, smul_add, Finset.sum_add_distrib,
    Finset.sum_smul, smul_smul]

theorem complement_span {n : ℕ} (coupling : V →ₗ[F2] F2)
    (basis : Fin (n + 1) → V) (pivot : Fin (n + 1))
    (pivot_coupling : coupling (basis pivot) = 1) :
    familySpan (complementVectors coupling basis pivot) =
      familySpan basis ⊓ LinearMap.ker coupling := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    constructor
    · exact (familySpan basis).add_mem (member_familySpan basis _)
        ((familySpan basis).smul_mem _ (member_familySpan basis pivot))
    · change coupling (complementVectors coupling basis pivot index) = 0
      simp [complementVectors, pivot_coupling]
  · intro vector member
    obtain ⟨coefficients, representation⟩ :=
      (Submodule.mem_span_range_iff_exists_fun F2).mp member.1
    have zero_coupling : coupling vector = 0 := member.2
    have coefficient_relation :
        coefficients pivot +
          ∑ index : Fin n,
            coefficients (pivot.succAbove index) *
              coupling (basis (pivot.succAbove index)) = 0 := by
      have applied := congrArg coupling representation
      rw [map_sum, Fin.sum_univ_succAbove _ pivot] at applied
      simpa [pivot_coupling, zero_coupling] using applied
    have pivot_coefficient :
        coefficients pivot =
          ∑ index : Fin n,
            coefficients (pivot.succAbove index) *
              coupling (basis (pivot.succAbove index)) := by
      simpa using eq_neg_of_add_eq_zero_left coefficient_relation
    apply (Submodule.mem_span_range_iff_exists_fun F2).mpr
    refine ⟨fun index => coefficients (pivot.succAbove index), ?_⟩
    rw [complement_sum, ← pivot_coefficient]
    rw [Fin.sum_univ_succAbove _ pivot] at representation
    simpa [add_comm] using representation

theorem complement_independent {n : ℕ} (coupling : V →ₗ[F2] F2)
    (basis : Fin (n + 1) → V) (pivot : Fin (n + 1))
    (independent : LinearIndependent F2 basis) :
    LinearIndependent F2 (complementVectors coupling basis pivot) := by
  apply Fintype.linearIndependent_iff.mpr
  intro coefficients relation index
  let pivotCoefficient :=
    ∑ index, coefficients index * coupling (basis (pivot.succAbove index))
  let extended : Fin (n + 1) → F2 :=
    Fin.insertNth pivot pivotCoefficient coefficients
  have extended_relation : (∑ position, extended position • basis position) = 0 := by
    rw [Fin.sum_univ_succAbove _ pivot]
    simp only [extended, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    rw [complement_sum] at relation
    simpa [pivotCoefficient, add_comm] using relation
  have zero := Fintype.linearIndependent_iff.mp independent extended extended_relation
  simpa [extended] using zero (pivot.succAbove index)

theorem complement_spec {n : ℕ} (coupling : V →ₗ[F2] F2)
    (basis : Fin (n + 1) → V) (pivot : Fin (n + 1))
    (independent : LinearIndependent F2 basis)
    (pivot_coupling : coupling (basis pivot) = 1) :
    LinearIndependent F2 (complementVectors coupling basis pivot) ∧
      familySpan (complementVectors coupling basis pivot) =
        familySpan basis ⊓ LinearMap.ker coupling ∧
      Module.finrank F2 (familySpan (complementVectors coupling basis pivot)) + 1 =
        Module.finrank F2 (familySpan basis) := by
  have new_independent := complement_independent coupling basis pivot independent
  refine ⟨new_independent, complement_span coupling basis pivot pivot_coupling, ?_⟩
  have old_rank : Module.finrank F2 (familySpan basis) = n + 1 := by
    simpa only [familySpan, Fintype.card_fin] using finrank_span_eq_card independent
  have new_rank :
      Module.finrank F2 (familySpan (complementVectors coupling basis pivot)) = n := by
    simpa only [familySpan, Fintype.card_fin] using finrank_span_eq_card new_independent
  rw [old_rank, new_rank]

/-- Exact half-matrix test used by the alternating-restriction fast path. -/
def alternatingCheck {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin n → V) : Bool :=
  decide (∀ index, form (basis index) (basis index) = 0 ∧
    ∀ earlier, earlier < index →
      form (basis index) (basis earlier) = form (basis earlier) (basis index))

theorem symmetry_on_span {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin n → V)
    (symmetric : ∀ first second, form (basis first) (basis second) =
      form (basis second) (basis first))
    {left right : V} (left_mem : left ∈ familySpan basis)
    (right_mem : right ∈ familySpan basis) :
    form left right = form right left := by
  have basis_against_span (index : Fin n) {vector : V}
      (member : vector ∈ familySpan basis) :
      form (basis index) vector = form vector (basis index) := by
    induction member using Submodule.span_induction with
    | mem vector member =>
        obtain ⟨other, rfl⟩ := member
        exact symmetric index other
    | zero => simp
    | add first second _ _ first_eq second_eq => simp [first_eq, second_eq]
    | smul scalar vector _ equal => simp [equal]
  induction left_mem using Submodule.span_induction with
  | mem vector member =>
      obtain ⟨index, rfl⟩ := member
      exact basis_against_span index right_mem
  | zero => simp
  | add first second _ _ first_eq second_eq => simp [first_eq, second_eq]
  | smul scalar vector _ equal => simp [equal]

theorem alternatingCheck_iff {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin n → V) :
    alternatingCheck form basis = true ↔
      ∀ vector ∈ familySpan basis, form vector vector = 0 := by
  rw [alternatingCheck, decide_eq_true_eq]
  constructor
  · intro checked
    have symmetric : ∀ first second, form (basis first) (basis second) =
        form (basis second) (basis first) := by
      intro first second
      rcases lt_trichotomy first second with before | equal | after
      · exact ((checked second).2 first before).symm
      · rw [equal]
      · exact (checked first).2 second after
    intro vector member
    induction member using Submodule.span_induction with
    | mem vector member =>
        obtain ⟨index, rfl⟩ := member
        exact (checked index).1
    | zero => simp
    | add first second first_mem second_mem first_zero second_zero =>
        have commute := symmetry_on_span form basis symmetric first_mem second_mem
        simp [first_zero, second_zero, commute]
    | smul scalar vector _ zero => simp [zero]
  · intro alternating index
    refine ⟨alternating _ (member_familySpan basis index), ?_⟩
    intro earlier _
    have sum_zero := alternating (basis index + basis earlier)
      ((familySpan basis).add_mem (member_familySpan basis index)
        (member_familySpan basis earlier))
    have cross_zero :
        form (basis index) (basis earlier) + form (basis earlier) (basis index) = 0 := by
      simpa [alternating _ (member_familySpan basis index),
        alternating _ (member_familySpan basis earlier)] using sum_zero
    simpa using eq_neg_of_add_eq_zero_left cross_zero

end PaulimerFormal.Triangularization
