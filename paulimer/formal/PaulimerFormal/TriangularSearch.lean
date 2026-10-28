import PaulimerFormal.SpanEnumeration
import PaulimerFormal.Minimality

/-!
# Uncached congruence-triangularizer search

The search follows PR #217's candidate order, first coupling pivot, alternating
guard, and first-success backtracking. Recursion decreases the basis length.
Failure caching and complement deduplication are not part of this model.
-/

namespace PaulimerFormal.Triangularization

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module F2 V]

def IsTriangularBasis {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (space : Submodule F2 V) (basis : Fin n → V) : Prop :=
  LinearIndependent F2 basis ∧ familySpan basis = space ∧
    IsUnitLowerTriangular (fun row column => form (basis row) (basis column))

theorem triangularBasis_tail {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (space : Submodule F2 V) (basis : Fin (n + 1) → V)
    (valid : IsTriangularBasis form space basis) :
    IsTriangularBasis form (space ⊓ LinearMap.ker (form (basis 0))) (Fin.tail basis) := by
  have complement_eq :
      complementVectors (form (basis 0)) basis 0 = Fin.tail basis := by
    ext index
    simp [complementVectors, valid.2.2.1 0 index.succ (by simp), Fin.tail]
  have independent := complement_independent (form (basis 0)) basis 0 valid.1
  have spans := complement_span (form (basis 0)) basis 0 (valid.2.2.2 0)
  rw [complement_eq] at independent spans
  rw [valid.2.1] at spans
  refine ⟨independent, spans, ?_, ?_⟩
  · intro row column before
    exact valid.2.2.1 row.succ column.succ (by simpa using before)
  · intro index
    exact valid.2.2.2 index.succ

theorem triangularBasis_cons {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (space : Submodule F2 V) (pick : V) (rest : Fin n → V)
    (pick_mem : pick ∈ space) (self_pairing : form pick pick = 1)
    (valid : IsTriangularBasis form (space ⊓ LinearMap.ker (form pick)) rest) :
    IsTriangularBasis form space (Fin.cons pick rest) := by
  have rest_mem (index : Fin n) : rest index ∈ space ⊓ LinearMap.ker (form pick) := by
    rw [← valid.2.1]
    exact member_familySpan rest index
  have rest_zero (index : Fin n) : form pick (rest index) = 0 := (rest_mem index).2
  have independent : LinearIndependent F2 (Fin.cons pick rest) := by
    apply linearIndependent_finCons.mpr
    refine ⟨valid.1, ?_⟩
    intro member
    change pick ∈ familySpan rest at member
    rw [valid.2.1] at member
    have zero : form pick pick = 0 := member.2
    exact one_ne_zero (self_pairing.symm.trans zero)
  have spans : familySpan (Fin.cons pick rest) = space := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨index, rfl⟩
      cases index using Fin.cases with
      | zero => exact pick_mem
      | succ index => exact (rest_mem index).1
    · have rest_le : familySpan rest ≤ familySpan (Fin.cons pick rest) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨index, rfl⟩
        exact member_familySpan (Fin.cons pick rest) index.succ
      intro vector member
      have orthogonal : vector + form pick vector • pick ∈ familySpan rest := by
        rw [valid.2.1]
        refine ⟨space.add_mem member (space.smul_mem _ pick_mem), ?_⟩
        change form pick (vector + form pick vector • pick) = 0
        simp [self_pairing]
      have reconstructed := (familySpan (Fin.cons pick rest)).add_mem (rest_le orthogonal)
        ((familySpan (Fin.cons pick rest)).smul_mem (form pick vector)
          (member_familySpan (Fin.cons pick rest) 0))
      simpa only [Fin.cons_zero, add_assoc, add_self_eq_zero_f2, add_zero] using reconstructed
  refine ⟨independent, spans, ?_, ?_⟩
  · intro row column before
    cases row using Fin.cases with
    | zero =>
        cases column using Fin.cases with
        | zero => simp at before
        | succ column => exact rest_zero column
    | succ row =>
        cases column using Fin.cases with
        | zero => simp at before
        | succ column => exact valid.2.2.1 row column (by simpa using before)
  · intro index
    cases index using Fin.cases with
    | zero => exact self_pairing
    | succ index => exact valid.2.2.2 index

def couplingPivot {n : ℕ} (coupling : V →ₗ[F2] F2) (basis : Fin n → V) :
    Option (Fin n) :=
  (List.finRange n).find? fun index => decide (coupling (basis index) = 1)

theorem couplingPivot_spec {n : ℕ} (coupling : V →ₗ[F2] F2)
    (basis : Fin n → V) (pivot : Fin n)
    (found : couplingPivot coupling basis = some pivot) :
    coupling (basis pivot) = 1 := by
  have accepted : decide (coupling (basis pivot) = 1) = true :=
    List.find?_some (p := fun index => decide (coupling (basis index) = 1)) found
  exact of_decide_eq_true accepted

theorem couplingPivot_exists {n : ℕ} (coupling : V →ₗ[F2] F2)
    (basis : Fin n → V) (pick : V)
    (pick_mem : pick ∈ familySpan basis) (self_pairing : coupling pick = 1) :
    ∃ pivot, couplingPivot coupling basis = some pivot := by
  obtain ⟨pivot, pairing⟩ := exists_coupling_pivot coupling basis pick pick_mem self_pairing
  cases found : couplingPivot coupling basis with
  | none =>
      have impossible := List.find?_eq_none.mp found pivot (by simp)
      simp [pairing] at impossible
  | some pivot => exact ⟨pivot, rfl⟩

def tryPick {n : ℕ} (form : LinearMap.BilinForm F2 V) (basis : Fin (n + 1) → V)
    (recurse : (Fin n → V) → Option (Fin n → V)) (pick : V) :
    Option (Fin (n + 1) → V) :=
  if form pick pick = 1 then
    (couplingPivot (form pick) basis).bind fun pivot =>
      (recurse (complementVectors (form pick) basis pivot)).map (Fin.cons pick)
  else none

def search (form : LinearMap.BilinForm F2 V) :
    {n : ℕ} → (Fin n → V) → Option (Fin n → V)
  | 0, basis => some basis
  | n + 1, basis =>
      if alternatingCheck form basis then none else
        (spanVectors basis).findSome? (tryPick form basis (search form (n := n)))

theorem tryPick_sound {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin (n + 1) → V) (independent : LinearIndependent F2 basis)
    (recurse : (Fin n → V) → Option (Fin n → V))
    (recursive_sound : ∀ basis, LinearIndependent F2 basis →
      ∀ result, recurse basis = some result → IsTriangularBasis form (familySpan basis) result)
    (pick : V) (pick_mem : pick ∈ familySpan basis)
    (result : Fin (n + 1) → V) (returned : tryPick form basis recurse pick = some result) :
    IsTriangularBasis form (familySpan basis) result := by
  unfold tryPick at returned
  split at returned
  next self_pairing =>
    cases found : couplingPivot (form pick) basis with
    | none => simp [found] at returned
    | some pivot =>
      cases recursed : recurse (complementVectors (form pick) basis pivot) with
      | none => simp [found, recursed] at returned
      | some rest =>
        have equal : Fin.cons pick rest = result := by simpa [found, recursed] using returned
        rw [← equal]
        have valid := recursive_sound _ (complement_independent _ _ _ independent) rest recursed
        rw [complement_span _ _ _ (couplingPivot_spec _ _ _ found)] at valid
        exact triangularBasis_cons form _ pick rest pick_mem self_pairing valid
  next rejected => simp at returned

theorem search_sound {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin n → V) (independent : LinearIndependent F2 basis)
    (result : Fin n → V) (returned : search form basis = some result) :
    IsTriangularBasis form (familySpan basis) result := by
  induction n with
  | zero =>
      have equal : basis = result := Option.some.inj returned
      subst result
      exact ⟨independent, rfl, fun row => Fin.elim0 row, fun index => Fin.elim0 index⟩
  | succ n induction =>
      unfold search at returned
      split at returned
      next alternating => simp at returned
      next not_alternating =>
        obtain ⟨pick, member, successful⟩ := List.exists_of_findSome?_eq_some returned
        exact tryPick_sound form basis independent _ induction pick
          ((mem_spanVectors_iff basis independent pick).mp member).1 result successful

theorem search_complete {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin n → V) (independent : LinearIndependent F2 basis)
    (solution : Fin n → V) (valid : IsTriangularBasis form (familySpan basis) solution) :
    search form basis ≠ none := by
  induction n with
  | zero => simp [search]
  | succ n induction =>
      have pick_mem : solution 0 ∈ familySpan basis := by
        rw [← valid.2.1]
        exact member_familySpan solution 0
      have self_pairing := valid.2.2.2 0
      have nonzero : solution 0 ≠ 0 := by
        intro zero
        simp [zero] at self_pairing
      have enumerated := (mem_spanVectors_iff basis independent (solution 0)).mpr
        ⟨pick_mem, nonzero⟩
      have not_alternating : alternatingCheck form basis ≠ true := by
        intro alternating
        have zero := (alternatingCheck_iff form basis).mp alternating _ pick_mem
        exact one_ne_zero (self_pairing.symm.trans zero)
      obtain ⟨pivot, found⟩ :=
        couplingPivot_exists (form (solution 0)) basis (solution 0) pick_mem self_pairing
      have tail_valid := triangularBasis_tail form _ solution valid
      rw [← complement_span _ basis pivot (couplingPivot_spec _ _ _ found)] at tail_valid
      have recursive_success := induction _ (complement_independent _ _ _ independent)
        (Fin.tail solution) tail_valid
      intro failed
      have every_failed : ∀ pick ∈ spanVectors basis,
          tryPick form basis (search form (n := n)) pick = none := by
        simpa [search, not_alternating] using failed
      have pick_failed := every_failed (solution 0) enumerated
      simp [tryPick, self_pairing, found] at pick_failed
      exact recursive_success pick_failed

theorem search_none_iff {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin n → V) (independent : LinearIndependent F2 basis) :
    search form basis = none ↔
      ¬∃ solution : Fin n → V, IsTriangularBasis form (familySpan basis) solution := by
  constructor
  · rintro failed ⟨solution, valid⟩
    exact search_complete form basis independent solution valid failed
  · intro impossible
    cases returned : search form basis with
    | none => rfl
    | some result => exact (impossible ⟨result, search_sound form basis independent result returned⟩).elim

theorem gram_eq_congruence {n : ℕ} (core change : Matrix (Fin n) (Fin n) F2) :
    (fun row column => core.toBilin' (change row) (change column)) =
      change * core * Matrix.transpose change := by
  ext row column
  simp only [Matrix.toBilin'_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem matrix_familySpan_eq_top {n : ℕ} (basis : Matrix (Fin n) (Fin n) F2)
    (independent : LinearIndependent F2 basis) : familySpan basis = ⊤ :=
  independent.span_eq_top_of_card_eq_finrank' (by simp)

theorem triangularBasis_matrix_iff {n : ℕ} (core change : Matrix (Fin n) (Fin n) F2) :
    IsTriangularBasis core.toBilin' ⊤ change ↔
      IsUnit change ∧ IsUnitLowerTriangular (change * core * Matrix.transpose change) := by
  constructor
  · intro valid
    refine ⟨Matrix.linearIndependent_rows_iff_isUnit.mp valid.1, ?_⟩
    rw [← gram_eq_congruence]
    exact valid.2.2
  · rintro ⟨unit, triangular⟩
    have independent := Matrix.linearIndependent_rows_iff_isUnit.mpr unit
    refine ⟨independent, matrix_familySpan_eq_top change independent, ?_⟩
    rwa [gram_eq_congruence]

def congruenceTriangularize {n : ℕ} (core : Matrix (Fin n) (Fin n) F2) :
    Option (Matrix (Fin n) (Fin n) F2) :=
  search core.toBilin' (1 : Matrix (Fin n) (Fin n) F2)

theorem congruenceTriangularize_sound {n : ℕ} (core change : Matrix (Fin n) (Fin n) F2)
    (returned : congruenceTriangularize core = some change) :
    IsUnit change ∧ IsUnitLowerTriangular (change * core * Matrix.transpose change) := by
  have independent : LinearIndependent F2 (1 : Matrix (Fin n) (Fin n) F2) :=
    Matrix.linearIndependent_rows_iff_isUnit.mpr isUnit_one
  have valid := search_sound core.toBilin' _ independent change returned
  rw [matrix_familySpan_eq_top _ independent] at valid
  exact (triangularBasis_matrix_iff core change).mp valid

theorem congruenceTriangularize_none_iff {n : ℕ} (core : Matrix (Fin n) (Fin n) F2) :
    congruenceTriangularize core = none ↔
      ¬∃ change : Matrix (Fin n) (Fin n) F2,
        IsUnit change ∧ IsUnitLowerTriangular (change * core * Matrix.transpose change) := by
  have independent : LinearIndependent F2 (1 : Matrix (Fin n) (Fin n) F2) :=
    Matrix.linearIndependent_rows_iff_isUnit.mpr isUnit_one
  apply (search_none_iff core.toBilin' (1 : Matrix (Fin n) (Fin n) F2) independent).trans
  apply not_congr
  apply exists_congr
  intro change
  rw [matrix_familySpan_eq_top _ independent]
  exact triangularBasis_matrix_iff core change

theorem core_search_none_iff {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n) :
    congruenceTriangularize presentation.core = none ↔ ¬presentation.IsTriangularizable :=
  congruenceTriangularize_none_iff presentation.core

example : congruenceTriangularize (1 : Matrix (Fin 0) (Fin 0) F2) = some 1 := by decide

example : congruenceTriangularize (1 : Matrix (Fin 2) (Fin 2) F2) = some 1 := by decide

example : congruenceTriangularize (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F2) = none := by
  decide

example :
    alternatingCheck (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F2).toBilin'
      (1 : Matrix (Fin 2) (Fin 2) F2) = false := by decide

example :
    let core : Matrix (Fin 3) (Fin 3) F2 := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
    let standard : Matrix (Fin 3) (Fin 3) F2 := 1
    tryPick core.toBilin' standard (search core.toBilin') (standard 0) = none ∧
      congruenceTriangularize core = some !![1, 1, 0; 1, 0, 1; 1, 1, 1] := by decide

end PaulimerFormal.Triangularization
