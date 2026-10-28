import PaulimerFormal.GreedyReduction
import PaulimerFormal.BinarBridge

/-! Ordered standard-vector and pair search for greedy residue updates. -/

namespace PaulimerFormal.GreedySearch

open Triangularization GreedyReduction

section Selection

variable {V : Type*} [AddCommGroup V] [Module F2 V]

def pairCandidates {n : ℕ} (basis : Fin n → V) : List V :=
  (List.finRange n).flatMap fun first =>
    ((List.finRange n).filter fun second => decide (first < second)).map
      fun second => basis first + basis second

def activeCandidates {n : ℕ} (basis : Fin n → V) : List V :=
  List.ofFn basis ++ pairCandidates basis

def findActive {n : ℕ} (form : LinearMap.BilinForm F2 V) (basis : Fin n → V) : Option V :=
  (activeCandidates basis).find? fun vector => decide (form vector vector = 1)

omit [Module F2 V] in
theorem basis_mem_candidates {n : ℕ} (basis : Fin n → V) (index : Fin n) :
    basis index ∈ activeCandidates basis := by
  simp [activeCandidates]

omit [Module F2 V] in
theorem pair_mem_candidates {n : ℕ} (basis : Fin n → V) (first second : Fin n)
    (before : first < second) : basis first + basis second ∈ activeCandidates basis := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨first, by simp, List.mem_map.mpr ⟨second, ?_, rfl⟩⟩
  simp [before]

theorem candidate_mem_span {n : ℕ} (basis : Fin n → V) (vector : V)
    (member : vector ∈ activeCandidates basis) : vector ∈ familySpan basis := by
  rcases List.mem_append.mp member with singleton | pair
  · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp singleton
    exact member_familySpan basis index
  · obtain ⟨first, _, member⟩ := List.mem_flatMap.mp pair
    obtain ⟨second, _, rfl⟩ := List.mem_map.mp member
    exact (familySpan basis).add_mem (member_familySpan basis first) (member_familySpan basis second)

theorem findActive_some {n : ℕ} (form : LinearMap.BilinForm F2 V) (basis : Fin n → V)
    (vector : V) (returned : findActive form basis = some vector) : form vector vector = 1 := by
  have accepted : decide (form vector vector = 1) = true :=
    List.find?_some (p := fun candidate => decide (form candidate candidate = 1)) returned
  exact of_decide_eq_true accepted

theorem findActive_none_iff {n : ℕ} (form : LinearMap.BilinForm F2 V) (basis : Fin n → V) :
    findActive form basis = none ↔ ∀ vector ∈ familySpan basis, form vector vector = 0 := by
  constructor
  · intro rejected
    have zero (vector : V) (member : vector ∈ activeCandidates basis) : form vector vector = 0 := by
      have failed := List.find?_eq_none.mp rejected vector member
      by_contra nonzero
      simp [f2_eq_one_of_ne_zero _ nonzero] at failed
    have diagonal (index : Fin n) := zero _ (basis_mem_candidates basis index)
    apply (alternatingCheck_iff form basis).mp
    rw [alternatingCheck, decide_eq_true_eq]
    intro index
    refine ⟨diagonal index, ?_⟩
    intro earlier before
    have sum_zero := zero _ (pair_mem_candidates basis earlier index before)
    have cross_zero : form (basis earlier) (basis index) + form (basis index) (basis earlier) = 0 := by
      simpa [diagonal] using sum_zero
    have equal : form (basis earlier) (basis index) = form (basis index) (basis earlier) := by
      simpa using eq_neg_of_add_eq_zero_left cross_zero
    exact equal.symm
  · intro alternating
    apply List.find?_eq_none.mpr
    intro vector member
    simp [alternating vector (candidate_mem_span basis vector member)]

theorem pair_test_eq {n : ℕ} (form : LinearMap.BilinForm F2 V) (basis : Fin n → V)
    (diagonal : ∀ index, form (basis index) (basis index) = 0) (first second : Fin n) :
    form (basis first + basis second) (basis first + basis second) =
      form (basis first) (basis second) + form (basis second) (basis first) := by
  simp [diagonal]

theorem findActive_eq_ordered_loops {n : ℕ} (form : LinearMap.BilinForm F2 V) (basis : Fin n → V) :
    findActive form basis =
      match (List.ofFn basis).find? (fun vector => decide (form vector vector = 1)) with
      | some vector => some vector
      | none =>
          (List.finRange n).findSome? fun first =>
            (((List.finRange n).filter fun second => decide (first < second)).find?
              fun second => decide
                (form (basis first) (basis second) + form (basis second) (basis first) = 1)).map
              fun second => basis first + basis second := by
  rw [findActive, activeCandidates, List.find?_append]
  cases singles : (List.ofFn basis).find? (fun vector => decide (form vector vector = 1)) with
  | some vector => simp
  | none =>
      have diagonal (index : Fin n) : form (basis index) (basis index) = 0 := by
        have failed := List.find?_eq_none.mp singles (basis index) (by simp)
        by_contra nonzero
        simp [f2_eq_one_of_ne_zero _ nonzero] at failed
      simp [pairCandidates, List.find?_flatMap, List.find?_map, diagonal]

end Selection

theorem cross_test_eq_xor (first second : F2) :
    decide (first + second = 1) = (decide (first = 1) ^^ decide (second = 1)) := by
  fin_cases first <;> fin_cases second <;> decide

def standardBasis (m : ℕ) (index : Fin (m + m)) : PhaseVector m :=
  Pi.single ((BinarBridge.phaseIndexEquiv m).symm index) 1

theorem standardBasis_span (m : ℕ) : familySpan (standardBasis m) = ⊤ := by
  have family : standardBasis m =
      fun index => ((Pi.basisFun F2 (PhaseIndex m)).reindex (BinarBridge.phaseIndexEquiv m)) index := by
    funext index
    simp only [Module.Basis.reindex_apply, Pi.basisFun_apply]
    rfl
  rw [family]
  exact ((Pi.basisFun F2 (PhaseIndex m)).reindex (BinarBridge.phaseIndexEquiv m)).span_eq

theorem findActive_standard_none_iff {m : ℕ} (action : ActionMatrix m) :
    findActive (imageForm action) (standardBasis m) = none ↔ IsHyperbolic action := by
  rw [findActive_none_iff, standardBasis_span]
  simp only [Submodule.mem_top, forall_true_left, imageForm_apply, IsHyperbolic]

theorem residueVector_eq_zero_iff {m : ℕ} (action : ActionMatrix m) (vector : PhaseVector m) :
    residueVector action vector = 0 ↔ rowAction vector action = vector := by
  change vector + rowAction vector action = 0 ↔ _
  constructor
  · intro zero
    simpa only [ZModModule.neg_eq_self] using (eq_neg_of_add_eq_zero_left zero).symm
  · intro fixed
    rw [fixed, ZModModule.add_self]

def findMoved {m : ℕ} (action : ActionMatrix m) : Option (PhaseVector m) :=
  (List.ofFn (standardBasis m)).find? fun vector => decide (residueVector action vector ≠ 0)

theorem findMoved_none_iff {m : ℕ} (action : ActionMatrix m) :
    findMoved action = none ↔ action = 1 := by
  constructor
  · intro rejected
    have fixed (index : Fin (m + m)) : rowAction (standardBasis m index) action = standardBasis m index := by
      have failed := List.find?_eq_none.mp rejected (standardBasis m index) (by simp)
      have zero : residueVector action (standardBasis m index) = 0 := by simpa using failed
      exact (residueVector_eq_zero_iff _ _).mp zero
    ext row column
    have entry := congrFun (fixed (BinarBridge.phaseIndexEquiv m row)) column
    simpa [standardBasis, rowAction, Matrix.one_apply, Pi.single_apply, eq_comm] using entry
  · rintro rfl
    apply List.find?_eq_none.mpr
    intro vector _
    simp [residueVector, ZModModule.add_self]

def nextVector {m : ℕ} (action : ActionMatrix m) : Option (PhaseVector m) :=
  match findActive (imageForm action) (standardBasis m) with
  | some vector => some vector
  | none => findMoved action

theorem nextVector_none_iff {m : ℕ} (action : ActionMatrix m) :
    nextVector action = none ↔ action = 1 := by
  constructor
  · intro rejected
    cases active : findActive (imageForm action) (standardBasis m) with
    | some vector => simp [nextVector, active] at rejected
    | none =>
        apply (findMoved_none_iff action).mp
        simpa [nextVector, active] using rejected
  · intro identity
    have hyperbolic : IsHyperbolic action := by simp [IsHyperbolic, identity]
    simp [nextVector, (findActive_standard_none_iff action).mpr hyperbolic,
      (findMoved_none_iff action).mpr identity]

theorem nextVector_some {m : ℕ} (action : ActionMatrix m) (vector : PhaseVector m)
    (returned : nextVector action = some vector) :
    residueVector action vector ≠ 0 ∧
      (pairing vector (rowAction vector action) = 1 ∨ IsHyperbolic action) := by
  cases active : findActive (imageForm action) (standardBasis m) with
  | some selected =>
      have same : selected = vector := by simpa [nextVector, active] using returned
      subst selected
      have paired := findActive_some (imageForm action) (standardBasis m) vector active
      rw [imageForm_apply] at paired
      refine ⟨?_, Or.inl paired⟩
      intro zero
      rw [(residueVector_eq_zero_iff action vector).mp zero, pairing_self] at paired
      exact zero_ne_one paired
  | none =>
      have moved : findMoved action = some vector := by simpa [nextVector, active] using returned
      have accepted : decide (residueVector action vector ≠ 0) = true :=
        List.find?_some (p := fun candidate => decide (residueVector action candidate ≠ 0)) moved
      exact ⟨of_decide_eq_true accepted,
        Or.inr ((findActive_standard_none_iff action).mp active)⟩

theorem selection_spec {m : ℕ} (action : ActionMatrix m) :
    (nextVector action = none ↔ action = 1) ∧
    (∀ vector, nextVector action = some vector →
      residueVector action vector ≠ 0 ∧
        (pairing vector (rowAction vector action) = 1 ∨ IsHyperbolic action)) := by
  exact ⟨nextVector_none_iff action, nextVector_some action⟩

end PaulimerFormal.GreedySearch
