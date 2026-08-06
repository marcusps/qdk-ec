import PaulimerFormal.UpperBound

/-!
# Executable reference decomposition

This deliberately simple finite search is a specification, not a performance
port of paulimer's optimized Rust implementation.
-/

namespace PaulimerFormal

def f2Values : List F2 := [0, 1]

@[simp]
theorem mem_f2Values (value : F2) : value ∈ f2Values := by
  by_cases value_zero : value = 0
  · subst value
    exact List.mem_cons_self
  · rw [f2_eq_one_of_ne_zero value value_zero]
    exact List.mem_cons_of_mem 0
      (List.mem_cons_self : (1 : F2) ∈ [1])

def allFinFunctions (values : List α) :
    (length : ℕ) → List (Fin length → α)
  | 0 => [Fin.elim0]
  | length + 1 =>
      values.flatMap fun head =>
        (allFinFunctions values length).map (Fin.cons head)

theorem mem_allFinFunctions (values : List α)
    (complete : ∀ value : α, value ∈ values)
    {length : ℕ} (function : Fin length → α) :
    function ∈ allFinFunctions values length := by
  induction length with
  | zero =>
      have function_eq : function = Fin.elim0 := by
        funext index
        exact Fin.elim0 index
      simp [allFinFunctions, function_eq]
  | succ length inductionHypothesis =>
      let head := function 0
      let tail : Fin length → α := fun index => function index.succ
      rw [allFinFunctions, List.mem_flatMap]
      refine ⟨head, complete head, ?_⟩
      rw [List.mem_map]
      refine ⟨tail, inductionHypothesis tail, ?_⟩
      funext index
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · rfl
      · rfl

def allPhaseVectors (m : ℕ) : List (PhaseVector m) :=
  (allFinFunctions f2Values m).flatMap fun xPart =>
    (allFinFunctions f2Values m).map fun zPart =>
      Sum.elim xPart zPart

theorem mem_allPhaseVectors {m : ℕ} (vector : PhaseVector m) :
    vector ∈ allPhaseVectors m := by
  let xPart : Fin m → F2 := fun index => vector (Sum.inl index)
  let zPart : Fin m → F2 := fun index => vector (Sum.inr index)
  rw [allPhaseVectors, List.mem_flatMap]
  refine ⟨xPart, mem_allFinFunctions f2Values mem_f2Values xPart, ?_⟩
  rw [List.mem_map]
  refine ⟨zPart, mem_allFinFunctions f2Values mem_f2Values zPart, ?_⟩
  funext index
  cases index <;> rfl

def factorizationSearch {m : ℕ} (target : SymplecticAction m)
    (length : ℕ) : Option (Fin length → PhaseVector m) :=
  (allFinFunctions (allPhaseVectors m) length).find? fun centers =>
    decide
      ((productTransvections (List.ofFn centers) : ActionMatrix m) =
        (target : ActionMatrix m))

theorem factorizationSearch_isSome_iff
    {m : ℕ} (target : SymplecticAction m) (length : ℕ) :
    (factorizationSearch target length).isSome ↔
      ∃ centers : Fin length → PhaseVector m,
        IsFactorization target (List.ofFn centers) := by
  constructor
  · intro is_some
    obtain ⟨centers, found⟩ :=
      Option.isSome_iff_exists.mp is_some
    refine ⟨centers, ?_⟩
    have accepted := List.find?_some found
    apply Subtype.ext
    simpa [factorizationSearch] using accepted
  · rintro ⟨centers, factorization⟩
    apply Option.isSome_iff_ne_none.mpr
    intro search_none
    have rejected :=
      (List.find?_eq_none.mp search_none) centers
        (mem_allFinFunctions (allPhaseVectors m)
          mem_allPhaseVectors centers)
    apply rejected
    simp only [decide_eq_true_eq]
    exact congrArg Subtype.val factorization

theorem factorizationSearch_of_eq_some
    {m : ℕ} {target : SymplecticAction m} {length : ℕ}
    {centers : Fin length → PhaseVector m}
    (found : factorizationSearch target length = some centers) :
    IsFactorization target (List.ofFn centers) := by
  have accepted := List.find?_some found
  apply Subtype.ext
  simpa [factorizationSearch] using accepted

def minimalDecompositionAtRank? {m : ℕ} (target : SymplecticAction m)
    (rank : ℕ) :
    Option (List (PhaseVector m)) :=
  match factorizationSearch target rank with
  | some centers => some (List.ofFn centers)
  | none =>
      (factorizationSearch target (rank + 1)).map List.ofFn

noncomputable def minimalDecomposition? {m : ℕ}
    (target : SymplecticAction m) : Option (List (PhaseVector m)) :=
  minimalDecompositionAtRank? target
    (residueRank (target : ActionMatrix m))

theorem minimalDecomposition_spec
    {m : ℕ} (target : SymplecticAction m) :
    ∃ centers : List (PhaseVector m),
      minimalDecomposition? target = some centers ∧
        IsFactorization target centers ∧
        (∀ other : List (PhaseVector m),
          IsFactorization target other →
            centers.length ≤ other.length) ∧
        (centers.length = residueRank (target : ActionMatrix m) ∨
          centers.length = residueRank (target : ActionMatrix m) + 1) ∧
        (centers.length = residueRank (target : ActionMatrix m) ↔
          (canonicalCorePresentation target).IsTriangularizable) := by
  classical
  let rank := residueRank (target : ActionMatrix m)
  cases search_eq : factorizationSearch target rank with
  | some family =>
      have factorization :=
        factorizationSearch_of_eq_some search_eq
      refine ⟨List.ofFn family, ?_, factorization, ?_, ?_, ?_⟩
      · change minimalDecompositionAtRank? target rank =
          some (List.ofFn family)
        rw [minimalDecompositionAtRank?, search_eq]
      · intro other other_factorization
        simpa [rank] using
          residueRank_le_length_of_factorization other_factorization
      · left
        simp [rank]
      · constructor
        · intro _
          apply (CorePresentation.exists_factorization_iff_isTriangularizable
            (canonicalCorePresentation target)).mp
          exact ⟨family, factorization⟩
        · intro _
          simp [rank]
  | none =>
      have no_rank_factorization :
          ¬∃ family : Fin rank → PhaseVector m,
            IsFactorization target (List.ofFn family) := by
        intro exists_factorization
        have is_some :=
          (factorizationSearch_isSome_iff target rank).mpr
            exists_factorization
        simp [search_eq] at is_some
      obtain ⟨successorFamily, successorFactorization⟩ :=
        exists_residueRank_succ_factorization target
      have successor_search_is_some :
          (factorizationSearch target (rank + 1)).isSome :=
        (factorizationSearch_isSome_iff target (rank + 1)).mpr
          ⟨successorFamily, successorFactorization⟩
      obtain ⟨foundFamily, found_eq⟩ :=
        Option.isSome_iff_exists.mp successor_search_is_some
      have found_factorization :
          IsFactorization target (List.ofFn foundFamily) :=
        factorizationSearch_of_eq_some found_eq
      refine ⟨List.ofFn foundFamily, ?_, found_factorization, ?_, ?_, ?_⟩
      · change minimalDecompositionAtRank? target rank =
          some (List.ofFn foundFamily)
        simp only [minimalDecompositionAtRank?, search_eq, found_eq,
          Option.map_some]
      · intro other other_factorization
        have lower : rank ≤ other.length := by
          simpa [rank] using
            residueRank_le_length_of_factorization other_factorization
        by_contra not_le
        have below : other.length < rank + 1 :=
          Nat.lt_of_not_ge (by simpa using not_le)
        have length_eq : other.length = rank :=
          Nat.le_antisymm (Nat.le_of_lt_succ below) lower
        apply no_rank_factorization
        let reindexed : Fin rank → PhaseVector m :=
          fun index => other.get ((finCongr length_eq).symm index)
        refine ⟨reindexed, ?_⟩
        have list_eq : List.ofFn reindexed = other := by
          apply List.ext_get
          · simp [reindexed, length_eq]
          · intro index leftBound rightBound
            simp [reindexed, finCongr]
            rfl
        rwa [list_eq]
      · right
        simp [rank]
      · constructor
        · intro length_eq
          simp [rank] at length_eq
        · intro triangularizable
          exfalso
          apply no_rank_factorization
          exact (CorePresentation.exists_factorization_iff_isTriangularizable
            (canonicalCorePresentation target)).mpr triangularizable

end PaulimerFormal
