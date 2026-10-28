import PaulimerFormal.UpperBound

/-!
# Checked transvection candidates and retained-search contracts

Refinement contracts for PR #217 at
`2ce895eda84473762d7db36bf6c3561460992858`.
`checkCandidate` models the final unsigned acceptance test after vector
lengths have been checked. Its types enforce the fixed `2m` coordinates.
Core presentations and rejection of triangularizability remain explicit
contracts for the Rust row reducer and complete congruence search.
-/

namespace PaulimerFormal.TransvectionRefinement

def IsShortest {m : ℕ} (target : SymplecticAction m)
    (centers : List (PhaseVector m)) : Prop :=
  IsFactorization target centers ∧
    ∀ other, IsFactorization target other → centers.length ≤ other.length

def checkCandidate {m : ℕ} (target : ActionMatrix m) (rank : ℕ)
    (centers : List (PhaseVector m)) : Bool :=
  decide (centers.length = rank + 1) &&
    centers.all (fun center => decide (center ≠ 0)) &&
    decide ((productTransvections centers : ActionMatrix m) = target)

theorem checkCandidate_iff {m : ℕ} (target : SymplecticAction m)
    (rank : ℕ) (centers : List (PhaseVector m)) :
    checkCandidate (target : ActionMatrix m) rank centers = true ↔
      centers.length = rank + 1 ∧
        (∀ center ∈ centers, center ≠ 0) ∧
        IsFactorization target centers := by
  have replay_iff :
      (productTransvections centers : ActionMatrix m) = (target : ActionMatrix m) ↔
        IsFactorization target centers :=
    ⟨fun equal => Subtype.ext equal, fun equal => congrArg Subtype.val equal⟩
  simp only [checkCandidate, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, replay_iff, and_assoc]

theorem shortest_of_rank_length {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (centers : List (PhaseVector m))
    (factorization : IsFactorization target centers)
    (length_eq : centers.length = n) :
    IsShortest target centers := by
  refine ⟨factorization, ?_⟩
  intro other other_factorization
  rw [length_eq, presentation.rank_eq]
  exact residueRank_le_length_of_factorization other_factorization

theorem shortest_of_rejected_core {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (not_triangularizable : ¬presentation.IsTriangularizable)
    (centers : List (PhaseVector m))
    (factorization : IsFactorization target centers)
    (length_eq : centers.length = n + 1) :
    IsShortest target centers := by
  refine ⟨factorization, ?_⟩
  intro other other_factorization
  have lower : n ≤ other.length := by
    rw [presentation.rank_eq]
    exact residueRank_le_length_of_factorization other_factorization
  have not_equal : other.length ≠ n := by
    intro equal
    exact not_triangularizable
      (presentation.isTriangularizable_of_factorization_length_eq
        other other_factorization equal)
  omega

theorem checked_candidate_spec {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (not_triangularizable : ¬presentation.IsTriangularizable)
    (centers : List (PhaseVector m))
    (accepted : checkCandidate (target : ActionMatrix m) n centers = true) :
    IsShortest target centers ∧
      centers.length = n + 1 ∧ ∀ center ∈ centers, center ≠ 0 := by
  obtain ⟨length_eq, nonzero, factorization⟩ :=
    (checkCandidate_iff target n centers).mp accepted
  exact ⟨shortest_of_rejected_core presentation not_triangularizable
    centers factorization length_eq, length_eq, nonzero⟩

/-- The coefficient validator's mathematical postconditions suffice for replay,
even without the separate action comparison. -/
theorem bordered_family_spec {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (not_triangularizable : ¬presentation.IsTriangularizable)
    (coefficients : Matrix (Fin (n + 1)) (Fin n) F2)
    (relation : Fin (n + 1) → F2)
    (valid : IsBorderedTriangularization presentation.core coefficients relation) :
    IsShortest target (List.ofFn (coefficients * presentation.basis)) := by
  exact shortest_of_rejected_core presentation not_triangularizable _
    (factorizationOfBordered presentation coefficients relation valid)
    List.length_ofFn

/-- A recursive factorization of `F T_w`, followed by `w`, has the required
order and is minimal on the rejected-core branch. -/
theorem retained_fallback_spec {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (not_triangularizable : ¬presentation.IsTriangularizable)
    (fix : PhaseVector m) (centers : List (PhaseVector m))
    (updated_factorization :
      IsFactorization (target * transvectionAction fix) centers)
    (length_eq : centers.length = n) :
    IsShortest target (centers ++ [fix]) := by
  apply shortest_of_rejected_core presentation not_triangularizable
  · change productTransvections (centers ++ [fix]) = target
    rw [productTransvections_append]
    change productTransvections centers *
      (transvectionAction fix * 1) = target
    rw [mul_one, updated_factorization, mul_assoc]
    have squared : transvectionAction fix * transvectionAction fix = 1 := by
      apply Subtype.ext
      exact transvection_squared fix
    rw [squared, mul_one]
  · simp [length_eq]

example :
    checkCandidate (1 : ActionMatrix 0) 0 [0] = false := by decide

end PaulimerFormal.TransvectionRefinement
