import PaulimerFormal.ResidueExtraction
import PaulimerFormal.TransvectionImplementation

/-!
# Complete residue-fix search

Enumerate the computed residue basis in little-endian coefficient order and
accept the first nonzero fix preserving rank whose updated core triangularizes.
-/

namespace PaulimerFormal.ResidueFixSearch

open ResidueExtraction Triangularization
open scoped Matrix

def acceptsFix {m : ℕ} (action : ActionMatrix m) (fix : PhaseVector m) : Bool :=
  decide (fix ≠ 0) &&
    decide (ResidueExtraction.rank (action * transvection fix) = ResidueExtraction.rank action) &&
    (memoizedTriangularize (core (action * transvection fix))).isSome

theorem acceptsFix_iff {m : ℕ} (target : SymplecticAction m) (fix : PhaseVector m) :
    acceptsFix (target : ActionMatrix m) fix = true ↔
      fix ≠ 0 ∧
        residueRank ((target * transvectionAction fix : SymplecticAction m) : ActionMatrix m) =
          residueRank (target : ActionMatrix m) ∧
        (canonicalCorePresentation (target * transvectionAction fix)).IsTriangularizable := by
  classical
  have rejection := ResidueExtraction.core_search_none_iff (target * transvectionAction fix)
  change memoizedTriangularize (core ((target : ActionMatrix m) * transvection fix)) = none ↔
    ¬(canonicalCorePresentation (target * transvectionAction fix)).IsTriangularizable at rejection
  simp only [acceptsFix, Bool.and_eq_true, decide_eq_true_eq, rank_eq,
    Option.isSome_iff_ne_none, and_assoc]
  exact and_congr Iff.rfl (and_congr Iff.rfl ((not_congr rejection).trans not_not))

def findFix {m : ℕ} (action : ActionMatrix m) : Option (PhaseVector m) :=
  (spanVectors (basis action)).find? (acceptsFix action)

theorem spanVectors_lift {m n : ℕ} (vectors : Matrix (Fin n) (PhaseIndex m) F2) :
    (spanVectors (1 : Matrix (Fin n) (Fin n) F2)).map (fun coefficients => coefficients ᵥ* vectors) =
      spanVectors vectors := by
  have standard (bits : Fin n → Bool) :
      selectedSum (1 : Matrix (Fin n) (Fin n) F2) bits =
        fun index => if bits index then (1 : F2) else 0 := by
    funext index
    unfold selectedSum
    rw [Finset.sum_apply]
    change (∑ row : Fin n, (if bits row then (1 : F2) else 0) *
      (if row = index then 1 else 0)) = _
    simp [mul_ite]
  simp only [spanVectors, List.map_map]
  apply List.map_congr_left
  intro bits _
  funext column
  simp only [Function.comp_apply, standard]
  change (∑ index : Fin n, (if bits index then (1 : F2) else 0) * vectors index column) =
    (∑ index : Fin n, (if bits index then (1 : F2) else 0) • vectors index) column
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem findFix_sound {m : ℕ} (target : SymplecticAction m) (fix : PhaseVector m)
    (found : findFix (target : ActionMatrix m) = some fix) :
    fix ≠ 0 ∧ fix ∈ residueSpace (target : ActionMatrix m) ∧
      residueRank ((target * transvectionAction fix : SymplecticAction m) : ActionMatrix m) =
        residueRank (target : ActionMatrix m) ∧
      (canonicalCorePresentation (target * transvectionAction fix)).IsTriangularizable := by
  have accepted := List.find?_some (p := acceptsFix (target : ActionMatrix m)) found
  obtain ⟨nonzero, same_rank, triangular⟩ := (acceptsFix_iff target fix).mp accepted
  have member := List.mem_of_find?_eq_some found
  have in_span := ((mem_spanVectors_iff (basis _) (basis_independent _) fix).mp member).1
  change fix ∈ Submodule.span F2 (Set.range (basis (target : ActionMatrix m))) at in_span
  rw [basis_span] at in_span
  exact ⟨nonzero, in_span, same_rank, triangular⟩

theorem findFix_complete {m : ℕ} (target : SymplecticAction m)
    (rejected : ¬(canonicalCorePresentation target).IsTriangularizable) :
    findFix (target : ActionMatrix m) ≠ none := by
  obtain ⟨fix, nonzero, in_span, same_rank, triangular⟩ :=
    exists_residue_fix_of_not_triangularizable target rejected
  have member : fix ∈ spanVectors (basis (target : ActionMatrix m)) := by
    apply (mem_spanVectors_iff _ (basis_independent _) fix).mpr
    exact ⟨by simpa only [familySpan, basis_span] using in_span, nonzero⟩
  have accepted := (acceptsFix_iff target fix).mpr ⟨nonzero, same_rank, triangular⟩
  intro failed
  have not_accepted := List.find?_eq_none.mp failed fix member
  simp [accepted] at not_accepted

theorem fix_enters_rank_branch {m : ℕ} (target : SymplecticAction m) (fix : PhaseVector m)
    (found : findFix (target : ActionMatrix m) = some fix) :
    rankDecomposition ((target * transvectionAction fix : SymplecticAction m) : ActionMatrix m) ≠
      none := by
  intro rejected
  exact (rankDecomposition_none_iff _).mp rejected (findFix_sound target fix found).2.2.2

def minimalDecomposition {m : ℕ} (target : SymplecticAction m) : List (PhaseVector m) :=
  match branch : rankDecomposition (target : ActionMatrix m) with
  | some centers => centers
  | none =>
      match found : findFix (target : ActionMatrix m) with
      | none => False.elim
          ((findFix_complete target ((rankDecomposition_none_iff target).mp branch)) found)
      | some fix => minimalDecomposition (target * transvectionAction fix) ++ [fix]
termination_by if (rankDecomposition (target : ActionMatrix m)).isSome then 0 else 1
decreasing_by
  have enters := Option.isSome_iff_ne_none.mpr (fix_enters_rank_branch target fix found)
  change (rankDecomposition ((target : ActionMatrix m) * transvection fix)).isSome = true at enters
  simp [enters, branch]

theorem minimalDecomposition_of_some {m : ℕ} (target : SymplecticAction m)
    (centers : List (PhaseVector m))
    (returned : rankDecomposition (target : ActionMatrix m) = some centers) :
    minimalDecomposition target = centers := by
  rw [minimalDecomposition]
  split <;> simp_all

theorem minimalDecomposition_of_fix {m : ℕ} (target : SymplecticAction m)
    (rejected : rankDecomposition (target : ActionMatrix m) = none)
    (fix : PhaseVector m) (found : findFix (target : ActionMatrix m) = some fix) :
    minimalDecomposition target = minimalDecomposition (target * transvectionAction fix) ++ [fix] := by
  rw [minimalDecomposition]
  split
  · simp_all
  · split <;> simp_all

theorem minimalDecomposition_spec {m : ℕ} (target : SymplecticAction m) :
    TransvectionRefinement.IsShortest target (minimalDecomposition target) := by
  cases branch : rankDecomposition (target : ActionMatrix m) with
  | some centers =>
      rw [minimalDecomposition_of_some target centers branch]
      have valid := rankDecomposition_some_spec target centers branch
      exact ⟨valid.1, valid.2.2⟩
  | none =>
      have not_triangular := (rankDecomposition_none_iff target).mp branch
      cases found : findFix (target : ActionMatrix m) with
      | none => exact ((findFix_complete target not_triangular) found).elim
      | some fix =>
          have accepted := findFix_sound target fix found
          cases updated : rankDecomposition
              ((target * transvectionAction fix : SymplecticAction m) : ActionMatrix m) with
          | none => exact ((fix_enters_rank_branch target fix found) updated).elim
          | some centers =>
              rw [minimalDecomposition_of_fix target branch fix found,
                minimalDecomposition_of_some _ centers updated]
              have valid := rankDecomposition_some_spec _ centers updated
              exact TransvectionRefinement.retained_fallback_spec
                (canonicalCorePresentation target) not_triangular fix centers valid.1
                (valid.2.1.trans accepted.2.2.1)

def checkedDecomposition {m : ℕ} (target : SymplecticAction m)
    (candidate : Option (List (PhaseVector m))) : List (PhaseVector m) :=
  match branch : rankDecomposition (target : ActionMatrix m) with
  | some centers => centers
  | none =>
      match candidate.filter
          (TransvectionRefinement.checkCandidate (target : ActionMatrix m)
            (ResidueExtraction.rank (target : ActionMatrix m))) with
      | some centers => centers
      | none =>
          match found : findFix (target : ActionMatrix m) with
          | none => False.elim
              ((findFix_complete target ((rankDecomposition_none_iff target).mp branch)) found)
          | some fix => minimalDecomposition (target * transvectionAction fix) ++ [fix]

theorem checkedDecomposition_spec {m : ℕ} (target : SymplecticAction m)
    (candidate : Option (List (PhaseVector m))) :
    TransvectionRefinement.IsShortest target (checkedDecomposition target candidate) := by
  unfold checkedDecomposition
  split
  · rename_i centers returned
    have valid := rankDecomposition_some_spec target centers returned
    exact ⟨valid.1, valid.2.2⟩
  · rename_i rejected
    have not_triangular := (rankDecomposition_none_iff target).mp rejected
    split
    · rename_i centers accepted
      have test := (Option.filter_eq_some_iff.mp accepted).2
      exact (TransvectionRefinement.checked_candidate_spec
        (canonicalCorePresentation target) not_triangular centers
        (by simpa only [rank_eq] using test)).1
    · split
      · rename_i failed
        exact ((findFix_complete target not_triangular) failed).elim
      · rename_i fix found
        rw [← minimalDecomposition_of_fix target rejected fix found]
        exact minimalDecomposition_spec target

theorem shortest_nonzero {m : ℕ} {target : SymplecticAction m}
    {centers : List (PhaseVector m)} (shortest : TransvectionRefinement.IsShortest target centers) :
    ∀ center ∈ centers, center ≠ 0 := by
  intro center member zero
  subst center
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  have identity : transvectionAction (0 : PhaseVector m) = 1 := by
    apply Subtype.ext
    exact transvection_zero
  have factors : IsFactorization target (before ++ after) := by
    change productTransvections (before ++ after) = target
    rw [← shortest.1, split, productTransvections_append, productTransvections_append,
      productTransvections_cons, identity, one_mul]
  have lower := shortest.2 (before ++ after) factors
  rw [split] at lower
  simp only [List.length_append, List.length_cons] at lower
  omega

theorem checkedDecomposition_nonzero {m : ℕ} (target : SymplecticAction m)
    (candidate : Option (List (PhaseVector m))) :
    ∀ center ∈ checkedDecomposition target candidate, center ≠ 0 :=
  shortest_nonzero (checkedDecomposition_spec target candidate)

theorem fullSearch_spec {m : ℕ} (target : SymplecticAction m)
    (candidate : Option (List (PhaseVector m))) :
    (¬(canonicalCorePresentation target).IsTriangularizable →
      findFix (target : ActionMatrix m) ≠ none) ∧
    (∀ fix, findFix (target : ActionMatrix m) = some fix →
      rankDecomposition ((target * transvectionAction fix : SymplecticAction m) : ActionMatrix m) ≠
        none) ∧
    TransvectionRefinement.IsShortest target (minimalDecomposition target) ∧
    TransvectionRefinement.IsShortest target (checkedDecomposition target candidate) ∧
    (∀ center ∈ checkedDecomposition target candidate, center ≠ 0) :=
  ⟨findFix_complete target, fix_enters_rank_branch target, minimalDecomposition_spec target,
    checkedDecomposition_spec target candidate, checkedDecomposition_nonzero target candidate⟩

end PaulimerFormal.ResidueFixSearch
