import PaulimerFormal.SymplecticPadding
import PaulimerFormal.GreedyBlockLength

/-! Exact four-step greedy counterexamples in every dimension at least three. -/

namespace PaulimerFormal.GreedyPadding

open SymplecticPadding GreedyBlocks GreedyReduction GreedySearch GreedyDecomposition
open TransvectionRefinement

theorem basis_prefix (extra : ℕ) :
    ∃ tail, List.ofFn (standardBasis (3 + extra)) =
      xBasis.map (SymplecticPadding.embed extra) ++ tail := by
  rw [List.ofFn_add]
  change ∃ tail : List (PhaseVector (3 + extra)),
    List.ofFn (fun index : Fin (3 + extra) => standardBasis (3 + extra) (Fin.castAdd (3 + extra) index)) ++
      List.ofFn (fun index : Fin (3 + extra) => standardBasis (3 + extra) (Fin.natAdd (3 + extra) index)) = _
  simp only [standardBasis, ← BinarBridge.phaseIndexEquiv_inl,
    ← BinarBridge.phaseIndexEquiv_inr, Equiv.symm_apply_apply]
  rw [List.ofFn_add, List.append_assoc]
  refine ⟨(List.ofFn fun index : Fin extra =>
    (Pi.single (Sum.inl (Fin.natAdd 3 index)) 1 : PhaseVector (3 + extra))) ++
      List.ofFn (fun index : Fin (3 + extra) => Pi.single (Sum.inr index) 1), ?_⟩
  congr 1
  rw [xBasis, List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  rw [Function.comp_apply, SymplecticPadding.embed_single]
  rfl

def selected (extra : ℕ) (stage : Fin 5) : PhaseVector (3 + extra) :=
  SymplecticPadding.embed extra (Pi.single (Sum.inl (localChoice stage)) 1)

theorem active_prefix (extra : ℕ) (stage : Fin 5) :
    ((xBasis.map (SymplecticPadding.embed extra)).find? fun vector =>
      decide (imageForm (action 3 extra (localAction stage) : ActionMatrix (3 + extra))
        vector vector = 1)) =
      if activeStage stage then some (selected extra stage) else none := by
  rw [List.find?_map]
  simp only [Function.comp_apply, imageForm_apply, embed_rowAction, embed_pairing, local_active_selection]
  cases activeStage stage <;> rfl

theorem moved_prefix (extra : ℕ) (stage : Fin 5)
    (inactive : activeStage stage = false) (unfinished : stage ≠ 4) :
    ((xBasis.map (SymplecticPadding.embed extra)).find? fun vector =>
      decide (residueVector (action 3 extra (localAction stage) : ActionMatrix (3 + extra))
        vector ≠ 0)) = some (selected extra stage) := by
  rw [List.find?_map]
  simp only [Function.comp_apply, ne_eq, embed_residueVector, ← SymplecticPadding.embed_zero extra 3,
    (SymplecticPadding.embed_injective extra 3).eq_iff]
  rw [local_inactive_moved stage inactive]
  simp [unfinished, selected]

theorem nextVector_stage (extra : ℕ) (stage : Fin 5) (unfinished : stage ≠ 4) :
    nextVector (action 3 extra (localAction stage) : ActionMatrix (3 + extra)) =
      some (selected extra stage) := by
  obtain ⟨tail, basis⟩ := basis_prefix extra
  cases active : activeStage stage with
  | true =>
      have accepted := active_prefix extra stage
      simp only [active, ↓reduceIte] at accepted
      simp [nextVector, findActive, activeCandidates, basis, List.find?_append, accepted]
  | false =>
      have hyperbolic := hyperbolic_action extra (localAction stage) (local_inactive_hyperbolic stage active)
      have rejected := (findActive_standard_none_iff _).mpr hyperbolic
      rw [nextVector, rejected]
      change findMoved (action 3 extra (localAction stage) : ActionMatrix (3 + extra)) = _
      rw [findMoved, basis, List.find?_append, moved_prefix extra stage active unfinished]
      rfl

theorem step (extra : ℕ) (stage : Fin 5) (unfinished : stage ≠ 4) :
    action 3 extra (localAction stage) *
      transvectionAction (residueVector
        (action 3 extra (localAction stage) : ActionMatrix (3 + extra)) (selected extra stage)) =
      action 3 extra (localAction (advance stage)) := by
  rw [selected, embed_residueVector, embed_transvection, ← map_mul, local_step stage unfinished]

theorem length_stage (extra : ℕ) (stage : Fin 5) :
    (decomposition (action 3 extra (localAction stage))).length = 4 - stage.val := by
  by_cases finished : stage = 4
  · subst stage
    have identity : localAction 4 = 1 := rfl
    rw [identity, map_one, decomposition_of_none 1 ((nextVector_none_iff _).mpr rfl)]
    rfl
  · have recursive := length_stage extra (advance stage)
    rw [decomposition_of_some _ _ (nextVector_stage extra stage finished), step extra stage finished,
      List.length_append, List.length_singleton, recursive]
    exact advance_weight stage finished
termination_by 4 - stage.val
decreasing_by
  have drop := advance_weight stage finished
  omega

theorem padded_spec (extra : ℕ) :
    IsFactorization (action 3 extra GreedyCounterexample.initial)
      (GreedyCounterexample.shortCenters.map (SymplecticPadding.embed extra)) ∧
    (GreedyCounterexample.shortCenters.map (SymplecticPadding.embed extra)).length = 3 ∧
    (decomposition (action 3 extra GreedyCounterexample.initial)).length = 4 ∧
    ¬IsShortest (action 3 extra GreedyCounterexample.initial)
      (decomposition (action 3 extra GreedyCounterexample.initial)) := by
  have replay : IsFactorization (action 3 extra GreedyCounterexample.initial)
      (GreedyCounterexample.shortCenters.map (SymplecticPadding.embed extra)) := by
    change productTransvections _ = _
    rw [embed_product, GreedyCounterexample.short_replay]
  have shorter : (GreedyCounterexample.shortCenters.map (SymplecticPadding.embed extra)).length = 3 := by
    simp [GreedyCounterexample.shortCenters]
  have greedy : (decomposition (action 3 extra GreedyCounterexample.initial)).length = 4 :=
    length_stage extra 0
  refine ⟨replay, shorter, greedy, ?_⟩
  intro minimal
  have bound := minimal.2 _ replay
  rw [shorter, greedy] at bound
  omega

theorem all_dimensions (size : ℕ) (at_least_three : 3 ≤ size) :
    ∃ (target : SymplecticAction size) (centers : List (PhaseVector size)),
      IsFactorization target centers ∧ centers.length = 3 ∧
      (decomposition target).length = 4 ∧ ¬IsShortest target (decomposition target) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le at_least_three
  exact ⟨_, _, padded_spec extra⟩

end PaulimerFormal.GreedyPadding
