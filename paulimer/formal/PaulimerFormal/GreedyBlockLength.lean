import PaulimerFormal.GreedyBlockSelection

/-! Exact greedy lengths for arbitrary disjoint witness blocks. -/

namespace PaulimerFormal.GreedyBlocks

open GreedyReduction GreedyDecomposition TransvectionRefinement

def advanceAt {count : ℕ} (stages : Fin count → Fin 5) (block : Fin count) : Fin count → Fin 5 :=
  Function.update stages block (advance (stages block))

theorem stateAction_step (count : ℕ) (stages : Fin count → Fin 5) (block : Fin count)
    (unfinished : stages block ≠ 4) :
    stateAction count stages *
      transvectionAction (residueVector (stateAction count stages : ActionMatrix (count * 3))
        (selectedVector count stages block)) =
      stateAction count (advanceAt stages block) := by
  change stateAction count stages *
    transvectionAction (residueVector
      (matrices count (fun block => (localAction (stages block) : ActionMatrix 3)))
      (embed count block (Pi.single (Sum.inl (localChoice (stages block))) 1))) = _
  rw [residueVector_embed, transvection_embed, stateAction, stateAction, ← map_mul]
  apply congrArg (actions count)
  funext other
  by_cases same : other = block
  · subst other
    simpa [advanceAt] using local_step (stages block) unfinished
  · simp [advanceAt, same]

def weight {count : ℕ} (stages : Fin count → Fin 5) : ℕ :=
  ∑ block, (4 - (stages block).val)

theorem advance_weight (stage : Fin 5) (unfinished : stage ≠ 4) :
    (4 - (advance stage).val) + 1 = 4 - stage.val := by
  fin_cases stage <;> simp [advance] at unfinished ⊢

theorem weight_advance (count : ℕ) (stages : Fin count → Fin 5) (block : Fin count)
    (unfinished : stages block ≠ 4) :
    weight (advanceAt stages block) + 1 = weight stages := by
  calc
    weight (advanceAt stages block) + 1 =
        ∑ other, ((4 - (advanceAt stages block other).val) + if other = block then 1 else 0) := by
      simp [weight, Finset.sum_add_distrib]
    _ = weight stages := by
      apply Finset.sum_congr rfl
      intro other _
      by_cases same : other = block
      · subst other
        simpa [advanceAt] using advance_weight (stages block) unfinished
      · simp [advanceAt, same]

theorem length_states (count : ℕ) (stages : Fin count → Fin 5) :
    (decomposition (stateAction count stages)).length = weight stages := by
  rcases block_selection_spec count stages with ⟨returned, finished⟩ | ⟨block, unfinished, returned⟩
  · rw [decomposition_of_none (stateAction count stages) returned]
    simp [weight, finished]
  · have recursive := length_states count (advanceAt stages block)
    rw [decomposition_of_some (stateAction count stages) (selectedVector count stages block) returned,
      stateAction_step count stages block unfinished, List.length_append, List.length_singleton, recursive]
    exact weight_advance count stages block unfinished
termination_by weight stages
decreasing_by
  have drop := weight_advance count stages block unfinished
  omega

theorem repeated_length (count : ℕ) :
    (decomposition (repeated count)).length = count * 4 := by
  have initial : stateAction count (fun _ => 0) = repeated count := rfl
  rw [← initial, length_states]
  simp [weight]

theorem repeated_not_shortest (count : ℕ) (positive : 0 < count) :
    ¬IsShortest (repeated count) (decomposition (repeated count)) := by
  intro shortest
  have bound := shortest.2 (shortCenters count) (shortCenters_replay count)
  rw [repeated_length, shortCenters_length] at bound
  omega

theorem unbounded_excess (gap : ℕ) :
    ∃ (target : SymplecticAction (gap * 3)) (centers : List (PhaseVector (gap * 3))),
      IsFactorization target centers ∧
      centers.length + gap = (decomposition target).length ∧
      ∀ shortest, IsShortest target shortest →
        shortest.length + gap ≤ (decomposition target).length := by
  refine ⟨repeated gap, shortCenters gap, shortCenters_replay gap, ?_, ?_⟩
  · rw [shortCenters_length, repeated_length]
    omega
  · intro shortest minimal
    have bound := minimal.2 (shortCenters gap) (shortCenters_replay gap)
    rw [shortCenters_length] at bound
    rw [repeated_length]
    omega

end PaulimerFormal.GreedyBlocks
