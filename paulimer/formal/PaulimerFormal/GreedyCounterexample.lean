import PaulimerFormal.GreedyDecomposition
import PaulimerFormal.TransvectionImplementation

/-! A three-qubit action with a four-factor greedy output and a three-factor witness. -/

namespace PaulimerFormal.GreedyCounterexample

open GreedyReduction GreedySearch GreedyDecomposition TransvectionRefinement

def vector (code : BitVec 6) : PhaseVector 3 :=
  BinarBridge.ofFinVector fun index => BinarFormal.Packed.Bool.toF2 (code.getLsbD index.val)

def matrix (rows : Fin 6 → BitVec 6) : ActionMatrix 3 :=
  fun row => vector (rows (BinarBridge.phaseIndexEquiv 3 row))

def initial : SymplecticAction 3 :=
  ⟨matrix ![30, 63, 18, 23, 59, 29], by rw [SymplecticGroup.mem_iff]; decide +kernel⟩

def second : SymplecticAction 3 :=
  ⟨matrix ![1, 32, 18, 8, 36, 2], by rw [SymplecticGroup.mem_iff]; decide +kernel⟩

def third : SymplecticAction 3 :=
  ⟨matrix ![1, 32, 48, 8, 6, 2], by rw [SymplecticGroup.mem_iff]; decide +kernel⟩

def fourth : SymplecticAction 3 :=
  ⟨matrix ![1, 20, 4, 8, 6, 54], by rw [SymplecticGroup.mem_iff]; decide +kernel⟩

def shortCenters : List (PhaseVector 3) := [vector 9, vector 61, vector 43]

def greedyCenters : List (PhaseVector 3) := [vector 22, vector 52, vector 34, vector 31]

theorem short_replay : IsFactorization initial shortCenters := by
  apply Subtype.ext
  decide +kernel

theorem initial_selected : nextVector (initial : ActionMatrix 3) = some (vector 1) := by decide +kernel
theorem second_selected : nextVector (second : ActionMatrix 3) = some (vector 2) := by decide +kernel
theorem third_selected : nextVector (third : ActionMatrix 3) = some (vector 4) := by decide +kernel
theorem fourth_selected : nextVector (fourth : ActionMatrix 3) = some (vector 2) := by decide +kernel

theorem initial_center : residueVector (initial : ActionMatrix 3) (vector 1) = vector 31 := by decide +kernel
theorem second_center : residueVector (second : ActionMatrix 3) (vector 2) = vector 34 := by decide +kernel
theorem third_center : residueVector (third : ActionMatrix 3) (vector 4) = vector 52 := by decide +kernel
theorem fourth_center : residueVector (fourth : ActionMatrix 3) (vector 2) = vector 22 := by decide +kernel

theorem initial_step : initial * transvectionAction (vector 31) = second := by
  apply Subtype.ext
  decide +kernel

theorem second_step : second * transvectionAction (vector 34) = third := by
  apply Subtype.ext
  decide +kernel

theorem third_step : third * transvectionAction (vector 52) = fourth := by
  apply Subtype.ext
  decide +kernel

theorem fourth_step : fourth * transvectionAction (vector 22) = 1 := by
  apply Subtype.ext
  decide +kernel

theorem greedy_eq : decomposition initial = greedyCenters := by
  rw [decomposition_of_some initial (vector 1) initial_selected, initial_center, initial_step,
    decomposition_of_some second (vector 2) second_selected, second_center, second_step,
    decomposition_of_some third (vector 4) third_selected, third_center, third_step,
    decomposition_of_some fourth (vector 2) fourth_selected, fourth_center, fourth_step,
    decomposition_of_none (1 : SymplecticAction 3)
      ((nextVector_none_iff (1 : ActionMatrix 3)).mpr rfl)]
  rfl

theorem not_shortest : ¬IsShortest initial (decomposition initial) := by
  intro shortest
  have bound := shortest.2 shortCenters short_replay
  rw [greedy_eq] at bound
  norm_num [greedyCenters, shortCenters] at bound

theorem witness_spec :
    IsFactorization initial shortCenters ∧ shortCenters.length = 3 ∧
    decomposition initial = greedyCenters ∧ greedyCenters.length = 4 ∧
    ¬IsShortest initial (decomposition initial) :=
  ⟨short_replay, rfl, greedy_eq, rfl, not_shortest⟩

end PaulimerFormal.GreedyCounterexample
