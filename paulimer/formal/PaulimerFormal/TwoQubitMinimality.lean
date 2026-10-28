import PaulimerFormal.TwoQubitGreedy
import PaulimerFormal.TwoQubitDistances
import PaulimerFormal.TransvectionImplementation
import Mathlib.Data.List.Induction

/-! A finite neighbor certificate bounds every transvection word. -/

namespace PaulimerFormal.TwoQubitEnumeration

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem lengths_checked :
    (frames.all fun frame =>
      decide (frame.certifiedLength = (Frame.greedy 10 frame).map List.length)) = true := by
  decide +kernel

theorem certifiedLength_eq (frame : Frame) (member : frame ∈ frames) :
    frame.certifiedLength =
      some (GreedyDecomposition.decomposition (frame.action member)).length := by
  obtain ⟨centers, returned, same, _⟩ := greedy_spec frame member
  have checked := of_decide_eq_true (List.all_eq_true.mp lengths_checked frame member)
  rw [checked, returned, Option.map_some, ← same, List.length_map]

def Frame.neighborCheck (frame : Frame) : Bool :=
  match frame.certifiedLength with
  | none => false
  | some length =>
      codes.all fun center =>
        match (frame.update center).certifiedLength with
        | none => false
        | some neighboring => decide (length ≤ neighboring + 1)

private def neighborsFrom (firstX : BitVec 4) : Bool :=
  (framesFrom firstX).all Frame.neighborCheck

section NeighborChecks

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem neighborsFrom_zero : neighborsFrom 0 = true := by decide +kernel
private theorem neighborsFrom_one : neighborsFrom 1 = true := by decide +kernel
private theorem neighborsFrom_two : neighborsFrom 2 = true := by decide +kernel
private theorem neighborsFrom_three : neighborsFrom 3 = true := by decide +kernel
private theorem neighborsFrom_four : neighborsFrom 4 = true := by decide +kernel
private theorem neighborsFrom_five : neighborsFrom 5 = true := by decide +kernel
private theorem neighborsFrom_six : neighborsFrom 6 = true := by decide +kernel
private theorem neighborsFrom_seven : neighborsFrom 7 = true := by decide +kernel
private theorem neighborsFrom_eight : neighborsFrom 8 = true := by decide +kernel
private theorem neighborsFrom_nine : neighborsFrom 9 = true := by decide +kernel
private theorem neighborsFrom_ten : neighborsFrom 10 = true := by decide +kernel
private theorem neighborsFrom_eleven : neighborsFrom 11 = true := by decide +kernel
private theorem neighborsFrom_twelve : neighborsFrom 12 = true := by decide +kernel
private theorem neighborsFrom_thirteen : neighborsFrom 13 = true := by decide +kernel
private theorem neighborsFrom_fourteen : neighborsFrom 14 = true := by decide +kernel
private theorem neighborsFrom_fifteen : neighborsFrom 15 = true := by decide +kernel

end NeighborChecks

theorem all_neighbors : frames.all Frame.neighborCheck = true := by
  rw [frames, List.all_flatMap]
  change codes.all neighborsFrom = true
  have values : codes = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
  rw [values]
  simp only [List.all_cons, List.all_nil,
    neighborsFrom_zero, neighborsFrom_one, neighborsFrom_two, neighborsFrom_three,
    neighborsFrom_four, neighborsFrom_five, neighborsFrom_six, neighborsFrom_seven,
    neighborsFrom_eight, neighborsFrom_nine, neighborsFrom_ten, neighborsFrom_eleven,
    neighborsFrom_twelve, neighborsFrom_thirteen, neighborsFrom_fourteen, neighborsFrom_fifteen,
    Bool.and_self]

theorem neighborCheck_spec (frame : Frame) (member : frame ∈ frames)
    (center : BitVec 4) :
    (GreedyDecomposition.decomposition (frame.action member)).length ≤
      (GreedyDecomposition.decomposition
        ((frame.update center).action (update_mem_frames frame member center))).length + 1 := by
  have checked := List.all_eq_true.mp all_neighbors frame member
  simp only [Frame.neighborCheck, certifiedLength_eq frame member] at checked
  have bound := List.all_eq_true.mp checked center (mem_codes center)
  simpa only [certifiedLength_eq (frame.update center) (update_mem_frames frame member center),
    decide_eq_true_eq] using bound

theorem greedy_neighbor (target : SymplecticAction 2) (center : PhaseVector 2) :
    (GreedyDecomposition.decomposition target).length ≤
      (GreedyDecomposition.decomposition (target * transvectionAction center)).length + 1 := by
  obtain ⟨frame, same⟩ := matrix_surjective (target : ActionMatrix 2)
  have member : frame ∈ frames := by
    rw [mem_frames_iff, canonical_iff_symplectic, same]
    exact target.property
  have action_same : frame.action member = target := Subtype.ext same
  obtain ⟨code, decoded⟩ := vector_surjective center
  have bound := neighborCheck_spec frame member code
  rw [action_update frame member, action_same, decoded] at bound
  exact bound

theorem greedy_length_le_word (centers : List (PhaseVector 2)) :
    (GreedyDecomposition.decomposition (productTransvections centers)).length ≤ centers.length := by
  induction centers using List.reverseRecOn with
  | nil =>
      have empty := GreedyDecomposition.decomposition_of_none (1 : SymplecticAction 2)
        ((GreedySearch.nextVector_none_iff (1 : ActionMatrix 2)).mpr rfl)
      simp only [productTransvections_nil, empty, List.length_nil, le_refl]
  | append_singleton earlier center induction =>
      have bound := greedy_neighbor (productTransvections (earlier ++ [center])) center
      have squared : transvectionAction center * transvectionAction center = 1 :=
        Subtype.ext (transvection_squared center)
      have cancel :
          productTransvections (earlier ++ [center]) * transvectionAction center =
            productTransvections earlier := by
        rw [productTransvections_append, productTransvections_cons, productTransvections_nil,
          mul_one, mul_assoc, squared, mul_one]
      rw [cancel] at bound
      simpa only [List.length_append, List.length_singleton] using
        bound.trans (Nat.add_le_add_right induction 1)

theorem greedy_shortest (target : SymplecticAction 2) :
    TransvectionRefinement.IsShortest target (GreedyDecomposition.decomposition target) := by
  refine ⟨(GreedyDecomposition.decomposition_spec target).1, ?_⟩
  intro other factorization
  have bound := greedy_length_le_word other
  rwa [factorization] at bound

end PaulimerFormal.TwoQubitEnumeration
