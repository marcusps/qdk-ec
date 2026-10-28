import PaulimerFormal.TwoQubitMinimality
import PaulimerFormal.TwoQubitRank

/-! Exact shortest lengths and the nonhyperbolic exceptions in Sp(4,2). -/

namespace PaulimerFormal.TwoQubitEnumeration

open TransvectionRefinement

theorem certifiedLength_iff (frame : Frame) (member : frame ∈ frames) (length : ℕ) :
    frame.certifiedLength = some length ↔
      ∃ centers, IsShortest (frame.action member) centers ∧ centers.length = length := by
  rw [certifiedLength_eq frame member, Option.some.injEq]
  constructor
  · intro same
    exact ⟨GreedyDecomposition.decomposition (frame.action member),
      greedy_shortest (frame.action member), same⟩
  · rintro ⟨centers, shortest, length_eq⟩
    have same := Nat.le_antisymm
      ((greedy_shortest (frame.action member)).2 centers shortest.1)
      (shortest.2 _ (GreedyDecomposition.decomposition_spec (frame.action member)).1)
    exact same.trans length_eq

def Frame.rankPlusOne (frame : Frame) : Bool :=
  !frame.hyperbolic && (frame.certifiedLength == some (frame.rank + 1))

theorem rankPlusOne_iff (frame : Frame) (member : frame ∈ frames) :
    frame.rankPlusOne = true ↔
      ¬GreedyReduction.IsHyperbolic frame.matrix ∧
      ∃ centers, IsShortest (frame.action member) centers ∧
        centers.length = residueRank frame.matrix + 1 := by
  have rejected : (!frame.hyperbolic) = true ↔ ¬GreedyReduction.IsHyperbolic frame.matrix := by
    rw [← hyperbolic_iff]
    cases frame.hyperbolic <;> decide
  simp only [Frame.rankPlusOne, Bool.and_eq_true, rejected, beq_iff_eq,
    rank_eq, certifiedLength_iff frame member]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem rank_plus_one_count :
    (frames.filter Frame.rankPlusOne).length = 210 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem shortest_length_distribution :
    (List.finRange 6).map
      (fun length => (frames.filter fun frame => frame.certifiedLength == some length.val).length) =
        [1, 15, 85, 225, 274, 120] := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem hyperbolic_rank_two_checked :
    (frames.all fun frame =>
      decide (frame.rank = 2 → frame.hyperbolic = true → frame.certifiedLength = some 3)) = true := by
  decide +kernel

theorem hyperbolic_rank_two_length (frame : Frame) (member : frame ∈ frames)
    (rank : residueRank frame.matrix = 2) (hyperbolic : GreedyReduction.IsHyperbolic frame.matrix) :
    (GreedyDecomposition.decomposition (frame.action member)).length = 3 := by
  have checked := of_decide_eq_true (List.all_eq_true.mp hyperbolic_rank_two_checked frame member)
  have length := checked ((rank_eq frame).trans rank) ((hyperbolic_iff frame).mpr hyperbolic)
  rw [certifiedLength_eq frame member] at length
  exact Option.some.inj length

theorem rank_three_obstructed_length (frame : Frame) (member : frame ∈ frames)
    (obstructed : frame.rankThreeObstructed = true) : frame.certifiedLength = some 4 := by
  obtain ⟨rank, not_hyperbolic, obstruction⟩ := (rankThreeObstructed_iff frame).mp obstructed
  rw [certifiedLength_eq frame member, Option.some.injEq]
  cases returned : GreedySearch.nextVector frame.matrix with
  | none =>
      have identity := (GreedySearch.nextVector_none_iff frame.matrix).mp returned
      exact (not_hyperbolic (by simp [GreedyReduction.IsHyperbolic, identity])).elim
  | some chosen =>
      have selected := GreedySearch.nextVector_some frame.matrix chosen returned
      have active := selected.2.resolve_right not_hyperbolic
      have lowering := GreedyReduction.lowering_rank (frame.action member) chosen active
      change residueRank (frame.matrix * transvection (GreedyReduction.residueVector frame.matrix chosen)) + 1 =
        residueRank frame.matrix at lowering
      have smaller : residueRank
          (frame.matrix * transvection (GreedyReduction.residueVector frame.matrix chosen)) < 3 := by omega
      obtain ⟨rank_two, hyperbolic⟩ := obstruction _ smaller
      obtain ⟨center, decoded⟩ := vector_surjective (GreedyReduction.residueVector frame.matrix chosen)
      have updated_rank : residueRank (frame.update center).matrix = 2 := by
        rwa [matrix_update, decoded]
      have updated_hyperbolic : GreedyReduction.IsHyperbolic (frame.update center).matrix := by
        rwa [matrix_update, decoded]
      have length := hyperbolic_rank_two_length (frame.update center)
        (update_mem_frames frame member center) updated_rank updated_hyperbolic
      rw [action_update frame member, decoded] at length
      rw [GreedyDecomposition.decomposition_of_some (frame.action member) chosen returned,
        List.length_append, List.length_singleton]
      simpa only [Frame.action] using congrArg (fun value : ℕ => value + 1) length

theorem classification_spec :
    (∀ target : SymplecticAction 2,
      IsShortest target (GreedyDecomposition.decomposition target)) ∧
    (∀ (frame : Frame) (member : frame ∈ frames),
      frame.rankPlusOne = true ↔
        ¬GreedyReduction.IsHyperbolic frame.matrix ∧
        ∃ centers, IsShortest (frame.action member) centers ∧
          centers.length = residueRank frame.matrix + 1) ∧
    (frames.filter Frame.rankPlusOne).length = 210 ∧
    (∀ (frame : Frame) (member : frame ∈ frames),
      frame.rankThreeObstructed = true →
        ∃ centers, IsShortest (frame.action member) centers ∧ centers.length = 4) ∧
    (frames.filter Frame.rankThreeObstructed).length = 90 ∧
    (List.finRange 6).map
      (fun length => (frames.filter fun frame => frame.certifiedLength == some length.val).length) =
        [1, 15, 85, 225, 274, 120] := by
  refine ⟨greedy_shortest, rankPlusOne_iff, rank_plus_one_count, ?_,
    rank_three_obstruction_count, shortest_length_distribution⟩
  intro frame member obstructed
  exact (certifiedLength_iff frame member 4).mp (rank_three_obstructed_length frame member obstructed)

end PaulimerFormal.TwoQubitEnumeration
