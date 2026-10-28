import PaulimerFormal.TwoQubitAction
import PaulimerFormal.GreedyDecomposition

/-! Four-bit execution of the verified ordered greedy decomposition. -/

namespace PaulimerFormal.TwoQubitEnumeration

open GreedyReduction GreedySearch

def standardCodes : List (BitVec 4) := [1, 2, 4, 8]

def activeCodes : List (BitVec 4) := [1, 2, 4, 8, 3, 5, 9, 6, 10, 12]

theorem standardCodes_vectors :
    List.ofFn (standardBasis 2) = standardCodes.map vector := by decide

theorem activeCodes_vectors :
    activeCandidates (standardBasis 2) = activeCodes.map vector := by decide

def Frame.nextCode (frame : Frame) : Option (BitVec 4) :=
  match activeCodes.find? (fun code => paired code (frame.image code)) with
  | some code => some code
  | none => standardCodes.find? fun code => decide (frame.image code ≠ code)

theorem nextCode_refines (frame : Frame) :
    nextVector frame.matrix = frame.nextCode.map vector := by
  have active_test (code : BitVec 4) :
      decide (imageForm frame.matrix (vector code) (vector code) = 1) =
        paired code (frame.image code) := by
    rw [imageForm_apply, ← vector_image, ← paired_eq_pairing]
    cases paired code (frame.image code) <;> rfl
  have moved_test (code : BitVec 4) :
      decide (residueVector frame.matrix (vector code) ≠ 0) =
        decide (frame.image code ≠ code) := by
    simp only [ne_eq, residueVector_eq_zero_iff, ← vector_image, vector_injective.eq_iff]
  have active :
      findActive (imageForm frame.matrix) (standardBasis 2) =
        (activeCodes.find? fun code => paired code (frame.image code)).map vector := by
    rw [findActive, activeCodes_vectors, List.find?_map]
    simp only [Function.comp_def, active_test]
  have moved :
      findMoved frame.matrix =
        (standardCodes.find? fun code => decide (frame.image code ≠ code)).map vector := by
    rw [findMoved, standardCodes_vectors, List.find?_map]
    simp only [Function.comp_def, moved_test]
  rw [nextVector, active, Frame.nextCode]
  cases activeCodes.find? (fun code => paired code (frame.image code)) <;> simp [moved]

def Frame.center (frame : Frame) (code : BitVec 4) : BitVec 4 :=
  code ^^^ frame.image code

theorem vector_center (frame : Frame) (code : BitVec 4) :
    vector (frame.center code) = residueVector frame.matrix (vector code) := by
  rw [Frame.center, vector_xor, vector_image]
  rfl

def Frame.greedy : ℕ → Frame → Option (List (BitVec 4))
  | 0, _ => none
  | fuel + 1, frame =>
      match frame.nextCode with
      | none => some []
      | some code =>
          (Frame.greedy fuel (frame.update (frame.center code))).map
            fun earlier => earlier ++ [frame.center code]

theorem action_update (frame : Frame) (member : frame ∈ frames) (center : BitVec 4) :
    (frame.update center).action (update_mem_frames frame member center) =
      frame.action member * transvectionAction (vector center) :=
  Subtype.ext (matrix_update frame center)

theorem greedy_refines (fuel : ℕ) (frame : Frame) (member : frame ∈ frames)
    (enough : GreedyDecomposition.potential frame.matrix < fuel) :
    (Frame.greedy fuel frame).map (List.map vector) =
      some (GreedyDecomposition.decomposition (frame.action member)) := by
  induction fuel generalizing frame with
  | zero => omega
  | succ fuel induction =>
      cases selected : frame.nextCode with
      | none =>
          have returned : nextVector frame.matrix = none := by
            rw [nextCode_refines, selected]
            rfl
          rw [GreedyDecomposition.decomposition_of_none (frame.action member) returned]
          simp [Frame.greedy, selected]
      | some code =>
          have returned : nextVector frame.matrix = some (vector code) := by
            rw [nextCode_refines, selected]
            rfl
          have decrease := GreedyDecomposition.step_decreases (frame.action member) (vector code) returned
          have smaller : GreedyDecomposition.potential (frame.update (frame.center code)).matrix < fuel := by
            rw [matrix_update, vector_center]
            change GreedyDecomposition.potential
              ((frame.action member : ActionMatrix 2) *
                transvection (residueVector (frame.action member : ActionMatrix 2) (vector code))) < fuel
            change GreedyDecomposition.potential (frame.action member : ActionMatrix 2) < fuel + 1 at enough
            omega
          have recursive := induction (frame.update (frame.center code))
            (update_mem_frames frame member (frame.center code)) smaller
          rw [action_update frame member, vector_center] at recursive
          rw [GreedyDecomposition.decomposition_of_some (frame.action member) (vector code) returned]
          simp only [Frame.greedy, selected, Option.map_map, Function.comp_def, List.map_append,
            List.map_cons, List.map_nil, vector_center]
          cases result : Frame.greedy fuel (frame.update (frame.center code)) <;>
            simp_all [Frame.action]

theorem greedy_ten_refines (frame : Frame) (member : frame ∈ frames) :
    (Frame.greedy 10 frame).map (List.map vector) =
      some (GreedyDecomposition.decomposition (frame.action member)) :=
  greedy_refines 10 frame member (by
    have bound := GreedyDecomposition.potential_bound frame.matrix
    omega)

theorem greedy_spec (frame : Frame) (member : frame ∈ frames) :
    ∃ centers : List (BitVec 4),
      Frame.greedy 10 frame = some centers ∧
      centers.map vector = GreedyDecomposition.decomposition (frame.action member) ∧
      IsFactorization (frame.action member) (centers.map vector) ∧
      centers.length ≤ 9 ∧
      ∀ center ∈ centers, center ≠ 0 := by
  have refined := greedy_ten_refines frame member
  have correct := GreedyDecomposition.decomposition_spec (frame.action member)
  have bound := GreedyDecomposition.potential_bound frame.matrix
  cases result : Frame.greedy 10 frame with
  | none => simp [result] at refined
  | some centers =>
      have same : centers.map vector = GreedyDecomposition.decomposition (frame.action member) := by
        simpa only [result, Option.map_some, Option.some.injEq] using refined
      refine ⟨centers, rfl, same, same.symm ▸ correct.1, ?_, ?_⟩
      · have length_bound := correct.2.1
        rw [← same, List.length_map] at length_bound
        change centers.length ≤ GreedyDecomposition.potential frame.matrix at length_bound
        omega
      · intro center member zero
        have nonzero := correct.2.2 (vector center) (same ▸ List.mem_map_of_mem member)
        exact nonzero (zero ▸ vector_zero)

end PaulimerFormal.TwoQubitEnumeration
