import PaulimerFormal.TwoQubitAction
import Mathlib.FieldTheory.Finiteness

/-! Computing residue rank by counting the finite fixed space. -/

namespace PaulimerFormal.TwoQubitEnumeration

def Frame.fixedCodes (frame : Frame) : List (BitVec 4) :=
  codes.filter fun code => frame.image code == code

theorem mem_fixedCodes_iff (frame : Frame) (code : BitVec 4) :
    code ∈ frame.fixedCodes ↔ vector code ∈ fixedSpace frame.matrix := by
  simp only [Frame.fixedCodes, List.mem_filter, mem_codes, true_and, beq_iff_eq]
  rw [← vector_injective.eq_iff, vector_image, mem_fixedSpace_iff]

theorem fixedCodes_length (frame : Frame) :
    frame.fixedCodes.length = Nat.card (fixedSpace frame.matrix) := by
  let mapping : {code : BitVec 4 // code ∈ frame.fixedCodes} → fixedSpace frame.matrix :=
    fun code => ⟨vector code.val, (mem_fixedCodes_iff frame code.val).mp code.property⟩
  have injective : Function.Injective mapping := by
    intro left right same
    exact Subtype.ext (vector_injective (congrArg Subtype.val same))
  have surjective : Function.Surjective mapping := by
    intro target
    obtain ⟨code, same⟩ := vector_surjective target.val
    have member : code ∈ frame.fixedCodes :=
      (mem_fixedCodes_iff frame code).mpr (same.symm ▸ target.property)
    exact ⟨⟨code, member⟩, Subtype.ext same⟩
  have distinct : frame.fixedCodes.Nodup :=
    (show codes.Nodup by decide).filter _
  have code_card :
      Nat.card {code : BitVec 4 // code ∈ frame.fixedCodes} = frame.fixedCodes.length := by
    simpa only [Nat.card_fin] using
      (Nat.card_congr (List.Nodup.getEquiv frame.fixedCodes distinct)).symm
  exact code_card.symm.trans (Nat.card_congr (Equiv.ofBijective mapping ⟨injective, surjective⟩))

theorem fixedCodes_length_pow (frame : Frame) :
    frame.fixedCodes.length = 2 ^ Module.finrank F2 (fixedSpace frame.matrix) := by
  rw [fixedCodes_length, Module.natCard_eq_pow_finrank (K := F2), Nat.card_zmod]

def Frame.rank (frame : Frame) : ℕ :=
  4 - frame.fixedCodes.length.log2

theorem rank_eq (frame : Frame) : frame.rank = residueRank frame.matrix := by
  rw [Frame.rank, fixedCodes_length_pow, Nat.log2_two_pow]
  have dimension := residueRank_add_finrank_fixedSpace frame.matrix
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem rank_distribution :
    (List.finRange 5).map (fun rank => (frames.filter fun frame => frame.rank == rank.val).length) =
      [1, 15, 100, 300, 304] := by
  decide +kernel

def Frame.rankThreeObstructed (frame : Frame) : Bool :=
  decide (frame.rank = 3 ∧ frame.hyperbolic = false) &&
    codes.all fun center =>
      let updated := frame.update center
      decide (updated.rank < 3 → updated.rank = 2 ∧ updated.hyperbolic = true)

theorem rankThreeObstructed_iff (frame : Frame) :
    frame.rankThreeObstructed = true ↔
      residueRank frame.matrix = 3 ∧ ¬GreedyReduction.IsHyperbolic frame.matrix ∧
      ∀ center : PhaseVector 2, residueRank (frame.matrix * transvection center) < 3 →
        residueRank (frame.matrix * transvection center) = 2 ∧
          GreedyReduction.IsHyperbolic (frame.matrix * transvection center) := by
  have rejected : frame.hyperbolic = false ↔ ¬GreedyReduction.IsHyperbolic frame.matrix := by
    rw [← hyperbolic_iff]
    cases frame.hyperbolic <;> simp
  simp only [Frame.rankThreeObstructed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  rw [rank_eq, rejected]
  constructor
  · rintro ⟨⟨rank, not_hyperbolic⟩, updates⟩
    refine ⟨rank, not_hyperbolic, ?_⟩
    intro target lowering
    obtain ⟨center, rfl⟩ := vector_surjective target
    have lower : (frame.update center).rank < 3 := by
      rwa [rank_eq, matrix_update]
    obtain ⟨rank_two, hyperbolic⟩ := updates center (mem_codes center) lower
    exact ⟨by simpa only [rank_eq, matrix_update] using rank_two,
      by simpa only [hyperbolic_iff, matrix_update] using hyperbolic⟩
  · rintro ⟨rank, not_hyperbolic, updates⟩
    refine ⟨⟨rank, not_hyperbolic⟩, ?_⟩
    intro center _ lower
    have lowering : residueRank (frame.matrix * transvection (vector center)) < 3 := by
      simpa only [← matrix_update, ← rank_eq] using lower
    obtain ⟨rank_two, hyperbolic⟩ := updates (vector center) lowering
    exact ⟨by simpa only [rank_eq, matrix_update] using rank_two,
      by simpa only [hyperbolic_iff, matrix_update] using hyperbolic⟩

private def obstructionCount (firstX : BitVec 4) : ℕ :=
  ((framesFrom firstX).filter Frame.rankThreeObstructed).length

section ObstructionCounts

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem obstructionCount_zero : obstructionCount 0 = 0 := by decide +kernel
private theorem obstructionCount_one : obstructionCount 1 = 6 := by decide +kernel
private theorem obstructionCount_two : obstructionCount 2 = 10 := by decide +kernel
private theorem obstructionCount_three : obstructionCount 3 = 10 := by decide +kernel
private theorem obstructionCount_four : obstructionCount 4 = 3 := by decide +kernel
private theorem obstructionCount_five : obstructionCount 5 = 3 := by decide +kernel
private theorem obstructionCount_six : obstructionCount 6 = 3 := by decide +kernel
private theorem obstructionCount_seven : obstructionCount 7 = 3 := by decide +kernel
private theorem obstructionCount_eight : obstructionCount 8 = 10 := by decide +kernel
private theorem obstructionCount_nine : obstructionCount 9 = 10 := by decide +kernel
private theorem obstructionCount_ten : obstructionCount 10 = 10 := by decide +kernel
private theorem obstructionCount_eleven : obstructionCount 11 = 10 := by decide +kernel
private theorem obstructionCount_twelve : obstructionCount 12 = 3 := by decide +kernel
private theorem obstructionCount_thirteen : obstructionCount 13 = 3 := by decide +kernel
private theorem obstructionCount_fourteen : obstructionCount 14 = 3 := by decide +kernel
private theorem obstructionCount_fifteen : obstructionCount 15 = 3 := by decide +kernel

end ObstructionCounts

theorem rank_three_obstruction_count :
    (frames.filter Frame.rankThreeObstructed).length = 90 := by
  rw [frames, List.filter_flatMap, List.length_flatMap]
  change (codes.map obstructionCount).sum = 90
  have values : codes = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] := by decide
  rw [values]
  norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    obstructionCount_zero, obstructionCount_one, obstructionCount_two, obstructionCount_three,
    obstructionCount_four, obstructionCount_five, obstructionCount_six, obstructionCount_seven,
    obstructionCount_eight, obstructionCount_nine, obstructionCount_ten, obstructionCount_eleven,
    obstructionCount_twelve, obstructionCount_thirteen, obstructionCount_fourteen, obstructionCount_fifteen]

theorem rank_spec :
    (∀ frame : Frame, frame.rank = residueRank frame.matrix) ∧
    (∀ frame : Frame, frame.rankThreeObstructed = true ↔
      residueRank frame.matrix = 3 ∧ ¬GreedyReduction.IsHyperbolic frame.matrix ∧
      ∀ center : PhaseVector 2, residueRank (frame.matrix * transvection center) < 3 →
        residueRank (frame.matrix * transvection center) = 2 ∧
          GreedyReduction.IsHyperbolic (frame.matrix * transvection center)) ∧
    (frames.filter Frame.rankThreeObstructed).length = 90 ∧
    (List.finRange 5).map (fun rank => (frames.filter fun frame => frame.rank == rank.val).length) =
      [1, 15, 100, 300, 304] :=
  ⟨rank_eq, rankThreeObstructed_iff, rank_three_obstruction_count, rank_distribution⟩

end PaulimerFormal.TwoQubitEnumeration
