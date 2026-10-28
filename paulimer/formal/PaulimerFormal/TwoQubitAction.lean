import PaulimerFormal.TwoQubitEnumeration
import PaulimerFormal.GreedyReduction

/-! Executable four-bit action and transvection updates, with exact matrix semantics. -/

namespace PaulimerFormal.TwoQubitEnumeration

open BinarFormal.Packed

theorem vector_zero : vector 0 = 0 := by
  funext index
  simp [vector]

theorem vector_xor (left right : BitVec 4) :
    vector (left ^^^ right) = vector left + vector right := by
  funext index
  simp [vector]

theorem vector_select (selected : Bool) (code : BitVec 4) :
    vector (bif selected then code else 0) = Bool.toF2 selected • vector code := by
  cases selected <;> funext index
  · change Bool.toF2 ((0 : BitVec 4).getLsbD (BinarBridge.phaseIndexEquiv 2 index).val) =
      (0 : F2) * vector code index
    simp
  · change vector code index = (1 : F2) * vector code index
    simp

def Frame.image (frame : Frame) (code : BitVec 4) : BitVec 4 :=
  (bif code.getLsbD 0 then frame.firstX else 0) ^^^
    (bif code.getLsbD 1 then frame.secondX else 0) ^^^
    (bif code.getLsbD 2 then frame.firstZ else 0) ^^^
    (bif code.getLsbD 3 then frame.secondZ else 0)

theorem vector_image (frame : Frame) (code : BitVec 4) :
    vector (frame.image code) = rowAction (vector code) frame.matrix := by
  simp only [Frame.image, vector_xor, vector_select]
  funext column
  simp [rowAction, Frame.matrix, Frame.row, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    vector, BinarBridge.phaseIndexEquiv, finSumFinEquiv, smul_eq_mul, add_assoc]

def transvect (target center : BitVec 4) : BitVec 4 :=
  target ^^^ (bif paired target center then center else 0)

theorem vector_transvect (target center : BitVec 4) :
    vector (transvect target center) = rowAction (vector target) (transvection (vector center)) := by
  rw [transvect, vector_xor, vector_select, paired_eq_pairing, rowAction_transvection]

def Frame.update (frame : Frame) (center : BitVec 4) : Frame :=
  ⟨transvect frame.firstX center, transvect frame.secondX center,
    transvect frame.firstZ center, transvect frame.secondZ center⟩

theorem matrix_update (frame : Frame) (center : BitVec 4) :
    (frame.update center).matrix = frame.matrix * transvection (vector center) := by
  funext row column
  have rows : (frame.update center).row row = transvect (frame.row row) center := by
    cases row <;> simp only [Frame.update, Frame.row] <;> split <;> rfl
  change vector ((frame.update center).row row) column = _
  rw [rows, vector_transvect]
  rfl

theorem update_mem_frames (frame : Frame) (member : frame ∈ frames) (center : BitVec 4) :
    frame.update center ∈ frames := by
  rw [mem_frames_iff, canonical_iff_symplectic, matrix_update]
  exact (frame.action member * transvectionAction (vector center)).property

def Frame.hyperbolic (frame : Frame) : Bool :=
  codes.all fun code => !(paired code (frame.image code))

theorem hyperbolic_iff (frame : Frame) :
    frame.hyperbolic = true ↔ GreedyReduction.IsHyperbolic frame.matrix := by
  simp only [Frame.hyperbolic, List.all_eq_true]
  constructor
  · intro checked target
    obtain ⟨code, rfl⟩ := vector_surjective target
    rw [← vector_image, ← paired_eq_pairing]
    have accepted := checked code (mem_codes code)
    cases result : paired code (frame.image code) <;> simp_all
  · intro hyperbolic code _
    have zero := hyperbolic (vector code)
    rw [← vector_image, ← paired_eq_pairing] at zero
    rw [Bool.toF2_injective (zero.trans Bool.toF2_false.symm)]
    rfl

def identityFrame : Frame := ⟨1, 2, 4, 8⟩

theorem identityFrame_matrix : identityFrame.matrix = 1 := by decide

theorem matrix_eq_one_iff (frame : Frame) :
    frame.matrix = 1 ↔ frame = identityFrame := by
  rw [← identityFrame_matrix, matrix_injective.eq_iff]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem nonidentity_hyperbolic_count :
    (frames.filter fun frame => frame.hyperbolic && decide (frame ≠ identityFrame)).length = 15 := by
  decide

theorem nonidentity_hyperbolic_iff (frame : Frame) :
    (frame.hyperbolic && decide (frame ≠ identityFrame)) = true ↔
      frame.matrix ≠ 1 ∧ GreedyReduction.IsHyperbolic frame.matrix := by
  simp [hyperbolic_iff, matrix_eq_one_iff, and_comm]

theorem action_spec :
    (∀ (frame : Frame) (code : BitVec 4),
      vector (frame.image code) = rowAction (vector code) frame.matrix) ∧
    (∀ (frame : Frame) (center : BitVec 4),
      (frame.update center).matrix = frame.matrix * transvection (vector center)) ∧
    (∀ frame : Frame, (frame.hyperbolic && decide (frame ≠ identityFrame)) = true ↔
      frame.matrix ≠ 1 ∧ GreedyReduction.IsHyperbolic frame.matrix) ∧
    (frames.filter fun frame => frame.hyperbolic && decide (frame ≠ identityFrame)).length = 15 :=
  ⟨vector_image, matrix_update, nonidentity_hyperbolic_iff, nonidentity_hyperbolic_count⟩

end PaulimerFormal.TwoQubitEnumeration
