import PaulimerFormal.CliffordTableau
import Mathlib.Data.BitVec
import Mathlib.Data.List.NodupEquivFin

/-! Exhaustive two-qubit symplectic frames in four-bit coordinates. -/

namespace PaulimerFormal.TwoQubitEnumeration

open BinarFormal.Packed

def vector (code : BitVec 4) : PhaseVector 2 :=
  fun index => Bool.toF2 (code.getLsbD (BinarBridge.phaseIndexEquiv 2 index).val)

theorem vector_injective : Function.Injective vector := by
  intro left right same
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  apply Bool.toF2_injective
  have entry := congrFun same ((BinarBridge.phaseIndexEquiv 2).symm ⟨index, bound⟩)
  simpa [vector] using entry

theorem vector_surjective : Function.Surjective vector := by
  let : Fintype (BitVec 4) :=
    Fintype.ofEquiv (Fin 16) (BitVec.equivFin (m := 4)).symm.toEquiv
  apply ((Fintype.bijective_iff_injective_and_card vector).mpr ⟨vector_injective, ?_⟩).2
  have codes : Fintype.card (BitVec 4) = 16 :=
    Fintype.card_congr BitVec.equivFin.toEquiv
  simp [codes, PhaseVector, PhaseIndex]

def paired (left right : BitVec 4) : Bool :=
  (left.getLsbD 0 && right.getLsbD 2) ^^
    (left.getLsbD 1 && right.getLsbD 3) ^^
    (left.getLsbD 2 && right.getLsbD 0) ^^
    (left.getLsbD 3 && right.getLsbD 1)

theorem paired_eq_pairing (left right : BitVec 4) :
    Bool.toF2 (paired left right) = pairing (vector left) (vector right) := by
  simp [paired, pairing, vector, omega, Matrix.J, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, BinarBridge.phaseIndexEquiv, finSumFinEquiv, add_assoc]

def codes : List (BitVec 4) := (List.finRange 16).map BitVec.ofFin

theorem mem_codes (code : BitVec 4) : code ∈ codes := by
  apply List.mem_map.mpr
  exact ⟨code.toFin, List.mem_finRange _, rfl⟩

structure Frame where
  firstX : BitVec 4
  secondX : BitVec 4
  firstZ : BitVec 4
  secondZ : BitVec 4
  deriving DecidableEq

def Frame.row (frame : Frame) : PhaseIndex 2 → BitVec 4
  | .inl qubit => if qubit = 0 then frame.firstX else frame.secondX
  | .inr qubit => if qubit = 0 then frame.firstZ else frame.secondZ

def Frame.matrix (frame : Frame) : ActionMatrix 2 :=
  fun row => vector (frame.row row)

def Frame.tableau (frame : Frame) : CliffordTableau.Tableau 2 :=
  fun row => Pauli.positiveRepresentative (ProjectivePauli.ofPhaseVector (vector (frame.row row)))

def Frame.IsCanonical (frame : Frame) : Prop :=
  paired frame.firstX frame.firstZ = true ∧
  paired frame.secondX frame.secondZ = true ∧
  paired frame.firstX frame.secondX = false ∧
  paired frame.firstX frame.secondZ = false ∧
  paired frame.firstZ frame.secondX = false ∧
  paired frame.firstZ frame.secondZ = false

def framesFrom (firstX : BitVec 4) : List Frame :=
  (codes.filter (paired firstX)).flatMap fun firstZ =>
    (codes.filter fun secondX => !(paired firstX secondX) && !(paired firstZ secondX)).flatMap
      fun secondX =>
        (codes.filter fun secondZ =>
          !(paired firstX secondZ) && !(paired firstZ secondZ) && paired secondX secondZ).map
          fun secondZ => ⟨firstX, secondX, firstZ, secondZ⟩

def frames : List Frame := codes.flatMap framesFrom

theorem mem_frames_iff (frame : Frame) : frame ∈ frames ↔ frame.IsCanonical := by
  cases frame
  simp [frames, framesFrom, Frame.IsCanonical, List.mem_flatMap, mem_codes,
    and_assoc, and_comm, and_left_comm]

theorem canonical_iff_symplectic (frame : Frame) :
    frame.IsCanonical ↔ IsSymplectic frame.matrix := by
  have criterion := CliffordTableau.upperValid_iff frame.tableau
  rw [CliffordTableau.valid_iff_symplectic] at criterion
  have matrix : CliffordTableau.preimageMatrix frame.tableau = frame.matrix := by
    funext row column
    simp [CliffordTableau.preimageMatrix, Frame.tableau, Frame.matrix]
  rw [matrix] at criterion
  simpa [CliffordTableau.UpperValid, Frame.tableau, Frame.row, Frame.IsCanonical,
    Pauli.positiveRepresentative_isOrderTwo,
    Fin.forall_fin_two, ProjectivePauli.commutationPairing_eq_pairing,
    ← paired_eq_pairing, ← Bool.toF2_true, ← Bool.toF2_false,
    Bool.toF2_injective.eq_iff, and_assoc, and_comm, and_left_comm] using criterion

theorem matrix_injective : Function.Injective Frame.matrix := by
  intro left right same
  have firstX := vector_injective (show vector left.firstX = vector right.firstX from
    congrFun same (.inl 0))
  have secondX := vector_injective (show vector left.secondX = vector right.secondX from
    congrFun same (.inl 1))
  have firstZ := vector_injective (show vector left.firstZ = vector right.firstZ from
    congrFun same (.inr 0))
  have secondZ := vector_injective (show vector left.secondZ = vector right.secondZ from
    congrFun same (.inr 1))
  cases left
  cases right
  simp_all

theorem matrix_surjective : Function.Surjective Frame.matrix := by
  intro target
  obtain ⟨firstX, firstX_row⟩ := vector_surjective (target (.inl 0))
  obtain ⟨secondX, secondX_row⟩ := vector_surjective (target (.inl 1))
  obtain ⟨firstZ, firstZ_row⟩ := vector_surjective (target (.inr 0))
  obtain ⟨secondZ, secondZ_row⟩ := vector_surjective (target (.inr 1))
  refine ⟨⟨firstX, secondX, firstZ, secondZ⟩, ?_⟩
  funext row column
  cases row <;> rename_i qubit <;> fin_cases qubit <;>
    simp [Frame.matrix, Frame.row, firstX_row, secondX_row, firstZ_row, secondZ_row]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem frames_length : frames.length = 720 := by decide

theorem frames_nodup : frames.Nodup := by
  have distinct : codes.Nodup := by decide
  unfold frames framesFrom
  simp only [List.nodup_flatMap]
  refine ⟨fun firstX _ => ⟨fun firstZ _ => ⟨fun secondX _ => ?_, ?_⟩, ?_⟩, ?_⟩
  · apply (distinct.filter _).map
    intro left right same
    exact congrArg Frame.secondZ same
  all_goals
    first | apply (distinct.filter _).imp | apply distinct.imp
    intro left right different frame left_member right_member
    simp only [List.mem_flatMap, List.mem_map] at left_member right_member
    aesop

def Frame.action (frame : Frame) (member : frame ∈ frames) : SymplecticAction 2 :=
  ⟨frame.matrix, (canonical_iff_symplectic frame).mp ((mem_frames_iff frame).mp member)⟩

def actions : List (SymplecticAction 2) :=
  frames.attach.map fun frame => frame.val.action frame.property

theorem actions_length : actions.length = 720 := by
  simpa only [actions, List.length_map, List.length_attach] using frames_length

theorem actions_nodup : actions.Nodup := by
  apply frames_nodup.attach.map
  intro left right same
  apply Subtype.ext
  apply matrix_injective
  exact congrArg Subtype.val same

theorem mem_actions (action : SymplecticAction 2) : action ∈ actions := by
  obtain ⟨frame, same⟩ := matrix_surjective (action : ActionMatrix 2)
  have member : frame ∈ frames := by
    rw [mem_frames_iff, canonical_iff_symplectic, same]
    exact action.property
  apply List.mem_map.mpr
  exact ⟨⟨frame, member⟩, List.mem_attach _ _, Subtype.ext same⟩

def enumerationEquiv : Fin actions.length ≃ SymplecticAction 2 :=
  List.Nodup.getEquivOfForallMemList actions actions_nodup mem_actions

theorem card_symplecticAction_two : Nat.card (SymplecticAction 2) = 720 := by
  simpa only [Nat.card_fin, actions_length] using (Nat.card_congr enumerationEquiv).symm

theorem enumeration_spec :
    actions.Nodup ∧ actions.length = 720 ∧
    (∀ action : SymplecticAction 2, action ∈ actions) ∧
    Nat.card (SymplecticAction 2) = 720 :=
  ⟨actions_nodup, actions_length, mem_actions, card_symplecticAction_two⟩

end PaulimerFormal.TwoQubitEnumeration
