import PaulimerFormal.PauliExponent
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Phase-preserving Pauli automorphisms, modulo unrepresented global Clifford phase. -/

namespace PaulimerFormal

def CliffordAction (m : ℕ) : Subgroup (MulAut (Pauli m)) where
  carrier := fun action => ∀ phase, action (Pauli.ofProjective 0 phase) = Pauli.ofProjective 0 phase
  one_mem' _ := rfl
  mul_mem' := by
    intro left right left_fixed right_fixed phase
    rw [MulAut.mul_apply, right_fixed, left_fixed]
  inv_mem' := by
    intro action fixed phase
    apply action.injective
    rw [MulAut.apply_inv_self, fixed]

namespace CliffordAction

variable {m : ℕ}

def image (action : CliffordAction m) (pauli : Pauli m) : Pauli m :=
  (action : MulAut (Pauli m)) pauli

def preimage (action : CliffordAction m) (pauli : Pauli m) : Pauli m :=
  image action⁻¹ pauli

theorem image_one (pauli : Pauli m) : image 1 pauli = pauli := rfl

theorem image_comp (left right : CliffordAction m) (pauli : Pauli m) :
    image (left * right) pauli = image left (image right pauli) := rfl

theorem image_preimage (action : CliffordAction m) (pauli : Pauli m) :
    image action (preimage action pauli) = pauli :=
  MulAut.apply_inv_self (Pauli m) (action : MulAut (Pauli m)) pauli

theorem preimage_image (action : CliffordAction m) (pauli : Pauli m) :
    preimage action (image action pauli) = pauli :=
  MulAut.inv_apply_self (Pauli m) (action : MulAut (Pauli m)) pauli

theorem image_mul (action : CliffordAction m) (left right : Pauli m) :
    image action (left * right) = image action left * image action right :=
  map_mul (action : MulAut (Pauli m)) left right

theorem image_scalar (action : CliffordAction m) (phase : PauliPhase) :
    image action (Pauli.ofProjective 0 phase) = Pauli.ofProjective 0 phase :=
  action.property phase

theorem image_isOrderTwo (action : CliffordAction m) (pauli : Pauli m)
    (hermitian : pauli.IsOrderTwo) : (image action pauli).IsOrderTwo := by
  change image action pauli * image action pauli = 1
  rw [← image_mul, hermitian]
  exact map_one (action : MulAut (Pauli m))

theorem scalar_mul (phase : PauliPhase) (pauli : Pauli m) :
    Pauli.ofProjective 0 phase * pauli = pauli.addPhase phase := by
  apply Pauli.ext
  · change (0 : Fin m → F2) + pauli.x = pauli.x
    exact zero_add _
  · change (0 : Fin m → F2) + pauli.z = pauli.z
    exact zero_add _
  · change phase + pauli.phase + Pauli.parityPhase (ProjectivePauli.xzCross 0 pauli.projective) =
      pauli.phase + phase
    simp [add_comm]

theorem image_addPhase (action : CliffordAction m) (pauli : Pauli m) (phase : PauliPhase) :
    image action (pauli.addPhase phase) = (image action pauli).addPhase phase := by
  rw [← scalar_mul, image_mul, image_scalar, scalar_mul]

theorem image_ofProjective_phase (action : CliffordAction m) (pauli : ProjectivePauli m)
    (phase : PauliPhase) :
    (image action (Pauli.ofProjective pauli phase)).projective =
      (image action (Pauli.ofProjective pauli 0)).projective := by
  have representation :
      (Pauli.ofProjective pauli 0).addPhase phase = Pauli.ofProjective pauli phase := by
    apply Pauli.ext
    · rfl
    · rfl
    · simp [Pauli.ofProjective]
  rw [← representation, image_addPhase, Pauli.projective_addPhase]

def vectorAction (action : CliffordAction m) (vector : PhaseVector m) : PhaseVector m :=
  (image action (Pauli.ofProjective (ProjectivePauli.ofPhaseVector vector) 0)).projective.toPhaseVector

theorem image_vector (action : CliffordAction m) (pauli : Pauli m) :
    (image action pauli).projective.toPhaseVector = vectorAction action pauli.projective.toPhaseVector := by
  unfold vectorAction
  rw [ProjectivePauli.ofPhaseVector_toPhaseVector]
  change (image action (Pauli.ofProjective pauli.projective pauli.phase)).projective.toPhaseVector = _
  rw [image_ofProjective_phase]

theorem vectorAction_add (action : CliffordAction m) (left right : PhaseVector m) :
    vectorAction action (left + right) = vectorAction action left + vectorAction action right := by
  have preserved := congrArg (fun pauli : Pauli m => pauli.projective.toPhaseVector)
    (image_mul action (Pauli.ofProjective (ProjectivePauli.ofPhaseVector left) 0)
      (Pauli.ofProjective (ProjectivePauli.ofPhaseVector right) 0))
  simpa only [Pauli.projective_mul, ProjectivePauli.toPhaseVector_add, image_vector,
    Pauli.projective_ofProjective, ProjectivePauli.toPhaseVector_ofPhaseVector] using preserved

theorem vectorAction_zero (action : CliffordAction m) : vectorAction action 0 = 0 := by
  have additive := vectorAction_add action 0 0
  simpa only [zero_add, ZModModule.add_self] using additive

theorem vectorAction_one (vector : PhaseVector m) : vectorAction 1 vector = vector := by
  simp [vectorAction, image_one]

theorem vectorAction_comp (left right : CliffordAction m) (vector : PhaseVector m) :
    vectorAction (left * right) vector = vectorAction left (vectorAction right vector) := by
  have composition := congrArg (fun pauli : Pauli m => pauli.projective.toPhaseVector)
    (image_comp left right (Pauli.ofProjective (ProjectivePauli.ofPhaseVector vector) 0))
  simpa only [image_vector, Pauli.projective_ofProjective,
    ProjectivePauli.toPhaseVector_ofPhaseVector] using composition

def linearAction (action : CliffordAction m) : PhaseVector m →ₗ[F2] PhaseVector m where
  toFun := vectorAction action
  map_add' := vectorAction_add action
  map_smul' := by
    intro scalar vector
    change vectorAction action (scalar • vector) = scalar • vectorAction action vector
    rcases Pauli.f2_eq_zero_or_one scalar with rfl | rfl <;> simp [vectorAction_zero]

theorem image_pairing (action : CliffordAction m) (left right : Pauli m) :
    ProjectivePauli.commutationPairing (image action left).projective (image action right).projective =
      ProjectivePauli.commutationPairing left.projective right.projective := by
  have zero_iff :
      ProjectivePauli.commutationPairing (image action left).projective (image action right).projective = 0 ↔
        ProjectivePauli.commutationPairing left.projective right.projective = 0 := by
    rw [← Pauli.mul_comm_iff_commutationPairing_eq_zero, ← Pauli.mul_comm_iff_commutationPairing_eq_zero,
      ← image_mul, ← image_mul]
    exact (action : MulAut (Pauli m)).injective.eq_iff
  rcases Pauli.f2_eq_zero_or_one
    (ProjectivePauli.commutationPairing left.projective right.projective) with zero | one
  · exact (zero_iff.mpr zero).trans zero.symm
  · rcases Pauli.f2_eq_zero_or_one
      (ProjectivePauli.commutationPairing (image action left).projective (image action right).projective) with zero | image_one
    · have impossible := zero_iff.mp zero
      rw [one] at impossible
      exact (one_ne_zero impossible).elim
    · exact image_one.trans one.symm

theorem vectorAction_pairing (action : CliffordAction m) (left right : PhaseVector m) :
    pairing (vectorAction action left) (vectorAction action right) = pairing left right := by
  have preserved := image_pairing action (Pauli.ofProjective (ProjectivePauli.ofPhaseVector left) 0)
    (Pauli.ofProjective (ProjectivePauli.ofPhaseVector right) 0)
  simpa only [ProjectivePauli.commutationPairing_eq_pairing, image_vector,
    Pauli.projective_ofProjective, ProjectivePauli.toPhaseVector_ofPhaseVector] using preserved

def actionMatrix (action : CliffordAction m) : ActionMatrix m :=
  (LinearMap.toMatrix' (linearAction action)).transpose

theorem rowAction_actionMatrix (action : CliffordAction m) (vector : PhaseVector m) :
    rowAction vector (actionMatrix action) = vectorAction action vector := by
  rw [rowAction, actionMatrix, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
    LinearMap.toMatrix'_mulVec]
  rfl

theorem actionMatrix_symplectic (action : CliffordAction m) : IsSymplectic (actionMatrix action) := by
  rw [IsSymplectic, SymplecticGroup.mem_iff]
  ext row column
  have preserved := vectorAction_pairing action (Pi.single row 1) (Pi.single column 1)
  rw [← rowAction_actionMatrix, ← rowAction_actionMatrix] at preserved
  simpa [rowAction, pairing, omega, Matrix.mul_mul_apply, Matrix.row_apply'] using preserved

def binaryAction (action : CliffordAction m) : SymplecticAction m :=
  ⟨actionMatrix action, actionMatrix_symplectic action⟩

theorem binaryAction_one : binaryAction (1 : CliffordAction m) = 1 := by
  apply Subtype.ext
  ext row column
  have fixed := rowAction_actionMatrix (1 : CliffordAction m) (Pi.single row 1)
  rw [vectorAction_one] at fixed
  simpa [rowAction, binaryAction, Matrix.one_apply, Pi.single_apply, eq_comm] using congrFun fixed column

theorem binaryAction_comp (left right : CliffordAction m) :
    binaryAction (left * right) = binaryAction right * binaryAction left := by
  apply Subtype.ext
  ext row column
  have composition :
      rowAction (Pi.single row 1) (actionMatrix (left * right)) =
        rowAction (Pi.single row 1) (actionMatrix right * actionMatrix left) := by
    rw [← rowAction_mul]
    simp only [rowAction_actionMatrix, vectorAction_comp]
  simpa [rowAction, binaryAction] using congrFun composition column

theorem binaryAction_inv (action : CliffordAction m) :
    binaryAction action⁻¹ = (binaryAction action)⁻¹ := by
  have product : binaryAction action * binaryAction action⁻¹ = 1 := by
    rw [← binaryAction_comp, inv_mul_cancel, binaryAction_one]
  exact (inv_eq_of_mul_eq_one_right product).symm

theorem image_binaryAction (action : CliffordAction m) (pauli : Pauli m) :
    (image action pauli).projective.toPhaseVector =
      rowAction pauli.projective.toPhaseVector (binaryAction action : ActionMatrix m) := by
  rw [image_vector, ← rowAction_actionMatrix]
  rfl

theorem preimage_binaryAction (action : CliffordAction m) (pauli : Pauli m) :
    (preimage action pauli).projective.toPhaseVector =
      rowAction pauli.projective.toPhaseVector
        (((binaryAction action)⁻¹ : SymplecticAction m) : ActionMatrix m) := by
  rw [preimage, image_binaryAction, binaryAction_inv]

def quarterTurn (exponent : Pauli m) (hermitian : exponent.IsOrderTwo) : CliffordAction m :=
  ⟨Pauli.exponentEquiv exponent hermitian, Pauli.exponentAction_scalar exponent⟩

theorem image_quarterTurn (exponent : Pauli m) (hermitian : exponent.IsOrderTwo) (pauli : Pauli m) :
    image (quarterTurn exponent hermitian) pauli = Pauli.exponentAction pauli exponent := rfl

theorem vectorAction_quarterTurn (exponent : Pauli m) (hermitian : exponent.IsOrderTwo)
    (vector : PhaseVector m) :
    vectorAction (quarterTurn exponent hermitian) vector =
      rowAction vector (transvection exponent.projective.toPhaseVector) := by
  unfold vectorAction
  rw [image_quarterTurn, Pauli.exponentAction_projective]
  simp

theorem binaryAction_quarterTurn (exponent : Pauli m) (hermitian : exponent.IsOrderTwo) :
    binaryAction (quarterTurn exponent hermitian) = transvectionAction exponent.projective.toPhaseVector := by
  apply Subtype.ext
  ext row column
  have projected := rowAction_actionMatrix (quarterTurn exponent hermitian) (Pi.single row 1)
  rw [vectorAction_quarterTurn] at projected
  simpa [rowAction, binaryAction] using congrFun projected column

theorem projection_spec (action : CliffordAction m) :
    IsSymplectic (actionMatrix action) ∧
    (∀ pauli, image action (preimage action pauli) = pauli ∧
      preimage action (image action pauli) = pauli) ∧
    (∀ pauli, (image action pauli).projective.toPhaseVector =
      rowAction pauli.projective.toPhaseVector (binaryAction action : ActionMatrix m)) ∧
    (∀ pauli, (preimage action pauli).projective.toPhaseVector =
      rowAction pauli.projective.toPhaseVector
        (((binaryAction action)⁻¹ : SymplecticAction m) : ActionMatrix m)) ∧
    (∀ other, binaryAction (action * other) = binaryAction other * binaryAction action) ∧
    (∀ pauli, pauli.IsOrderTwo → (image action pauli).IsOrderTwo) := by
  exact ⟨actionMatrix_symplectic action,
    fun pauli => ⟨image_preimage action pauli, preimage_image action pauli⟩,
    image_binaryAction action, preimage_binaryAction action, binaryAction_comp action, image_isOrderTwo action⟩

end CliffordAction

end PaulimerFormal
