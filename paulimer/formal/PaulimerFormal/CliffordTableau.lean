import PaulimerFormal.Clifford
import PaulimerFormal.TransvectionSigns

/-! Valid signed preimage rows and their binary symplectic matrices. -/

namespace PaulimerFormal.CliffordTableau

open CliffordAction

abbrev Tableau (m : ℕ) := TransvectionSigns.PreimageTableau m

def standardPauli {m : ℕ} (index : PhaseIndex m) : Pauli m :=
  Pauli.positiveRepresentative
    (match index with
    | .inl qubit => ProjectivePauli.singleX qubit
    | .inr qubit => ProjectivePauli.singleZ qubit)

theorem standardPauli_vector {m : ℕ} (index : PhaseIndex m) :
    (standardPauli index).projective.toPhaseVector = Pi.single index 1 := by
  funext coordinate
  cases index <;> cases coordinate <;>
    simp [standardPauli, ProjectivePauli.singleX, ProjectivePauli.singleZ, Pi.single_apply]

theorem standardPauli_isOrderTwo {m : ℕ} (index : PhaseIndex m) :
    (standardPauli index).IsOrderTwo :=
  Pauli.positiveRepresentative_isOrderTwo _

def IsValid {m : ℕ} (tableau : Tableau m) : Prop :=
  (∀ index, (tableau index).IsOrderTwo) ∧
    ∀ first second, ProjectivePauli.commutationPairing
      (tableau first).projective (tableau second).projective = omega m first second

def validCheck {m : ℕ} (tableau : Tableau m) : Bool :=
  let pairCheck := fun first second : PhaseIndex m =>
    decide (ProjectivePauli.commutationPairing
      (tableau first).projective (tableau second).projective = omega m first second)
  decide (∀ index,
    (tableau index).phase + (tableau index).phase =
      Pauli.parityPhase (ProjectivePauli.xzCross (tableau index).projective (tableau index).projective) ∧
    ∀ other, pairCheck index other = true)

theorem validCheck_iff {m : ℕ} (tableau : Tableau m) :
    validCheck tableau = true ↔ IsValid tableau := by
  simp only [validCheck, decide_eq_true_eq, IsValid, Pauli.isOrderTwo_iff_phase, forall_and]

/-- The per-qubit and upper-triangle conditions of `is_valid_clifford`. -/
def UpperValid {m : ℕ} (tableau : Tableau m) : Prop :=
  ∀ index : Fin m,
    (tableau (.inl index)).IsOrderTwo ∧
    (tableau (.inr index)).IsOrderTwo ∧
    ProjectivePauli.commutationPairing
      (tableau (.inl index)).projective (tableau (.inr index)).projective = 1 ∧
    ∀ other : Fin m, index < other →
      ProjectivePauli.commutationPairing
        (tableau (.inl index)).projective (tableau (.inl other)).projective = 0 ∧
      ProjectivePauli.commutationPairing
        (tableau (.inl index)).projective (tableau (.inr other)).projective = 0 ∧
      ProjectivePauli.commutationPairing
        (tableau (.inr index)).projective (tableau (.inl other)).projective = 0 ∧
      ProjectivePauli.commutationPairing
        (tableau (.inr index)).projective (tableau (.inr other)).projective = 0

theorem upperValid_iff {m : ℕ} (tableau : Tableau m) :
    UpperValid tableau ↔ IsValid tableau := by
  constructor
  · intro upper
    refine ⟨?_, ?_⟩
    · intro index
      cases index with
      | inl index => exact (upper index).1
      | inr index => exact (upper index).2.1
    · intro first second
      cases first <;> cases second <;> rename_i first second
      all_goals
        have diagonal := (upper first).2.2.1
        have forward := (upper first).2.2.2 second
        have backward := (upper second).2.2.2 first
        rcases lt_trichotomy first second with before | rfl | after <;>
          simp_all [omega, Matrix.J, ne_of_lt, ne_of_gt,
            ProjectivePauli.commutationPairing_comm]
  · intro valid index
    refine ⟨valid.1 _, valid.1 _, ?_, ?_⟩
    · simpa [omega, Matrix.J] using valid.2 (.inl index) (.inr index)
    · intro other ordered
      have different := ne_of_lt ordered
      exact ⟨by simpa [omega, Matrix.J] using valid.2 (.inl index) (.inl other),
        by simpa [omega, Matrix.J, different] using valid.2 (.inl index) (.inr other),
        by simpa [omega, Matrix.J, different] using valid.2 (.inr index) (.inl other),
        by simpa [omega, Matrix.J] using valid.2 (.inr index) (.inr other)⟩

def preimageMatrix {m : ℕ} (tableau : Tableau m) : ActionMatrix m :=
  fun row column => (tableau row).projective.toPhaseVector column

theorem rowAction_standard {m : ℕ} (tableau : Tableau m) (index : PhaseIndex m) :
    rowAction (Pi.single index 1) (preimageMatrix tableau) =
      (tableau index).projective.toPhaseVector := by
  funext column
  simp [rowAction, preimageMatrix]

theorem valid_symplectic {m : ℕ} (tableau : Tableau m) (valid : IsValid tableau) :
    IsSymplectic (preimageMatrix tableau) := by
  rw [IsSymplectic, SymplecticGroup.mem_iff]
  ext row column
  have paired := valid.2 row column
  rw [ProjectivePauli.commutationPairing_eq_pairing, ← rowAction_standard, ← rowAction_standard] at paired
  simpa [rowAction, pairing, omega, Matrix.mul_mul_apply, Matrix.row_apply'] using paired

theorem valid_iff_symplectic {m : ℕ} (tableau : Tableau m) :
    IsValid tableau ↔
      (∀ index, (tableau index).IsOrderTwo) ∧ IsSymplectic (preimageMatrix tableau) := by
  constructor
  · intro valid
    exact ⟨valid.1, valid_symplectic tableau valid⟩
  · rintro ⟨hermitian, symplectic⟩
    refine ⟨hermitian, ?_⟩
    intro row column
    have paired := pairing_rowAction symplectic (Pi.single row 1) (Pi.single column 1)
    rw [rowAction_standard, rowAction_standard] at paired
    rw [ProjectivePauli.commutationPairing_eq_pairing]
    simpa [pairing] using paired

def preimages {m : ℕ} (action : CliffordAction m) : Tableau m :=
  fun index => preimage action (standardPauli index)

theorem preimages_valid {m : ℕ} (action : CliffordAction m) : IsValid (preimages action) := by
  constructor
  · intro index
    exact image_isOrderTwo action⁻¹ _ (standardPauli_isOrderTwo index)
  · intro row column
    change ProjectivePauli.commutationPairing
      (image action⁻¹ (standardPauli row)).projective
      (image action⁻¹ (standardPauli column)).projective = _
    rw [image_pairing, ProjectivePauli.commutationPairing_eq_pairing,
      standardPauli_vector, standardPauli_vector]
    simp [pairing]

theorem preimageMatrix_preimages {m : ℕ} (action : CliffordAction m) :
    preimageMatrix (preimages action) =
      (((binaryAction action)⁻¹ : SymplecticAction m) : ActionMatrix m) := by
  ext row column
  have projected := preimage_binaryAction action (standardPauli row)
  rw [standardPauli_vector] at projected
  simpa [preimageMatrix, preimages, rowAction] using congrFun projected column

theorem preimages_same_binary {m : ℕ} (left right : CliffordAction m)
    (same : binaryAction left = binaryAction right) :
    ∀ index, (preimages left index).projective = (preimages right index).projective := by
  intro index
  have matrices : preimageMatrix (preimages left) = preimageMatrix (preimages right) := by
    rw [preimageMatrix_preimages, preimageMatrix_preimages, same]
  have vectors := congrFun matrices index
  change (preimages left index).projective.toPhaseVector =
    (preimages right index).projective.toPhaseVector at vectors
  simpa only [ProjectivePauli.ofPhaseVector_toPhaseVector] using
    congrArg ProjectivePauli.ofPhaseVector vectors

theorem tableau_spec {m : ℕ} (tableau : Tableau m) :
    (validCheck tableau = true ↔ IsValid tableau) ∧
    (UpperValid tableau ↔ IsValid tableau) ∧
    (IsValid tableau ↔
      (∀ index, (tableau index).IsOrderTwo) ∧ IsSymplectic (preimageMatrix tableau)) := by
  exact ⟨validCheck_iff tableau, upperValid_iff tableau, valid_iff_symplectic tableau⟩

theorem preimages_spec {m : ℕ} (action : CliffordAction m) :
    IsValid (preimages action) ∧
    preimageMatrix (preimages action) =
      (((binaryAction action)⁻¹ : SymplecticAction m) : ActionMatrix m) :=
  ⟨preimages_valid action, preimageMatrix_preimages action⟩

example : validCheck (@standardPauli 0) = true := by decide
example : validCheck (@standardPauli 1) = true := by decide
example : validCheck (fun index : PhaseIndex 1 => -standardPauli index) = true := by decide
example : validCheck (fun _ : PhaseIndex 1 => 1) = false := by decide
example :
    validCheck (fun index : PhaseIndex 1 => Pauli.addPhase (standardPauli index) 1) = false := by
  decide

end PaulimerFormal.CliffordTableau
