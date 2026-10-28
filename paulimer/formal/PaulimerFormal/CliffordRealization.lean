import PaulimerFormal.CliffordTableau
import PaulimerFormal.ResidueFixSearch

/-! Constructing phase-preserving Clifford actions from valid signed preimages. -/

namespace PaulimerFormal

namespace CliffordAction

variable {m : ℕ}

def rotations : List (PhaseVector m) → CliffordAction m
  | [] => 1
  | center :: centers =>
      rotations centers * quarterTurn
        (Pauli.positiveRepresentative (ProjectivePauli.ofPhaseVector center))
        (Pauli.positiveRepresentative_isOrderTwo _)

theorem binaryAction_rotations (centers : List (PhaseVector m)) :
    binaryAction (rotations centers) = productTransvections centers := by
  induction centers with
  | nil => exact binaryAction_one
  | cons center centers inductionHypothesis =>
      simp only [rotations, binaryAction_comp, binaryAction_quarterTurn,
        Pauli.projective_positiveRepresentative, ProjectivePauli.toPhaseVector_ofPhaseVector,
        inductionHypothesis, productTransvections_cons]

def pauliConjugation (pauli : Pauli m) : CliffordAction m :=
  ⟨MulAut.conj pauli, by
    intro phase
    change Pauli.conjugate pauli (Pauli.ofProjective 0 phase) = _
    apply Pauli.conjugate_eq_of_commutationPairing_eq_zero
    simp [ProjectivePauli.commutationPairing, ProjectivePauli.xzCross]⟩

theorem preimage_pauliConjugation (pauli target : Pauli m) :
    preimage (pauliConjugation pauli) target =
      if ProjectivePauli.commutationPairing pauli.projective target.projective = 0
      then target else -target := by
  change pauli⁻¹ * target * pauli = _
  by_cases commutes : ProjectivePauli.commutationPairing
      pauli.projective target.projective = 0 <;>
    simpa [Pauli.conjugate, commutes] using Pauli.conjugate_eq_if pauli⁻¹ target

theorem image_neg (action : CliffordAction m) (pauli : Pauli m) :
    image action (-pauli) = -image action pauli := by
  rw [← Pauli.addPhase_two, image_addPhase, Pauli.addPhase_two]

end CliffordAction

namespace CliffordTableau

open CliffordAction TransvectionSigns

variable {m : ℕ}

theorem preimages_pauli_left (action : CliffordAction m) (correction : Pauli m) :
    preimages (pauliConjugation correction * action) =
      leftMulPauli (preimages action) correction := by
  funext index
  rw [leftMulPauli_eq_pairing]
  change preimage (pauliConjugation correction * action) (standardPauli index) = _
  have composition :
      preimage (pauliConjugation correction * action) (standardPauli index) =
        image action⁻¹ (preimage (pauliConjugation correction) (standardPauli index)) := by
    simp only [preimage, _root_.mul_inv_rev, image_comp]
  rw [composition, preimage_pauliConjugation]
  cases index <;> simp [standardPauli, apply_ite, image_neg, preimages, preimage] <;>
    split <;> simp_all

def preimageAction (tableau : Tableau m) (valid : IsValid tableau) : SymplecticAction m :=
  ⟨preimageMatrix tableau, valid_symplectic tableau valid⟩

def unsignedRealization (tableau : Tableau m) (valid : IsValid tableau) : CliffordAction m :=
  rotations (ResidueFixSearch.minimalDecomposition (preimageAction tableau valid)⁻¹)

theorem preimageMatrix_unsignedRealization (tableau : Tableau m) (valid : IsValid tableau) :
    preimageMatrix (preimages (unsignedRealization tableau valid)) = preimageMatrix tableau := by
  rw [preimageMatrix_preimages, unsignedRealization, binaryAction_rotations,
    (ResidueFixSearch.minimalDecomposition_spec (preimageAction tableau valid)⁻¹).1,
    inv_inv]
  rfl

def realize (tableau : Tableau m) (valid : IsValid tableau) : CliffordAction m :=
  let rebuilt := unsignedRealization tableau valid
  pauliConjugation (finalPauliCorrection tableau (preimages rebuilt)) * rebuilt

theorem preimages_realize (tableau : Tableau m) (valid : IsValid tableau) :
    preimages (realize tableau valid) = tableau := by
  rw [realize, preimages_pauli_left]
  apply (finalPauliCorrection_spec tableau
    (preimages (unsignedRealization tableau valid)) ?_ valid.1
    (preimages_valid (unsignedRealization tableau valid)).1).1
  intro index
  have vectors := congrFun (preimageMatrix_unsignedRealization tableau valid) index
  change (preimages (unsignedRealization tableau valid) index).projective.toPhaseVector =
    (tableau index).projective.toPhaseVector at vectors
  simpa only [ProjectivePauli.ofPhaseVector_toPhaseVector] using
    congrArg ProjectivePauli.ofPhaseVector vectors.symm

theorem valid_iff_exists_action (tableau : Tableau m) :
    IsValid tableau ↔ ∃ action : CliffordAction m, preimages action = tableau := by
  constructor
  · intro valid
    exact ⟨realize tableau valid, preimages_realize tableau valid⟩
  · rintro ⟨action, rfl⟩
    exact preimages_valid action

theorem realization_spec (tableau : Tableau m) (valid : IsValid tableau) :
    preimages (realize tableau valid) = tableau ∧
    TransvectionRefinement.IsShortest (preimageAction tableau valid)⁻¹
      (ResidueFixSearch.minimalDecomposition (preimageAction tableau valid)⁻¹) ∧
    (finalPauliCorrection tableau
      (preimages (unsignedRealization tableau valid))).xyzPhase = 0 ∧
    (finalPauliCorrection tableau
      (preimages (unsignedRealization tableau valid))).IsOrderTwo := by
  exact ⟨preimages_realize tableau valid, ResidueFixSearch.minimalDecomposition_spec _,
    Pauli.xyzPhase_positiveRepresentative _, Pauli.positiveRepresentative_isOrderTwo _⟩

end CliffordTableau

end PaulimerFormal
