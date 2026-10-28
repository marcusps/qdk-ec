import PaulimerFormal.CliffordRealization
import PaulimerFormal.PauliGroup

/-! Standard signed preimages determine a phase-preserving Pauli automorphism uniquely. -/

namespace PaulimerFormal.CliffordTableau

open CliffordAction

variable {m : ℕ}

theorem standardPauli_row (index : Fin (m + m)) :
    (standardPauli ((BinarBridge.phaseIndexEquiv m).symm index)).projectiveRow =
      Pi.single index 1 := by
  rw [Pauli.projectiveRow, standardPauli_vector]
  funext column
  simp [BinarBridge.toFinVector, Pi.single_apply]

theorem image_eq_of_standard (left right : CliffordAction m)
    (same : ∀ index, image left (standardPauli index) = image right (standardPauli index))
    (pauli : Pauli m) : image left pauli = image right pauli := by
  let equalizer := (left : MulAut (Pauli m)).toMonoidHom.eqLocus
    (right : MulAut (Pauli m)).toMonoidHom
  have witnesses : ∀ index : Fin (m + m), ∃ representative ∈ equalizer,
      representative.projectiveRow = (Pi.basisFun F2 (Fin (m + m))) index := by
    intro index
    refine ⟨standardPauli ((BinarBridge.phaseIndexEquiv m).symm index), same _, ?_⟩
    simpa only [Pi.basisFun_apply] using standardPauli_row index
  have spans : pauli.projectiveRow ∈
      Submodule.span F2 (Set.range (Pi.basisFun F2 (Fin (m + m)))) := by
    rw [(Pi.basisFun F2 (Fin (m + m))).span_eq]
    trivial
  obtain ⟨representative, agrees, row⟩ :=
    exists_mem_subgroup_projectiveRow_eq equalizer _ witnesses spans
  have shifted : representative.addPhase (pauli.phase - representative.phase) = pauli := by
    apply Pauli.ext
    · funext index
      change representative.x index = pauli.x index
      simpa only [Pauli.projectiveRow_x] using congrFun row (Fin.castAdd m index)
    · funext index
      change representative.z index = pauli.z index
      simpa only [Pauli.projectiveRow_z] using congrFun row (Fin.natAdd m index)
    · simp [Pauli.phase_addPhase]
  rw [← shifted, image_addPhase, image_addPhase]
  exact congrArg (fun value : Pauli m => value.addPhase (pauli.phase - representative.phase)) agrees

theorem preimages_injective :
    Function.Injective (@preimages m) := by
  intro left right same
  have inverses : left⁻¹ = right⁻¹ := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro pauli
    exact image_eq_of_standard left⁻¹ right⁻¹ (congrFun same) pauli
  exact inv_injective inverses

theorem realize_preimages (action : CliffordAction m) :
    realize (preimages action) (preimages_valid action) = action :=
  preimages_injective (preimages_realize _ _)

theorem valid_iff_exists_unique_action (tableau : Tableau m) :
    IsValid tableau ↔ ∃! action : CliffordAction m, preimages action = tableau := by
  constructor
  · intro valid
    refine ⟨realize tableau valid, preimages_realize tableau valid, ?_⟩
    intro action same
    exact preimages_injective (same.trans (preimages_realize tableau valid).symm)
  · rintro ⟨action, same, _⟩
    exact (valid_iff_exists_action tableau).mpr ⟨action, same⟩

def actionEquivValidTableau : CliffordAction m ≃ {tableau : Tableau m // IsValid tableau} where
  toFun action := ⟨preimages action, preimages_valid action⟩
  invFun tableau := realize tableau.val tableau.property
  left_inv := realize_preimages
  right_inv tableau := Subtype.ext (preimages_realize tableau.val tableau.property)

theorem signedDecomposition_spec (action : CliffordAction m) :
    let centers := ResidueFixSearch.minimalDecomposition (binaryAction action)
    let correction := TransvectionSigns.finalPauliCorrection
      (preimages action) (preimages (rotations centers))
    pauliConjugation correction * rotations centers = action ∧
    TransvectionRefinement.IsShortest (binaryAction action) centers ∧
    correction.xyzPhase = 0 ∧ correction.IsOrderTwo ∧
    ∀ center ∈ centers, center ≠ 0 := by
  dsimp only
  refine ⟨?_, ResidueFixSearch.minimalDecomposition_spec _,
    Pauli.xyzPhase_positiveRepresentative _, Pauli.positiveRepresentative_isOrderTwo _,
    ResidueFixSearch.shortest_nonzero (ResidueFixSearch.minimalDecomposition_spec _)⟩
  have inverse : preimageAction (preimages action) (preimages_valid action) =
      (binaryAction action)⁻¹ :=
    Subtype.ext (preimageMatrix_preimages action)
  simpa only [realize, unsignedRealization, inverse, inv_inv] using realize_preimages action

end PaulimerFormal.CliffordTableau
