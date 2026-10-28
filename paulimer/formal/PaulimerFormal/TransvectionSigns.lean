import PaulimerFormal.Pauli

/-!
# Final Pauli correction for a signed preimage tableau

This models `final_pauli_correction` and `left_mul_pauli` in PR #217 at
`2ce895eda84473762d7db36bf6c3561460992858`. Rows are indexed by the standard
X/Z generators, not by their images. The correction is applied on the left
of the rebuilt unitary, so its Z bits negate X preimages and conversely.

The theorem requires equal binary preimages and self-inverse rows. It does
not assume, or prove, that the preceding Rust rotation search establishes
these conditions. Equality here includes every tableau phase modulo four,
but not the unrepresented global Clifford phase.
-/

namespace PaulimerFormal.TransvectionSigns

abbrev PreimageTableau (m : ℕ) := PhaseIndex m → Pauli m

def phaseMismatch {m : ℕ} (target rebuilt : Pauli m) : F2 :=
  if target.phase = rebuilt.phase then 0 else 1

def finalPauliCorrection {m : ℕ} (target rebuilt : PreimageTableau m) :
    Pauli m :=
  Pauli.positiveRepresentative {
    x := fun index => phaseMismatch (target (.inr index)) (rebuilt (.inr index))
    z := fun index => phaseMismatch (target (.inl index)) (rebuilt (.inl index))
  }

/-- The preimage-row update performed by Rust's X/Z support loops. -/
def leftMulPauli {m : ℕ} (rebuilt : PreimageTableau m)
    (correction : Pauli m) : PreimageTableau m
  | .inl index =>
      if correction.z index = 0 then rebuilt (.inl index) else -rebuilt (.inl index)
  | .inr index =>
      if correction.x index = 0 then rebuilt (.inr index) else -rebuilt (.inr index)

theorem phase_difference_is_sign (left right : PauliPhase)
    (same_double : left + left = right + right)
    (different : left ≠ right) :
    left = right + 2 := by
  have criterion : ∀ first second : PauliPhase,
      first + first = second + second →
        first = second ∨ first = second + 2 := by decide
  exact (criterion left right same_double).resolve_left different

theorem correct_row {m : ℕ} (target rebuilt : Pauli m)
    (same_binary : target.projective = rebuilt.projective)
    (target_hermitian : target.IsOrderTwo)
    (rebuilt_hermitian : rebuilt.IsOrderTwo) :
    (if target.phase = rebuilt.phase then rebuilt else -rebuilt) = target := by
  have same_double :
      target.phase + target.phase = rebuilt.phase + rebuilt.phase := by
    rw [Pauli.isOrderTwo_iff_phase] at target_hermitian rebuilt_hermitian
    rw [target_hermitian, rebuilt_hermitian, same_binary]
  by_cases same_phase : target.phase = rebuilt.phase
  · rw [ite_eq_left same_phase]
    apply Pauli.ext
    · exact congrArg ProjectivePauli.x same_binary.symm
    · exact congrArg ProjectivePauli.z same_binary.symm
    · exact same_phase.symm
  · rw [ite_eq_right same_phase]
    apply Pauli.ext
    · exact congrArg ProjectivePauli.x same_binary.symm
    · exact congrArg ProjectivePauli.z same_binary.symm
    · exact (phase_difference_is_sign _ _ same_double same_phase).symm

theorem finalPauliCorrection_spec {m : ℕ}
    (target rebuilt : PreimageTableau m)
    (same_binary : ∀ index, (target index).projective = (rebuilt index).projective)
    (target_hermitian : ∀ index, (target index).IsOrderTwo)
    (rebuilt_hermitian : ∀ index, (rebuilt index).IsOrderTwo) :
    leftMulPauli rebuilt (finalPauliCorrection target rebuilt) = target ∧
      (finalPauliCorrection target rebuilt).xyzPhase = 0 ∧
      (finalPauliCorrection target rebuilt).IsOrderTwo := by
  refine ⟨?_, Pauli.xyzPhase_positiveRepresentative _,
    Pauli.positiveRepresentative_isOrderTwo _⟩
  funext index
  have row := correct_row (target index) (rebuilt index)
    (same_binary index) (target_hermitian index) (rebuilt_hermitian index)
  cases index <;>
    simpa [leftMulPauli, finalPauliCorrection, Pauli.positiveRepresentative,
      Pauli.ofXYZPhase, Pauli.ofProjective, phaseMismatch] using row

/-- The row update uses the standard generator, not the current preimage,
in the commutation test. This is the left-multiplication convention. -/
theorem leftMulPauli_eq_pairing {m : ℕ}
    (rebuilt : PreimageTableau m) (correction : Pauli m)
    (index : PhaseIndex m) :
    leftMulPauli rebuilt correction index =
      if ProjectivePauli.commutationPairing correction.projective
          (match index with
            | .inl qubit => ProjectivePauli.singleX qubit
            | .inr qubit => ProjectivePauli.singleZ qubit) = 0
      then rebuilt index else -rebuilt index := by
  cases index <;> simp [leftMulPauli, Pauli.projective]

/-- Arbitrary signed rows are allowed: for identical tableaux the correction
is identity, including the zero-qubit case. -/
theorem finalPauliCorrection_self {m : ℕ} (tableau : PreimageTableau m) :
    finalPauliCorrection tableau tableau = 1 := by
  have coordinates :
      (⟨fun index => phaseMismatch (tableau (.inr index)) (tableau (.inr index)),
        fun index => phaseMismatch (tableau (.inl index)) (tableau (.inl index))⟩ :
          ProjectivePauli m) = 0 := by
    ext <;> simp [phaseMismatch]
  rw [finalPauliCorrection, coordinates]
  apply Pauli.ext
  · rfl
  · rfl
  · simp [Pauli.yCountPhase]

private def exampleRebuilt : PreimageTableau 1
  | .inl _ =>
      Pauli.positiveRepresentative
        (ProjectivePauli.singleX 0 + ProjectivePauli.singleZ 0)
  | .inr _ => Pauli.positiveRepresentative (ProjectivePauli.singleZ 0)

private def exampleTarget : PreimageTableau 1
  | .inl index => -exampleRebuilt (.inl index)
  | .inr index => exampleRebuilt (.inr index)

example : (finalPauliCorrection exampleTarget exampleRebuilt).x 0 = 0 := by decide
example : (finalPauliCorrection exampleTarget exampleRebuilt).z 0 = 1 := by decide

example :
    (finalPauliCorrection (fun index => -exampleRebuilt index) exampleRebuilt).phase = 1 := by
  decide

end PaulimerFormal.TransvectionSigns
