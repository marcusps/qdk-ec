import PaulimerFormal.PauliAlgorithms

/-! Phase-aware Pauli-exponent automorphisms and their binary transvections. -/

namespace PaulimerFormal.Pauli

variable {m : ℕ}

@[simp]
theorem addPhase_zero (pauli : Pauli m) : addPhase pauli 0 = pauli := by
  apply Pauli.ext
  · rfl
  · rfl
  · simp

theorem addPhase_mul (left right : Pauli m) (phase : PauliPhase) :
    addPhase left phase * right = addPhase (left * right) phase := by
  apply Pauli.ext
  · rfl
  · rfl
  · simp only [phase_mul, phase_addPhase, projective_addPhase]
    abel

theorem mul_addPhase (left right : Pauli m) (phase : PauliPhase) :
    left * addPhase right phase = addPhase (left * right) phase := by
  apply Pauli.ext
  · rfl
  · rfl
  · simp only [phase_mul, phase_addPhase, projective_addPhase]
    abel

theorem addPhase_addPhase (pauli : Pauli m) (first second : PauliPhase) :
    addPhase (addPhase pauli first) second = addPhase pauli (first + second) := by
  apply Pauli.ext
  · rfl
  · rfl
  · simp only [phase_addPhase, add_assoc]

theorem addPhase_two (pauli : Pauli m) : addPhase pauli 2 = -pauli := rfl

theorem exponentAction_projective (target exponent : Pauli m) :
    (exponentAction target exponent).projective.toPhaseVector =
      rowAction target.projective.toPhaseVector (transvection exponent.projective.toPhaseVector) := by
  by_cases commutes : ProjectivePauli.commutationPairing target.projective exponent.projective = 0
  · simp [exponentAction, commutes, rowAction_transvection,
      ← ProjectivePauli.commutationPairing_eq_pairing]
  · have paired := (f2_eq_zero_or_one
      (ProjectivePauli.commutationPairing target.projective exponent.projective)).resolve_left commutes
    simp [exponentAction, rowAction_transvection,
      ← ProjectivePauli.commutationPairing_eq_pairing, paired, add_comm]

theorem exponentAction_mul (exponent : Pauli m) (hermitian : exponent.IsOrderTwo)
    (left right : Pauli m) :
    exponentAction (left * right) exponent =
      exponentAction left exponent * exponentAction right exponent := by
  rcases f2_eq_zero_or_one
    (ProjectivePauli.commutationPairing left.projective exponent.projective) with left_zero | left_one
  · rcases f2_eq_zero_or_one
      (ProjectivePauli.commutationPairing right.projective exponent.projective) with right_zero | right_one
    · simp [exponentAction, ProjectivePauli.commutationPairing_add_left, left_zero, right_zero]
    · have commutes := (mul_comm_iff_commutationPairing_eq_zero left exponent).mpr left_zero
      have reorder : exponent * (left * right) = left * (exponent * right) := by
        rw [← mul_assoc, ← commutes, mul_assoc]
      simp [exponentAction, ProjectivePauli.commutationPairing_add_left, left_zero, right_one,
        mul_addPhase, reorder]
  · rcases f2_eq_zero_or_one
      (ProjectivePauli.commutationPairing right.projective exponent.projective) with right_zero | right_one
    · simp [exponentAction, ProjectivePauli.commutationPairing_add_left, left_one, right_zero,
        addPhase_mul, mul_assoc]
    · have inverse : exponent⁻¹ = exponent := (isHermitian_iff_isOrderTwo exponent).mpr hermitian
      have conjugation : exponent * left * exponent = -left := by
        have paired : ProjectivePauli.commutationPairing exponent.projective left.projective = 1 := by
          rw [ProjectivePauli.commutationPairing_comm]
          exact left_one
        simpa only [conjugate, inverse] using conjugate_eq_neg_of_commutationPairing_eq_one exponent left paired
      have products : (exponent * left) * (exponent * right) = -(left * right) := by
        rw [← mul_assoc, conjugation, neg_mul]
      simp [exponentAction, ProjectivePauli.commutationPairing_add_left, left_one, right_one,
        addPhase_mul, mul_addPhase, addPhase_addPhase,
        show (1 : PauliPhase) + 1 = 2 by decide, addPhase_two, products]

theorem exponentAction_pairing (target exponent : Pauli m) :
    ProjectivePauli.commutationPairing (exponentAction target exponent).projective exponent.projective =
      ProjectivePauli.commutationPairing target.projective exponent.projective := by
  by_cases commutes : ProjectivePauli.commutationPairing target.projective exponent.projective = 0 <;>
    simp [exponentAction, commutes, ProjectivePauli.commutationPairing_add_left]

theorem exponentAction_neg_inverse (exponent : Pauli m) (hermitian : exponent.IsOrderTwo)
    (target : Pauli m) : exponentAction (exponentAction target exponent) (-exponent) = target := by
  by_cases commutes : ProjectivePauli.commutationPairing target.projective exponent.projective = 0
  · simp [exponentAction, commutes]
  · rw [exponentAction, projective_neg, exponentAction_pairing, ite_eq_right commutes,
      exponentAction, ite_eq_right commutes, mul_addPhase, addPhase_addPhase,
      show (1 : PauliPhase) + 1 = 2 by decide, addPhase_two]
    have square : exponent * exponent = 1 := hermitian
    simp [← mul_assoc, square]

theorem exponentAction_scalar (exponent : Pauli m) (phase : PauliPhase) :
    exponentAction (ofProjective 0 phase) exponent = ofProjective 0 phase := by
  simp [exponentAction, ProjectivePauli.commutationPairing, ProjectivePauli.xzCross]

def exponentEquiv (exponent : Pauli m) (hermitian : exponent.IsOrderTwo) : Pauli m ≃* Pauli m where
  toFun := fun target => exponentAction target exponent
  invFun := fun target => exponentAction target (-exponent)
  left_inv := exponentAction_neg_inverse exponent hermitian
  right_inv := by
    intro target
    have negative_hermitian : (-exponent).IsOrderTwo := by
      change (-exponent) * (-exponent) = 1
      simpa [IsOrderTwo] using hermitian
    simpa only [neg_neg] using exponentAction_neg_inverse (-exponent) negative_hermitian target
  map_mul' := exponentAction_mul exponent hermitian

theorem exponentAction_isOrderTwo (exponent : Pauli m) (hermitian : exponent.IsOrderTwo)
    (target : Pauli m) (target_hermitian : target.IsOrderTwo) :
    (exponentAction target exponent).IsOrderTwo := by
  change exponentEquiv exponent hermitian target * exponentEquiv exponent hermitian target = 1
  rw [← map_mul, target_hermitian, map_one]

theorem exponent_spec (exponent : Pauli m) (hermitian : exponent.IsOrderTwo) :
    Function.Bijective (fun target => exponentAction target exponent) ∧
    (∀ left right, exponentAction (left * right) exponent =
      exponentAction left exponent * exponentAction right exponent) ∧
    (∀ target, exponentAction (exponentAction target exponent) (-exponent) = target) ∧
    (∀ phase, exponentAction (ofProjective 0 phase) exponent = ofProjective 0 phase) ∧
    (∀ target, (exponentAction target exponent).projective.toPhaseVector =
      rowAction target.projective.toPhaseVector (transvection exponent.projective.toPhaseVector)) ∧
    (∀ target, target.IsOrderTwo → (exponentAction target exponent).IsOrderTwo) := by
  exact ⟨(exponentEquiv exponent hermitian).bijective, exponentAction_mul exponent hermitian,
    exponentAction_neg_inverse exponent hermitian, exponentAction_scalar exponent,
    fun target => exponentAction_projective target exponent, exponentAction_isOrderTwo exponent hermitian⟩

end PaulimerFormal.Pauli
