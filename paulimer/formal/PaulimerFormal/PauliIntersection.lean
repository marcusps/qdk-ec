import PaulimerFormal.PauliGroupMembership

/-! Phase compatibility in a projective Pauli-group intersection. -/

namespace PaulimerFormal.PauliIntersection

open PauliGroupMembership

variable {size : ℕ}

def Compatible (first second : Subgroup (Pauli size)) (pauli : Pauli size) : Prop :=
  ∃ common, common ∈ first ∧ common ∈ second ∧ common.projectiveRow = pauli.projectiveRow

theorem compatible_iff (first second : Subgroup (Pauli size)) (left right : Pauli size)
    (left_mem : left ∈ first) (right_mem : right ∈ second)
    (same : left.projectiveRow = right.projectiveRow) :
    Compatible first second left ↔ right.phase - left.phase ∈ scalarPhases first ⊔ scalarPhases second := by
  constructor
  · rintro ⟨common, in_first, in_second, row⟩
    have first_phase := (correction_mem_iff first left common left_mem row.symm).mp in_first
    have second_phase := (correction_mem_iff second right common right_mem
      (row.trans same).symm).mp in_second
    have difference : right.phase - left.phase =
        (common.phase - left.phase) - (common.phase - right.phase) := by abel
    rw [difference]
    exact (scalarPhases first ⊔ scalarPhases second).sub_mem
      (AddSubgroup.mem_sup_left first_phase) (AddSubgroup.mem_sup_right second_phase)
  · intro member
    obtain ⟨left_phase, in_first, right_phase, in_second, phases⟩ := AddSubgroup.mem_sup.mp member
    have replay : left * Pauli.scalar (left_phase + right_phase) = right := by
      rw [phases]
      exact correction_eq left right same
    have adjustment : left * Pauli.scalar left_phase = right * Pauli.scalar (-right_phase) := by
      rw [← replay, mul_assoc, ← Pauli.scalar_add]
      congr 2
      abel
    refine ⟨left * Pauli.scalar left_phase, first.mul_mem left_mem in_first, ?_, ?_⟩
    · rw [adjustment]
      exact second.mul_mem right_mem ((scalarPhases second).neg_mem in_second)
    · simp

theorem phase_difference_mul (left_first left_second right_first right_second : Pauli size)
    (same_first : left_first.projectiveRow = right_first.projectiveRow)
    (same_second : left_second.projectiveRow = right_second.projectiveRow) :
    (right_first * right_second).phase - (left_first * left_second).phase =
      (right_first.phase - left_first.phase) + (right_second.phase - left_second.phase) := by
  have first_projective := Pauli.projective_eq_of_projectiveRow_eq same_first
  have second_projective := Pauli.projective_eq_of_projectiveRow_eq same_second
  simp only [Pauli.phase_mul, ← first_projective, ← second_projective]
  abel

theorem square_phase_mem (group : Subgroup (Pauli size)) (pauli : Pauli size)
    (member : pauli ∈ group) : (pauli * pauli).phase ∈ scalarPhases group := by
  have scalar := Pauli.eq_scalar_phase_of_projective_eq_zero (pauli * pauli) (by simp)
  change Pauli.scalar (pauli * pauli).phase ∈ group
  rw [← scalar]
  exact group.mul_mem member member

theorem double_difference_mem (first second : Subgroup (Pauli size)) (left right : Pauli size)
    (left_mem : left ∈ first) (right_mem : right ∈ second)
    (same : left.projectiveRow = right.projectiveRow) :
    (right.phase - left.phase) + (right.phase - left.phase) ∈ scalarPhases first ⊔ scalarPhases second := by
  have member := (scalarPhases first ⊔ scalarPhases second).sub_mem
    (AddSubgroup.mem_sup_right (square_phase_mem second right right_mem))
    (AddSubgroup.mem_sup_left (square_phase_mem first left left_mem))
  rwa [phase_difference_mul left left right right same same] at member

theorem rejected_phases_cancel (phases : AddSubgroup PauliPhase) (first second : PauliPhase)
    (first_rejected : first ∉ phases) (second_rejected : second ∉ phases)
    (first_double : first + first ∈ phases) (second_double : second + second ∈ phases) :
    first + second ∈ phases := by
  have zero := phases.zero_mem
  fin_cases first <;> fin_cases second
  all_goals first
    | exact zero
    | exact first_double
    | exact (first_rejected zero).elim
    | exact (second_rejected zero).elim
    | exact (first_rejected second_double).elim
    | exact (second_rejected first_double).elim

theorem pair_rejected (first second : Subgroup (Pauli size))
    (left_first left_second right_first right_second : Pauli size)
    (left_first_mem : left_first ∈ first) (left_second_mem : left_second ∈ first)
    (right_first_mem : right_first ∈ second) (right_second_mem : right_second ∈ second)
    (same_first : left_first.projectiveRow = right_first.projectiveRow)
    (same_second : left_second.projectiveRow = right_second.projectiveRow)
    (first_rejected : ¬ Compatible first second left_first)
    (second_rejected : ¬ Compatible first second left_second) :
    Compatible first second (left_first * left_second) := by
  have same_product : (left_first * left_second).projectiveRow =
      (right_first * right_second).projectiveRow := by simp [same_first, same_second]
  apply (compatible_iff first second _ _ (first.mul_mem left_first_mem left_second_mem)
    (second.mul_mem right_first_mem right_second_mem) same_product).mpr
  rw [phase_difference_mul _ _ _ _ same_first same_second]
  exact rejected_phases_cancel _
    (right_first.phase - left_first.phase) (right_second.phase - left_second.phase)
    (fun member => first_rejected ((compatible_iff first second _ _ left_first_mem
      right_first_mem same_first).mpr member))
    (fun member => second_rejected ((compatible_iff first second _ _ left_second_mem
      right_second_mem same_second).mpr member))
    (double_difference_mem first second _ _ left_first_mem right_first_mem same_first)
    (double_difference_mem first second _ _ left_second_mem right_second_mem same_second)

end PaulimerFormal.PauliIntersection
