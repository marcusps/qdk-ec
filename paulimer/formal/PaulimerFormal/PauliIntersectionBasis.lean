import PaulimerFormal.PauliIntersection

/-! Completeness of intersection generators obtained by pairing rejected rows. -/

namespace PaulimerFormal.PauliIntersection

variable {size : ℕ}

def rowImage (group : Subgroup (Pauli size)) : Submodule F2 (Fin (size + size) → F2) where
  carrier := { vector | ∃ pauli ∈ group, pauli.projectiveRow = vector }
  zero_mem' := ⟨1, group.one_mem, Pauli.projectiveRow_one⟩
  add_mem' := by
    rintro _ _ ⟨first, first_mem, rfl⟩ ⟨second, second_mem, rfl⟩
    exact ⟨first * second, group.mul_mem first_mem second_mem, Pauli.projectiveRow_mul _ _⟩
  smul_mem' := by
    intro scalar vector member
    rcases Pauli.f2_eq_zero_or_one scalar with zero | one
    · rw [zero, zero_smul]
      exact ⟨1, group.one_mem, Pauli.projectiveRow_one⟩
    · simpa only [one, one_smul] using member

theorem rowImage_mono {first second : Subgroup (Pauli size)} (included : first ≤ second) :
    rowImage first ≤ rowImage second := by
  rintro _ ⟨pauli, member, rfl⟩
  exact ⟨pauli, included member, rfl⟩

theorem compatible_row (first second : Subgroup (Pauli size)) (pauli : Pauli size) :
    Compatible first second pauli ↔ pauli.projectiveRow ∈ rowImage (first ⊓ second) := by
  constructor
  · rintro ⟨common, in_first, in_second, row⟩
    exact ⟨common, ⟨in_first, in_second⟩, row⟩
  · rintro ⟨common, member, row⟩
    exact ⟨common, member.1, member.2, row⟩

theorem rejected_rows_add (first second : Subgroup (Pauli size))
    (left right : Fin (size + size) → F2)
    (left_mem : left ∈ rowImage first ⊓ rowImage second)
    (right_mem : right ∈ rowImage first ⊓ rowImage second)
    (left_rejected : left ∉ rowImage (first ⊓ second))
    (right_rejected : right ∉ rowImage (first ⊓ second)) :
    left + right ∈ rowImage (first ⊓ second) := by
  obtain ⟨left_first, left_first_mem, left_first_row⟩ := left_mem.1
  obtain ⟨right_first, right_first_mem, right_first_row⟩ := right_mem.1
  obtain ⟨left_second, left_second_mem, left_second_row⟩ := left_mem.2
  obtain ⟨right_second, right_second_mem, right_second_row⟩ := right_mem.2
  have paired := pair_rejected first second left_first right_first left_second right_second
    left_first_mem right_first_mem left_second_mem right_second_mem
    (left_first_row.trans left_second_row.symm) (right_first_row.trans right_second_row.symm)
    (fun accepted => left_rejected (left_first_row ▸ (compatible_row _ _ _).mp accepted))
    (fun accepted => right_rejected (right_first_row ▸ (compatible_row _ _ _).mp accepted))
  simpa only [Pauli.projectiveRow_mul, left_first_row, right_first_row] using
    (compatible_row _ _ _).mp paired

section Linear

variable {Vector Index : Type*} [AddCommGroup Vector] [Module F2 Vector]

noncomputable def correctedRow (common : Submodule F2 Vector) (anchor vector : Vector) : Vector := by
  classical
  exact if vector ∈ common then vector else vector + anchor

theorem corrected_span (common : Submodule F2 Vector) (basis : Index → Vector) (anchor : Vector)
    (anchor_mem : anchor ∈ Submodule.span F2 (Set.range basis))
    (anchor_rejected : anchor ∉ common)
    (pairs : ∀ index, basis index ∉ common → basis index + anchor ∈ common) :
    Submodule.span F2 (Set.range fun index => correctedRow common anchor (basis index)) =
      common ⊓ Submodule.span F2 (Set.range basis) := by
  classical
  let repaired := Submodule.span F2 (Set.range fun index => correctedRow common anchor (basis index))
  have in_common : repaired ≤ common := by
    apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    dsimp only [correctedRow]
    split_ifs with member
    · exact member
    · exact pairs index member
  have in_original : repaired ≤ Submodule.span F2 (Set.range basis) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    have member : basis index ∈ Submodule.span F2 (Set.range basis) :=
      Submodule.subset_span (Set.mem_range_self index)
    dsimp only [correctedRow]
    split_ifs
    · exact member
    · exact Submodule.add_mem _ member anchor_mem
  have two_cosets (vector : Vector) (member : vector ∈ Submodule.span F2 (Set.range basis)) :
      vector ∈ repaired ∨ vector + anchor ∈ repaired := by
    induction member using Submodule.span_induction with
    | mem vector member =>
        obtain ⟨index, rfl⟩ := member
        have included : correctedRow common anchor (basis index) ∈ repaired :=
          Submodule.subset_span (Set.mem_range_self index)
        dsimp only [correctedRow] at included
        split_ifs at included with accepted
        · exact Or.inl included
        · exact Or.inr included
    | zero => exact Or.inl repaired.zero_mem
    | add left right _ _ left_case right_case =>
        rcases left_case with plain_left | shifted_left <;>
          rcases right_case with plain_right | shifted_right
        · exact Or.inl (repaired.add_mem plain_left plain_right)
        · exact Or.inr (by simpa only [add_assoc] using repaired.add_mem plain_left shifted_right)
        · exact Or.inr (by simpa only [add_assoc, add_comm anchor right] using
            repaired.add_mem shifted_left plain_right)
        · left
          have cancel : (left + anchor) + (right + anchor) = left + right := by
            calc
              _ = (left + right) + (anchor + anchor) := by abel
              _ = _ := by rw [ZModModule.add_self, add_zero]
          exact cancel ▸ repaired.add_mem shifted_left shifted_right
    | smul scalar vector _ cases =>
        rcases Pauli.f2_eq_zero_or_one scalar with zero | one
        · simp only [zero, zero_smul]
          exact Or.inl repaired.zero_mem
        · simpa only [one, one_smul] using cases
  apply le_antisymm (le_inf in_common in_original)
  intro vector member
  rcases two_cosets vector member.2 with plain | shifted
  · exact plain
  · exfalso
    apply anchor_rejected
    have cancel : (vector + anchor) - vector = anchor := by abel
    exact cancel ▸ common.sub_mem (in_common shifted) member.1

end Linear

theorem subgroup_eq_of_rows_and_scalars {found target : Subgroup (Pauli size)}
    (sound : found ≤ target) (rows : rowImage target ≤ rowImage found)
    (scalars : scalarPhases target ≤ scalarPhases found) : found = target := by
  apply le_antisymm sound
  intro pauli member
  obtain ⟨representative, represented, same⟩ := rows ⟨pauli, member, rfl⟩
  have correction := (PauliGroupMembership.correction_mem_iff target representative pauli
    (sound represented) same).mp member
  exact (PauliGroupMembership.correction_mem_iff found representative pauli represented same).mpr
    (scalars correction)

theorem lifted_generators_complete {Index : Type*} (target : Subgroup (Pauli size))
    (selected : Index → Pauli size)
    (selected_mem : ∀ index, selected index ∈ target)
    (spanning : Submodule.span F2 (Set.range fun index => (selected index).projectiveRow) = rowImage target) :
    Subgroup.closure (Set.range selected) ⊔ scalarPauliSubgroup (scalarPhases target) = target := by
  let found := Subgroup.closure (Set.range selected) ⊔ scalarPauliSubgroup (scalarPhases target)
  have sound : found ≤ target := by
    apply sup_le
    · rw [Subgroup.closure_le]
      rintro _ ⟨index, rfl⟩
      exact selected_mem index
    · exact scalarPauliSubgroup_le_group _
  apply subgroup_eq_of_rows_and_scalars sound
  · rw [← spanning]
    apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    exact ⟨selected index, Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_range_self index)), rfl⟩
  · intro phase member
    change Pauli.scalar phase ∈ found
    apply Subgroup.mem_sup_right
    exact ⟨by simp, member⟩

theorem corrected_basis_complete {Index : Type*} (first second : Subgroup (Pauli size))
    (basis : Index → Fin (size + size) → F2)
    (spanning : Submodule.span F2 (Set.range basis) = rowImage first ⊓ rowImage second)
    (anchor : Index) (rejected : basis anchor ∉ rowImage (first ⊓ second))
    (selected : Index → Pauli size)
    (selected_mem : ∀ index, selected index ∈ first ⊓ second)
    (selected_row : ∀ index, (selected index).projectiveRow =
      correctedRow (rowImage (first ⊓ second)) (basis anchor) (basis index)) :
    Subgroup.closure (Set.range selected) ⊔ scalarPauliSubgroup (scalarPhases (first ⊓ second)) =
      first ⊓ second := by
  have original_member (index : Index) : basis index ∈ rowImage first ⊓ rowImage second := by
    rw [← spanning]
    exact Submodule.subset_span (Set.mem_range_self index)
  have complete := corrected_span (rowImage (first ⊓ second)) basis (basis anchor)
    (Submodule.subset_span (Set.mem_range_self anchor)) rejected
    (fun index failure => rejected_rows_add first second _ _ (original_member index)
      (original_member anchor) failure rejected)
  have contained : rowImage (first ⊓ second) ≤ Submodule.span F2 (Set.range basis) := by
    rw [spanning]
    exact le_inf (rowImage_mono inf_le_left) (rowImage_mono inf_le_right)
  apply lifted_generators_complete _ selected selected_mem
  simp_rw [selected_row]
  exact complete.trans (inf_eq_left.mpr contained)

theorem basis_spec {Index : Type*} (first second : Subgroup (Pauli size))
    (basis : Index → Fin (size + size) → F2)
    (spanning : Submodule.span F2 (Set.range basis) = rowImage first ⊓ rowImage second)
    (anchor : Option Index)
    (valid : match anchor with
      | none => ∀ index, basis index ∈ rowImage (first ⊓ second)
      | some index => basis index ∉ rowImage (first ⊓ second)) :
    ∃ selected : Index → Pauli size,
      (∀ index, selected index ∈ first ⊓ second) ∧
      (∀ index, (selected index).projectiveRow = match anchor with
        | none => basis index
        | some rejected => correctedRow (rowImage (first ⊓ second)) (basis rejected) (basis index)) ∧
      Subgroup.closure (Set.range selected) ⊔ scalarPauliSubgroup (scalarPhases (first ⊓ second)) =
        first ⊓ second := by
  classical
  cases anchor with
  | none =>
      dsimp only
      change ∀ index, ∃ pauli ∈ first ⊓ second, pauli.projectiveRow = basis index at valid
      choose selected selected_mem selected_row using valid
      refine ⟨selected, selected_mem, selected_row, lifted_generators_complete _ _ selected_mem ?_⟩
      simp_rw [selected_row]
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨index, rfl⟩
        exact ⟨selected index, selected_mem index, selected_row index⟩
      · rw [spanning]
        exact le_inf (rowImage_mono inf_le_left) (rowImage_mono inf_le_right)
  | some anchor =>
      have corrected (index : Index) :
          correctedRow (rowImage (first ⊓ second)) (basis anchor) (basis index) ∈ rowImage (first ⊓ second) := by
        dsimp only [correctedRow]
        split_ifs with member
        · exact member
        · have original_member (position : Index) : basis position ∈ rowImage first ⊓ rowImage second := by
            rw [← spanning]
            exact Submodule.subset_span (Set.mem_range_self position)
          exact rejected_rows_add first second _ _ (original_member index) (original_member anchor) member valid
      change ∀ index, ∃ pauli ∈ first ⊓ second,
        pauli.projectiveRow = correctedRow (rowImage (first ⊓ second)) (basis anchor) (basis index) at corrected
      choose selected selected_mem selected_row using corrected
      exact ⟨selected, selected_mem, selected_row,
        corrected_basis_complete first second basis spanning anchor valid selected selected_mem selected_row⟩

end PaulimerFormal.PauliIntersection
