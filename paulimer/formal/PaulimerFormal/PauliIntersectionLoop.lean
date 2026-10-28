import PaulimerFormal.PauliIntersectionSelection

/-! Ordered one-pass intersection traversal, with explicit failure for a missing paired phase. -/

namespace PaulimerFormal.PauliIntersection

variable {size : ℕ}

def listGroup (paulis : List (Pauli size)) : Subgroup (Pauli size) :=
  Subgroup.closure { pauli | pauli ∈ paulis }

theorem listGroup_mono {first second : List (Pauli size)} (included : first ⊆ second) :
    listGroup first ≤ listGroup second :=
  Subgroup.closure_mono included

theorem listGroup_cons_le (pauli : Pauli size) (tail : List (Pauli size)) (group : Subgroup (Pauli size))
    (member : pauli ∈ group) (included : listGroup tail ≤ group) :
    listGroup (pauli :: tail) ≤ group := by
  rw [listGroup, Subgroup.closure_le]
  intro candidate in_list
  rcases List.mem_cons.mp in_list with rfl | in_tail
  · exact member
  · exact included (Subgroup.subset_closure in_tail)

theorem listGroup_append (first second : List (Pauli size)) :
    listGroup (first ++ second) = listGroup first ⊔ listGroup second := by
  simp only [listGroup, List.mem_append, Set.ofPred_or, Subgroup.closure_union]

def Covers (anchor : Option (Pauli size)) (output : List (Pauli size)) (base : Pauli size) : Prop :=
  base.projectiveRow ∈ rowImage (listGroup output) ∨
    ∃ rejected, anchor = some rejected ∧
      base.projectiveRow + rejected.projectiveRow ∈ rowImage (listGroup output)

theorem covers_mono {first second : List (Pauli size)} (included : first ⊆ second)
    {anchor : Option (Pauli size)} {base : Pauli size} (covered : Covers anchor first base) :
    Covers anchor second base := by
  rcases covered with plain | ⟨rejected, same, shifted⟩
  · exact Or.inl (rowImage_mono (listGroup_mono included) plain)
  · exact Or.inr ⟨rejected, same, rowImage_mono (listGroup_mono included) shifted⟩

def scan (first second : List (DensePauli size)) :
    Option (Pauli size) → List (Pauli size) → Option (List (Pauli size))
  | _, [] => some []
  | anchor, base :: tail =>
      match commonVariant first second base with
      | some candidate => (scan first second anchor tail).map (candidate :: ·)
      | none =>
          match anchor with
          | none => scan first second (some base) tail
          | some rejected => do
              let candidate ← commonVariant first second (base * rejected)
              let remaining ← scan first second anchor tail
              pure (candidate :: remaining)

theorem scan_anchored (first second : List (DensePauli size)) (anchor : Pauli size)
    (anchor_row : anchor.projectiveRow ∈ rowImage (generatedPauliGroup first) ⊓ rowImage (generatedPauliGroup second))
    (anchor_rejected : commonVariant first second anchor = none)
    (basis : List (Pauli size))
    (valid : ∀ base ∈ basis,
      base.projectiveRow ∈ rowImage (generatedPauliGroup first) ⊓ rowImage (generatedPauliGroup second)) :
    ∃ output, scan first second (some anchor) basis = some output ∧
      listGroup output ≤ generatedPauliGroup first ⊓ generatedPauliGroup second ∧
      ∀ base ∈ basis, Covers (some anchor) output base := by
  induction basis with
  | nil =>
      refine ⟨[], rfl, ?_, by simp⟩
      rw [listGroup, Subgroup.closure_le]
      simp
  | cons base tail induction =>
      obtain ⟨output, returned, sound, covered⟩ := induction (fun pauli member => valid pauli (by simp [member]))
      cases chosen : commonVariant first second base with
      | some candidate =>
          have candidate_spec := commonVariant_some first second base candidate chosen
          refine ⟨candidate :: output, by simp [scan, chosen, returned],
            listGroup_cons_le _ _ _ candidate_spec.1 sound, ?_⟩
          intro pauli member
          rcases List.mem_cons.mp member with rfl | in_tail
          · exact Or.inl ⟨candidate, Subgroup.subset_closure (by simp), candidate_spec.2⟩
          · exact covers_mono (by intro item member; simp [member]) (covered pauli in_tail)
      | none =>
          have exists_pair := pairedVariant_exists first second base anchor (valid base (by simp))
            anchor_row chosen anchor_rejected
          cases paired : commonVariant first second (base * anchor) with
          | none => simp [paired] at exists_pair
          | some candidate =>
              have candidate_spec := commonVariant_some first second (base * anchor) candidate paired
              refine ⟨candidate :: output, by simp [scan, chosen, paired, returned],
                listGroup_cons_le _ _ _ candidate_spec.1 sound, ?_⟩
              intro pauli member
              rcases List.mem_cons.mp member with rfl | in_tail
              · exact Or.inr ⟨anchor, rfl, candidate, Subgroup.subset_closure (by simp),
                  by simpa only [Pauli.projectiveRow_mul] using candidate_spec.2⟩
              · exact covers_mono (by intro item member; simp [member]) (covered pauli in_tail)

theorem scan_unanchored (first second : List (DensePauli size)) (basis : List (Pauli size))
    (valid : ∀ base ∈ basis,
      base.projectiveRow ∈ rowImage (generatedPauliGroup first) ⊓ rowImage (generatedPauliGroup second)) :
    ∃ output, scan first second none basis = some output ∧
      listGroup output ≤ generatedPauliGroup first ⊓ generatedPauliGroup second ∧
      ∀ base ∈ basis, Covers (rejectedAnchor first second basis) output base := by
  induction basis with
  | nil =>
      refine ⟨[], rfl, ?_, by simp⟩
      rw [listGroup, Subgroup.closure_le]
      simp
  | cons base tail induction =>
      have tail_valid := fun pauli member => valid pauli (List.mem_cons_of_mem base member)
      cases chosen : commonVariant first second base with
      | some candidate =>
          obtain ⟨output, returned, sound, covered⟩ := induction tail_valid
          have candidate_spec := commonVariant_some first second base candidate chosen
          have same_anchor : rejectedAnchor first second (base :: tail) = rejectedAnchor first second tail := by
            simp [rejectedAnchor, chosen]
          refine ⟨candidate :: output, by simp [scan, chosen, returned],
            listGroup_cons_le _ _ _ candidate_spec.1 sound, ?_⟩
          intro pauli member
          rw [same_anchor]
          rcases List.mem_cons.mp member with rfl | in_tail
          · exact Or.inl ⟨candidate, Subgroup.subset_closure (by simp), candidate_spec.2⟩
          · exact covers_mono (by intro item member; simp [member]) (covered pauli in_tail)
      | none =>
          obtain ⟨output, returned, sound, covered⟩ :=
            scan_anchored first second base (valid base (by simp)) chosen tail tail_valid
          have same_anchor : rejectedAnchor first second (base :: tail) = some base := by
            simp [rejectedAnchor, chosen]
          refine ⟨output, by simpa only [scan, chosen] using returned, sound, ?_⟩
          intro pauli member
          rw [same_anchor]
          rcases List.mem_cons.mp member with rfl | in_tail
          · refine Or.inr ⟨pauli, rfl, ?_⟩
            simpa only [ZModModule.add_self] using (rowImage (listGroup output)).zero_mem
          · exact covered pauli in_tail

def ValidBasis (first second : List (DensePauli size)) (basis : List (Pauli size)) : Prop :=
  Submodule.span F2 (Set.range fun index : Fin basis.length => basis[index].projectiveRow) =
    rowImage (generatedPauliGroup first) ⊓ rowImage (generatedPauliGroup second)

theorem loop_spec (first second : List (DensePauli size)) (basis : List (Pauli size))
    (spanning : ValidBasis first second basis) :
    ∃ output, scan first second none basis = some output ∧
      listGroup output ⊔ scalarPauliSubgroup
        (scalarPhases (generatedPauliGroup first ⊓ generatedPauliGroup second)) =
          generatedPauliGroup first ⊓ generatedPauliGroup second := by
  unfold ValidBasis at spanning
  let target := generatedPauliGroup first ⊓ generatedPauliGroup second
  let rows := fun index : Fin basis.length => basis[index].projectiveRow
  have original_member (base : Pauli size) (member : base ∈ basis) :
      base.projectiveRow ∈ Submodule.span F2 (Set.range rows) := by
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    exact Submodule.subset_span (Set.mem_range_self index)
  have valid (base : Pauli size) (member : base ∈ basis) :
      base.projectiveRow ∈ rowImage (generatedPauliGroup first) ⊓ rowImage (generatedPauliGroup second) := by
    rw [← spanning]
    exact original_member base member
  obtain ⟨output, returned, sound, covered⟩ := scan_unanchored first second basis valid
  refine ⟨output, returned, ?_⟩
  let found := listGroup output ⊔ scalarPauliSubgroup (scalarPhases target)
  have sound_found : found ≤ target := sup_le sound (scalarPauliSubgroup_le_group _)
  have output_le : listGroup output ≤ found := le_sup_left
  have target_contained : rowImage target ≤ Submodule.span F2 (Set.range rows) := by
    rw [spanning]
    exact le_inf (rowImage_mono inf_le_left) (rowImage_mono inf_le_right)
  apply subgroup_eq_of_rows_and_scalars sound_found
  · cases anchor : rejectedAnchor first second basis with
    | none =>
        apply le_trans target_contained
        apply Submodule.span_le.mpr
        rintro _ ⟨index, rfl⟩
        have coverage := covered basis[index] (List.get_mem basis index)
        rw [anchor] at coverage
        rcases coverage with plain | ⟨_, impossible, _⟩
        · exact rowImage_mono output_le plain
        · cases impossible
    | some rejected =>
        obtain ⟨rejected_mem, rejected_bad⟩ := rejectedAnchor_some first second basis rejected anchor
        have rejected_row : rejected.projectiveRow ∉ rowImage target :=
          fun member => rejected_bad ((compatible_row _ _ _).mpr member)
        have complete := corrected_span (rowImage target) rows rejected.projectiveRow
          (original_member rejected rejected_mem) rejected_row
          (fun index failed => rejected_rows_add _ _ _ _ (valid basis[index] (List.get_mem basis index))
            (valid rejected rejected_mem) failed rejected_row)
        rw [inf_eq_left.mpr target_contained] at complete
        rw [← complete]
        apply Submodule.span_le.mpr
        rintro _ ⟨index, rfl⟩
        have coverage := covered basis[index] (List.get_mem basis index)
        rw [anchor] at coverage
        dsimp only [correctedRow]
        split_ifs with compatible
        · rcases coverage with plain | ⟨other, same, shifted⟩
          · exact rowImage_mono output_le plain
          · cases same
            exfalso
            apply rejected_row
            have cancel : (rows index + rejected.projectiveRow) - rows index = rejected.projectiveRow := by abel
            exact cancel ▸ (rowImage target).sub_mem (rowImage_mono sound shifted) compatible
        · rcases coverage with plain | ⟨other, same, shifted⟩
          · exact (compatible (rowImage_mono sound plain)).elim
          · cases same
            exact rowImage_mono output_le shifted
  · intro phase member
    change Pauli.scalar phase ∈ found
    apply Subgroup.mem_sup_right
    exact ⟨by simp, member⟩

def commonPhases (first second : List (DensePauli size)) : List PauliPhase :=
  (PauliGroupMembership.phases first).filter fun phase => (PauliGroupMembership.phases second).contains phase

theorem mem_commonPhases_iff (first second : List (DensePauli size)) (phase : PauliPhase) :
    phase ∈ commonPhases first second ↔ phase ∈ scalarPhases (generatedPauliGroup first ⊓ generatedPauliGroup second) := by
  simp [commonPhases, PauliGroupMembership.mem_phases_iff, scalarPhases]
  rfl

theorem common_scalars_generate (first second : List (DensePauli size)) :
    listGroup ((commonPhases first second).map (Pauli.scalar (m := size))) =
      scalarPauliSubgroup (scalarPhases (generatedPauliGroup first ⊓ generatedPauliGroup second)) := by
  apply le_antisymm
  · rw [listGroup, Subgroup.closure_le]
    rintro pauli member
    obtain ⟨phase, phase_mem, rfl⟩ := List.mem_map.mp member
    exact ⟨by simp, (mem_commonPhases_iff first second phase).mp phase_mem⟩
  · intro pauli member
    have scalar := Pauli.eq_scalar_phase_of_projective_eq_zero pauli member.1
    apply Subgroup.subset_closure
    exact List.mem_map.mpr ⟨pauli.phase, (mem_commonPhases_iff first second _).mpr member.2, scalar.symm⟩

def intersectionFromBasis (first second : List (DensePauli size)) (basis : List (Pauli size)) :
    Option (List (Pauli size)) :=
  (scan first second none basis).map fun output => output ++ (commonPhases first second).map Pauli.scalar

theorem intersection_spec (first second : List (DensePauli size)) (basis : List (Pauli size))
    (spanning : ValidBasis first second basis) :
    ∃ output, intersectionFromBasis first second basis = some output ∧
      listGroup output = generatedPauliGroup first ⊓ generatedPauliGroup second := by
  obtain ⟨output, returned, complete⟩ := loop_spec first second basis spanning
  refine ⟨output ++ (commonPhases first second).map Pauli.scalar, ?_, ?_⟩
  · simp [intersectionFromBasis, returned]
  · rwa [listGroup_append, common_scalars_generate]

theorem traversal_spec (first second : List (DensePauli size)) (basis : List (Pauli size))
    (spanning : ValidBasis first second basis) :
    (intersectionFromBasis first second basis).isSome = true ∧
      ∀ output, intersectionFromBasis first second basis = some output →
        listGroup output = generatedPauliGroup first ⊓ generatedPauliGroup second := by
  obtain ⟨output, returned, complete⟩ := intersection_spec first second basis spanning
  refine ⟨by simp [returned], ?_⟩
  intro candidate candidate_returned
  rw [returned] at candidate_returned
  cases candidate_returned
  exact complete

end PaulimerFormal.PauliIntersection
