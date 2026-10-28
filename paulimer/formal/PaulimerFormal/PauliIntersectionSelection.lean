import PaulimerFormal.PauliIntersectionBasis

/-! Executable common-phase selection and rejected-anchor discovery. -/

namespace PaulimerFormal.PauliIntersection

open PauliGroupMembership

variable {size : ℕ}

def accepts (first second : List (DensePauli size)) (pauli : Pauli size) : Bool :=
  (factorization first (DensePauli.ofPauli pauli)).isSome &&
    (factorization second (DensePauli.ofPauli pauli)).isSome

theorem accepts_iff (first second : List (DensePauli size)) (pauli : Pauli size) :
    accepts first second pauli = true ↔
      pauli ∈ generatedPauliGroup first ⊓ generatedPauliGroup second := by
  simp [accepts, factorization_isSome_iff]

def variants (base : Pauli size) : List (Pauli size) :=
  [0, 1, 2, 3].map fun phase => { base with phase }

theorem mem_variants_iff (base candidate : Pauli size) :
    candidate ∈ variants base ↔ candidate.projectiveRow = base.projectiveRow := by
  constructor
  · intro member
    obtain ⟨phase, _, rfl⟩ := List.mem_map.mp member
    rfl
  · intro same
    have projective := Pauli.projective_eq_of_projectiveRow_eq same
    have all_phases : ∀ phase : PauliPhase, phase ∈ [0, 1, 2, 3] := by decide +kernel
    apply List.mem_map.mpr
    refine ⟨candidate.phase, all_phases _, ?_⟩
    apply Pauli.ext
    · exact (congrArg ProjectivePauli.x projective).symm
    · exact (congrArg ProjectivePauli.z projective).symm
    · rfl

def commonVariant (first second : List (DensePauli size)) (base : Pauli size) : Option (Pauli size) :=
  (variants base).find? (accepts first second)

theorem commonVariant_some (first second : List (DensePauli size)) (base candidate : Pauli size)
    (returned : commonVariant first second base = some candidate) :
    candidate ∈ generatedPauliGroup first ⊓ generatedPauliGroup second ∧
      candidate.projectiveRow = base.projectiveRow :=
  ⟨(accepts_iff first second candidate).mp (List.find?_some returned),
    (mem_variants_iff base candidate).mp (List.mem_of_find?_eq_some returned)⟩

theorem commonVariant_none_iff (first second : List (DensePauli size)) (base : Pauli size) :
    commonVariant first second base = none ↔
      ¬ Compatible (generatedPauliGroup first) (generatedPauliGroup second) base := by
  constructor
  · intro returned
    rintro ⟨candidate, in_first, in_second, row⟩
    have rejected := List.find?_eq_none.mp returned candidate ((mem_variants_iff base candidate).mpr row)
    have accepted := (accepts_iff first second candidate).mpr ⟨in_first, in_second⟩
    exact rejected accepted
  · intro absent
    apply List.find?_eq_none.mpr
    intro candidate member result
    have accepted := (accepts_iff first second candidate).mp result
    exact absent ⟨candidate, accepted.1, accepted.2, (mem_variants_iff base candidate).mp member⟩

theorem commonVariant_isSome_iff (first second : List (DensePauli size)) (base : Pauli size) :
    (commonVariant first second base).isSome = true ↔
      Compatible (generatedPauliGroup first) (generatedPauliGroup second) base := by
  classical
  simp only [Option.isSome_iff_ne_none, ne_eq, commonVariant_none_iff, not_not]

def rejectedAnchor (first second : List (DensePauli size)) (basis : List (Pauli size)) : Option (Pauli size) :=
  basis.find? fun base => (commonVariant first second base).isNone

theorem rejectedAnchor_some (first second : List (DensePauli size)) (basis : List (Pauli size))
    (anchor : Pauli size) (returned : rejectedAnchor first second basis = some anchor) :
    anchor ∈ basis ∧ ¬ Compatible (generatedPauliGroup first) (generatedPauliGroup second) anchor := by
  refine ⟨List.mem_of_find?_eq_some returned, (commonVariant_none_iff first second anchor).mp ?_⟩
  have rejected := List.find?_some returned
  cases choice : commonVariant first second anchor <;> simp_all

theorem rejectedAnchor_none (first second : List (DensePauli size)) (basis : List (Pauli size))
    (returned : rejectedAnchor first second basis = none) :
    ∀ base ∈ basis, Compatible (generatedPauliGroup first) (generatedPauliGroup second) base := by
  intro base member
  have accepted := List.find?_eq_none.mp returned base member
  apply (commonVariant_isSome_iff first second base).mp
  cases choice : commonVariant first second base <;> simp_all

theorem pairedVariant_exists (first second : List (DensePauli size)) (base anchor : Pauli size)
    (base_row : base.projectiveRow ∈ rowImage (generatedPauliGroup first) ⊓ rowImage (generatedPauliGroup second))
    (anchor_row : anchor.projectiveRow ∈ rowImage (generatedPauliGroup first) ⊓ rowImage (generatedPauliGroup second))
    (base_rejected : commonVariant first second base = none)
    (anchor_rejected : commonVariant first second anchor = none) :
    (commonVariant first second (base * anchor)).isSome = true := by
  apply (commonVariant_isSome_iff first second _).mpr
  apply (compatible_row _ _ _).mpr
  rw [Pauli.projectiveRow_mul]
  apply rejected_rows_add _ _ _ _ base_row anchor_row
  · exact fun member => (commonVariant_none_iff first second base).mp base_rejected
      ((compatible_row _ _ _).mpr member)
  · exact fun member => (commonVariant_none_iff first second anchor).mp anchor_rejected
      ((compatible_row _ _ _).mpr member)

theorem selection_spec (first second : List (DensePauli size)) (basis : List (Pauli size)) :
    (∀ base, (commonVariant first second base).isSome = true ↔
      Compatible (generatedPauliGroup first) (generatedPauliGroup second) base) ∧
    (∀ base candidate, commonVariant first second base = some candidate →
      candidate ∈ generatedPauliGroup first ⊓ generatedPauliGroup second ∧
        candidate.projectiveRow = base.projectiveRow) ∧
    (∀ anchor, rejectedAnchor first second basis = some anchor →
      anchor ∈ basis ∧ ¬ Compatible (generatedPauliGroup first) (generatedPauliGroup second) anchor) ∧
    (rejectedAnchor first second basis = none →
      ∀ base ∈ basis, Compatible (generatedPauliGroup first) (generatedPauliGroup second) base) :=
  ⟨commonVariant_isSome_iff first second, commonVariant_some first second,
    rejectedAnchor_some first second basis, rejectedAnchor_none first second basis⟩

end PaulimerFormal.PauliIntersection
