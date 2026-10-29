import PaulimerFormal.TriangularSearch

/-! Ordered symplectic-simplex construction from PR #217. -/

namespace PaulimerFormal.ConstructiveSimplex

open Triangularization
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module F2 V]

def pairComplement {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin (n + 2) → V) (partner : Fin (n + 1)) : Fin n → V :=
  fun index =>
    let vector := basis (partner.succAbove index).succ
    vector + form (basis partner.succ) vector • basis 0 +
      form (basis 0) vector • basis partner.succ

def simplex (form : LinearMap.BilinForm F2 V) :
    {n : ℕ} → (Fin n → V) → Option (Fin (n + 1) → V)
  | 0, _ => some fun _ => 0
  | 1, _ => none
  | _n + 2, basis =>
      (couplingPivot (form (basis 0)) (Fin.tail basis)).bind fun partner =>
        (simplex form (pairComplement form basis partner)).map fun points =>
          Fin.cons (basis partner.succ)
            (Fin.cons (basis 0 + basis partner.succ) (fun index => points index + basis 0))

def IsSimplex {k : ℕ} (form : LinearMap.BilinForm F2 V)
    (space : Submodule F2 V) (points : Fin k → V) : Prop :=
  Odd k ∧ (∑ index, points index) = 0 ∧ familySpan points = space ∧
    ∀ first second, first ≠ second → form (points first) (points second) = 1

theorem pairComplement_eq {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin (n + 2) → V) (partner : Fin (n + 1))
    (first_zero : form (basis 0) (basis 0) = 0)
    (second_zero : form (basis partner.succ) (basis partner.succ) = 0) :
    pairComplement form basis partner =
      complementVectors (form (basis partner.succ))
        (complementVectors (form (basis 0)) basis partner.succ) 0 := by
  funext index
  simp [pairComplement, complementVectors, first_zero, second_zero,
    add_assoc, add_comm, add_left_comm]

theorem pairComplement_spec {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin (n + 2) → V) (partner : Fin (n + 1))
    (independent : LinearIndependent F2 basis)
    (alternating : ∀ vector ∈ familySpan basis, form vector vector = 0)
    (paired : form (basis 0) (basis partner.succ) = 1) :
    LinearIndependent F2 (pairComplement form basis partner) ∧
      familySpan (pairComplement form basis partner) =
        familySpan basis ⊓ LinearMap.ker (form (basis 0)) ⊓
          LinearMap.ker (form (basis partner.succ)) := by
  have first_zero := alternating _ (member_familySpan basis 0)
  have second_zero := alternating _ (member_familySpan basis partner.succ)
  have reverse : form (basis partner.succ) (basis 0) = 1 := by
    have sum_zero := alternating _ ((familySpan basis).add_mem
      (member_familySpan basis 0) (member_familySpan basis partner.succ))
    have cross : 1 + form (basis partner.succ) (basis 0) = 0 := by
      simpa [first_zero, second_zero, paired] using sum_zero
    simpa using eq_neg_of_add_eq_zero_right cross
  rw [pairComplement_eq form basis partner first_zero second_zero]
  refine ⟨complement_independent _ _ _ (complement_independent _ _ _ independent), ?_⟩
  rw [complement_span, complement_span _ _ _ paired]
  simpa [complementVectors, first_zero] using reverse

theorem symmetry (form : LinearMap.BilinForm F2 V) (space : Submodule F2 V)
    (alternating : ∀ vector ∈ space, form vector vector = 0)
    {first second : V} (first_mem : first ∈ space) (second_mem : second ∈ space) :
    form first second = form second first := by
  have restricted : (form.restrict space).IsAlt := fun vector => alternating _ vector.property
  exact (LinearMap.BilinForm.IsAlt.isSymm_f2 restricted).eq
    ⟨first, first_mem⟩ ⟨second, second_mem⟩

theorem partner_exists {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin (n + 1) → V) (independent : LinearIndependent F2 basis)
    (nondegenerate : (form.restrict (familySpan basis)).Nondegenerate)
    (alternating : ∀ vector ∈ familySpan basis, form vector vector = 0) :
    ∃ partner, couplingPivot (form (basis 0)) (Fin.tail basis) = some partner := by
  cases found : couplingPivot (form (basis 0)) (Fin.tail basis) with
  | some partner => exact ⟨partner, rfl⟩
  | none =>
    have tail_zero (index : Fin n) : form (basis 0) (basis index.succ) = 0 := by
      have failed := List.find?_eq_none.mp found index (by simp)
      by_contra nonzero
      simp [Fin.tail, f2_eq_one_of_ne_zero _ nonzero] at failed
    have contained : familySpan basis ≤ LinearMap.ker (form (basis 0)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨index, rfl⟩
      cases index using Fin.cases with
      | zero => exact alternating _ (member_familySpan basis 0)
      | succ index => exact tail_zero index
    have zero := nondegenerate.1 ⟨basis 0, member_familySpan basis 0⟩
      (fun vector => contained vector.property)
    exact (independent.ne_zero 0 (congrArg Subtype.val zero)).elim

theorem extend_spec {n k : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin (n + 2) → V) (partner : Fin (n + 1))
    (independent : LinearIndependent F2 basis)
    (alternating : ∀ vector ∈ familySpan basis, form vector vector = 0)
    (paired : form (basis 0) (basis partner.succ) = 1)
    (points : Fin k → V)
    (valid : IsSimplex form (familySpan (pairComplement form basis partner)) points) :
    IsSimplex form (familySpan basis)
      (Fin.cons (basis partner.succ)
        (Fin.cons (basis 0 + basis partner.succ) (fun index => points index + basis 0))) := by
  let first := basis 0
  let second := basis partner.succ
  let result : Fin (k + 2) → V :=
    Fin.cons second (Fin.cons (first + second) (fun index => points index + first))
  have first_mem := member_familySpan basis 0
  have second_mem := member_familySpan basis partner.succ
  have first_zero : form first first = 0 := alternating _ first_mem
  have second_zero : form second second = 0 := alternating _ second_mem
  have reverse : form second first = 1 :=
    (symmetry form _ alternating second_mem first_mem).trans paired
  have spans := (pairComplement_spec form basis partner independent alternating paired).2
  have point_mem (index : Fin k) :
      points index ∈ familySpan basis ⊓ LinearMap.ker (form first) ⊓ LinearMap.ker (form second) := by
    rw [← spans, ← valid.2.2.1]
    exact member_familySpan points index
  have point_first (index : Fin k) : form (points index) first = 0 :=
    (symmetry form _ alternating (point_mem index).1.1 first_mem).trans (point_mem index).1.2
  have point_second (index : Fin k) : form (points index) second = 0 :=
    (symmetry form _ alternating (point_mem index).1.1 second_mem).trans (point_mem index).2
  have first_point (index : Fin k) : form first (points index) = 0 := (point_mem index).1.2
  have second_point (index : Fin k) : form second (points index) = 0 := (point_mem index).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨half, odd⟩ := valid.1
    exact ⟨half + 1, by omega⟩
  · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.sum_add_distrib,
      valid.2.1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, zero_add]
    rw [nsmul_eq_self_of_odd_f2 _ valid.1]
    simp only [add_assoc, add_left_comm, add_self_eq_zero_f2, add_zero]
  · change familySpan result = familySpan basis
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨index, rfl⟩
      cases index using Fin.cases with
      | zero => exact second_mem
      | succ index =>
        cases index using Fin.cases with
        | zero => exact (familySpan basis).add_mem first_mem second_mem
        | succ index => exact (familySpan basis).add_mem (point_mem index).1.1 first_mem
    · have second_in : second ∈ familySpan result := member_familySpan result 0
      have sum_in : first + second ∈ familySpan result := member_familySpan result (Fin.succ 0)
      have first_in : first ∈ familySpan result := by
        simpa [add_assoc, add_self_eq_zero_f2] using (familySpan result).add_mem sum_in second_in
      have old_le : familySpan points ≤ familySpan result := by
        apply Submodule.span_le.mpr
        rintro _ ⟨index, rfl⟩
        have shifted : points index + first ∈ familySpan result :=
          member_familySpan result index.succ.succ
        simpa [add_assoc, add_self_eq_zero_f2] using (familySpan result).add_mem shifted first_in
      rw [valid.2.2.1, spans] at old_le
      intro vector member
      let projected := vector + form second vector • first + form first vector • second
      have projected_in : projected ∈ familySpan basis ⊓ LinearMap.ker (form first) ⊓
          LinearMap.ker (form second) := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact (familySpan basis).add_mem
            ((familySpan basis).add_mem member ((familySpan basis).smul_mem _ first_mem))
            ((familySpan basis).smul_mem _ second_mem)
        · change form first projected = 0
          simp [projected, first_zero, show form first second = 1 from paired]
        · change form second projected = 0
          simp [projected, second_zero, reverse, add_assoc]
      have reconstructed := (familySpan result).add_mem
        ((familySpan result).add_mem (old_le projected_in)
          ((familySpan result).smul_mem (form first vector) second_in))
        ((familySpan result).smul_mem (form second vector) first_in)
      simpa only [projected, add_assoc, add_self_eq_zero_f2, add_zero] using reconstructed
  · intro left right distinct
    dsimp only [first, second] at first_zero second_zero reverse
    dsimp only [first, second] at point_first point_second first_point second_point
    cases left using Fin.cases with
    | zero =>
      cases right using Fin.cases with
      | zero => exact (distinct rfl).elim
      | succ right =>
        cases right using Fin.cases with
        | zero => simp [reverse, second_zero]
        | succ right => simp [second_point, reverse]
    | succ left =>
      cases left using Fin.cases with
      | zero =>
        cases right using Fin.cases with
        | zero => simp [paired, second_zero]
        | succ right =>
          cases right using Fin.cases with
          | zero => exact (distinct rfl).elim
          | succ right => simp [first_point, second_point, first_zero, reverse]
      | succ left =>
        cases right using Fin.cases with
        | zero => simp [point_second, paired]
        | succ right =>
          cases right using Fin.cases with
          | zero => simp [point_first, point_second, first_zero, paired]
          | succ right =>
            have unequal : left ≠ right := fun equal => distinct (by rw [equal])
            simpa [point_first, first_point, first_zero] using valid.2.2.2 left right unequal

variable [FiniteDimensional F2 V]

theorem pairComplement_nondegenerate {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin (n + 2) → V) (partner : Fin (n + 1))
    (independent : LinearIndependent F2 basis)
    (nondegenerate : (form.restrict (familySpan basis)).Nondegenerate)
    (alternating : ∀ vector ∈ familySpan basis, form vector vector = 0)
    (paired : form (basis 0) (basis partner.succ) = 1) :
    (form.restrict (familySpan (pairComplement form basis partner))).Nondegenerate := by
  rw [(pairComplement_spec form basis partner independent alternating paired).2]
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro vector annihilates
  apply Subtype.ext
  have first_mem := member_familySpan basis 0
  have second_mem := member_familySpan basis partner.succ
  have first_zero := alternating _ first_mem
  have second_zero := alternating _ second_mem
  have reverse : form (basis partner.succ) (basis 0) = 1 :=
    (symmetry form _ alternating second_mem first_mem).trans paired
  have vector_first : form vector.1 (basis 0) = 0 :=
    (symmetry form _ alternating vector.property.1.1 first_mem).trans vector.property.1.2
  have vector_second : form vector.1 (basis partner.succ) = 0 :=
    (symmetry form _ alternating vector.property.1.1 second_mem).trans vector.property.2
  have zero := nondegenerate.1 ⟨vector.1, vector.property.1.1⟩ (fun test => by
    let projected := test.1 + form (basis partner.succ) test.1 • basis 0 +
      form (basis 0) test.1 • basis partner.succ
    have member : projected ∈ familySpan basis ⊓ LinearMap.ker (form (basis 0)) ⊓
        LinearMap.ker (form (basis partner.succ)) := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact (familySpan basis).add_mem
          ((familySpan basis).add_mem test.property ((familySpan basis).smul_mem _ first_mem))
          ((familySpan basis).smul_mem _ second_mem)
      · change form (basis 0) projected = 0
        simp [projected, first_zero, paired]
      · change form (basis partner.succ) projected = 0
        simp [projected, second_zero, reverse, add_assoc]
    have evaluated := annihilates ⟨projected, member⟩
    change form vector.1 projected = 0 at evaluated
    simpa [projected, vector_first, vector_second] using evaluated)
  exact congrArg (fun point : familySpan basis => (point : V)) zero

theorem simplex_spec {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin n → V) (independent : LinearIndependent F2 basis)
    (nondegenerate : (form.restrict (familySpan basis)).Nondegenerate)
    (alternating : ∀ vector ∈ familySpan basis, form vector vector = 0) :
    ∃ points, simplex form basis = some points ∧ IsSimplex form (familySpan basis) points := by
  induction n using Nat.twoStepInduction with
  | zero =>
    refine ⟨fun _ => 0, rfl, by decide, by simp, ?_, ?_⟩
    · simp [familySpan]
    · intro first second distinct
      exact (distinct (Fin.ext (by omega))).elim
  | one =>
    obtain ⟨partner, _⟩ := partner_exists form basis independent nondegenerate alternating
    exact Fin.elim0 partner
  | more n induction _ =>
    obtain ⟨partner, found⟩ := partner_exists form basis independent nondegenerate alternating
    have paired : form (basis 0) (basis partner.succ) = 1 :=
      couplingPivot_spec (form (basis 0)) (Fin.tail basis) partner found
    have complement := pairComplement_spec form basis partner independent alternating paired
    have nondegenerate' :=
      pairComplement_nondegenerate form basis partner independent nondegenerate alternating paired
    have alternating' : ∀ vector ∈ familySpan (pairComplement form basis partner),
        form vector vector = 0 := by
      intro vector member
      rw [complement.2] at member
      exact alternating vector member.1.1
    obtain ⟨points, returned, valid⟩ :=
      induction (pairComplement form basis partner) complement.1 nondegenerate' alternating'
    refine ⟨_, ?_, extend_spec form basis partner independent alternating paired points valid⟩
    simp only [simplex, found, Option.bind_some, returned, Option.map_some]

end PaulimerFormal.ConstructiveSimplex
