import PaulimerFormal.ConstructiveSimplex
import PaulimerFormal.GreedySearch
import PaulimerFormal.ResidueFixSearch

/-! Complete ordered bordered-family construction from PR #217. -/

namespace PaulimerFormal.ConstructiveBordered

open Triangularization
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module F2 V]

structure Family (V : Type*) (dimension : ℕ) where
  vectors : Fin (dimension + 1) → V
  relation : Fin (dimension + 1) → F2

def construct (form : LinearMap.BilinForm F2 V) :
    {n : ℕ} → (Fin n → V) → Option (Family V n)
  | 0, _ => some ⟨fun _ => 0, fun _ => 1⟩
  | _n + 1, basis =>
      match GreedySearch.findActive form basis with
      | none => (ConstructiveSimplex.simplex form basis).map fun points => ⟨points, fun _ => 1⟩
      | some pick =>
          (couplingPivot (form pick) basis).bind fun pivot =>
            (construct form (complementVectors (form pick) basis pivot)).map fun family =>
              ⟨Fin.cons pick family.vectors, Fin.cons 0 family.relation⟩

def Valid {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (space : Submodule F2 V) (family : Family V n) : Prop :=
  IsUnitLowerTriangular (fun row column =>
    form (family.vectors row) (family.vectors column) + family.relation row * family.relation column) ∧
    (∑ index, family.relation index • family.vectors index) = 0 ∧
    dotProduct family.relation family.relation = 1 ∧ familySpan family.vectors = space

theorem simplex_valid {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (space : Submodule F2 V)
    (alternating : ∀ vector ∈ space, form vector vector = 0)
    (points : Fin (n + 1) → V) (valid : ConstructiveSimplex.IsSimplex form space points) :
    Valid form space (⟨points, fun _ => 1⟩ : Family V n) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, valid.2.2.1⟩
  · intro row column before
    change form (points row) (points column) + 1 * 1 = 0
    rw [valid.2.2.2 row column before.ne]
    decide
  · intro index
    have member : points index ∈ space := by
      rw [← valid.2.2.1]
      exact member_familySpan points index
    change form (points index) (points index) + 1 * 1 = 1
    simp [alternating _ member]
  · simpa using valid.2.1
  · obtain ⟨half, odd⟩ := valid.1
    change dotProduct (fun _ : Fin (n + 1) => (1 : F2)) (fun _ => 1) = 1
    simp [dotProduct, odd, show (2 : F2) = 0 by decide]

theorem cons_valid {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (space : Submodule F2 V) (pick : V)
    (member : pick ∈ space) (paired : form pick pick = 1)
    (family : Family V n)
    (valid : Valid form (space ⊓ LinearMap.ker (form pick)) family) :
    Valid form space (⟨Fin.cons pick family.vectors, Fin.cons 0 family.relation⟩ : Family V (n + 1)) := by
  have rest_mem (index : Fin (n + 1)) :
      family.vectors index ∈ space ⊓ LinearMap.ker (form pick) := by
    rw [← valid.2.2.2]
    exact member_familySpan family.vectors index
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro row column before
    cases row using Fin.cases with
    | zero =>
      cases column using Fin.cases with
      | zero => simp at before
      | succ column => simpa using (rest_mem column).2
    | succ row =>
      cases column using Fin.cases with
      | zero => simp at before
      | succ column => exact valid.1.1 row column (by simpa using before)
  · intro index
    cases index using Fin.cases with
    | zero => simpa using paired
    | succ index => exact valid.1.2 index
  · simpa [Fin.sum_univ_succ] using valid.2.1
  · simpa [dotProduct, Fin.sum_univ_succ] using valid.2.2.1
  · change familySpan (Fin.cons pick family.vectors) = space
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨index, rfl⟩
      cases index using Fin.cases with
      | zero => exact member
      | succ index => exact (rest_mem index).1
    · have pick_mem := member_familySpan (Fin.cons pick family.vectors) 0
      have rest_le : familySpan family.vectors ≤ familySpan (Fin.cons pick family.vectors) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨index, rfl⟩
        exact member_familySpan (Fin.cons pick family.vectors) index.succ
      intro vector vector_mem
      have projected : vector + form pick vector • pick ∈ familySpan family.vectors := by
        rw [valid.2.2.2]
        refine ⟨space.add_mem vector_mem (space.smul_mem _ member), ?_⟩
        change form pick (vector + form pick vector • pick) = 0
        simp [paired]
      have reconstructed := (familySpan (Fin.cons pick family.vectors)).add_mem (rest_le projected)
        ((familySpan (Fin.cons pick family.vectors)).smul_mem (form pick vector) pick_mem)
      simpa only [Fin.cons_zero, add_assoc, add_self_eq_zero_f2, add_zero] using reconstructed

variable [FiniteDimensional F2 V]

theorem complement_nondegenerate (form : LinearMap.BilinForm F2 V)
    (space : Submodule F2 V) (nondegenerate : (form.restrict space).Nondegenerate)
    (pick : V) (member : pick ∈ space) (paired : form pick pick = 1) :
    (form.restrict (space ⊓ LinearMap.ker (form pick))).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingRight
  intro vector annihilates
  apply Subtype.ext
  have orthogonal : form pick vector.1 = 0 := vector.property.2
  have zero := nondegenerate.2 ⟨vector.1, vector.property.1⟩ (fun test => by
    let projected := test.1 + form pick test.1 • pick
    have projected_mem : projected ∈ space ⊓ LinearMap.ker (form pick) := by
      refine ⟨space.add_mem test.property (space.smul_mem _ member), ?_⟩
      change form pick projected = 0
      simp [projected, paired]
    have evaluated := annihilates ⟨projected, projected_mem⟩
    change form projected vector.1 = 0 at evaluated
    simpa [projected, orthogonal] using evaluated)
  exact congrArg (fun point : space => (point : V)) zero

theorem construct_spec {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (basis : Fin n → V) (independent : LinearIndependent F2 basis)
    (nondegenerate : (form.restrict (familySpan basis)).Nondegenerate) :
    ∃ family, construct form basis = some family ∧ Valid form (familySpan basis) family := by
  induction n with
  | zero =>
    refine ⟨⟨fun _ => 0, fun _ => 1⟩, rfl, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro row column before
      omega
    · intro index
      simp
    · simp
    · simp [dotProduct]
    · simp [familySpan]
  | succ n induction =>
    cases selected : GreedySearch.findActive form basis with
    | none =>
      have alternating := (GreedySearch.findActive_none_iff form basis).mp selected
      obtain ⟨points, returned, valid⟩ :=
        ConstructiveSimplex.simplex_spec form basis independent nondegenerate alternating
      refine ⟨⟨points, fun _ => 1⟩, ?_, simplex_valid form _ alternating points valid⟩
      simp [construct, selected, returned]
    | some pick =>
      have paired := GreedySearch.findActive_some form basis pick selected
      have member := GreedySearch.candidate_mem_span basis pick (List.mem_of_find?_eq_some selected)
      obtain ⟨pivot, found⟩ := couplingPivot_exists (form pick) basis pick member paired
      have complement := complement_spec (form pick) basis pivot independent
        (couplingPivot_spec _ _ _ found)
      have nondegenerate' := complement_nondegenerate form _ nondegenerate pick member paired
      rw [← complement.2.1] at nondegenerate'
      obtain ⟨family, returned, valid⟩ :=
        induction _ complement.1 nondegenerate'
      rw [complement.2.1] at valid
      refine ⟨⟨Fin.cons pick family.vectors, Fin.cons 0 family.relation⟩, ?_,
        cons_valid form _ pick member paired family valid⟩
      simp [construct, selected, found, returned]

def matrixFamily {n : ℕ} (core : Matrix (Fin n) (Fin n) F2) : Option (Family (Fin n → F2) n) :=
  construct core.toBilin' (1 : Matrix (Fin n) (Fin n) F2)

theorem matrixFamily_spec {n : ℕ} (core : Matrix (Fin n) (Fin n) F2) (unit : IsUnit core) :
    ∃ family, matrixFamily core = some family ∧
      IsBorderedTriangularization core family.vectors family.relation := by
  have independent : LinearIndependent F2 (1 : Matrix (Fin n) (Fin n) F2) :=
    Matrix.linearIndependent_rows_iff_isUnit.mpr isUnit_one
  have spans := matrix_familySpan_eq_top _ independent
  have nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' core
    ((Matrix.isUnit_iff_isUnit_det core).mp unit).ne_zero
  have restricted : (core.toBilin'.restrict (familySpan (1 : Matrix (Fin n) (Fin n) F2))).Nondegenerate := by
    rw [spans]
    constructor
    · intro vector annihilates
      apply Subtype.ext
      exact nondegenerate.1 vector.1 (fun test => annihilates ⟨test, Submodule.mem_top⟩)
    · intro vector annihilates
      apply Subtype.ext
      exact nondegenerate.2 vector.1 (fun test => annihilates ⟨test, Submodule.mem_top⟩)
  obtain ⟨family, returned, valid⟩ := construct_spec core.toBilin' _ independent restricted
  rw [spans] at valid
  exact ⟨family, returned, isBorderedTriangularization_of_family core _ _ valid⟩

def decompose {m n : ℕ} (core : Matrix (Fin n) (Fin n) F2)
    (basis : Matrix (Fin n) (PhaseIndex m) F2) : Option (List (PhaseVector m)) :=
  (matrixFamily core).map fun family =>
    ((List.ofFn ((family.vectors : Matrix (Fin (n + 1)) (Fin n) F2) * basis)).map
      ResidueExtraction.storeVector).map ResidueExtraction.readVector

theorem decompose_eq {m n : ℕ} (core : Matrix (Fin n) (Fin n) F2)
    (basis : Matrix (Fin n) (PhaseIndex m) F2) :
    decompose core basis = (matrixFamily core).map
      (fun family => List.ofFn ((family.vectors : Matrix (Fin (n + 1)) (Fin n) F2) * basis)) := by
  unfold decompose
  simp only [List.map_map, Function.comp_def, ResidueExtraction.storeVector_eq]
  congr 1
  funext family
  exact List.map_id _

theorem decompose_spec {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n) (rejected : ¬presentation.IsTriangularizable) :
    ∃ centers, decompose presentation.core presentation.basis = some centers ∧
      TransvectionRefinement.IsShortest target centers ∧
      TransvectionRefinement.checkCandidate (target : ActionMatrix m) n centers = true := by
  obtain ⟨family, returned, valid⟩ := matrixFamily_spec presentation.core presentation.core_unit
  have shortest := TransvectionRefinement.bordered_family_spec presentation rejected
    family.vectors family.relation valid
  refine ⟨_, ?_, shortest, ?_⟩
  · simp [decompose_eq, returned]
  · apply (TransvectionRefinement.checkCandidate_iff target n _).mpr
    exact ⟨List.length_ofFn, ResidueFixSearch.shortest_nonzero shortest, shortest.1⟩

def candidate {m : ℕ} (action : ActionMatrix m) : Option (List (PhaseVector m)) :=
  decompose (ResidueExtraction.core action) (ResidueExtraction.basis action)

theorem candidate_spec {m : ℕ} (target : SymplecticAction m)
    (rejected : ResidueExtraction.rankDecomposition (target : ActionMatrix m) = none) :
    ∃ centers, candidate (target : ActionMatrix m) = some centers ∧
      TransvectionRefinement.checkCandidate (target : ActionMatrix m)
        (ResidueExtraction.rank (target : ActionMatrix m)) centers = true ∧
      TransvectionRefinement.IsShortest target centers ∧
      ResidueFixSearch.checkedDecomposition target (candidate (target : ActionMatrix m)) = centers := by
  obtain ⟨presentation, basis_eq, core_eq⟩ := ResidueExtraction.core_spec target
  have not_triangular := (ResidueExtraction.rankDecomposition_none_iff target).mp rejected
  rw [← presentation.isTriangularizable_iff_canonical] at not_triangular
  obtain ⟨centers, returned, shortest, accepted⟩ := decompose_spec presentation not_triangular
  rw [basis_eq, core_eq] at returned
  refine ⟨centers, returned, accepted, shortest, ?_⟩
  change candidate (target : ActionMatrix m) = some centers at returned
  unfold ResidueFixSearch.checkedDecomposition
  split
  · rename_i result branch
    rw [rejected] at branch
    contradiction
  · rw [returned]
    simp only [Option.filter_some, accepted, ite_true]

end PaulimerFormal.ConstructiveBordered
