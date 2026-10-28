import PaulimerFormal.GreedyBlocks
import Mathlib.Data.List.OfFn

/-! Componentwise semantics and ordered selection for disjoint witness blocks. -/

namespace PaulimerFormal.GreedyBlocks

open GreedyReduction GreedySearch

def component (count : ℕ) (block : Fin count) (vector : PhaseVector (count * 3)) : PhaseVector 3 :=
  fun coordinate => vector (indices count (coordinate, block))

theorem component_mulVec (count : ℕ) (family : Fin count → ActionMatrix 3)
    (block : Fin count) (vector : PhaseVector (count * 3)) :
    component count block ((matrices count family).mulVec vector) =
      (family block).mulVec (component count block vector) := by
  funext coordinate
  change (∑ column, matrices count family (indices count (coordinate, block)) column * vector column) = _
  rw [← (indices count).sum_comp]
  simp only [← Finset.univ_product_univ, Finset.sum_product, matrices_apply]
  simp [ite_mul, component, Matrix.mulVec, dotProduct]

theorem component_rowAction (count : ℕ) (family : Fin count → ActionMatrix 3)
    (block : Fin count) (vector : PhaseVector (count * 3)) :
    component count block (rowAction vector (matrices count family)) =
      rowAction (component count block vector) (family block) := by
  rw [rowAction, ← Matrix.mulVec_transpose, ← matrices_transpose, component_mulVec]
  rw [Matrix.mulVec_transpose]
  rfl

theorem pairing_components (count : ℕ) (left right : PhaseVector (count * 3)) :
    pairing left right =
      ∑ block : Fin count, pairing (component count block left) (component count block right) := by
  unfold pairing
  rw [← matrices_omega count]
  change (∑ coordinate, left coordinate * (matrices count (fun _ => omega 3)).mulVec right coordinate) = _
  rw [← (indices count).sum_comp]
  simp only [← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro block _
  change (∑ coordinate, component count block left coordinate *
    component count block ((matrices count (fun _ => omega 3)).mulVec right) coordinate) = _
  rw [component_mulVec]
  rfl

theorem hyperbolic_assembly (count : ℕ) (family : Fin count → ActionMatrix 3)
    (hyperbolic : ∀ block, IsHyperbolic (family block)) :
    IsHyperbolic (matrices count family) := by
  intro vector
  rw [pairing_components]
  apply Finset.sum_eq_zero
  intro block _
  rw [component_rowAction]
  exact hyperbolic block (component count block vector)

theorem embed_single (count : ℕ) (block : Fin count) (coordinate : PhaseIndex 3) :
    embed count block (Pi.single coordinate 1) = Pi.single (indices count (coordinate, block)) 1 := by
  funext index
  obtain ⟨⟨other_coordinate, other_block⟩, rfl⟩ := (indices count).surjective index
  rw [embed_apply]
  by_cases same_block : other_block = block <;> by_cases same_coordinate : other_coordinate = coordinate <;>
    simp_all [eq_comm]

def localAction (stage : Fin 5) : SymplecticAction 3 :=
  ![GreedyCounterexample.initial, GreedyCounterexample.second,
    GreedyCounterexample.third, GreedyCounterexample.fourth, 1] stage

def advance (stage : Fin 5) : Fin 5 := ![1, 2, 3, 4, 4] stage

def localChoice (stage : Fin 5) : Fin 3 := ![0, 1, 2, 1, 0] stage

def activeStage (stage : Fin 5) : Bool := decide (stage ≠ 1 ∧ stage ≠ 4)

def xBasis : List (PhaseVector 3) :=
  List.ofFn fun index : Fin 3 => Pi.single (Sum.inl index) 1

def zBasis : List (PhaseVector 3) :=
  List.ofFn fun index : Fin 3 => Pi.single (Sum.inr index) 1

def assembledBasis (count : ℕ) (basis : List (PhaseVector 3)) : List (PhaseVector (count * 3)) :=
  (List.ofFn fun block : Fin count => basis.map (embed count block)).flatten

theorem standard_basis_blocks (count : ℕ) :
    List.ofFn (standardBasis (count * 3)) =
      assembledBasis count xBasis ++ assembledBasis count zBasis := by
  rw [List.ofFn_add]
  change List.ofFn (fun index : Fin (count * 3) => standardBasis (count * 3)
      (Fin.castAdd (count * 3) index)) ++
    List.ofFn (fun index : Fin (count * 3) => standardBasis (count * 3)
      (Fin.natAdd (count * 3) index)) = _
  simp only [standardBasis, ← BinarBridge.phaseIndexEquiv_inl,
    ← BinarBridge.phaseIndexEquiv_inr, Equiv.symm_apply_apply]
  unfold assembledBasis
  congr 1 <;> rw [List.ofFn_mul]
  all_goals
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext block
    simp only [xBasis, zBasis, List.map_ofFn]
    apply congrArg List.ofFn
    funext coordinate
    simp only [Function.comp_apply, embed_single]
    simp [indices, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

theorem local_active_selection (stage : Fin 5) :
    (xBasis.find? fun vector => decide
      (pairing vector (rowAction vector (localAction stage : ActionMatrix 3)) = 1)) =
        if activeStage stage then some (Pi.single (Sum.inl (localChoice stage)) 1) else none := by
  fin_cases stage <;> decide +kernel

theorem local_inactive_hyperbolic (stage : Fin 5) (inactive : activeStage stage = false) :
    IsHyperbolic (localAction stage : ActionMatrix 3) := by
  rw [← findActive_standard_none_iff]
  fin_cases stage <;> simp [activeStage] at inactive <;> decide +kernel

theorem local_inactive_moved (stage : Fin 5) (inactive : activeStage stage = false) :
    (xBasis.find? fun vector => decide
      (residueVector (localAction stage : ActionMatrix 3) vector ≠ 0)) =
        if stage = 4 then none else some (Pi.single (Sum.inl (localChoice stage)) 1) := by
  fin_cases stage <;> simp [activeStage] at inactive <;> decide +kernel

theorem local_step (stage : Fin 5) (unfinished : stage ≠ 4) :
    localAction stage *
      transvectionAction (residueVector (localAction stage : ActionMatrix 3)
        (Pi.single (Sum.inl (localChoice stage)) 1)) = localAction (advance stage) := by
  fin_cases stage <;> simp at unfinished
  all_goals apply Subtype.ext; decide +kernel

theorem embed_zero (count : ℕ) (block : Fin count) : embed count block 0 = 0 := by
  funext index
  simp [embed]

theorem embed_add (count : ℕ) (block : Fin count) (left right : PhaseVector 3) :
    embed count block (left + right) = embed count block left + embed count block right := by
  funext index
  simp only [embed, Pi.add_apply]
  split_ifs <;> simp

theorem component_embed_same (count : ℕ) (block : Fin count) (vector : PhaseVector 3) :
    component count block (embed count block vector) = vector := by
  funext coordinate
  simp [component, embed_apply]

theorem embed_injective (count : ℕ) (block : Fin count) : Function.Injective (embed count block) := by
  intro left right same
  have components := congrArg (component count block) same
  simpa only [component_embed_same] using components

theorem rowAction_embed (count : ℕ) (family : Fin count → ActionMatrix 3)
    (block : Fin count) (vector : PhaseVector 3) :
    rowAction (embed count block vector) (matrices count family) =
      embed count block (rowAction vector (family block)) := by
  rw [rowAction, ← Matrix.mulVec_transpose, ← matrices_transpose, matrices_mulVec_embed,
    Matrix.mulVec_transpose]
  rfl

theorem residueVector_embed (count : ℕ) (family : Fin count → ActionMatrix 3)
    (block : Fin count) (vector : PhaseVector 3) :
    residueVector (matrices count family) (embed count block vector) =
      embed count block (residueVector (family block) vector) := by
  rw [residueVector, rowAction_embed, ← embed_add]
  rfl

theorem pairing_embed_same (count : ℕ) (block : Fin count) (left right : PhaseVector 3) :
    pairing (embed count block left) (embed count block right) = pairing left right := by
  rw [pairing, omega_mulVec_embed]
  change (∑ index, embed count block left index * embed count block ((omega 3).mulVec right) index) = _
  rw [← (indices count).sum_comp]
  simp only [← Finset.univ_product_univ, Finset.sum_product, embed_apply]
  simp [pairing, dotProduct]

private theorem assembled_find (count : ℕ) (basis : List (PhaseVector 3))
    (predicate : PhaseVector (count * 3) → Bool) :
    (assembledBasis count basis).find? predicate =
      (List.ofFn (id : Fin count → Fin count)).findSome? fun block =>
        (basis.find? fun vector => predicate (embed count block vector)).map (embed count block) := by
  have expanded :
      List.ofFn (fun block : Fin count => basis.map (embed count block)) =
        (List.ofFn (id : Fin count → Fin count)).map fun block => basis.map (embed count block) :=
    List.ofFn_comp' (id : Fin count → Fin count)
      (fun block : Fin count => basis.map (embed count block))
  rw [assembledBasis, List.find?_flatten, expanded, List.findSome?_map]
  simp only [Function.comp_def, List.find?_map]

private theorem findSome_guard_map {α β : Type*} (values : List α) (predicate : α → Bool) (mapping : α → β) :
    (values.findSome? fun value => if predicate value then some (mapping value) else none) =
      (values.find? predicate).map mapping := by
  rw [List.find?_eq_findSome?_guard, List.map_findSome?]
  congr 1
  funext value
  cases result : predicate value <;> simp [Option.guard, result]

def stateAction (count : ℕ) (stages : Fin count → Fin 5) : SymplecticAction (count * 3) :=
  actions count (fun block => localAction (stages block))

def selectedVector (count : ℕ) (stages : Fin count → Fin 5) (block : Fin count) : PhaseVector (count * 3) :=
  embed count block (Pi.single (Sum.inl (localChoice (stages block))) 1)

def activeBlock (count : ℕ) (stages : Fin count → Fin 5) : Option (Fin count) :=
  (List.ofFn id).find? fun block => activeStage (stages block)

def unfinishedBlock (count : ℕ) (stages : Fin count → Fin 5) : Option (Fin count) :=
  (List.ofFn id).find? fun block => decide (stages block ≠ 4)

theorem assembled_active_selection (count : ℕ) (stages : Fin count → Fin 5) :
    ((assembledBasis count xBasis).find? fun vector =>
      decide (imageForm (stateAction count stages : ActionMatrix (count * 3)) vector vector = 1)) =
        (activeBlock count stages).map (selectedVector count stages) := by
  rw [assembled_find]
  change (List.ofFn id).findSome? (fun block =>
    (xBasis.find? fun vector => decide (imageForm
      (matrices count (fun block => (localAction (stages block) : ActionMatrix 3)))
        (embed count block vector) (embed count block vector) = 1)).map (embed count block)) = _
  simp only [imageForm_apply, rowAction_embed, pairing_embed_same, local_active_selection]
  have mapped (block : Fin count) :
      (if activeStage (stages block)
        then some (Pi.single (Sum.inl (localChoice (stages block))) 1) else none).map (embed count block) =
      if activeStage (stages block) then some (selectedVector count stages block) else none := by
    cases activeStage (stages block) <;> rfl
  simp only [mapped]
  exact findSome_guard_map _ _ _

theorem assembled_inactive_moved (count : ℕ) (stages : Fin count → Fin 5)
    (inactive : ∀ block, activeStage (stages block) = false) :
    ((assembledBasis count xBasis).find? fun vector =>
      decide (residueVector (stateAction count stages : ActionMatrix (count * 3)) vector ≠ 0)) =
        (unfinishedBlock count stages).map (selectedVector count stages) := by
  rw [assembled_find]
  have test (block : Fin count) (vector : PhaseVector 3) :
      decide (residueVector (stateAction count stages : ActionMatrix (count * 3))
        (embed count block vector) ≠ 0) =
      decide (residueVector (localAction (stages block) : ActionMatrix 3) vector ≠ 0) := by
    change decide (residueVector (matrices count
      (fun block => (localAction (stages block) : ActionMatrix 3))) (embed count block vector) ≠ 0) = _
    simp only [ne_eq, residueVector_embed, ← embed_zero count block,
      (embed_injective count block).eq_iff]
  simp only [test]
  simp_rw [local_inactive_moved _ (inactive _)]
  have mapped (block : Fin count) :
      (if stages block = 4 then none
        else some (Pi.single (Sum.inl (localChoice (stages block))) 1)).map (embed count block) =
      if decide (stages block ≠ 4) then some (selectedVector count stages block) else none := by
    by_cases finished : stages block = 4 <;> simp [finished, selectedVector]
  simp only [mapped]
  exact findSome_guard_map _ _ _

theorem activeBlock_some (count : ℕ) (stages : Fin count → Fin 5) (block : Fin count)
    (returned : activeBlock count stages = some block) : stages block ≠ 4 := by
  have accepted := List.find?_some (p := fun block => activeStage (stages block)) returned
  simp only [activeStage, decide_eq_true_eq] at accepted
  exact accepted.2

theorem activeBlock_none (count : ℕ) (stages : Fin count → Fin 5)
    (returned : activeBlock count stages = none) : ∀ block, activeStage (stages block) = false := by
  intro block
  simpa using List.find?_eq_none.mp returned block (by simp)

theorem unfinishedBlock_some (count : ℕ) (stages : Fin count → Fin 5) (block : Fin count)
    (returned : unfinishedBlock count stages = some block) : stages block ≠ 4 := by
  exact of_decide_eq_true (List.find?_some (p := fun block => decide (stages block ≠ 4)) returned)

theorem unfinishedBlock_none (count : ℕ) (stages : Fin count → Fin 5)
    (returned : unfinishedBlock count stages = none) : ∀ block, stages block = 4 := by
  intro block
  have rejected := List.find?_eq_none.mp returned block (by simp)
  simpa using rejected

theorem stateAction_finished (count : ℕ) (stages : Fin count → Fin 5)
    (finished : ∀ block, stages block = 4) : stateAction count stages = 1 := by
  have family : (fun block => localAction (stages block)) = (1 : Fin count → SymplecticAction 3) := by
    funext block
    rw [finished]
    rfl
  rw [stateAction, family, map_one]

theorem nextVector_active (count : ℕ) (stages : Fin count → Fin 5) (block : Fin count)
    (returned : activeBlock count stages = some block) :
    nextVector (stateAction count stages : ActionMatrix (count * 3)) =
      some (selectedVector count stages block) := by
  have singles := assembled_active_selection count stages
  rw [returned, Option.map_some] at singles
  simp [nextVector, findActive, activeCandidates, standard_basis_blocks, List.find?_append, singles]

theorem nextVector_inactive (count : ℕ) (stages : Fin count → Fin 5) (block : Fin count)
    (inactive : ∀ block, activeStage (stages block) = false)
    (returned : unfinishedBlock count stages = some block) :
    nextVector (stateAction count stages : ActionMatrix (count * 3)) =
      some (selectedVector count stages block) := by
  have hyperbolic : IsHyperbolic (stateAction count stages : ActionMatrix (count * 3)) :=
    hyperbolic_assembly count (fun block => (localAction (stages block) : ActionMatrix 3))
      (fun block => local_inactive_hyperbolic (stages block) (inactive block))
  have rejected := (findActive_standard_none_iff _).mpr hyperbolic
  have singles := assembled_inactive_moved count stages inactive
  rw [returned, Option.map_some] at singles
  rw [nextVector, rejected]
  change findMoved (stateAction count stages : ActionMatrix (count * 3)) = _
  rw [findMoved, standard_basis_blocks, List.find?_append, singles]
  rfl

theorem block_selection_spec (count : ℕ) (stages : Fin count → Fin 5) :
    (nextVector (stateAction count stages : ActionMatrix (count * 3)) = none ∧
      ∀ block, stages block = 4) ∨
    ∃ block, stages block ≠ 4 ∧
      nextVector (stateAction count stages : ActionMatrix (count * 3)) =
        some (selectedVector count stages block) := by
  cases active : activeBlock count stages with
  | some block =>
      exact Or.inr ⟨block, activeBlock_some count stages block active,
        nextVector_active count stages block active⟩
  | none =>
      have inactive := activeBlock_none count stages active
      cases unfinished : unfinishedBlock count stages with
      | some block =>
          exact Or.inr ⟨block, unfinishedBlock_some count stages block unfinished,
            nextVector_inactive count stages block inactive unfinished⟩
      | none =>
          have finished := unfinishedBlock_none count stages unfinished
          refine Or.inl ⟨?_, finished⟩
          apply (nextVector_none_iff _).mpr
          exact congrArg Subtype.val (stateAction_finished count stages finished)

end PaulimerFormal.GreedyBlocks
