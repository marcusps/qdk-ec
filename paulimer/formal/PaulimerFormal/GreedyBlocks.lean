import PaulimerFormal.GreedyCounterexample
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Symplectic block assembly in Paulimer's X-then-Z coordinate order. -/

namespace PaulimerFormal.GreedyBlocks

def indices (count : ℕ) : PhaseIndex 3 × Fin count ≃ PhaseIndex (count * 3) :=
  (Equiv.sumProdDistrib (Fin 3) (Fin 3) (Fin count)).trans
    (Equiv.sumCongr
      ((Equiv.prodComm (Fin 3) (Fin count)).trans finProdFinEquiv)
      ((Equiv.prodComm (Fin 3) (Fin count)).trans finProdFinEquiv))

def matrices (count : ℕ) : (Fin count → ActionMatrix 3) →+* ActionMatrix (count * 3) :=
  (Matrix.reindexAlgEquiv F2 F2 (indices count)).toRingHom.comp
    (Matrix.blockDiagonalRingHom (PhaseIndex 3) (Fin count) F2)

theorem matrices_apply (count : ℕ) (family : Fin count → ActionMatrix 3)
    (row column : PhaseIndex 3) (first second : Fin count) :
    matrices count family (indices count (row, first)) (indices count (column, second)) =
      if first = second then family first row column else 0 := by
  change Matrix.blockDiagonal family
    ((indices count).symm (indices count (row, first)))
    ((indices count).symm (indices count (column, second))) = _
  simp [Matrix.blockDiagonal_apply]

theorem matrices_transpose (count : ℕ) (family : Fin count → ActionMatrix 3) :
    matrices count (fun block => (family block).transpose) = (matrices count family).transpose := by
  ext row column
  obtain ⟨⟨local_row, first⟩, rfl⟩ := (indices count).surjective row
  obtain ⟨⟨local_column, second⟩, rfl⟩ := (indices count).surjective column
  simp only [Matrix.transpose_apply, matrices_apply]
  by_cases same : first = second <;> simp_all [eq_comm]

theorem matrices_omega (count : ℕ) :
    matrices count (fun _ => omega 3) = omega (count * 3) := by
  ext row column
  obtain ⟨⟨local_row, first⟩, rfl⟩ := (indices count).surjective row
  obtain ⟨⟨local_column, second⟩, rfl⟩ := (indices count).surjective column
  rw [matrices_apply]
  rcases local_row with row | row <;> rcases local_column with column | column <;>
    by_cases same_block : first = second <;> by_cases same_coordinate : row = column <;>
    simp [indices, omega, Matrix.J, Matrix.fromBlocks,
      same_block, same_coordinate]

theorem matrices_symplectic (count : ℕ) (family : Fin count → SymplecticAction 3) :
    IsSymplectic (matrices count (fun block => (family block : ActionMatrix 3))) := by
  rw [IsSymplectic, SymplecticGroup.mem_iff]
  change matrices count (fun block => (family block : ActionMatrix 3)) * omega (count * 3) *
      (matrices count (fun block => (family block : ActionMatrix 3))).transpose = omega (count * 3)
  rw [← matrices_omega, ← matrices_transpose, ← map_mul, ← map_mul]
  apply congrArg (matrices count)
  funext block
  exact SymplecticGroup.mem_iff.mp (family block).property

def actions (count : ℕ) : (Fin count → SymplecticAction 3) →* SymplecticAction (count * 3) where
  toFun family := ⟨matrices count (fun block => (family block : ActionMatrix 3)),
    matrices_symplectic count family⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (matrices count)
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul (matrices count)
      (fun block => (first block : ActionMatrix 3)) (fun block => (second block : ActionMatrix 3))

def repeated (count : ℕ) : SymplecticAction (count * 3) :=
  actions count (fun _ => GreedyCounterexample.initial)

def embed (count : ℕ) (block : Fin count) (vector : PhaseVector 3) : PhaseVector (count * 3) :=
  fun index =>
    let position := (indices count).symm index
    if position.2 = block then vector position.1 else 0

theorem embed_apply (count : ℕ) (block : Fin count) (vector : PhaseVector 3)
    (coordinate : PhaseIndex 3) (other : Fin count) :
    embed count block vector (indices count (coordinate, other)) =
      if other = block then vector coordinate else 0 := by
  simp [embed]

theorem matrices_mulVec_embed (count : ℕ) (family : Fin count → ActionMatrix 3)
    (block : Fin count) (vector : PhaseVector 3) :
    (matrices count family).mulVec (embed count block vector) =
      embed count block ((family block).mulVec vector) := by
  funext index
  obtain ⟨⟨coordinate, other⟩, rfl⟩ := (indices count).surjective index
  change (∑ column, matrices count family (indices count (coordinate, other)) column *
    embed count block vector column) = _
  rw [← (indices count).sum_comp]
  simp only [← Finset.univ_product_univ, Finset.sum_product, matrices_apply, embed_apply]
  by_cases same : other = block
  · subst other
    simp [Matrix.mulVec, dotProduct]
  · simp [same, mul_ite]

theorem omega_mulVec_embed (count : ℕ) (block : Fin count) (vector : PhaseVector 3) :
    (omega (count * 3)).mulVec (embed count block vector) =
      embed count block ((omega 3).mulVec vector) := by
  rw [← matrices_omega]
  exact matrices_mulVec_embed count (fun _ => omega 3) block vector

theorem transvection_embed (count : ℕ) (block : Fin count) (center : PhaseVector 3) :
    transvectionAction (embed count block center) =
      actions count (Function.update (fun _ => 1) block (transvectionAction center)) := by
  apply Subtype.ext
  ext row column
  obtain ⟨⟨local_row, first⟩, rfl⟩ := (indices count).surjective row
  obtain ⟨⟨local_column, second⟩, rfl⟩ := (indices count).surjective column
  change transvection (embed count block center)
    (indices count (local_row, first)) (indices count (local_column, second)) =
      matrices count (fun other =>
        (Function.update (fun _ => (1 : SymplecticAction 3)) block
          (transvectionAction center) other : ActionMatrix 3))
          (indices count (local_row, first)) (indices count (local_column, second))
  rw [matrices_apply]
  simp only [transvection, Matrix.add_apply, Matrix.vecMulVec_apply, omega_mulVec_embed, embed_apply]
  by_cases first_block : first = block <;> by_cases second_block : second = block <;>
    by_cases same_block : first = second <;>
    simp_all [Matrix.one_apply, transvection,
      Matrix.vecMulVec_apply, Matrix.add_apply]

def inclusion (count : ℕ) (block : Fin count) : SymplecticAction 3 →* SymplecticAction (count * 3) :=
  (actions count).comp (MonoidHom.mulSingle (fun _ : Fin count => SymplecticAction 3) block)

theorem transvection_inclusion (count : ℕ) (block : Fin count) (center : PhaseVector 3) :
    transvectionAction (embed count block center) = inclusion count block (transvectionAction center) := by
  have identity : actions count (fun _ : Fin count => (1 : SymplecticAction 3)) = 1 :=
    map_one (actions count)
  simpa [inclusion, Pi.update_eq_div_mul_mulSingle, identity] using transvection_embed count block center

theorem product_embed (count : ℕ) (block : Fin count) (centers : List (PhaseVector 3)) :
    productTransvections (centers.map (embed count block)) =
      inclusion count block (productTransvections centers) := by
  induction centers with
  | nil => simp
  | cons center centers induction =>
      simp [productTransvections_cons, transvection_inclusion, induction]

private theorem product_single_blocks (count : ℕ) (blocks : List (Fin count)) (distinct : blocks.Nodup) :
    (blocks.map fun block => Pi.mulSingle block GreedyCounterexample.initial).prod =
      fun block => if block ∈ blocks then GreedyCounterexample.initial else 1 := by
  induction blocks with
  | nil => funext block; simp
  | cons first blocks induction =>
      obtain ⟨absent, tail_distinct⟩ := List.nodup_cons.mp distinct
      rw [List.map_cons, List.prod_cons, induction tail_distinct]
      funext block
      by_cases same : first = block
      · subst block
        simp [absent]
      · simp [Ne.symm same]

def shortCenters (count : ℕ) : List (PhaseVector (count * 3)) :=
  (List.finRange count).flatMap fun block => GreedyCounterexample.shortCenters.map (embed count block)

theorem shortCenters_length (count : ℕ) : (shortCenters count).length = count * 3 := by
  simp [shortCenters, List.length_flatMap, GreedyCounterexample.shortCenters]

theorem shortCenters_replay (count : ℕ) : IsFactorization (repeated count) (shortCenters count) := by
  change productTransvections (shortCenters count) = repeated count
  rw [shortCenters, productTransvections, List.map_flatMap, List.flatMap_def,
    List.prod_flatten, List.map_map]
  change ((List.finRange count).map fun block =>
    productTransvections (GreedyCounterexample.shortCenters.map (embed count block))).prod = _
  have short : productTransvections GreedyCounterexample.shortCenters = GreedyCounterexample.initial :=
    GreedyCounterexample.short_replay
  simp only [product_embed, short, inclusion, MonoidHom.comp_apply,
    MonoidHom.mulSingle_apply]
  change ((List.finRange count).map
    ((actions count) ∘ fun block => Pi.mulSingle block GreedyCounterexample.initial)).prod = _
  rw [← List.map_map, ← map_list_prod, product_single_blocks count _ (List.nodup_finRange count)]
  simp [repeated]

theorem assembly_spec (count : ℕ) :
    (∀ (family : Fin count → SymplecticAction 3) (row column : PhaseIndex 3) (first second : Fin count),
      (actions count family : ActionMatrix (count * 3))
          (indices count (row, first)) (indices count (column, second)) =
        if first = second then (family first : ActionMatrix 3) row column else 0) ∧
    (∀ first second : Fin count → SymplecticAction 3,
      actions count (first * second) = actions count first * actions count second) ∧
    actions count 1 = 1 :=
  ⟨fun family => matrices_apply count (fun block => (family block : ActionMatrix 3)),
    map_mul (actions count), map_one (actions count)⟩

theorem short_factorization_spec (count : ℕ) :
    IsFactorization (repeated count) (shortCenters count) ∧ (shortCenters count).length = count * 3 :=
  ⟨shortCenters_replay count, shortCenters_length count⟩

end PaulimerFormal.GreedyBlocks
