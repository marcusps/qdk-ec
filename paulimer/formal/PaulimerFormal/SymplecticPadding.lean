import PaulimerFormal.GreedyBlockSelection

/-! Identity padding in global X-then-Z order. -/

namespace PaulimerFormal.SymplecticPadding

def indices (size extra : ℕ) : PhaseIndex size ⊕ PhaseIndex extra ≃ PhaseIndex (size + extra) :=
  (Equiv.sumSumSumComm (Fin size) (Fin size) (Fin extra) (Fin extra)).trans
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

def assemble {size extra : ℕ} (first : ActionMatrix size) (second : ActionMatrix extra) :
    ActionMatrix (size + extra) :=
  Matrix.reindexAlgEquiv F2 F2 (indices size extra) (Matrix.fromBlocks first 0 0 second)

theorem assemble_apply {size extra : ℕ} (first : ActionMatrix size) (second : ActionMatrix extra)
    (row column : PhaseIndex size ⊕ PhaseIndex extra) :
    assemble first second (indices size extra row) (indices size extra column) =
      Matrix.fromBlocks first 0 0 second row column := by
  change Matrix.fromBlocks first 0 0 second
    ((indices size extra).symm (indices size extra row))
    ((indices size extra).symm (indices size extra column)) = _
  simp

theorem assemble_mul {size extra : ℕ} (first next : ActionMatrix size)
    (second later : ActionMatrix extra) :
    assemble (first * next) (second * later) = assemble first second * assemble next later := by
  simp [assemble, Matrix.fromBlocks_multiply]

theorem assemble_one (size extra : ℕ) : assemble (1 : ActionMatrix size) (1 : ActionMatrix extra) = 1 := by
  simp [assemble, Matrix.fromBlocks_one]

theorem assemble_transpose {size extra : ℕ} (first : ActionMatrix size) (second : ActionMatrix extra) :
    assemble first.transpose second.transpose = (assemble first second).transpose := by
  ext row column
  obtain ⟨row, rfl⟩ := (indices size extra).surjective row
  obtain ⟨column, rfl⟩ := (indices size extra).surjective column
  simp only [Matrix.transpose_apply, assemble_apply]
  cases row <;> cases column <;> rfl

theorem assemble_omega (size extra : ℕ) : assemble (omega size) (omega extra) = omega (size + extra) := by
  ext row column
  obtain ⟨row, rfl⟩ := (indices size extra).surjective row
  obtain ⟨column, rfl⟩ := (indices size extra).surjective column
  rw [assemble_apply]
  rcases row with (row | row) | (row | row) <;>
    rcases column with (column | column) | (column | column) <;>
    simp [indices, Equiv.sumSumSumComm, omega, Matrix.J, Matrix.fromBlocks, Matrix.one_apply]
  all_goals
    intro same
    have equal := congrArg Fin.val same
    simp only [Fin.val_castAdd, Fin.val_natAdd] at equal
    omega

theorem assemble_symplectic {size extra : ℕ} (first : SymplecticAction size)
    (second : SymplecticAction extra) : IsSymplectic (assemble first.val second.val) := by
  rw [IsSymplectic, SymplecticGroup.mem_iff]
  change assemble first.val second.val * omega (size + extra) *
    (assemble first.val second.val).transpose = omega (size + extra)
  rw [← assemble_omega, ← assemble_transpose, ← assemble_mul, ← assemble_mul]
  simp only [omega, SymplecticGroup.mem_iff.mp first.property, SymplecticGroup.mem_iff.mp second.property]

def action (size extra : ℕ) : SymplecticAction size →* SymplecticAction (size + extra) where
  toFun first := ⟨assemble first.val (1 : ActionMatrix extra), assemble_symplectic first 1⟩
  map_one' := Subtype.ext (assemble_one size extra)
  map_mul' first second := by
    apply Subtype.ext
    simpa using assemble_mul first.val second.val (1 : ActionMatrix extra) 1

def vectors {size extra : ℕ} (first : PhaseVector size) (second : PhaseVector extra) :
    PhaseVector (size + extra) :=
  (Sum.elim first second) ∘ (indices size extra).symm

theorem vectors_apply {size extra : ℕ} (first : PhaseVector size) (second : PhaseVector extra)
    (coordinate : PhaseIndex size ⊕ PhaseIndex extra) :
    vectors first second (indices size extra coordinate) = Sum.elim first second coordinate := by
  simp [vectors]

theorem vectors_surjective (size extra : ℕ) (vector : PhaseVector (size + extra)) :
    ∃ first second, vector = vectors first second := by
  refine ⟨fun index => vector (indices size extra (Sum.inl index)),
    fun index => vector (indices size extra (Sum.inr index)), ?_⟩
  funext index
  obtain ⟨index, rfl⟩ := (indices size extra).surjective index
  cases index <;> simp [vectors_apply]

theorem vectors_add {size extra : ℕ} (first next : PhaseVector size) (second later : PhaseVector extra) :
    vectors (first + next) (second + later) = vectors first second + vectors next later := by
  funext index
  obtain ⟨index, rfl⟩ := (indices size extra).surjective index
  cases index <;> simp [vectors_apply]

theorem vectors_mulVec {size extra : ℕ} (first : ActionMatrix size) (second : ActionMatrix extra)
    (left : PhaseVector size) (right : PhaseVector extra) :
    (assemble first second).mulVec (vectors left right) = vectors (first.mulVec left) (second.mulVec right) := by
  funext row
  obtain ⟨row, rfl⟩ := (indices size extra).surjective row
  change (∑ column, assemble first second (indices size extra row) column * vectors left right column) = _
  rw [← (indices size extra).sum_comp]
  simp only [assemble_apply, vectors_apply, Fintype.sum_sum_type]
  cases row <;> simp [Matrix.fromBlocks, Matrix.mulVec, dotProduct]

theorem vectors_rowAction {size extra : ℕ} (first : ActionMatrix size) (second : ActionMatrix extra)
    (left : PhaseVector size) (right : PhaseVector extra) :
    rowAction (vectors left right) (assemble first second) =
      vectors (rowAction left first) (rowAction right second) := by
  rw [rowAction, ← Matrix.mulVec_transpose, ← assemble_transpose, vectors_mulVec]
  simp only [Matrix.mulVec_transpose]
  rfl

theorem pairing_vectors {size extra : ℕ} (first next : PhaseVector size)
    (second later : PhaseVector extra) :
    pairing (vectors first second) (vectors next later) = pairing first next + pairing second later := by
  rw [pairing, ← assemble_omega, vectors_mulVec]
  change (∑ index, vectors first second index * vectors ((omega size).mulVec next)
    ((omega extra).mulVec later) index) = _
  rw [← (indices size extra).sum_comp]
  simp [vectors_apply, pairing, dotProduct]

def embed (extra : ℕ) {size : ℕ} (vector : PhaseVector size) : PhaseVector (size + extra) :=
  vectors vector 0

theorem embed_injective (extra size : ℕ) : Function.Injective (embed extra (size := size)) := by
  intro first second same
  funext coordinate
  have entry := congrFun same (indices size extra (Sum.inl coordinate))
  simpa [embed, vectors_apply] using entry

theorem embed_zero (extra size : ℕ) : embed extra (0 : PhaseVector size) = 0 := by
  funext index
  obtain ⟨index, rfl⟩ := (indices size extra).surjective index
  cases index <;> simp [embed, vectors_apply]

theorem embed_single {size : ℕ} (extra : ℕ) (coordinate : PhaseIndex size) :
    embed extra (Pi.single coordinate 1) =
      Pi.single (indices size extra (Sum.inl coordinate)) 1 := by
  funext index
  obtain ⟨index, rfl⟩ := (indices size extra).surjective index
  cases index <;> simp [embed, vectors_apply, Pi.single_apply]

theorem embed_pairing {size : ℕ} (extra : ℕ) (first second : PhaseVector size) :
    pairing (embed extra first) (embed extra second) = pairing first second := by
  simp [embed, pairing_vectors]

theorem embed_rowAction {size : ℕ} (extra : ℕ) (target : SymplecticAction size) (vector : PhaseVector size) :
    rowAction (embed extra vector) (action size extra target : ActionMatrix (size + extra)) =
      embed extra (rowAction vector target.val) := by
  change rowAction (vectors vector 0) (assemble target.val 1) = _
  simp [vectors_rowAction, embed]

theorem embed_residueVector {size : ℕ} (extra : ℕ) (target : SymplecticAction size)
    (vector : PhaseVector size) :
    GreedyReduction.residueVector (action size extra target : ActionMatrix (size + extra)) (embed extra vector) =
      embed extra (GreedyReduction.residueVector target.val vector) := by
  rw [GreedyReduction.residueVector, embed_rowAction]
  exact (vectors_add vector (rowAction vector target.val) 0 0).symm

theorem embed_transvection {size : ℕ} (extra : ℕ) (center : PhaseVector size) :
    transvectionAction (embed extra center) = action size extra (transvectionAction center) := by
  apply Subtype.ext
  ext row column
  obtain ⟨row, rfl⟩ := (indices size extra).surjective row
  obtain ⟨column, rfl⟩ := (indices size extra).surjective column
  change transvection (vectors center 0) (indices size extra row) (indices size extra column) =
    assemble (transvection center) 1 (indices size extra row) (indices size extra column)
  rw [assemble_apply]
  simp only [transvection, Matrix.add_apply, Matrix.vecMulVec_apply, ← assemble_omega size extra,
    vectors_mulVec]
  cases row <;> cases column <;>
    simp [vectors_apply, Matrix.fromBlocks, Matrix.one_apply, Matrix.vecMulVec_apply]

theorem embed_product {size : ℕ} (extra : ℕ) (centers : List (PhaseVector size)) :
    productTransvections (centers.map (embed extra)) = action size extra (productTransvections centers) := by
  induction centers with
  | nil => simp
  | cons center centers induction => simp [embed_transvection, induction]

theorem hyperbolic_action {size : ℕ} (extra : ℕ) (target : SymplecticAction size)
    (hyperbolic : GreedyReduction.IsHyperbolic target.val) :
    GreedyReduction.IsHyperbolic (action size extra target : ActionMatrix (size + extra)) := by
  intro vector
  obtain ⟨first, second, rfl⟩ := vectors_surjective size extra vector
  change pairing (vectors first second) (rowAction (vectors first second) (assemble target.val 1)) = 0
  rw [vectors_rowAction, pairing_vectors, rowAction_one, hyperbolic]
  simp

end PaulimerFormal.SymplecticPadding
