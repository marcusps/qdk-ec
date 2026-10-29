import PaulimerFormal.PauliAlgorithms
import PaulimerFormal.TriangularKeys

/-!
# Executable residue extraction

Retain Binar's pivot rows and their row-operation transforms, then compute
the core as `V Rᵀ`. Noncomputable witnesses appear only in the specification,
not in the extracted basis, rank, transform, or core.
-/

namespace PaulimerFormal.ResidueExtraction

open BinarFormal.Packed BinarFormal.Echelon BinarBridge

theorem pivotRows_independent {rows columns : ℕ} (matrix : PackedMatrix rows columns) :
    LinearIndependent F2 (pivotRow matrix) :=
  (rrefCompletionFamily_linearIndependent matrix).comp Sum.inl Sum.inl_injective

theorem pivotRows_span {rows columns : ℕ} (matrix : PackedMatrix rows columns) :
    Submodule.span F2 (Set.range (pivotRow matrix)) =
      Submodule.span F2 (Set.range matrix.decode) := by
  rw [← echelonize_rowSpace_eq matrix]
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨row, rfl⟩
    exact ⟨⟨row.val, row.isLt.trans_le (EchelonForm.new_pivots_length_le matrix)⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨row, rfl⟩
    by_cases retained : row.val < (EchelonForm.new matrix).pivots.length
    · exact Submodule.subset_span ⟨⟨row.val, retained⟩, rfl⟩
    · have zero : (echelonize matrix).decode row = 0 := by
        funext column
        rw [echelonize, PackedMatrix.decode_get,
          EchelonForm.new_rows_zero matrix row (by omega) column.val column.isLt]
        rfl
      rw [zero]
      exact Submodule.zero_mem _

def retainedTransform {rows columns : ℕ} (matrix : PackedMatrix rows columns) :
    Matrix (Fin (EchelonForm.new matrix).pivots.length) (Fin rows) F2 :=
  fun row => (EchelonForm.new matrix).transform.decode
    ⟨row.val, row.isLt.trans_le (EchelonForm.new_pivots_length_le matrix)⟩

theorem retainedTransform_mul {rows columns : ℕ} (matrix : PackedMatrix rows columns) :
    retainedTransform matrix * matrix.decode = pivotRow matrix := by
  funext row column
  exact congrFun (congrFun (EchelonForm.new_transform_mul_eq matrix)
    ⟨row.val, row.isLt.trans_le (EchelonForm.new_pivots_length_le matrix)⟩) column

/-- Return stored data: a function-valued cache can be eta-expanded into repeated reconstruction. -/
def storeAction {m : ℕ} (action : ActionMatrix m) : Vector (Vector F2 (m + m)) (m + m) :=
  Vector.ofFn fun row : Fin (m + m) =>
    Vector.ofFn fun column : Fin (m + m) =>
      action ((phaseIndexEquiv m).symm row) ((phaseIndexEquiv m).symm column)

def readAction {m : ℕ} (rows : Vector (Vector F2 (m + m)) (m + m)) : ActionMatrix m :=
  fun row column => rows[phaseIndexEquiv m row][phaseIndexEquiv m column]

@[simp]
theorem storeAction_eq {m : ℕ} (action : ActionMatrix m) : readAction (storeAction action) = action := by
  funext row column
  simp [readAction, storeAction]

def storeVector {m : ℕ} (vector : PhaseVector m) : Vector F2 (m + m) :=
  Vector.ofFn (toFinVector vector)

def readVector {m : ℕ} (coordinates : Vector F2 (m + m)) : PhaseVector m :=
  ofFinVector fun index => coordinates[index]

@[simp]
theorem storeVector_eq {m : ℕ} (vector : PhaseVector m) : readVector (storeVector vector) = vector := by
  simp [readVector, storeVector]

def packedResidue {m : ℕ} (action : ActionMatrix m) : PackedActionMatrix m :=
  (⟨fun row => packVector fun column =>
    residueMatrix action ((phaseIndexEquiv m).symm row) ((phaseIndexEquiv m).symm column)⟩ :
      PackedActionMatrix m).materialize

@[simp]
theorem decode_packedResidue {m : ℕ} (action : ActionMatrix m) :
    (packedResidue action).decode = fun row column =>
      residueMatrix action ((phaseIndexEquiv m).symm row) ((phaseIndexEquiv m).symm column) := by
  simp only [packedResidue, PackedMatrix.materialize_eq, PackedMatrix.decode, decode_packVector]
  rfl

def rank {m : ℕ} (action : ActionMatrix m) : ℕ :=
  (EchelonForm.new (packedResidue action)).pivots.length

def basis {m : ℕ} (action : ActionMatrix m) :
    Matrix (Fin (rank action)) (PhaseIndex m) F2 :=
  fun row => ofFinVector (pivotRow (packedResidue action) row)

def transform {m : ℕ} (action : ActionMatrix m) :
    Matrix (Fin (rank action)) (PhaseIndex m) F2 :=
  fun row => ofFinVector (retainedTransform (packedResidue action) row)

def core {m : ℕ} (action : ActionMatrix m) :
    Matrix (Fin (rank action)) (Fin (rank action)) F2 :=
  basis action * Matrix.transpose (transform action)

theorem basis_independent {m : ℕ} (action : ActionMatrix m) :
    LinearIndependent F2 (basis action) := by
  let reindex := LinearEquiv.funCongrLeft F2 F2 (phaseIndexEquiv m)
  exact (pivotRows_independent (packedResidue action)).map' reindex.toLinearMap
    (LinearMap.ker_eq_bot.mpr reindex.injective)

theorem basis_span {m : ℕ} (action : ActionMatrix m) :
    Submodule.span F2 (Set.range (basis action)) = residueSpace action := by
  let reindex := LinearEquiv.funCongrLeft F2 F2 (phaseIndexEquiv m)
  change Submodule.span F2 (Set.range (reindex.toLinearMap ∘
    pivotRow (packedResidue action))) = _
  rw [Set.range_comp, Submodule.span_image, pivotRows_span, ← Submodule.span_image]
  change Submodule.span F2 (reindex.toLinearMap ''
    Set.range (fun row column => (packedResidue action).decode row column)) = _
  rw [← Set.range_comp]
  have rows : reindex.toLinearMap ∘ (fun row column => (packedResidue action).decode row column) =
      (fun row column => residueMatrix action ((phaseIndexEquiv m).symm row) column) := by
    funext row column
    change (packedResidue action).decode row (phaseIndexEquiv m column) = _
    rw [decode_packedResidue]
    simp
  rw [rows]
  have ranges : Set.range (fun row column =>
      residueMatrix action ((phaseIndexEquiv m).symm row) column) =
      Set.range (fun row column => residueMatrix action row column) := by
    ext vector
    constructor
    · rintro ⟨row, rfl⟩
      exact ⟨(phaseIndexEquiv m).symm row, rfl⟩
    · rintro ⟨row, rfl⟩
      exact ⟨phaseIndexEquiv m row, by simp⟩
  rw [ranges]
  exact (residueSpace_eq_span_rows_residueMatrix action).symm

theorem rank_eq {m : ℕ} (action : ActionMatrix m) :
    rank action = residueRank action := by
  have dimension := finrank_span_eq_card (basis_independent action)
  rw [basis_span] at dimension
  simpa [residueRank] using dimension.symm

theorem transform_mul {m : ℕ} (action : ActionMatrix m) :
    transform action * residueMatrix action = basis action := by
  funext row column
  have reduced := congrFun (congrFun (retainedTransform_mul (packedResidue action)) row)
    (phaseIndexEquiv m column)
  change (∑ index : Fin (m + m), retainedTransform (packedResidue action) row index *
    (packedResidue action).decode index (phaseIndexEquiv m column)) = _ at reduced
  simp only [decode_packedResidue, Equiv.symm_apply_apply] at reduced
  change (∑ index : PhaseIndex m,
    retainedTransform (packedResidue action) row (phaseIndexEquiv m index) *
      residueMatrix action index column) = _
  calc
    _ = ∑ index : Fin (m + m), retainedTransform (packedResidue action) row index *
        residueMatrix action ((phaseIndexEquiv m).symm index) column := by
      simpa only [Equiv.symm_apply_apply] using
        (phaseIndexEquiv m).sum_comp (fun index =>
          retainedTransform (packedResidue action) row index *
            residueMatrix action ((phaseIndexEquiv m).symm index) column)
    _ = _ := reduced

/-- The semantic certificate witnesses the computed data; it is not executed. -/
theorem core_spec {m : ℕ} (target : SymplecticAction m) :
    ∃ presentation : CorePresentation target (rank (target : ActionMatrix m)),
      presentation.basis = basis (target : ActionMatrix m) ∧
      presentation.core = core (target : ActionMatrix m) := by
  obtain ⟨coefficient, unit, residue⟩ := exists_residue_coefficient_of_basis target
    (rank_eq _) (basis _) (basis_independent _) (basis_span _)
  let presentation : CorePresentation target (rank (target : ActionMatrix m)) :=
    { rank_eq := rank_eq _
      basis := basis _
      basis_independent := basis_independent _
      basis_span := basis_span _
      coefficient := coefficient
      coefficient_unit := unit
      residue_eq := residue }
  exact ⟨presentation, rfl, presentation.core_eq_of_row_reduction (transform _)
    (transform_mul _)⟩

theorem core_search_none_iff {m : ℕ} (target : SymplecticAction m) :
    Triangularization.memoizedTriangularize (core (target : ActionMatrix m)) = none ↔
      ¬(canonicalCorePresentation target).IsTriangularizable := by
  obtain ⟨presentation, _, core_eq⟩ := core_spec target
  rw [← core_eq, Triangularization.memoized_core_none_iff,
    presentation.isTriangularizable_iff_canonical]

def rankDecomposition {m : ℕ} (action : ActionMatrix m) : Option (List (PhaseVector m)) :=
  let action := readAction (storeAction action)
  (Triangularization.memoizedTriangularize (core action)).map fun change =>
    ((List.ofFn (change * basis action)).map storeVector).map readVector

theorem rankDecomposition_eq {m : ℕ} (action : ActionMatrix m) :
    rankDecomposition action =
      (Triangularization.memoizedTriangularize (core action)).map
        (fun change => List.ofFn (change * basis action)) := by
  unfold rankDecomposition
  rw [storeAction_eq]
  simp only [List.map_map, Function.comp_def, storeVector_eq]
  congr 1
  funext change
  exact List.map_id _

theorem rankDecomposition_some_spec {m : ℕ} (target : SymplecticAction m)
    (centers : List (PhaseVector m))
    (returned : rankDecomposition (target : ActionMatrix m) = some centers) :
    IsFactorization target centers ∧ centers.length = residueRank (target : ActionMatrix m) ∧
      ∀ other, IsFactorization target other → centers.length ≤ other.length := by
  obtain ⟨presentation, basis_eq, core_eq⟩ := core_spec target
  rw [rankDecomposition_eq] at returned
  obtain ⟨change, found, rfl⟩ := Option.map_eq_some_iff.mp returned
  rw [Triangularization.memoizedTriangularize_eq] at found
  obtain ⟨unit, lower⟩ := Triangularization.congruenceTriangularize_sound _ _ found
  have factorization := presentation.factorization_of_triangularizer change unit
    (by simpa only [core_eq] using lower)
  rw [basis_eq] at factorization
  refine ⟨factorization, ?_, ?_⟩
  · rw [List.length_ofFn, rank_eq]
  · intro other factors
    rw [List.length_ofFn, rank_eq]
    change productTransvections other = target at factors
    simpa only [factors] using residueRank_product_le_length other

theorem rankDecomposition_none_iff {m : ℕ} (target : SymplecticAction m) :
    rankDecomposition (target : ActionMatrix m) = none ↔
      ¬(canonicalCorePresentation target).IsTriangularizable := by
  simp only [rankDecomposition_eq, Option.map_eq_none_iff, core_search_none_iff]

example : rank (1 : ActionMatrix 0) = 0 := by decide

end PaulimerFormal.ResidueExtraction
