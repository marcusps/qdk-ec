import Mathlib.LinearAlgebra.Dimension.Free
import PaulimerFormal.Product

/-!
# Minimal binary symplectic transvection factorizations

A core presentation writes the residue matrix as `Vᵀ D V`, where the rows of
`V` are a basis of the residue space and `D` is invertible. The Rust residue
core is `D⁻ᵀ`.
-/

namespace PaulimerFormal

/-- A square matrix is unit lower triangular in the standard `Fin` order. -/
def IsUnitLowerTriangular {n : ℕ} (matrix : Matrix (Fin n) (Fin n) F2) :
    Prop :=
  (∀ row column, row < column → matrix row column = 0) ∧
    ∀ index, matrix index index = 1

theorem isUnitLowerTriangular_ext {n : ℕ}
    {first second : Matrix (Fin n) (Fin n) F2}
    (first_lower : IsUnitLowerTriangular first)
    (second_lower : IsUnitLowerTriangular second)
    (symmetrizations :
      first + Matrix.transpose first =
        second + Matrix.transpose second) :
    first = second := by
  ext row column
  rcases lt_trichotomy row column with before | equal | after
  · rw [first_lower.1 row column before,
      second_lower.1 row column before]
  · subst column
    rw [first_lower.2, second_lower.2]
  · have entry_eq := congrFun (congrFun symmetrizations column) row
    simpa [Matrix.add_apply, Matrix.transpose_apply,
      first_lower.1 column row after,
      second_lower.1 column row after] using entry_eq

theorem pairingUpper_transpose_isUnitLowerTriangular {m : ℕ}
    (centers : List (PhaseVector m)) :
    IsUnitLowerTriangular
      (Matrix.transpose (pairingUpper centers)) := by
  constructor
  · intro row column before
    rw [Matrix.transpose_apply, pairingUpper_apply]
    simp [Ne.symm before.ne, before.asymm]
  · intro index
    rw [Matrix.transpose_apply, pairingUpper_apply]
    simp

theorem pairingUpperFin_transpose_isUnitLowerTriangular {m n : ℕ}
    (centers : Fin n → PhaseVector m) :
    IsUnitLowerTriangular
      (Matrix.transpose (pairingUpperFin centers)) := by
  let indexEquiv := ofFnIndexEquiv centers
  have triangular :=
    pairingUpper_transpose_isUnitLowerTriangular (List.ofFn centers)
  constructor
  · intro row column above
    have reindexedAbove :
        (indexEquiv.symm row).val < (indexEquiv.symm column).val := by
      simpa [indexEquiv, ofFnIndexEquiv] using above
    have zero := triangular.1
      (indexEquiv.symm row) (indexEquiv.symm column) reindexedAbove
    simpa [pairingUpperFin, indexEquiv, Matrix.reindex_apply]
      using zero
  · intro index
    have diagonal := triangular.2 (indexEquiv.symm index)
    simpa [pairingUpperFin, indexEquiv, Matrix.reindex_apply]
      using diagonal

/-- A faithful basis presentation of a symplectic residue matrix. -/
structure CorePresentation {m : ℕ} (target : SymplecticAction m)
    (dimension : ℕ) where
  rank_eq : dimension = residueRank (target : ActionMatrix m)
  basis : Matrix (Fin dimension) (PhaseIndex m) F2
  basis_independent : LinearIndependent F2 basis
  basis_span :
    Submodule.span F2 (Set.range basis) =
      residueSpace (target : ActionMatrix m)
  coefficient : Matrix (Fin dimension) (Fin dimension) F2
  coefficient_unit : IsUnit coefficient
  residue_eq :
    residueMatrix (target : ActionMatrix m) =
      Matrix.transpose basis * coefficient * basis

/-- The residue core represented by `D⁻ᵀ` when `F̂ = Vᵀ D V`. -/
noncomputable def CorePresentation.core {m : ℕ}
    {target : SymplecticAction m} {dimension : ℕ}
    (presentation : CorePresentation target dimension) :
    Matrix (Fin dimension) (Fin dimension) F2 :=
  Matrix.transpose presentation.coefficient⁻¹

/-- Congruence triangularizability of a faithful residue core. -/
def CorePresentation.IsTriangularizable {m : ℕ}
    {target : SymplecticAction m} {dimension : ℕ}
    (presentation : CorePresentation target dimension) : Prop :=
  ∃ change : Matrix (Fin dimension) (Fin dimension) F2,
    IsUnit change ∧
      IsUnitLowerTriangular
        (change * presentation.core * Matrix.transpose change)

theorem CorePresentation.coefficient_mul_core_transpose {m : ℕ}
    {target : SymplecticAction m} {dimension : ℕ}
    (presentation : CorePresentation target dimension) :
    presentation.coefficient *
        Matrix.transpose presentation.core = 1 := by
  rw [CorePresentation.core, Matrix.transpose_transpose]
  exact Matrix.mul_nonsing_inv presentation.coefficient
    ((Matrix.isUnit_iff_isUnit_det presentation.coefficient).mp
      presentation.coefficient_unit)

theorem CorePresentation.core_transpose_mul_coefficient {m : ℕ}
    {target : SymplecticAction m} {dimension : ℕ}
    (presentation : CorePresentation target dimension) :
    Matrix.transpose presentation.core *
        presentation.coefficient = 1 := by
  rw [CorePresentation.core, Matrix.transpose_transpose]
  exact Matrix.nonsing_inv_mul presentation.coefficient
    ((Matrix.isUnit_iff_isUnit_det presentation.coefficient).mp
      presentation.coefficient_unit)

/-- The core computed from row reduction, `V Rᵀ` with `V = R F̂`, is `D⁻ᵀ`. -/
theorem CorePresentation.core_eq_of_row_reduction {m n : ℕ}
    {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (transform : Matrix (Fin n) (PhaseIndex m) F2)
    (reduced :
      transform * residueMatrix (target : ActionMatrix m) =
        presentation.basis) :
    presentation.core = presentation.basis * Matrix.transpose transform := by
  have left_inverse :
      transform * Matrix.transpose presentation.basis *
        presentation.coefficient = 1 := by
    apply mul_right_cancel_of_vecMul_injective presentation.basis _ _
      (Matrix.vecMul_injective_iff.mpr presentation.basis_independent)
    simpa only [presentation.residue_eq, Matrix.mul_assoc,
      Matrix.one_mul] using reduced
  have transform_eq :
      transform * Matrix.transpose presentation.basis =
        Matrix.transpose presentation.core := by
    calc
      transform * Matrix.transpose presentation.basis =
          (transform * Matrix.transpose presentation.basis) *
            (presentation.coefficient * Matrix.transpose presentation.core) := by
              rw [presentation.coefficient_mul_core_transpose, Matrix.mul_one]
      _ = Matrix.transpose presentation.core := by
        rw [← Matrix.mul_assoc, left_inverse, Matrix.one_mul]
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
    (congrArg Matrix.transpose transform_eq).symm

theorem inverseSandwichIff {n : ℕ}
    (factor inverseCore basisChange path pairing :
      Matrix (Fin n) (Fin n) F2)
    (factor_mul_inverseCore : factor * inverseCore = 1)
    (inverseCore_mul_factor : inverseCore * factor = 1)
    (basisChange_unit : IsUnit basisChange)
    (path_mul_pairing : path * pairing = 1)
    (pairing_mul_path : pairing * path = 1) :
    factor =
        Matrix.transpose basisChange * path * basisChange ↔
      basisChange * inverseCore * Matrix.transpose basisChange =
        pairing := by
  obtain ⟨basisChangeInverse, basisChange_mul_inverse,
    inverse_mul_basisChange⟩ :=
      isUnit_iff_exists.mp basisChange_unit
  constructor
  · intro factor_eq
    have transpose_path_eq :
        Matrix.transpose basisChange * path =
          factor * basisChangeInverse := by
      calc
        Matrix.transpose basisChange * path =
            (Matrix.transpose basisChange * path) * 1 := by simp
        _ = (Matrix.transpose basisChange * path) *
            (basisChange * basisChangeInverse) := by
              rw [basisChange_mul_inverse]
        _ = (Matrix.transpose basisChange * path * basisChange) *
            basisChangeInverse := by simp [Matrix.mul_assoc]
        _ = factor * basisChangeInverse := by rw [← factor_eq]
    have transformed_mul_path :
        (basisChange * inverseCore *
            Matrix.transpose basisChange) * path = 1 := by
      calc
        (basisChange * inverseCore *
            Matrix.transpose basisChange) * path =
            basisChange * inverseCore *
              (Matrix.transpose basisChange * path) := by
                simp [Matrix.mul_assoc]
        _ = basisChange * inverseCore *
            (factor * basisChangeInverse) := by
              rw [transpose_path_eq]
        _ = basisChange * (inverseCore * factor) *
            basisChangeInverse := by simp [Matrix.mul_assoc]
        _ = basisChange * basisChangeInverse := by
              rw [inverseCore_mul_factor, Matrix.mul_one]
        _ = 1 := basisChange_mul_inverse
    calc
      basisChange * inverseCore * Matrix.transpose basisChange =
          (basisChange * inverseCore *
            Matrix.transpose basisChange) * 1 := by simp
      _ = (basisChange * inverseCore *
            Matrix.transpose basisChange) * (path * pairing) := by
              rw [path_mul_pairing]
      _ = ((basisChange * inverseCore *
            Matrix.transpose basisChange) * path) * pairing := by
              simp [Matrix.mul_assoc]
      _ = pairing := by rw [transformed_mul_path, Matrix.one_mul]
  · intro transformed_eq
    have inverseCore_transpose_eq :
        inverseCore * Matrix.transpose basisChange =
          basisChangeInverse * pairing := by
      calc
        inverseCore * Matrix.transpose basisChange =
            1 * (inverseCore * Matrix.transpose basisChange) := by simp
        _ = (basisChangeInverse * basisChange) *
            (inverseCore * Matrix.transpose basisChange) := by
              rw [inverse_mul_basisChange]
        _ = basisChangeInverse *
            (basisChange * inverseCore *
              Matrix.transpose basisChange) := by
                simp [Matrix.mul_assoc]
        _ = basisChangeInverse * pairing := by rw [transformed_eq]
    have inverseCore_mul_candidate :
        inverseCore *
            (Matrix.transpose basisChange * path * basisChange) =
          1 := by
      calc
        inverseCore *
            (Matrix.transpose basisChange * path * basisChange) =
            (inverseCore * Matrix.transpose basisChange) *
              path * basisChange := by simp [Matrix.mul_assoc]
        _ = (basisChangeInverse * pairing) *
            path * basisChange := by rw [inverseCore_transpose_eq]
        _ = basisChangeInverse * (pairing * path) *
            basisChange := by simp [Matrix.mul_assoc]
        _ = basisChangeInverse * basisChange := by
              rw [pairing_mul_path, Matrix.mul_one]
        _ = 1 := inverse_mul_basisChange
    symm
    calc
      Matrix.transpose basisChange * path * basisChange =
          1 * (Matrix.transpose basisChange * path *
            basisChange) := by simp
      _ = (factor * inverseCore) *
          (Matrix.transpose basisChange * path *
            basisChange) := by rw [factor_mul_inverseCore]
      _ = factor *
          (inverseCore *
            (Matrix.transpose basisChange * path *
              basisChange)) := by simp [Matrix.mul_assoc]
      _ = factor := by rw [inverseCore_mul_candidate, Matrix.mul_one]

theorem CorePresentation.coefficient_eq_path_iff_core_eq_pairing
    {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (centers : Fin n → PhaseVector m)
    (basisChange : Matrix (Fin n) (Fin n) F2)
    (basisChange_unit : IsUnit basisChange) :
    presentation.coefficient =
        Matrix.transpose basisChange * pathMatrixFin centers *
          basisChange ↔
      basisChange * presentation.core *
          Matrix.transpose basisChange =
        Matrix.transpose (pairingUpperFin centers) := by
  have inverseEquivalence := inverseSandwichIff
    presentation.coefficient
    (Matrix.transpose presentation.core)
    basisChange
    (pathMatrixFin centers)
    (pairingUpperFin centers)
    presentation.coefficient_mul_core_transpose
    presentation.core_transpose_mul_coefficient
    basisChange_unit
    (pathMatrixFin_mul_pairingUpperFin centers)
    (pairingUpperFin_mul_pathMatrixFin centers)
  constructor
  · intro coefficient_eq
    have transformed := inverseEquivalence.mp coefficient_eq
    have transposed := congrArg Matrix.transpose transformed
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using transposed
  · intro transformed
    apply inverseEquivalence.mpr
    have transposed := congrArg Matrix.transpose transformed
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using transposed

/-- A canonical finite basis of the residue space, embedded in phase space. -/
noncomputable def residueBasisMatrix {m : ℕ}
    (target : SymplecticAction m) :
    Matrix (Fin (residueRank (target : ActionMatrix m))) (PhaseIndex m) F2 :=
  fun index =>
    (Module.finBasis F2 (residueSpace (target : ActionMatrix m)) index :
      residueSpace (target : ActionMatrix m))

theorem residueBasisMatrix_independent {m : ℕ}
    (target : SymplecticAction m) :
    LinearIndependent F2 (residueBasisMatrix target) := by
  let basis :=
    Module.finBasis F2 (residueSpace (target : ActionMatrix m))
  have independent :=
    basis.linearIndependent.map'
      (residueSpace (target : ActionMatrix m)).subtype
      (Submodule.ker_subtype _)
  change LinearIndependent F2
    (fun index : Fin
        (Module.finrank F2 (residueSpace (target : ActionMatrix m))) =>
      ((Module.finBasis F2
        (residueSpace (target : ActionMatrix m)) index :
          residueSpace (target : ActionMatrix m)) : PhaseVector m))
  exact independent

theorem residueBasisMatrix_span {m : ℕ}
    (target : SymplecticAction m) :
    Submodule.span F2 (Set.range (residueBasisMatrix target)) =
      residueSpace (target : ActionMatrix m) := by
  let basis :=
    Module.finBasis F2 (residueSpace (target : ActionMatrix m))
  change Submodule.span F2
      (Set.range ((residueSpace (target : ActionMatrix m)).subtype ∘ basis)) =
    residueSpace (target : ActionMatrix m)
  rw [Set.range_comp, Submodule.span_image, basis.span_eq,
    Submodule.map_subtype_top]

theorem exists_residue_coefficient_of_basis {m n : ℕ}
    (target : SymplecticAction m)
    (rank_eq : n = residueRank (target : ActionMatrix m))
    (basis : Matrix (Fin n) (PhaseIndex m) F2)
    (basis_independent : LinearIndependent F2 basis)
    (basis_span :
      Submodule.span F2 (Set.range basis) =
        residueSpace (target : ActionMatrix m)) :
    ∃ coefficient : Matrix (Fin n) (Fin n) F2,
      IsUnit coefficient ∧
        residueMatrix (target : ActionMatrix m) =
          Matrix.transpose basis * coefficient * basis := by
  let residue := residueMatrix (target : ActionMatrix m)
  have basis_span_rows :
      Submodule.span F2 (Set.range basis.row) =
        residueSpace (target : ActionMatrix m) := by
    exact basis_span
  have residue_span :
      Submodule.span F2 (Set.range residue.row) =
        residueSpace (target : ActionMatrix m) := by
    exact (residueSpace_eq_span_rows_residueMatrix
      (target : ActionMatrix m)).symm
  have residue_le_basis :
      Submodule.span F2 (Set.range residue.row) ≤
        Submodule.span F2 (Set.range basis.row) := by
    rw [residue_span, basis_span_rows]
  obtain ⟨left, left_mul_basis⟩ :=
    exists_mul_eq_of_span_rows_le residue basis residue_le_basis
  have transpose_factor :
      Matrix.transpose basis * Matrix.transpose left =
        Matrix.transpose residue := by
    calc
      Matrix.transpose basis * Matrix.transpose left =
          Matrix.transpose (left * basis) := by
        rw [Matrix.transpose_mul]
      _ = Matrix.transpose residue := by rw [left_mul_basis]
  have transpose_residue_span :
      Submodule.span F2 (Set.range (Matrix.transpose residue).row) =
        residueSpace (target : ActionMatrix m) := by
    exact (span_rows_residueMatrix_transpose target).trans residue_span
  have residue_le_transpose_left :
      residueSpace (target : ActionMatrix m) ≤
        Submodule.span F2 (Set.range (Matrix.transpose left).row) := by
    rw [← transpose_residue_span, ← transpose_factor]
    exact span_rows_mul_le_right
      (Matrix.transpose basis) (Matrix.transpose left)
  have transpose_basis_injective :
      Function.Injective (Matrix.transpose basis).mulVec :=
    transpose_mulVec_injective_of_linearIndependent basis
      basis_independent
  have transpose_left_rank :
      (Matrix.transpose left).rank =
        (Matrix.transpose residue).rank := by
    rw [← transpose_factor,
      rank_mul_eq_right_of_mulVec_injective _ _
        transpose_basis_injective]
  have transpose_left_span :
      Submodule.span F2 (Set.range (Matrix.transpose left).row) =
        residueSpace (target : ActionMatrix m) := by
    symm
    refine Submodule.eq_of_le_of_finrank_eq
      (K := F2) residue_le_transpose_left ?_
    rw [← Matrix.rank_eq_finrank_span_row,
      transpose_left_rank, Matrix.rank_transpose,
      rank_residueMatrix]
    rfl
  have transpose_left_le_basis :
      Submodule.span F2 (Set.range (Matrix.transpose left).row) ≤
        Submodule.span F2 (Set.range basis.row) := by
    rw [transpose_left_span, basis_span_rows]
  obtain ⟨middle, middle_mul_basis⟩ :=
    exists_mul_eq_of_span_rows_le
      (Matrix.transpose left) basis transpose_left_le_basis
  have left_factor :
      Matrix.transpose basis * Matrix.transpose middle = left := by
    calc
      Matrix.transpose basis * Matrix.transpose middle =
          Matrix.transpose (middle * basis) := by
        rw [Matrix.transpose_mul]
      _ = left := by rw [middle_mul_basis, Matrix.transpose_transpose]
  let coefficient := Matrix.transpose middle
  have residue_factor :
      residue =
        Matrix.transpose basis * coefficient * basis := by
    calc
      residue = left * basis := left_mul_basis.symm
      _ = (Matrix.transpose basis * Matrix.transpose middle) * basis := by
        rw [left_factor]
      _ = Matrix.transpose basis * coefficient * basis := rfl
  have residue_rank_le_coefficient :
      residue.rank ≤ coefficient.rank := by
    rw [residue_factor]
    exact (Matrix.rank_mul_le_left _ _).trans
      (Matrix.rank_mul_le_right _ _)
  have coefficient_rank :
      coefficient.rank = Fintype.card (Fin n) := by
    apply le_antisymm (Matrix.rank_le_card_width coefficient)
    rw [Fintype.card_fin]
    calc
      n = residueRank (target : ActionMatrix m) := rank_eq
      _ = residue.rank := by
        exact (rank_residueMatrix (target : ActionMatrix m)).symm
      _ ≤ coefficient.rank := residue_rank_le_coefficient
  have coefficient_independent :
      LinearIndependent F2 coefficient.row := by
    rw [linearIndependent_iff_card_eq_finrank_span,
      Set.finrank, ← Matrix.rank_eq_finrank_span_row]
    exact coefficient_rank.symm
  refine ⟨coefficient,
    Matrix.linearIndependent_rows_iff_isUnit.mp coefficient_independent, ?_⟩
  exact residue_factor

theorem exists_residue_coefficient {m : ℕ}
    (target : SymplecticAction m) :
    ∃ coefficient :
        Matrix (Fin (residueRank (target : ActionMatrix m)))
          (Fin (residueRank (target : ActionMatrix m))) F2,
      IsUnit coefficient ∧
        residueMatrix (target : ActionMatrix m) =
          Matrix.transpose (residueBasisMatrix target) * coefficient *
            residueBasisMatrix target :=
  exists_residue_coefficient_of_basis target rfl
    (residueBasisMatrix target) (residueBasisMatrix_independent target)
    (residueBasisMatrix_span target)

noncomputable def canonicalCorePresentation {m : ℕ}
    (target : SymplecticAction m) :
    CorePresentation target (residueRank (target : ActionMatrix m)) := by
  choose coefficient coefficient_unit residue_eq using
    exists_residue_coefficient target
  exact
    { rank_eq := rfl
      basis := residueBasisMatrix target
      basis_independent := residueBasisMatrix_independent target
      basis_span := residueBasisMatrix_span target
      coefficient
      coefficient_unit
      residue_eq }

theorem CorePresentation.coefficient_add_transpose {m : ℕ}
    {target : SymplecticAction m} {dimension : ℕ}
    (presentation : CorePresentation target dimension) :
    presentation.coefficient +
        Matrix.transpose presentation.coefficient =
      Matrix.transpose presentation.coefficient *
        (presentation.basis * omega m *
          Matrix.transpose presentation.basis) *
        presentation.coefficient := by
  have residue_identity := residueMatrix_add_transpose target
  rw [presentation.residue_eq] at residue_identity
  have factored :
      Matrix.transpose presentation.basis *
          (presentation.coefficient +
            Matrix.transpose presentation.coefficient) *
          presentation.basis =
        Matrix.transpose presentation.basis *
          (Matrix.transpose presentation.coefficient *
            (presentation.basis * omega m *
              Matrix.transpose presentation.basis) *
            presentation.coefficient) *
          presentation.basis := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] using
        residue_identity
  have basis_vecMul_injective :
      Function.Injective presentation.basis.vecMul :=
    Matrix.vecMul_injective_iff.mpr presentation.basis_independent
  have cancel_right :=
    mul_right_cancel_of_vecMul_injective presentation.basis
      (Matrix.transpose presentation.basis *
        (presentation.coefficient +
          Matrix.transpose presentation.coefficient))
      (Matrix.transpose presentation.basis *
        (Matrix.transpose presentation.coefficient *
          (presentation.basis * omega m *
            Matrix.transpose presentation.basis) *
          presentation.coefficient))
      basis_vecMul_injective factored
  exact mul_left_cancel_of_mulVec_injective
    (Matrix.transpose presentation.basis)
    (presentation.coefficient +
      Matrix.transpose presentation.coefficient)
    (Matrix.transpose presentation.coefficient *
      (presentation.basis * omega m *
        Matrix.transpose presentation.basis) *
      presentation.coefficient)
    (transpose_mulVec_injective_of_linearIndependent
      presentation.basis presentation.basis_independent)
    cancel_right

theorem CorePresentation.core_add_transpose {m : ℕ}
    {target : SymplecticAction m} {dimension : ℕ}
    (presentation : CorePresentation target dimension) :
    presentation.core + Matrix.transpose presentation.core =
      presentation.basis * omega m *
        Matrix.transpose presentation.basis := by
  have coefficient_det :
      IsUnit presentation.coefficient.det :=
    (Matrix.isUnit_iff_isUnit_det presentation.coefficient).mp
      presentation.coefficient_unit
  have transpose_det :
      IsUnit (Matrix.transpose presentation.coefficient).det :=
    Matrix.isUnit_det_transpose presentation.coefficient coefficient_det
  have sandwich :
      Matrix.transpose presentation.coefficient *
          (presentation.core + Matrix.transpose presentation.core) *
          presentation.coefficient =
        Matrix.transpose presentation.coefficient *
          (presentation.basis * omega m *
            Matrix.transpose presentation.basis) *
          presentation.coefficient := by
    rw [CorePresentation.core, Matrix.transpose_transpose,
      Matrix.mul_add, Matrix.add_mul,
      Matrix.transpose_nonsing_inv]
    rw [Matrix.mul_nonsing_inv
      (Matrix.transpose presentation.coefficient) transpose_det,
      Matrix.one_mul]
    rw [Matrix.mul_assoc,
      Matrix.nonsing_inv_mul presentation.coefficient coefficient_det,
      Matrix.mul_one]
    exact presentation.coefficient_add_transpose
  have coefficient_vecMul_injective :
      Function.Injective presentation.coefficient.vecMul :=
    Matrix.vecMul_injective_of_isUnit presentation.coefficient_unit
  have cancel_right :=
    mul_right_cancel_of_vecMul_injective presentation.coefficient
      (Matrix.transpose presentation.coefficient *
        (presentation.core + Matrix.transpose presentation.core))
      (Matrix.transpose presentation.coefficient *
        (presentation.basis * omega m *
          Matrix.transpose presentation.basis))
      coefficient_vecMul_injective sandwich
  exact mul_left_cancel_of_mulVec_injective
    (Matrix.transpose presentation.coefficient)
    (presentation.core + Matrix.transpose presentation.core)
    (presentation.basis * omega m *
      Matrix.transpose presentation.basis)
    (Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_transpose presentation.coefficient).mpr
        presentation.coefficient_unit))
    cancel_right

theorem CorePresentation.coreCongruence_add_transpose
    {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (basisChange : Matrix (Fin n) (Fin n) F2) :
    let centers : Fin n → PhaseVector m :=
      basisChange * presentation.basis
    basisChange * presentation.core *
          Matrix.transpose basisChange +
        Matrix.transpose
          (basisChange * presentation.core *
            Matrix.transpose basisChange) =
      centerMatrixFin centers * omega m *
        Matrix.transpose (centerMatrixFin centers) := by
  dsimp only
  rw [centerMatrixFin_eq]
  calc
    basisChange * presentation.core *
          Matrix.transpose basisChange +
        Matrix.transpose
          (basisChange * presentation.core *
            Matrix.transpose basisChange) =
      basisChange *
          (presentation.core +
            Matrix.transpose presentation.core) *
        Matrix.transpose basisChange := by
          simp [Matrix.transpose_mul, Matrix.mul_add,
            Matrix.add_mul, Matrix.mul_assoc]
    _ = basisChange *
          (presentation.basis * omega m *
            Matrix.transpose presentation.basis) *
        Matrix.transpose basisChange := by
          rw [presentation.core_add_transpose]
    _ = (basisChange * presentation.basis) * omega m *
        Matrix.transpose
          (basisChange * presentation.basis) := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem CorePresentation.coreCongruence_eq_pairing_of_lower
    {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (basisChange : Matrix (Fin n) (Fin n) F2)
    (lower :
      IsUnitLowerTriangular
        (basisChange * presentation.core *
          Matrix.transpose basisChange)) :
    let centers : Fin n → PhaseVector m :=
      basisChange * presentation.basis
    basisChange * presentation.core *
        Matrix.transpose basisChange =
      Matrix.transpose (pairingUpperFin centers) := by
  dsimp only
  apply isUnitLowerTriangular_ext
    lower
    (pairingUpperFin_transpose_isUnitLowerTriangular
      (basisChange * presentation.basis))
  calc
    basisChange * presentation.core *
          Matrix.transpose basisChange +
        Matrix.transpose
          (basisChange * presentation.core *
            Matrix.transpose basisChange) =
      centerMatrixFin (basisChange * presentation.basis) * omega m *
        Matrix.transpose
          (centerMatrixFin
            (basisChange * presentation.basis)) :=
      presentation.coreCongruence_add_transpose basisChange
    _ = pairingUpperFin (basisChange * presentation.basis) +
        Matrix.transpose
          (pairingUpperFin
            (basisChange * presentation.basis)) :=
      (pairingUpperFin_add_transpose
        (basisChange * presentation.basis)).symm
    _ = Matrix.transpose
          (pairingUpperFin
            (basisChange * presentation.basis)) +
        Matrix.transpose
          (Matrix.transpose
            (pairingUpperFin
              (basisChange * presentation.basis))) := by
      rw [Matrix.transpose_transpose, add_comm]

theorem CorePresentation.exists_unit_basisChange_of_factorization
    {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (centers : Fin n → PhaseVector m)
    (factorization :
      IsFactorization target (List.ofFn centers)) :
    ∃ basisChange : Matrix (Fin n) (Fin n) F2,
      IsUnit basisChange ∧
        basisChange * presentation.basis =
          centerMatrixFin centers := by
  have rank_eq_length :
      residueRank (target : ActionMatrix m) =
        (List.ofFn centers).length := by
    rw [← presentation.rank_eq]
    simp
  have listIndependent :=
    centerMatrix_linearIndependent_of_rank_eq_length
      target (List.ofFn centers) factorization rank_eq_length
  have centersIndependent :
      LinearIndependent F2 (centerMatrixFin centers) := by
    have reindexed := listIndependent.comp
      (ofFnIndexEquiv centers).symm
      (ofFnIndexEquiv centers).symm.injective
    have reindexed_eq :
        centerMatrix (List.ofFn centers) ∘
            (ofFnIndexEquiv centers).symm =
          centers := by
      ext index column
      simp [centerMatrix, ofFnIndexEquiv]
    rw [reindexed_eq] at reindexed
    rw [centerMatrixFin_eq]
    exact reindexed
  have residue_eq_centerSpan :=
    residueSpace_eq_centerSpan_of_rank_eq_length
      target (List.ofFn centers) factorization rank_eq_length
  have center_span_le :
      Submodule.span F2 (Set.range (centerMatrixFin centers)) ≤
        Submodule.span F2 (Set.range presentation.basis) := by
    rw [presentation.basis_span]
    refine Submodule.span_le.mpr ?_
    rintro vector ⟨index, rfl⟩
    rw [centerMatrixFin_eq, residue_eq_centerSpan]
    apply mem_centerSpan_of_mem
    simp
  obtain ⟨basisChange, basisChange_eq⟩ :=
    exists_mul_eq_of_span_rows_le
      (centerMatrixFin centers) presentation.basis center_span_le
  refine ⟨basisChange, ?_, basisChange_eq⟩
  apply Matrix.vecMul_injective_iff_isUnit.mp
  have centers_vecMul_injective :
      Function.Injective
        (fun vector =>
          Matrix.vecMul vector (centerMatrixFin centers)) :=
    Matrix.vecMul_injective_iff.mpr centersIndependent
  intro first second equal
  apply centers_vecMul_injective
  have composed := congrArg
    (fun vector => Matrix.vecMul vector presentation.basis) equal
  rw [← basisChange_eq]
  simpa only [Matrix.vecMul_vecMul] using composed

theorem CorePresentation.coefficient_eq_path_of_factorization
    {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (centers : Fin n → PhaseVector m)
    (factorization :
      IsFactorization target (List.ofFn centers))
    (basisChange : Matrix (Fin n) (Fin n) F2)
    (basisChange_eq :
      basisChange * presentation.basis = centerMatrixFin centers) :
    presentation.coefficient =
      Matrix.transpose basisChange * pathMatrixFin centers *
        basisChange := by
  have residue_eq :
      residueMatrix
          (productTransvections (List.ofFn centers) : ActionMatrix m) =
        residueMatrix (target : ActionMatrix m) :=
    congrArg residueMatrix (congrArg Subtype.val factorization)
  have sandwich :
      Matrix.transpose presentation.basis *
          presentation.coefficient * presentation.basis =
        Matrix.transpose presentation.basis *
          (Matrix.transpose basisChange * pathMatrixFin centers *
            basisChange) * presentation.basis := by
    calc
      Matrix.transpose presentation.basis *
          presentation.coefficient * presentation.basis =
        residueMatrix (target : ActionMatrix m) :=
          presentation.residue_eq.symm
      _ = residueMatrix
          (productTransvections
            (List.ofFn centers) : ActionMatrix m) :=
        residue_eq.symm
      _ = Matrix.transpose (centerMatrixFin centers) *
          pathMatrixFin centers * centerMatrixFin centers :=
        residueMatrix_product_ofFn_eq centers
      _ = Matrix.transpose presentation.basis *
          (Matrix.transpose basisChange * pathMatrixFin centers *
            basisChange) * presentation.basis := by
        rw [← basisChange_eq]
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have cancel_left :
      presentation.coefficient * presentation.basis =
        (Matrix.transpose basisChange * pathMatrixFin centers *
          basisChange) * presentation.basis := by
    apply mul_left_cancel_of_mulVec_injective
      (Matrix.transpose presentation.basis)
    · exact transpose_mulVec_injective_of_linearIndependent
        presentation.basis presentation.basis_independent
    · simpa only [Matrix.mul_assoc] using sandwich
  exact mul_right_cancel_of_vecMul_injective
    presentation.basis
    presentation.coefficient
    (Matrix.transpose basisChange * pathMatrixFin centers *
      basisChange)
    (Matrix.vecMul_injective_iff.mpr
      presentation.basis_independent)
    cancel_left

/-- A valid congruence triangularizer supplies the concrete ordered centers `Q V`. -/
theorem CorePresentation.factorization_of_triangularizer
    {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (basisChange : Matrix (Fin n) (Fin n) F2)
    (basisChange_unit : IsUnit basisChange)
    (lower :
      IsUnitLowerTriangular
        (basisChange * presentation.core * Matrix.transpose basisChange)) :
    IsFactorization target (List.ofFn (basisChange * presentation.basis)) := by
  let centers : Fin n → PhaseVector m := basisChange * presentation.basis
  have core_eq :
      basisChange * presentation.core * Matrix.transpose basisChange =
        Matrix.transpose (pairingUpperFin centers) := by
    simpa [centers] using
      presentation.coreCongruence_eq_pairing_of_lower basisChange lower
  have coefficient_eq :=
    (presentation.coefficient_eq_path_iff_core_eq_pairing
      centers basisChange basisChange_unit).mpr core_eq
  apply target_eq_of_residueMatrix_eq target
    (productTransvections (List.ofFn centers))
  rw [residueMatrix_product_ofFn_eq, presentation.residue_eq,
    coefficient_eq, centerMatrixFin_eq]
  simp [centers, Matrix.transpose_mul, Matrix.mul_assoc]

theorem CorePresentation.exists_factorization_iff_isTriangularizable
    {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n) :
    (∃ centers : Fin n → PhaseVector m,
      IsFactorization target (List.ofFn centers)) ↔
      presentation.IsTriangularizable := by
  constructor
  · rintro ⟨centers, factorization⟩
    obtain ⟨basisChange, basisChange_unit, basisChange_eq⟩ :=
      presentation.exists_unit_basisChange_of_factorization
        centers factorization
    refine ⟨basisChange, basisChange_unit, ?_⟩
    have coefficient_eq :=
      presentation.coefficient_eq_path_of_factorization
        centers factorization basisChange basisChange_eq
    have core_eq :=
      (presentation.coefficient_eq_path_iff_core_eq_pairing
        centers basisChange basisChange_unit).mp coefficient_eq
    rw [core_eq]
    exact pairingUpperFin_transpose_isUnitLowerTriangular centers
  · rintro ⟨basisChange, basisChange_unit, lower⟩
    exact ⟨basisChange * presentation.basis,
      presentation.factorization_of_triangularizer
        basisChange basisChange_unit lower⟩

theorem CorePresentation.isTriangularizable_iff_canonical
    {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n) :
    presentation.IsTriangularizable ↔
      (canonicalCorePresentation target).IsTriangularizable := by
  rw [← presentation.exists_factorization_iff_isTriangularizable,
    ← (canonicalCorePresentation target).exists_factorization_iff_isTriangularizable,
    presentation.rank_eq]

end PaulimerFormal
