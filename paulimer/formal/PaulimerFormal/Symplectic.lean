import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Binary symplectic matrices

The symplectic representation of an `m`-qubit Clifford uses row vectors over
`F2`, indexed by the `X` and `Z` halves `Fin m ⊕ Fin m`.
-/

namespace PaulimerFormal

open Matrix

abbrev F2 := ZMod 2

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev PhaseIndex (m : ℕ) := Fin m ⊕ Fin m

abbrev PhaseVector (m : ℕ) := PhaseIndex m → F2

abbrev ActionMatrix (m : ℕ) := Matrix (PhaseIndex m) (PhaseIndex m) F2

abbrev SymplecticAction (m : ℕ) := Matrix.symplecticGroup (Fin m) F2

@[simp]
theorem f2_add_self (value : F2) : value + value = 0 := by
  exact ZModModule.add_self value

@[simp]
theorem f2_neg (value : F2) : -value = value := by
  exact ZModModule.neg_eq_self value

/-- The standard symplectic form matrix. -/
def omega (m : ℕ) : ActionMatrix m := Matrix.J (Fin m) F2

@[simp]
theorem omega_transpose (m : ℕ) : (omega m)ᵀ = omega m := by
  rw [omega, Matrix.J_transpose]
  exact ZModModule.neg_eq_self _

@[simp]
theorem omega_squared (m : ℕ) : omega m * omega m = 1 := by
  rw [omega, Matrix.J_squared]
  exact ZModModule.neg_eq_self _

/-- The symplectic pairing `left * Ω * rightᵀ`. -/
def pairing {m : ℕ} (left right : PhaseVector m) : F2 :=
  left ⬝ᵥ (omega m).mulVec right

/-- Right action of a symplectic matrix on a row vector. -/
def rowAction {m : ℕ} (vector : PhaseVector m) (action : ActionMatrix m) :
    PhaseVector m :=
  vector ᵥ* action

@[simp]
theorem rowAction_one {m : ℕ} (vector : PhaseVector m) :
    rowAction vector (1 : ActionMatrix m) = vector := by
  simp [rowAction]

theorem rowAction_mul {m : ℕ} (vector : PhaseVector m)
    (left right : ActionMatrix m) :
    rowAction (rowAction vector left) right = rowAction vector (left * right) := by
  simp [rowAction]

theorem rowAction_add {m : ℕ} (first second : PhaseVector m)
    (action : ActionMatrix m) :
    rowAction (first + second) action =
      rowAction first action + rowAction second action := by
  simp [rowAction, Matrix.add_vecMul]

theorem rowAction_smul {m : ℕ} (scalar : F2) (vector : PhaseVector m)
    (action : ActionMatrix m) :
    rowAction (scalar • vector) action =
      scalar • rowAction vector action := by
  simp [rowAction, Matrix.smul_vecMul]

/-- The symplectic transvection `T_v = I + Ω vᵀ v`. -/
def transvection {m : ℕ} (center : PhaseVector m) : ActionMatrix m :=
  1 + Matrix.vecMulVec ((omega m).mulVec center) center

/-- Whether a matrix preserves the standard symplectic form. -/
def IsSymplectic {m : ℕ} (action : ActionMatrix m) : Prop :=
  action ∈ Matrix.symplecticGroup (Fin m) F2

/-- The residue matrix `F̂ = Ω(I + F)`. -/
def residueMatrix {m : ℕ} (action : ActionMatrix m) : ActionMatrix m :=
  omega m * (1 + action)

/-- The fixed space `ker(I + F)` for the row action over `F2`. -/
def fixedSpace {m : ℕ} (action : ActionMatrix m) : Submodule F2 (PhaseVector m) :=
  LinearMap.ker (1 + action).vecMulLinear

/-- The residue space, represented as the span of the rows of `I + F`. -/
def residueSpace {m : ℕ} (action : ActionMatrix m) : Submodule F2 (PhaseVector m) :=
  Submodule.span F2 (Set.range (1 + action).row)

/-- The residue rank, i.e. the dimension of the row space of `I + F`. -/
noncomputable def residueRank {m : ℕ} (action : ActionMatrix m) : ℕ :=
  Module.finrank F2 (residueSpace action)

theorem span_rows_mul_le_right {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n]
    (left : Matrix l m F2) (right : Matrix m n F2) :
    Submodule.span F2 (Set.range (left * right).row) ≤
      Submodule.span F2 (Set.range right.row) := by
  rw [← range_vecMulLinear, ← range_vecMulLinear]
  rintro _ ⟨vector, rfl⟩
  refine ⟨vector ᵥ* left, ?_⟩
  exact Matrix.vecMul_vecMul vector left right

theorem exists_mul_eq_of_span_rows_le {l m n : Type*}
    [Fintype l] [Fintype m] [Fintype n]
    (left : Matrix l n F2) (right : Matrix m n F2)
    (containment :
      Submodule.span F2 (Set.range left.row) ≤
        Submodule.span F2 (Set.range right.row)) :
    ∃ coefficients : Matrix l m F2, coefficients * right = left := by
  classical
  have coefficient_exists (row : l) :
      ∃ coefficients : m → F2,
        ∑ index, coefficients index • right.row index = left.row row := by
    apply (Submodule.mem_span_range_iff_exists_fun F2).mp
    exact containment (Submodule.subset_span (Set.mem_range_self row))
  choose coefficients coefficient_eq using coefficient_exists
  refine ⟨coefficients, ?_⟩
  ext row column
  have entry_eq := congrFun (coefficient_eq row) column
  simpa [Matrix.mul_apply] using entry_eq

theorem one_add_eq_omega_mul_residueMatrix {m : ℕ}
    (action : ActionMatrix m) :
    1 + action = omega m * residueMatrix action := by
  rw [residueMatrix, ← Matrix.mul_assoc, omega_squared, Matrix.one_mul]

theorem residueMatrix_injective {m : ℕ} :
    Function.Injective (residueMatrix :
      ActionMatrix m → ActionMatrix m) := by
  intro first second equal_residue
  apply add_left_cancel (a := (1 : ActionMatrix m))
  rw [one_add_eq_omega_mul_residueMatrix,
    one_add_eq_omega_mul_residueMatrix, equal_residue]

theorem residueSpace_eq_span_rows_residueMatrix {m : ℕ}
    (action : ActionMatrix m) :
    residueSpace action =
      Submodule.span F2 (Set.range (residueMatrix action).row) := by
  apply le_antisymm
  · rw [residueSpace, one_add_eq_omega_mul_residueMatrix]
    exact span_rows_mul_le_right (omega m) (residueMatrix action)
  · rw [residueSpace, residueMatrix]
    exact span_rows_mul_le_right (omega m) (1 + action)

theorem residueRank_eq_finrank_span_rows_residueMatrix {m : ℕ}
    (action : ActionMatrix m) :
    residueRank action =
      Module.finrank F2
        (Submodule.span F2 (Set.range (residueMatrix action).row)) := by
  rw [residueRank, residueSpace_eq_span_rows_residueMatrix]

theorem rank_residueMatrix {m : ℕ} (action : ActionMatrix m) :
    (residueMatrix action).rank = residueRank action := by
  rw [Matrix.rank_eq_finrank_span_row]
  exact (residueRank_eq_finrank_span_rows_residueMatrix action).symm

theorem rank_one_add {m : ℕ} (action : ActionMatrix m) :
    (1 + action).rank = residueRank action := by
  rw [Matrix.rank_eq_finrank_span_row]
  rfl

theorem rank_mul_eq_right_of_mulVec_injective
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    (left : Matrix l m F2) (right : Matrix m n F2)
    (injective : Function.Injective left.mulVec) :
    (left * right).rank = right.rank := by
  let restricted :=
    left.mulVecLin.domRestrict (LinearMap.range right.mulVecLin)
  have restricted_injective : Function.Injective restricted := by
    intro first second equal
    exact Subtype.ext (injective equal)
  rw [Matrix.rank, Matrix.rank, Matrix.mulVecLin_mul,
    LinearMap.range_comp, ← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj restricted_injective

theorem transpose_mulVec_injective_of_linearIndependent
    {m n : Type*} [Fintype m] [Fintype n]
    (matrix : Matrix m n F2)
    (independent : LinearIndependent F2 matrix) :
    Function.Injective matrix.transpose.mulVec := by
  intro first second equal
  apply (Matrix.vecMul_injective_iff.mpr independent)
  simpa only [Matrix.mulVec_transpose] using equal

theorem mul_left_cancel_of_mulVec_injective
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    (left : Matrix l m F2) (first second : Matrix m n F2)
    (injective : Function.Injective left.mulVec)
    (equal : left * first = left * second) :
    first = second := by
  ext row column
  have column_eq : first.col column = second.col column := by
    apply injective
    ext index
    exact congrFun (congrFun equal index) column
  exact congrFun column_eq row

theorem mul_right_cancel_of_vecMul_injective
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    (right : Matrix m n F2) (first second : Matrix l m F2)
    (injective : Function.Injective right.vecMul)
    (equal : first * right = second * right) :
    first = second := by
  ext row column
  have row_eq : Matrix.vecMul (first.row row) right =
      Matrix.vecMul (second.row row) right := by
    ext index
    exact congrFun (congrFun equal row) index
  exact congrFun (injective row_eq) column

theorem residueMatrix_transpose_eq {m : ℕ}
    (action : SymplecticAction m) :
    (residueMatrix (action : ActionMatrix m))ᵀ =
      (action : ActionMatrix m)ᵀ * residueMatrix action := by
  have symplectic :
      (action : ActionMatrix m)ᵀ * omega m *
        (action : ActionMatrix m) = omega m := by
    exact SymplecticGroup.mem_iff'.mp action.property
  rw [residueMatrix, Matrix.transpose_mul, Matrix.transpose_add,
    Matrix.transpose_one, omega_transpose]
  calc
    (1 + (action : ActionMatrix m)ᵀ) * omega m =
        omega m + (action : ActionMatrix m)ᵀ * omega m := by
      rw [Matrix.add_mul, Matrix.one_mul]
    _ = (action : ActionMatrix m)ᵀ * omega m + omega m :=
      add_comm _ _
    _ = (action : ActionMatrix m)ᵀ * omega m +
        ((action : ActionMatrix m)ᵀ * omega m) *
          (action : ActionMatrix m) := by
      rw [symplectic]
    _ = (action : ActionMatrix m)ᵀ *
        (omega m + omega m * (action : ActionMatrix m)) := by
      rw [Matrix.mul_add, Matrix.mul_assoc]
    _ = (action : ActionMatrix m)ᵀ *
        (omega m * (1 + (action : ActionMatrix m))) := by
      simp only [Matrix.mul_add, Matrix.mul_one]

theorem span_rows_residueMatrix_transpose {m : ℕ}
    (action : SymplecticAction m) :
    Submodule.span F2
        (Set.range (residueMatrix (action : ActionMatrix m))ᵀ.row) =
      Submodule.span F2
        (Set.range (residueMatrix (action : ActionMatrix m)).row) := by
  have containment :
      Submodule.span F2
          (Set.range (residueMatrix (action : ActionMatrix m))ᵀ.row) ≤
        Submodule.span F2
          (Set.range (residueMatrix (action : ActionMatrix m)).row) := by
    rw [residueMatrix_transpose_eq]
    exact span_rows_mul_le_right
      (action : ActionMatrix m)ᵀ (residueMatrix action)
  refine Submodule.eq_of_le_of_finrank_eq (K := F2) containment ?_
  rw [← Matrix.rank_eq_finrank_span_row,
    ← Matrix.rank_eq_finrank_span_row, Matrix.rank_transpose]

theorem residueMatrix_add_transpose {m : ℕ}
    (action : SymplecticAction m) :
    residueMatrix (action : ActionMatrix m) +
        Matrix.transpose (residueMatrix action) =
      Matrix.transpose (residueMatrix action) * omega m *
        residueMatrix action := by
  have symplectic :
      (action : ActionMatrix m)ᵀ * omega m *
        (action : ActionMatrix m) = omega m :=
    SymplecticGroup.mem_iff'.mp action.property
  have left_expansion :
      residueMatrix (action : ActionMatrix m) +
          Matrix.transpose (residueMatrix action) =
        omega m * (action : ActionMatrix m) +
          (action : ActionMatrix m)ᵀ * omega m := by
    rw [residueMatrix, Matrix.transpose_mul, Matrix.transpose_add,
      Matrix.transpose_one, omega_transpose, Matrix.mul_add,
      Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
    calc
      omega m + omega m * (action : ActionMatrix m) +
          (omega m + (action : ActionMatrix m)ᵀ * omega m) =
        (omega m + omega m) +
          (omega m * (action : ActionMatrix m) +
            (action : ActionMatrix m)ᵀ * omega m) := by
          abel
      _ = omega m * (action : ActionMatrix m) +
          (action : ActionMatrix m)ᵀ * omega m := by
        rw [ZModModule.add_self, zero_add]
  have right_reduction :
      Matrix.transpose (residueMatrix action) * omega m *
          residueMatrix action =
        (1 + (action : ActionMatrix m)ᵀ) * omega m *
          (1 + (action : ActionMatrix m)) := by
    rw [residueMatrix, Matrix.transpose_mul, Matrix.transpose_add,
      Matrix.transpose_one, omega_transpose]
    calc
      (1 + (action : ActionMatrix m)ᵀ) * omega m * omega m *
          (omega m * (1 + (action : ActionMatrix m))) =
        ((1 + (action : ActionMatrix m)ᵀ) * (omega m * omega m)) *
          (omega m * (1 + (action : ActionMatrix m))) := by
        exact congrArg
          (fun matrix => matrix *
            (omega m * (1 + (action : ActionMatrix m))))
          (Matrix.mul_assoc
            (1 + (action : ActionMatrix m)ᵀ) (omega m) (omega m))
      _ = ((1 + (action : ActionMatrix m)ᵀ) * 1) *
          (omega m * (1 + (action : ActionMatrix m))) := by
        rw [omega_squared]
      _ = (1 + (action : ActionMatrix m)ᵀ) *
          (omega m * (1 + (action : ActionMatrix m))) := by
        rw [Matrix.mul_one]
      _ = (1 + (action : ActionMatrix m)ᵀ) * omega m *
          (1 + (action : ActionMatrix m)) := by
        exact (Matrix.mul_assoc
          (1 + (action : ActionMatrix m)ᵀ) (omega m)
          (1 + (action : ActionMatrix m))).symm
  rw [left_expansion, right_reduction]
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
    Matrix.mul_one, Matrix.add_mul]
  rw [symplectic]
  symm
  calc
    omega m + (action : ActionMatrix m)ᵀ * omega m +
        (omega m * (action : ActionMatrix m) + omega m) =
      (omega m + omega m) +
        (omega m * (action : ActionMatrix m) +
          (action : ActionMatrix m)ᵀ * omega m) := by
      abel
    _ = omega m * (action : ActionMatrix m) +
        (action : ActionMatrix m)ᵀ * omega m := by
      rw [ZModModule.add_self, zero_add]

theorem mem_fixedSpace_iff {m : ℕ} (action : ActionMatrix m)
    (vector : PhaseVector m) :
    vector ∈ fixedSpace action ↔ rowAction vector action = vector := by
  rw [fixedSpace, LinearMap.mem_ker]
  change vector ᵥ* (1 + action) = 0 ↔ rowAction vector action = vector
  rw [Matrix.vecMul_add, Matrix.vecMul_one]
  constructor
  · intro sum_zero
    have equals_negative := eq_neg_of_add_eq_zero_left sum_zero
    simpa [rowAction, ZModModule.neg_eq_self] using equals_negative.symm
  · intro fixed
    rw [rowAction] at fixed
    rw [fixed]
    exact ZModModule.add_self vector

@[simp]
theorem pairing_self {m : ℕ} (vector : PhaseVector m) :
    pairing vector vector = 0 := by
  simp [pairing, omega, Matrix.J, Matrix.fromBlocks_mulVec, Matrix.dotProduct_block,
    Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_comm]

theorem pairing_comm {m : ℕ} (left right : PhaseVector m) :
    pairing left right = pairing right left := by
  rw [pairing, pairing, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    omega_transpose, dotProduct_comm]

theorem pairing_add_left {m : ℕ} (first second right : PhaseVector m) :
    pairing (first + second) right = pairing first right + pairing second right := by
  simp [pairing, add_dotProduct]

theorem pairing_add_right {m : ℕ} (left first second : PhaseVector m) :
    pairing left (first + second) = pairing left first + pairing left second := by
  simp [pairing, Matrix.mulVec_add, dotProduct_add]

theorem pairing_smul_left {m : ℕ} (scalar : F2) (left right : PhaseVector m) :
    pairing (scalar • left) right = scalar * pairing left right := by
  simp [pairing, smul_dotProduct]

theorem pairing_smul_right {m : ℕ} (scalar : F2) (left right : PhaseVector m) :
    pairing left (scalar • right) = scalar * pairing left right := by
  simp [pairing, Matrix.mulVec_smul, dotProduct_smul]

theorem rowAction_transvection {m : ℕ} (vector center : PhaseVector m) :
    rowAction vector (transvection center) =
      vector + pairing vector center • center := by
  rw [rowAction, transvection, pairing, Matrix.vecMul_add, Matrix.vecMul_one,
    Matrix.vecMul_vecMulVec]

theorem pairing_rowAction_transvection {m : ℕ}
    (left right center : PhaseVector m) :
    pairing (rowAction left (transvection center))
        (rowAction right (transvection center)) =
      pairing left right := by
  rw [rowAction_transvection, rowAction_transvection]
  simp only [pairing_add_left, pairing_add_right, pairing_smul_left,
    pairing_smul_right, pairing_self, mul_zero, add_zero]
  rw [pairing_comm center right,
    mul_comm (pairing right center) (pairing left center), add_assoc,
    f2_add_self, add_zero]

theorem pairing_rowAction {m : ℕ} {action : ActionMatrix m}
    (symplectic : IsSymplectic action) (left right : PhaseVector m) :
    pairing (rowAction left action) (rowAction right action) =
      pairing left right := by
  rw [pairing, rowAction, rowAction, omega,
    ← Matrix.mulVec_transpose action right,
    Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.mul_assoc, SymplecticGroup.mem_iff.mp symplectic,
    ← Matrix.dotProduct_mulVec]
  rfl

theorem transvection_isSymplectic {m : ℕ} (center : PhaseVector m) :
    IsSymplectic (transvection center) := by
  rw [IsSymplectic, SymplecticGroup.mem_iff]
  ext i j
  have preserves := pairing_rowAction_transvection
    (Pi.single i 1) (Pi.single j 1) center
  simpa [rowAction, pairing, omega, Matrix.mul_mul_apply, Matrix.row_apply'] using preserves

/-- A symplectic transvection as an element of the symplectic group. -/
def transvectionAction {m : ℕ} (center : PhaseVector m) : SymplecticAction m :=
  ⟨transvection center, transvection_isSymplectic center⟩

@[simp]
theorem coe_transvectionAction {m : ℕ} (center : PhaseVector m) :
    (transvectionAction center : ActionMatrix m) = transvection center := rfl

theorem rowAction_conjugate_transvection {m : ℕ}
    {action inverse : ActionMatrix m}
    (symplectic : IsSymplectic action)
    (inverse_left : inverse * action = 1)
    (vector center : PhaseVector m) :
    rowAction vector (inverse * transvection center * action) =
      rowAction vector (transvection (rowAction center action)) := by
  have coefficient :
      pairing (rowAction vector inverse) center =
        pairing vector (rowAction center action) := by
    calc
      pairing (rowAction vector inverse) center =
          pairing (rowAction (rowAction vector inverse) action)
            (rowAction center action) := by
        symm
        exact pairing_rowAction symplectic _ _
      _ = pairing vector (rowAction center action) := by
        rw [rowAction_mul, inverse_left, rowAction_one]
  calc
    rowAction vector (inverse * transvection center * action) =
        rowAction (rowAction (rowAction vector inverse)
          (transvection center)) action := by
      rw [rowAction_mul, rowAction_mul, Matrix.mul_assoc]
    _ = rowAction
          (rowAction vector inverse + pairing (rowAction vector inverse) center • center)
          action := by
      rw [rowAction_transvection]
    _ = rowAction (rowAction vector inverse) action +
          pairing (rowAction vector inverse) center • rowAction center action := by
      rw [rowAction_add, rowAction_smul]
    _ = vector + pairing vector (rowAction center action) •
          rowAction center action := by
      rw [rowAction_mul, inverse_left, rowAction_one, coefficient]
    _ = rowAction vector (transvection (rowAction center action)) := by
      symm
      exact rowAction_transvection _ _

theorem conjugate_transvection {m : ℕ}
    {action inverse : ActionMatrix m}
    (symplectic : IsSymplectic action)
    (inverse_left : inverse * action = 1)
    (center : PhaseVector m) :
    inverse * transvection center * action =
      transvection (rowAction center action) := by
  ext i j
  have acts_equally := rowAction_conjugate_transvection symplectic inverse_left
    (Pi.single i 1) center
  simpa [rowAction, Matrix.row_apply'] using congrFun acts_equally j

theorem conjugate_transvectionAction {m : ℕ}
    (action : SymplecticAction m) (center : PhaseVector m) :
    (↑action⁻¹ : ActionMatrix m) * transvection center * action =
      transvection (rowAction center action) := by
  apply conjugate_transvection action.property
  exact congrArg Subtype.val (Group.inv_mul_cancel action)

@[simp]
theorem transvection_zero {m : ℕ} :
    transvection (0 : PhaseVector m) = 1 := by
  simp [transvection]

@[simp]
theorem transvection_squared {m : ℕ} (center : PhaseVector m) :
    transvection center * transvection center = 1 := by
  let outer := Matrix.vecMulVec ((omega m).mulVec center) center
  have outer_squared : outer * outer = 0 := by
    dsimp [outer]
    rw [Matrix.vecMulVec_mul_vecMulVec]
    have isotropic : center ⬝ᵥ (omega m).mulVec center = 0 := by
      simpa [pairing] using pairing_self center
    rw [isotropic]
    simp
  change (1 + outer) * (1 + outer) = 1
  have outer_add_self : outer + outer = 0 := by
    ext i j
    exact f2_add_self (outer i j)
  calc
    (1 + outer) * (1 + outer) = 1 + outer + outer + outer * outer := by
      simp only [add_mul, mul_add, one_mul, mul_one, add_assoc]
    _ = 1 := by
      rw [outer_squared, add_zero, add_assoc, outer_add_self, add_zero]

example : (0 : F2) ≠ 1 := by decide

end PaulimerFormal
