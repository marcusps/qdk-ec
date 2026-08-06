import Mathlib.LinearAlgebra.Matrix.Reindex
import PaulimerFormal.Symplectic

/-!
# Ordered transvection products

The list order matches paulimer's replay convention: `[u, v]` denotes
`T_u * T_v`, so a row vector encounters `T_u` before `T_v`.
-/

namespace PaulimerFormal

/-- The ordered product of the transvections with the given centers. -/
def productTransvections {m : ℕ} (centers : List (PhaseVector m)) :
    SymplecticAction m :=
  (centers.map transvectionAction).prod

/-- A list of centers is a factorization when its ordered product is the target. -/
def IsFactorization {m : ℕ} (target : SymplecticAction m)
    (centers : List (PhaseVector m)) : Prop :=
  productTransvections centers = target

/-- Replays centers in the same order as paulimer. -/
def replay {m : ℕ} (centers : List (PhaseVector m)) (vector : PhaseVector m) :
    PhaseVector m :=
  centers.foldl (fun current center => rowAction current (transvection center)) vector

@[simp]
theorem productTransvections_nil {m : ℕ} :
    productTransvections ([] : List (PhaseVector m)) = 1 := by
  simp [productTransvections]

@[simp]
theorem productTransvections_cons {m : ℕ} (center : PhaseVector m)
    (centers : List (PhaseVector m)) :
    productTransvections (center :: centers) =
      transvectionAction center * productTransvections centers := by
  simp [productTransvections]

theorem productTransvections_append {m : ℕ}
    (first second : List (PhaseVector m)) :
    productTransvections (first ++ second) =
      productTransvections first * productTransvections second := by
  simp [productTransvections, List.prod_append]

theorem productTransvections_pair {m : ℕ} (first second : PhaseVector m) :
    (productTransvections [first, second] : ActionMatrix m) =
      transvection first * transvection second := by
  simp [productTransvections]

theorem replay_eq_rowAction_product {m : ℕ}
    (centers : List (PhaseVector m)) (vector : PhaseVector m) :
    replay centers vector = rowAction vector (productTransvections centers) := by
  induction centers generalizing vector with
  | nil =>
      simp [replay]
  | cons center centers inductionHypothesis =>
      simp only [replay, List.foldl_cons, productTransvections_cons]
      change replay centers (rowAction vector (transvection center)) =
        rowAction vector
          (transvection center * (productTransvections centers : ActionMatrix m))
      rw [inductionHypothesis, rowAction_mul]

theorem residueMatrix_product_cons {m : ℕ} (center : PhaseVector m)
    (centers : List (PhaseVector m)) :
    residueMatrix (productTransvections (center :: centers) : ActionMatrix m) =
      residueMatrix (productTransvections centers : ActionMatrix m) +
        Matrix.vecMulVec center (replay centers center) := by
  change omega m *
      (1 + (1 + Matrix.vecMulVec ((omega m).mulVec center) center) *
        (productTransvections centers : ActionMatrix m)) = _
  rw [add_mul, one_mul, ← add_assoc, mul_add]
  change residueMatrix (productTransvections centers : ActionMatrix m) +
      omega m *
        (Matrix.vecMulVec ((omega m).mulVec center) center *
          (productTransvections centers : ActionMatrix m)) = _
  rw [← Matrix.mul_assoc, Matrix.mul_vecMulVec,
    Matrix.mulVec_mulVec, omega_squared, Matrix.one_mulVec,
    Matrix.vecMulVec_mul, replay_eq_rowAction_product, rowAction]

/-- The matrix whose rows are the centers in list order. -/
def centerMatrix {m : ℕ} (centers : List (PhaseVector m)) :
    Matrix (Fin centers.length) (PhaseIndex m) F2 :=
  fun row => centers.get row

/-- Coefficients of the centers accumulated while replaying a vector. -/
def replayCoefficients {m : ℕ} :
    (centers : List (PhaseVector m)) →
      PhaseVector m → Fin centers.length → F2
  | [], _ => Fin.elim0
  | center :: centers, vector =>
      Fin.cons (pairing vector center)
        (replayCoefficients centers
          (rowAction vector (transvection center)))

theorem vecMul_centerMatrix_cons {m : ℕ} (scalar : F2)
    (center : PhaseVector m) (centers : List (PhaseVector m))
    (coefficients : Fin centers.length → F2) :
    Matrix.vecMul (Fin.cons scalar coefficients)
        (centerMatrix (center :: centers)) =
      scalar • center + Matrix.vecMul coefficients (centerMatrix centers) := by
  ext column
  simp [Matrix.vecMul, dotProduct, centerMatrix, Fin.sum_univ_succ]

theorem replay_eq_add_vecMul_centerMatrix {m : ℕ}
    (centers : List (PhaseVector m)) (vector : PhaseVector m) :
    replay centers vector =
      vector +
        Matrix.vecMul (replayCoefficients centers vector)
          (centerMatrix centers) := by
  induction centers generalizing vector with
  | nil =>
      simp [replay, replayCoefficients]
  | cons center centers inductionHypothesis =>
      simp only [replay, List.foldl_cons]
      change replay centers (rowAction vector (transvection center)) = _
      rw [inductionHypothesis]
      rw [replayCoefficients, vecMul_centerMatrix_cons,
        rowAction_transvection]
      abel

/-- The unit-upper coefficient matrix of all increasing interaction paths. -/
def pathMatrix {m : ℕ} :
    (centers : List (PhaseVector m)) →
      Matrix (Fin centers.length) (Fin centers.length) F2
  | [], row => Fin.elim0 row
  | center :: centers, row =>
      Fin.cases
        (Fin.cons 1 (replayCoefficients centers center))
        (fun tailRow => Fin.cons 0 (pathMatrix centers tailRow))
        row

@[simp]
theorem pathMatrix_cons_zero_zero {m : ℕ} (center : PhaseVector m)
    (centers : List (PhaseVector m)) :
    pathMatrix (center :: centers) 0 0 = 1 := rfl

@[simp]
theorem pathMatrix_cons_zero_succ {m : ℕ} (center : PhaseVector m)
    (centers : List (PhaseVector m)) (column : Fin centers.length) :
    pathMatrix (center :: centers) 0 column.succ =
      replayCoefficients centers center column := rfl

@[simp]
theorem pathMatrix_cons_succ_zero {m : ℕ} (center : PhaseVector m)
    (centers : List (PhaseVector m)) (row : Fin centers.length) :
    pathMatrix (center :: centers) row.succ 0 = 0 := rfl

@[simp]
theorem pathMatrix_cons_succ_succ {m : ℕ} (center : PhaseVector m)
    (centers : List (PhaseVector m)) (row column : Fin centers.length) :
    pathMatrix (center :: centers) row.succ column.succ =
      pathMatrix centers row column := rfl

theorem pathMatrix_diagonal {m : ℕ} (centers : List (PhaseVector m))
    (index : Fin centers.length) :
    pathMatrix centers index index = 1 := by
  induction centers with
  | nil => exact Fin.elim0 index
  | cons center centers inductionHypothesis =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · exact pathMatrix_cons_zero_zero center centers
      · exact inductionHypothesis tailIndex

theorem pathMatrix_below_diagonal {m : ℕ}
    (centers : List (PhaseVector m)) (row column : Fin centers.length)
    (below : column < row) :
    pathMatrix centers row column = 0 := by
  induction centers with
  | nil => exact Fin.elim0 row
  | cons center centers inductionHypothesis =>
      revert column
      refine Fin.cases ?_ (fun tailRow => ?_) row
      · intro column below
        exact (Fin.not_lt_zero column below).elim
      · intro column
        refine Fin.cases ?_ (fun tailColumn => ?_) column
        · intro _
          exact pathMatrix_cons_succ_zero center centers tailRow
        · intro below
          exact inductionHypothesis tailRow tailColumn
              (Fin.succ_lt_succ_iff.mp below)

theorem pathMatrix_blockTriangular {m : ℕ}
    (centers : List (PhaseVector m)) :
    (pathMatrix centers).BlockTriangular id := by
  intro row column below
  exact pathMatrix_below_diagonal centers row column below

theorem pathMatrix_det {m : ℕ} (centers : List (PhaseVector m)) :
    (pathMatrix centers).det = 1 := by
  rw [Matrix.det_of_upperTriangular
    (pathMatrix_blockTriangular centers)]
  simp [pathMatrix_diagonal]

theorem pathMatrix_isUnit {m : ℕ}
    (centers : List (PhaseVector m)) :
    IsUnit (pathMatrix centers) := by
  rw [Matrix.isUnit_iff_isUnit_det, pathMatrix_det]
  exact isUnit_one

/-- The direct unit-upper matrix of pairings between ordered centers. -/
def pairingUpper {m : ℕ} :
    (centers : List (PhaseVector m)) →
      Matrix (Fin centers.length) (Fin centers.length) F2
  | [], row => Fin.elim0 row
  | center :: centers, row =>
      Fin.cases
        (Fin.cons 1 (fun column => pairing center (centers.get column)))
        (fun tailRow => Fin.cons 0 (pairingUpper centers tailRow))
        row

@[simp]
theorem pairingUpper_cons_zero_zero {m : ℕ} (center : PhaseVector m)
    (centers : List (PhaseVector m)) :
    pairingUpper (center :: centers) 0 0 = 1 := rfl

@[simp]
theorem pairingUpper_cons_zero_succ {m : ℕ} (center : PhaseVector m)
    (centers : List (PhaseVector m)) (column : Fin centers.length) :
    pairingUpper (center :: centers) 0 column.succ =
      pairing center (centers.get column) := rfl

@[simp]
theorem pairingUpper_cons_succ_zero {m : ℕ} (center : PhaseVector m)
    (centers : List (PhaseVector m)) (row : Fin centers.length) :
    pairingUpper (center :: centers) row.succ 0 = 0 := rfl

@[simp]
theorem pairingUpper_cons_succ_succ {m : ℕ} (center : PhaseVector m)
    (centers : List (PhaseVector m)) (row column : Fin centers.length) :
    pairingUpper (center :: centers) row.succ column.succ =
      pairingUpper centers row column := rfl

theorem pairingUpper_apply {m : ℕ} (centers : List (PhaseVector m))
    (row column : Fin centers.length) :
    pairingUpper centers row column =
      if row = column then 1
      else if row < column then
        pairing (centers.get row) (centers.get column)
      else 0 := by
  induction centers with
  | nil => exact Fin.elim0 row
  | cons center centers inductionHypothesis =>
      revert column
      refine Fin.cases ?_ (fun tailRow => ?_) row
      · intro column
        refine Fin.cases ?_ (fun tailColumn => ?_) column
        · simp
        · rw [if_neg (Fin.succ_ne_zero tailColumn).symm,
            if_pos (Fin.succ_pos tailColumn)]
          rfl
      · intro column
        refine Fin.cases ?_ (fun tailColumn => ?_) column
        · simp
        · simpa using inductionHypothesis tailRow tailColumn

theorem vecMul_pairingUpper_cons {m : ℕ} (scalar : F2)
    (center : PhaseVector m) (centers : List (PhaseVector m))
    (coefficients : Fin centers.length → F2) :
    Matrix.vecMul (Fin.cons scalar coefficients)
        (pairingUpper (center :: centers)) =
      Fin.cons scalar (fun column =>
        scalar * pairing center (centers.get column) +
          Matrix.vecMul coefficients (pairingUpper centers) column) := by
  ext column
  refine Fin.cases ?_ (fun tailColumn => ?_) column
  · simp [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]
  · simp [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_succ]

theorem replayCoefficients_vecMul_pairingUpper {m : ℕ}
    (centers : List (PhaseVector m)) (vector : PhaseVector m) :
    Matrix.vecMul (replayCoefficients centers vector)
        (pairingUpper centers) =
      fun column => pairing vector (centers.get column) := by
  induction centers generalizing vector with
  | nil =>
      ext column
      exact Fin.elim0 column
  | cons center centers inductionHypothesis =>
      rw [replayCoefficients, vecMul_pairingUpper_cons]
      ext column
      refine Fin.cases ?_ (fun tailColumn => ?_) column
      · rfl
      · rw [Fin.cons_succ, inductionHypothesis]
        change pairing vector center * pairing center (centers.get tailColumn) +
            pairing (rowAction vector (transvection center))
              (centers.get tailColumn) =
          pairing vector (centers.get tailColumn)
        rw [rowAction_transvection, pairing_add_left,
          pairing_smul_left]
        rw [add_comm (pairing vector (centers.get tailColumn)),
          ← add_assoc, f2_add_self, zero_add]

theorem pathMatrix_mul_pairingUpper {m : ℕ}
    (centers : List (PhaseVector m)) :
    pathMatrix centers * pairingUpper centers = 1 := by
  induction centers with
  | nil =>
      ext row
      exact Fin.elim0 row
  | cons center centers inductionHypothesis =>
      ext row column
      revert column
      refine Fin.cases ?_ (fun tailRow => ?_) row
      · intro column
        refine Fin.cases ?_ (fun tailColumn => ?_) column
        · simp [Matrix.mul_apply, Fin.sum_univ_succ]
        · have coefficient_eq :=
            congrFun
              (replayCoefficients_vecMul_pairingUpper centers center)
              tailColumn
          rw [Matrix.one_apply,
            if_neg (Fin.succ_ne_zero tailColumn).symm]
          simpa [Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
            Fin.sum_univ_succ] using
              congrArg
                (fun value =>
                  pairing center (centers.get tailColumn) + value)
                coefficient_eq
      · intro column
        refine Fin.cases ?_ (fun tailColumn => ?_) column
        · simp [Matrix.mul_apply, Fin.sum_univ_succ]
        · simpa [Matrix.mul_apply, Fin.sum_univ_succ,
            Matrix.one_apply] using
              congrFun (congrFun inductionHypothesis tailRow) tailColumn

theorem pairingUpper_mul_pathMatrix {m : ℕ}
    (centers : List (PhaseVector m)) :
    pairingUpper centers * pathMatrix centers = 1 :=
  mul_eq_one_comm.mp (pathMatrix_mul_pairingUpper centers)

theorem centerPairingMatrix_apply {m : ℕ}
    (centers : List (PhaseVector m)) (row column : Fin centers.length) :
    (centerMatrix centers * omega m *
        Matrix.transpose (centerMatrix centers)) row column =
      pairing (centers.get row) (centers.get column) := by
  change
    (Matrix.vecMul (centers.get row) (omega m)) ⬝ᵥ
        centers.get column =
      pairing (centers.get row) (centers.get column)
  rw [pairing, Matrix.dotProduct_mulVec]

theorem pairingUpper_add_transpose {m : ℕ}
    (centers : List (PhaseVector m)) :
    pairingUpper centers + Matrix.transpose (pairingUpper centers) =
      centerMatrix centers * omega m *
        Matrix.transpose (centerMatrix centers) := by
  ext row column
  rw [Matrix.add_apply, Matrix.transpose_apply,
    centerPairingMatrix_apply, pairingUpper_apply,
    pairingUpper_apply]
  rcases lt_trichotomy row column with before | equal | after
  · simp [before, before.ne, Ne.symm before.ne, before.asymm]
  · subst column
    simp [pairing_self]
  · simp [after, after.ne, Ne.symm after.ne, after.asymm,
      pairing_comm]

/-- Reindexes `List.ofFn` back to the family's original `Fin` index. -/
def ofFnIndexEquiv {m n : ℕ} (centers : Fin n → PhaseVector m) :
    Fin (List.ofFn centers).length ≃ Fin n :=
  finCongr List.length_ofFn

/-- The center matrix of a fixed-length family, on its original index. -/
def centerMatrixFin {m n : ℕ} (centers : Fin n → PhaseVector m) :
    Matrix (Fin n) (PhaseIndex m) F2 :=
  Matrix.reindexLinearEquiv F2 F2
    (ofFnIndexEquiv centers) (Equiv.refl _) <|
      centerMatrix (List.ofFn centers)

/-- The path matrix of a fixed-length family, on its original index. -/
def pathMatrixFin {m n : ℕ} (centers : Fin n → PhaseVector m) :
    Matrix (Fin n) (Fin n) F2 :=
  Matrix.reindexLinearEquiv F2 F2
    (ofFnIndexEquiv centers) (ofFnIndexEquiv centers) <|
      pathMatrix (List.ofFn centers)

/-- The direct pairing matrix of a fixed-length family. -/
def pairingUpperFin {m n : ℕ} (centers : Fin n → PhaseVector m) :
    Matrix (Fin n) (Fin n) F2 :=
  Matrix.reindexLinearEquiv F2 F2
    (ofFnIndexEquiv centers) (ofFnIndexEquiv centers) <|
      pairingUpper (List.ofFn centers)

@[simp]
theorem centerMatrixFin_eq {m n : ℕ}
    (centers : Fin n → PhaseVector m) :
    centerMatrixFin centers = centers := by
  ext row column
  simp [centerMatrixFin, ofFnIndexEquiv, Matrix.reindex_apply,
    centerMatrix]

theorem pathMatrixFin_mul_pairingUpperFin {m n : ℕ}
    (centers : Fin n → PhaseVector m) :
    pathMatrixFin centers * pairingUpperFin centers = 1 := by
  rw [pathMatrixFin, pairingUpperFin,
    Matrix.reindexLinearEquiv_mul, pathMatrix_mul_pairingUpper]
  simp

theorem pairingUpperFin_mul_pathMatrixFin {m n : ℕ}
    (centers : Fin n → PhaseVector m) :
    pairingUpperFin centers * pathMatrixFin centers = 1 := by
  rw [pairingUpperFin, pathMatrixFin,
    Matrix.reindexLinearEquiv_mul, pairingUpper_mul_pathMatrix]
  simp

theorem pairingUpperFin_add_transpose {m n : ℕ}
    (centers : Fin n → PhaseVector m) :
    pairingUpperFin centers +
        Matrix.transpose (pairingUpperFin centers) =
      centerMatrixFin centers * omega m *
        Matrix.transpose (centerMatrixFin centers) := by
  ext row column
  have entry := congrFun
    (congrFun (pairingUpper_add_transpose (List.ofFn centers))
      ((ofFnIndexEquiv centers).symm row))
    ((ofFnIndexEquiv centers).symm column)
  simpa [pairingUpperFin, centerMatrixFin, Matrix.reindex_apply,
    Matrix.mul_apply] using entry

/-- The subspace spanned by the transvection centers. -/
def centerSpan {m : ℕ} (centers : List (PhaseVector m)) :
    Submodule F2 (PhaseVector m) :=
  Submodule.span F2 (centers.toFinset : Set (PhaseVector m))

theorem mem_centerSpan_of_mem {m : ℕ} {center : PhaseVector m}
    {centers : List (PhaseVector m)} (member : center ∈ centers) :
    center ∈ centerSpan centers := by
  apply Submodule.subset_span
  simpa [centerSpan] using member

theorem centerSpan_le_cons {m : ℕ} (center : PhaseVector m)
    (centers : List (PhaseVector m)) :
    centerSpan centers ≤ centerSpan (center :: centers) := by
  apply Submodule.span_mono
  intro vector member
  simp only [List.coe_toFinset, Set.mem_setOf_eq] at member ⊢
  exact List.mem_cons_of_mem center member

theorem replay_add_initial_mem_centerSpan {m : ℕ}
    (centers : List (PhaseVector m)) (vector : PhaseVector m) :
    replay centers vector + vector ∈ centerSpan centers := by
  induction centers generalizing vector with
  | nil =>
      simp [replay, centerSpan, ZModModule.add_self]
  | cons center centers inductionHypothesis =>
      let updated := rowAction vector (transvection center)
      have tail :
          replay centers updated + updated ∈ centerSpan (center :: centers) :=
        centerSpan_le_cons center centers (inductionHypothesis updated)
      have step : updated + vector ∈ centerSpan (center :: centers) := by
        have center_mem : center ∈ centerSpan (center :: centers) :=
          mem_centerSpan_of_mem (by simp)
        have scaled :
            pairing vector center • center ∈ centerSpan (center :: centers) :=
          Submodule.smul_mem _ _ center_mem
        have step_eq : updated + vector = pairing vector center • center := by
          dsimp only [updated]
          rw [rowAction_transvection, add_assoc, add_comm
            (pairing vector center • center) vector, ← add_assoc,
            ZModModule.add_self, zero_add]
        rwa [step_eq]
      have combined := (centerSpan (center :: centers)).add_mem tail step
      change replay centers updated + vector ∈ centerSpan (center :: centers)
      simpa only [ZModModule.add_add_add_cancel] using combined

theorem residueSpace_product_le_centerSpan {m : ℕ}
    (centers : List (PhaseVector m)) :
    residueSpace (productTransvections centers : ActionMatrix m) ≤
      centerSpan centers := by
  rw [residueSpace]
  apply Submodule.span_le.mpr
  rintro _ ⟨row, rfl⟩
  have replay_difference :=
    replay_add_initial_mem_centerSpan centers (Pi.single row 1)
  rw [replay_eq_rowAction_product] at replay_difference
  have row_eq :
      (1 + (productTransvections centers : ActionMatrix m)).row row =
        Pi.single row 1 + (productTransvections centers : ActionMatrix m).row row := by
    classical
    ext column
    simp only [Matrix.row_apply, Matrix.add_apply, Pi.add_apply]
    rw [Matrix.one_eq_pi_single]
  rw [row_eq]
  simpa [rowAction, Matrix.row_apply', add_comm] using replay_difference

theorem finrank_centerSpan_le_length {m : ℕ}
    (centers : List (PhaseVector m)) :
    Module.finrank F2 (centerSpan centers) ≤ centers.length := by
  exact (finrank_span_finset_le_card centers.toFinset).trans
    centers.toFinset_card_le

theorem residueRank_product_le_length {m : ℕ}
    (centers : List (PhaseVector m)) :
    residueRank (productTransvections centers : ActionMatrix m) ≤
      centers.length := by
  exact (Submodule.finrank_mono
    (residueSpace_product_le_centerSpan centers)).trans
      (finrank_centerSpan_le_length centers)

@[simp]
theorem centerMatrix_apply {m : ℕ} (centers : List (PhaseVector m))
    (row : Fin centers.length) :
    centerMatrix centers row = centers.get row := rfl

@[simp]
theorem pathMatrix_pair_zero_one {m : ℕ}
    (first second : PhaseVector m) :
    pathMatrix [first, second] 0 1 = pairing first second := rfl

theorem residueMatrix_product_eq_centerMatrix {m : ℕ}
    (centers : List (PhaseVector m)) :
    residueMatrix (productTransvections centers : ActionMatrix m) =
      Matrix.transpose (centerMatrix centers) * pathMatrix centers *
        centerMatrix centers := by
  induction centers with
  | nil =>
      ext row column
      simp [residueMatrix, Matrix.mul_apply]
  | cons center centers inductionHypothesis =>
      rw [residueMatrix_product_cons, inductionHypothesis,
        replay_eq_add_vecMul_centerMatrix]
      ext row column
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply,
        Matrix.vecMul_apply_eq_sum, centerMatrix, pathMatrix,
        Fin.sum_univ_succ]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      rw [mul_add, Finset.mul_sum]
      ring_nf

theorem residueMatrix_product_ofFn_eq {m n : ℕ}
    (centers : Fin n → PhaseVector m) :
    residueMatrix
        (productTransvections (List.ofFn centers) : ActionMatrix m) =
      Matrix.transpose (centerMatrixFin centers) * pathMatrixFin centers *
        centerMatrixFin centers := by
  rw [residueMatrix_product_eq_centerMatrix]
  simp [centerMatrixFin, pathMatrixFin, Matrix.reindex_apply]

theorem range_centerMatrix {m : ℕ}
    (centers : List (PhaseVector m)) :
    Set.range (centerMatrix centers) =
      (centers.toFinset : Set (PhaseVector m)) := by
  ext vector
  simpa [centerMatrix, eq_comm] using
    (List.exists_mem_iff_get
      (l := centers) (p := fun item => item = vector)).symm

theorem centerMatrix_linearIndependent_iff {m : ℕ}
    (centers : List (PhaseVector m)) :
    LinearIndependent F2 (centerMatrix centers) ↔
      centers.length ≤ Module.finrank F2 (centerSpan centers) := by
  rw [linearIndependent_iff_card_le_finrank_span,
    Fintype.card_fin, Set.finrank, range_centerMatrix]
  rfl

theorem residueRank_product_eq_length_of_linearIndependent {m : ℕ}
    (centers : List (PhaseVector m))
    (independent : LinearIndependent F2 (centerMatrix centers)) :
    residueRank (productTransvections centers : ActionMatrix m) =
      centers.length := by
  rw [← rank_residueMatrix,
    residueMatrix_product_eq_centerMatrix, Matrix.mul_assoc]
  have transpose_injective :
      Function.Injective
        (Matrix.transpose (centerMatrix centers)).mulVec :=
    transpose_mulVec_injective_of_linearIndependent
      (centerMatrix centers) independent
  rw [rank_mul_eq_right_of_mulVec_injective _ _ transpose_injective]
  rw [Matrix.rank_mul_eq_right_of_isUnit_det
    (pathMatrix centers) (centerMatrix centers)
    (by rw [pathMatrix_det]; exact isUnit_one)]
  change Matrix.rank (fun row : Fin centers.length => centers.get row) =
    centers.length
  simpa only [Fintype.card_fin] using independent.rank_matrix

theorem centerMatrix_linearIndependent_of_rank_eq_length {m : ℕ}
    (target : SymplecticAction m) (centers : List (PhaseVector m))
    (factorization : IsFactorization target centers)
    (rank_eq_length : residueRank (target : ActionMatrix m) =
      centers.length) :
    LinearIndependent F2 (centerMatrix centers) := by
  rw [linearIndependent_iff_card_le_finrank_span]
  rw [Fintype.card_fin, Set.finrank, range_centerMatrix]
  change centers.length ≤ Module.finrank F2 (centerSpan centers)
  rw [← rank_eq_length]
  apply Submodule.finrank_mono
  rw [← factorization]
  exact residueSpace_product_le_centerSpan centers

theorem residueSpace_eq_centerSpan_of_rank_eq_length {m : ℕ}
    (target : SymplecticAction m) (centers : List (PhaseVector m))
    (factorization : IsFactorization target centers)
    (rank_eq_length : residueRank (target : ActionMatrix m) =
      centers.length) :
    residueSpace (target : ActionMatrix m) = centerSpan centers := by
  have containment :
      residueSpace (target : ActionMatrix m) ≤ centerSpan centers := by
    rw [← factorization]
    exact residueSpace_product_le_centerSpan centers
  refine Submodule.eq_of_le_of_finrank_eq (K := F2) containment ?_
  apply Nat.le_antisymm
  · exact Submodule.finrank_mono containment
  · change Module.finrank F2 (centerSpan centers) ≤
      residueRank (target : ActionMatrix m)
    rw [rank_eq_length]
    exact finrank_centerSpan_le_length centers

theorem finrank_centerSpan_eq_rank_of_length_eq_rank_add_one {m : ℕ}
    (target : SymplecticAction m) (centers : List (PhaseVector m))
    (factorization : IsFactorization target centers)
    (length_eq_rank_add_one :
      centers.length = residueRank (target : ActionMatrix m) + 1) :
    Module.finrank F2 (centerSpan centers) =
      residueRank (target : ActionMatrix m) := by
  have residue_containment :
      residueSpace (target : ActionMatrix m) ≤ centerSpan centers := by
    rw [← factorization]
    exact residueSpace_product_le_centerSpan centers
  have rank_le_span :
      residueRank (target : ActionMatrix m) ≤
        Module.finrank F2 (centerSpan centers) :=
    Submodule.finrank_mono residue_containment
  have span_le_rank_add_one :
      Module.finrank F2 (centerSpan centers) ≤
        residueRank (target : ActionMatrix m) + 1 := by
    rw [← length_eq_rank_add_one]
    exact finrank_centerSpan_le_length centers
  by_contra unequal
  have span_eq_length :
      Module.finrank F2 (centerSpan centers) = centers.length := by
    omega
  have independent : LinearIndependent F2 (centerMatrix centers) :=
    (centerMatrix_linearIndependent_iff centers).mpr
      (by rw [span_eq_length])
  have product_rank :=
    residueRank_product_eq_length_of_linearIndependent centers independent
  rw [factorization] at product_rank
  omega

theorem residueSpace_eq_centerSpan_of_length_eq_rank_add_one {m : ℕ}
    (target : SymplecticAction m) (centers : List (PhaseVector m))
    (factorization : IsFactorization target centers)
    (length_eq_rank_add_one :
      centers.length = residueRank (target : ActionMatrix m) + 1) :
    residueSpace (target : ActionMatrix m) = centerSpan centers := by
  have containment :
      residueSpace (target : ActionMatrix m) ≤ centerSpan centers := by
    rw [← factorization]
    exact residueSpace_product_le_centerSpan centers
  refine Submodule.eq_of_le_of_finrank_eq (K := F2) containment ?_
  change residueRank (target : ActionMatrix m) =
    Module.finrank F2 (centerSpan centers)
  exact (finrank_centerSpan_eq_rank_of_length_eq_rank_add_one target
    centers factorization length_eq_rank_add_one).symm

theorem target_eq_of_residueMatrix_eq {m : ℕ}
    (target candidate : SymplecticAction m)
    (equal_residue :
      residueMatrix (candidate : ActionMatrix m) =
        residueMatrix (target : ActionMatrix m)) :
    candidate = target := by
  apply Subtype.ext
  exact residueMatrix_injective equal_residue

theorem factorization_iff_residueMatrix_eq {m : ℕ}
    (target : SymplecticAction m) (centers : List (PhaseVector m)) :
    IsFactorization target centers ↔
      Matrix.transpose (centerMatrix centers) * pathMatrix centers *
        centerMatrix centers =
          residueMatrix (target : ActionMatrix m) := by
  rw [← residueMatrix_product_eq_centerMatrix]
  constructor
  · exact fun factorization => congrArg residueMatrix
      (congrArg Subtype.val factorization)
  · intro equal_residue
    exact target_eq_of_residueMatrix_eq target
      (productTransvections centers) equal_residue

end PaulimerFormal
