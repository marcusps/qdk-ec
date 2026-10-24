import BinarFormal.Packed
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Field.ZMod

/-!
# Echelon form (RREF) with transforms

An executable Lean model of `binar`'s reduced row echelon form computation, refined against
`BinarFormal.Packed.PackedMatrix`. This mirrors, in order of composition,
`binar/src/matrix/aligned_bitmatrix.rs`:

* `AlignedBitMatrix::identity` → `BinarFormal.Packed.PackedMatrix.identity`, with refinement
  `decode_identity`.
* `AlignedBitMatrix::swap_rows` → `BinarFormal.Echelon.swapRows`, with refinement
  `decode_swapRows` (against `Matrix.swap`) and the raw-bit lemma `get_swapRows`.
* `AlignedBitMatrix::add_into_row` (already modelled as `PackedMatrix.xorRow` in `Packed.lean`)
  is bridged to the elementary row operation on decoded content by
  `decode_xorRow_eq_transvection_mul` (against `Matrix.transvection`).
* `pivot_of` → `BinarFormal.Echelon.pivotOf`, built from the two nested searches
  `rowSearch` (fixed column, scans rows) and `pivotSearchAux` (scans columns), with the
  single reusable specification lemma `pivotSearchAux_spec` (and its `pivotOf`-level
  corollaries `pivotOf_col_ge`, `pivotOf_success`, `pivotOf_lt_zero`).
* `xor_if_column_with_transforms` → `BinarFormal.Echelon.xorIfColumn`.
* `reduce_with_transforms` → `BinarFormal.Echelon.reduceWithTransforms`, built from the single
  fuel-recursive helper `reduceFrom` (covering both of Rust's `0..from.0` and
  `from.0+1..row_count` loops in one structurally recursive definition).
* `EchelonForm`/`EchelonForm::new` → `BinarFormal.Echelon.EchelonForm` (fields `matrix`,
  `transform`, `transformInvT`, `pivots`) and `BinarFormal.Echelon.EchelonForm.new`, built from
  `applyPivot` (one swap + one `reduceWithTransforms` + pushing a pivot) and the
  fuel-recursive main loop `echelonAux`.
* `AlignedBitMatrix::echelonize`/`rank` → the transform-free projections
  `BinarFormal.Echelon.echelonize` and `BinarFormal.Echelon.PackedMatrix.rank`.

## Main correctness results

* `EchelonForm.new_transform_mul_eq`: `T.decode * original.decode = reduced.decode`.
* `EchelonForm.new_transform_mul_inv`: `T.decode * (U.decode)ᵀ = 1`, in the exact
  orientation Rust maintains (see the trust boundary note below).
* `EchelonForm.new_isRREF`: the reduced matrix satisfies the precise `IsRREF` predicate,
  whose `sorted`/`lt_n`/`pivot_unit`/`rows_zero` fields give the strictly increasing pivot
  list, its range check, and its exact row/column characterization.
* `EchelonForm.new_rowSpace_eq`: the reduced matrix has the same row space as the original.
* `EchelonForm.new_pivots_length_eq_rank`: `pivots.length = original.decode.rank`, connecting
  the executable pivot count to Mathlib's `Matrix.rank`, generically over rectangular and
  zero-dimensional shapes.
* `echelonize`, `PackedMatrix.rank`: transform-free projections of `EchelonForm.new`, with
  `echelonize_isRREF`, `echelonize_rowSpace_eq`, `PackedMatrix.rank_eq_decode_rank` restating
  the above transform-free.

## Semantic trust boundary

* **`pivot_of`'s dead out-of-bounds early return is omitted.** Rust's `pivot_of` opens with
  `if row_index >= matrix.row_count() || column_index >= matrix.column_count() { return
  (row_index, column_index); }`. Every call site is `pivot_of(&matrix, (0, 0))` or
  `pivot_of(&matrix, (pivot.0 + 1, pivot.1 + 1))` where `pivot.1 < column_count` was just
  checked by the enclosing loop; the only call whose argument could be out of bounds is the
  final recomputation right before the loop's own `0..row_count` bound terminates it, and that
  result is discarded (the loop condition is checked at the *top* of the next iteration, which
  never happens once the `Nat` fuel below is exhausted). `pivotOf`/`pivotSearchAux`/`rowSearch`
  hence model only the `while` search itself; this never changes an observable result.
* **One fuel-recursive `reduceFrom` instead of two near-identical ranges.** Rust's
  `reduce_with_transforms` runs `xor_if_column_with_transforms` over `0..from.0` then
  `from.0+1..row_count`. Both ranges only ever read the fixed pivot row (never written by
  either range) and write only their own target row, so the two ranges' effects are mutually
  independent; `reduceFrom` is a single fuel-recursive helper processing `0..row_count` while
  skipping the pivot row inline, with its per-row effect pinned down exactly by
  `reduceFrom_pivotRow_get` (pivot row untouched), `reduceFrom_outside_get` (rows outside the
  touched range untouched) and `reduceFrom_inside_get` (every other row reduced against the
  pivot row), then instantiated at `reduceWithTransforms`.
* **The transform-free block-offset reducer is covered extensionally.** Rust's separate
  `echelonize` path uses `reduce`, which starts each row XOR at the 512-bit block containing
  the pivot, while this model projects the full-row reducer used by `EchelonForm::new`.
  Earlier blocks of the pivot row are zero when that pivot is selected, so the skipped XORs
  cannot change the result. This source-level correspondence is reviewed rather than a claim
  of machine-checked Rust translation.
* **The exact `transform_inv_t` orientation is preserved, not normalized.** Rust's
  `xor_if_column_with_transforms` updates `matrix`/`transform` by adding the pivot/source row
  into the target row (`add_into_row(row_index, from_row_index)`), but updates
  `transform_inv_t` with its operands *swapped*
  (`transform_inv_t.add_into_row(from_row_index, row_index)`, i.e. the target row is added into
  the pivot/source row). `xorIfColumn` reproduces this exact asymmetry, and
  `EchelonForm.new_transform_mul_inv` proves the documented invariant
  `T.decode * (U.decode)ᵀ = 1` in this exact orientation.
* **Row-minimality of the chosen pivot is not modelled or used.** `pivotOf` faithfully
  reproduces Rust's search *order* (columns outermost, rows innermost, always resetting to the
  original starting row), but no downstream theorem needs "the chosen row is the smallest row
  with a nonzero entry", only that *some* row with a nonzero entry in that column was found; a
  row-minimality lemma is deliberately not proved.
* **Out of scope**, matching `BinarFormal.Packed`'s own boundary: raw pointer arithmetic and
  `BitBlock`/word-array allocation. Only the logical bit contents of `matrix`, `transform`,
  `transform_inv_t`, and `pivots` are modelled.
-/

namespace BinarFormal.Echelon

open BinarFormal.Packed BinarFormal.Packed.PackedMatrix
open scoped Matrix

variable {m n : Nat}

/-! ## Row-total read, row swap, and identity -/

/-- Read row `i` (totalized: out-of-range rows read as the all-zero row), mirroring how
`pivot_of`/`reduce_with_transforms` only ever read rows already known to be in range while
letting the search helpers below stay simple total `Nat`-indexed functions. -/
def getTotal (M : PackedMatrix m n) (i : Nat) (j : Nat) : Bool :=
  if h : i < m then M.get ⟨i, h⟩ j else false

/-- Swap packed rows `i` and `j`, mirroring `AlignedBitMatrix::swap_rows`. -/
def swapRows (M : PackedMatrix m n) (i j : Fin m) : PackedMatrix m n where
  rows := M.rows ∘ Equiv.swap i j

@[simp] theorem get_swapRows (M : PackedMatrix m n) (i j row : Fin m) (col : Nat) :
    (swapRows M i j).get row col = M.get (Equiv.swap i j row) col := rfl

/-- `swapRows` refines `Matrix.swap`: swapping packed rows decodes to left-multiplying by the
corresponding swap matrix. -/
theorem decode_swapRows (M : PackedMatrix m n) (i j : Fin m) :
    (swapRows M i j).decode = Matrix.swap F2 i j * M.decode := by
  funext row col
  show Bool.toF2 ((swapRows M i j).get row col.val) = _
  rw [get_swapRows]
  rcases eq_or_ne row i with hri | hri
  · subst hri
    rw [Equiv.swap_apply_left, Matrix.swap_mul_apply_left]
    rfl
  rcases eq_or_ne row j with hrj | hrj
  · subst hrj
    rw [Equiv.swap_apply_right, Matrix.swap_mul_apply_right]
    rfl
  · rw [Equiv.swap_apply_of_ne_of_ne hri hrj, Matrix.swap_mul_of_ne hri hrj]
    rfl

/-- The `m × m` identity packed matrix, mirroring `AlignedBitMatrix::identity`. Rust builds this
by writing each diagonal bit of a zero matrix in a loop; since those writes touch pairwise
disjoint cells, writing every diagonal bit directly (as done here) is the same matrix. -/
def PackedMatrix.identity (m : Nat) : PackedMatrix m m where
  rows := fun i => (PackedVec.zero m).set i.val i.isLt true

@[simp] theorem decode_identity (m : Nat) :
    (PackedMatrix.identity m).decode = (1 : Matrix (Fin m) (Fin m) F2) := by
  funext i j
  show ((PackedVec.zero m).set i.val i.isLt true).decode j = (1 : Matrix (Fin m) (Fin m) F2) i j
  rw [PackedVec.decode_set, PackedVec.decode_zero]
  rcases eq_or_ne j ⟨i.val, i.isLt⟩ with hj | hj
  · rw [hj, Function.update_self, Matrix.one_apply_eq]
    rfl
  · rw [Function.update_of_ne hj, Matrix.one_apply_ne hj.symm]
    rfl

/-- XOR-ing packed row `src` into packed row `dst` decodes to left-multiplying by the
transvection matrix that adds `src`'s row into `dst`'s row: the algebraic bridge from
`PackedMatrix.xorRow` (already defined in `Packed.lean`) to `Matrix.transvection`. -/
theorem decode_xorRow_eq_transvection_mul (M : PackedMatrix m n) (dst src : Fin m) :
    (M.xorRow dst src).decode = Matrix.transvection dst src (1 : F2) * M.decode := by
  rw [PackedMatrix.decode_xorRow]
  funext i j
  rcases eq_or_ne i dst with hi | hi
  · subst hi
    rw [Matrix.updateRow_self, Matrix.transvection_mul_apply_same]
    show M.decode i j + M.decode src j = M.decode i j + 1 * M.decode src j
    rw [one_mul]
  · rw [Matrix.updateRow_ne hi, Matrix.transvection_mul_apply_of_ne dst src i j hi]

theorem PackedVec.get_xor {n : Nat} (u v : PackedVec n) (i : Nat) :
    (u.xor v).get i = (u.get i ^^ v.get i) := by
  show (u.storage ^^^ v.storage).getLsbD i = (u.storage.getLsbD i ^^ v.storage.getLsbD i)
  rw [BitVec.getLsbD_xor]

theorem PackedMatrix.get_xorRow {m n : Nat} (M : PackedMatrix m n) (dst src : Fin m) (t : Fin m)
    (c : Nat) :
    (M.xorRow dst src).get t c = if t = dst then (M.get t c ^^ M.get src c) else M.get t c := by
  show (Function.update M.rows dst ((M.rows dst).xor (M.rows src)) t).get c = _
  by_cases ht : t = dst
  · subst ht
    rw [Function.update_self, ite_eq_left rfl, PackedVec.get_xor]
    rfl
  · rw [Function.update_of_ne ht, ite_eq_right ht]
    rfl

/-! ## `pivot_of`: nested row/column search

`pivotOf` mirrors `pivot_of`'s `while` loop as a nested search: `pivotSearchAux` scans
columns starting at `c0` (mirroring the loop's `column_index`), and for each column calls
`rowSearchAux` to scan rows starting at `r0` (mirroring the loop's `row_index`, which is
reset to `starting_at.0` every time the column advances). Both are structured as
`Nat`-fuel recursions so that "fuel exhausted" exactly models "ran past the last row" /
"ran past the last column". The dead out-of-bounds early return of Rust's `pivot_of` is
not modelled (see the module-level trust boundary note). -/

/-- Scan rows `r0, r0 + 1, …` (for `fuel` steps) of column `col`, returning the first row
with a set bit, mirroring one pass of `pivot_of`'s inner row search. -/
def rowSearchAux (M : PackedMatrix m n) (col r0 : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 => bif getTotal M r0 col then some r0 else rowSearchAux M col (r0 + 1) fuel

/-- Scan rows `r0, r0 + 1, …, m - 1` of column `col` for the first set bit. -/
def rowSearch (M : PackedMatrix m n) (col r0 : Nat) : Option Nat := rowSearchAux M col r0 (m - r0)

theorem rowSearchAux_some {M : PackedMatrix m n} {col r0 fuel r : Nat}
    (h : rowSearchAux M col r0 fuel = some r) : r0 ≤ r ∧ getTotal M r col = true := by
  induction fuel generalizing r0 with
  | zero => simp [rowSearchAux] at h
  | succ fuel ih =>
    unfold rowSearchAux at h
    rcases hb : getTotal M r0 col with _ | _ <;> rw [hb] at h
    · simp only [Bool.cond_false] at h
      obtain ⟨hle, hget⟩ := ih h
      exact ⟨by omega, hget⟩
    · simp only [Bool.cond_true, Option.some.injEq] at h
      exact ⟨by omega, h ▸ hb⟩

theorem rowSearchAux_none {M : PackedMatrix m n} {col r0 fuel : Nat}
    (h : rowSearchAux M col r0 fuel = none) :
    ∀ r, r0 ≤ r → r < r0 + fuel → getTotal M r col = false := by
  induction fuel generalizing r0 with
  | zero => intro r hr1 hr2; omega
  | succ fuel ih =>
    unfold rowSearchAux at h
    rcases hb : getTotal M r0 col with _ | _ <;> rw [hb] at h
    · simp only [Bool.cond_false] at h
      intro r hr1 hr2
      rcases eq_or_lt_of_le hr1 with heq | hlt
      · exact heq ▸ hb
      · exact ih h r (by omega) (by omega)
    · exact absurd h (by simp)

theorem rowSearch_some {M : PackedMatrix m n} {col r0 r : Nat} (h : rowSearch M col r0 = some r) :
    r0 ≤ r ∧ getTotal M r col = true :=
  rowSearchAux_some h

theorem rowSearch_none {M : PackedMatrix m n} {col r0 : Nat} (h : rowSearch M col r0 = none) :
    ∀ r, r0 ≤ r → r < m → getTotal M r col = false := by
  intro r hr1 hr2
  exact rowSearchAux_none h r hr1 (by omega)

/-- A bit that reads as set is necessarily an in-range row. -/
theorem lt_of_getTotal {M : PackedMatrix m n} {i col : Nat} (h : getTotal M i col = true) :
    i < m := by
  unfold getTotal at h
  split at h
  · assumption
  · simp at h

/-- Scan columns `c0, c0 + 1, …` (for `fuel` steps), for each column re-searching rows
from `r0`, returning as soon as some column has a set bit in the row range; if no column
in range has one, returns the final column reached together with the frozen `r0`,
mirroring `pivot_of`'s outer column search (and its "not found" result, which resets
`row_index` to `starting_at.0` right before breaking). -/
def pivotSearchAux (M : PackedMatrix m n) (r0 c0 : Nat) : Nat → Nat × Nat
  | 0 => (r0, c0)
  | fuel + 1 =>
    match rowSearch M c0 r0 with
    | some r => (r, c0)
    | none => pivotSearchAux M r0 (c0 + 1) fuel

theorem pivotSearchAux_spec (M : PackedMatrix m n) (r0 c0 fuel : Nat) :
    c0 ≤ (pivotSearchAux M r0 c0 fuel).2 ∧
      (∀ c, c0 ≤ c → c < (pivotSearchAux M r0 c0 fuel).2 →
          ∀ r, r0 ≤ r → r < m → getTotal M r c = false) ∧
      ((pivotSearchAux M r0 c0 fuel).2 < c0 + fuel →
          getTotal M (pivotSearchAux M r0 c0 fuel).1 (pivotSearchAux M r0 c0 fuel).2 = true ∧
            r0 ≤ (pivotSearchAux M r0 c0 fuel).1) := by
  induction fuel generalizing c0 with
  | zero =>
    have heq : pivotSearchAux M r0 c0 0 = (r0, c0) := rfl
    rw [heq]
    exact ⟨le_refl c0, fun c hc1 hc2 => absurd hc2 (by omega), fun h => absurd h (by omega)⟩
  | succ fuel ih =>
    rcases hrs : rowSearch M c0 r0 with _ | r
    · have heq : pivotSearchAux M r0 c0 (fuel + 1) = pivotSearchAux M r0 (c0 + 1) fuel := by
        show (match rowSearch M c0 r0 with
          | some r => (r, c0)
          | none => pivotSearchAux M r0 (c0 + 1) fuel) = pivotSearchAux M r0 (c0 + 1) fuel
        rw [hrs]
      rw [heq]
      obtain ⟨hge, hzero, hfound⟩ := ih (c0 + 1)
      refine ⟨by omega, fun c hc1 hc2 r hr1 hr2 => ?_, fun h => hfound (by omega)⟩
      rcases eq_or_lt_of_le hc1 with heq2 | hlt
      · exact heq2 ▸ rowSearch_none hrs r hr1 hr2
      · exact hzero c (by omega) hc2 r hr1 hr2
    · have heq : pivotSearchAux M r0 c0 (fuel + 1) = (r, c0) := by
        show (match rowSearch M c0 r0 with
          | some r => (r, c0)
          | none => pivotSearchAux M r0 (c0 + 1) fuel) = (r, c0)
        rw [hrs]
      rw [heq]
      exact ⟨le_refl c0, fun c hc1 hc2 => absurd hc2 (by omega),
        fun _ => ⟨(rowSearch_some hrs).2, (rowSearch_some hrs).1⟩⟩

/-- Search for the next pivot starting from row `r0`, column `c0`, mirroring
`pivot_of(matrix, (r0, c0))` (ignoring its dead out-of-bounds early return; see the
module-level trust boundary note). Returns `(row, col)`. -/
def pivotOf (M : PackedMatrix m n) (r0 c0 : Nat) : Nat × Nat := pivotSearchAux M r0 c0 (n - c0)

/-- The search never moves the column backward. -/
theorem pivotOf_col_ge (M : PackedMatrix m n) (r0 c0 : Nat) : c0 ≤ (pivotOf M r0 c0).2 :=
  (pivotSearchAux_spec M r0 c0 (n - c0)).1

/-- Every column strictly between the search start and the found column has no set bit
anywhere in the searched row range. -/
theorem pivotOf_lt_zero (M : PackedMatrix m n) (r0 c0 : Nat) :
    ∀ c, c0 ≤ c → c < (pivotOf M r0 c0).2 → ∀ r, r0 ≤ r → r < m → getTotal M r c = false :=
  (pivotSearchAux_spec M r0 c0 (n - c0)).2.1

/-- If the search finds a column in range, that column has a set bit at the returned row,
which is itself at or after the search's starting row. -/
theorem pivotOf_success {M : PackedMatrix m n} {r0 c0 : Nat} (h : (pivotOf M r0 c0).2 < n) :
    getTotal M (pivotOf M r0 c0).1 (pivotOf M r0 c0).2 = true ∧ r0 ≤ (pivotOf M r0 c0).1 := by
  unfold pivotOf at h ⊢
  have hge := (pivotSearchAux_spec M r0 c0 (n - c0)).1
  exact (pivotSearchAux_spec M r0 c0 (n - c0)).2.2 (by omega)

/-! ## `EchelonForm`: transform-carrying reduction state and result

`EchelonForm` mirrors Rust's `EchelonForm` struct exactly, doubling as both the
in-progress loop state and the final result: `pivots` records the pivot columns found so
far (its length is exactly the number of rows already fixed, i.e. Rust's `row_index` loop
variable at the top of each iteration), so no separate `searchRow` field is needed;
`searchCol` below recovers the analogous column bookkeeping purely from `pivots`. -/

/-- Reduced-row-echelon-form state/result: the matrix under reduction, the accumulated
transform `T` (`T * original = matrix`), its `transform_inv_t` companion `U` (with
`T * Uᵀ = 1`), and the pivot columns found so far, mirroring Rust's `EchelonForm`. -/
structure EchelonForm (m n : Nat) where
  /-- The matrix under reduction, mirroring `EchelonForm::matrix`. -/
  matrix : PackedMatrix m n
  /-- The accumulated row-operation transform, mirroring `EchelonForm::transform`. -/
  transform : PackedMatrix m m
  /-- The accumulated inverse-transpose companion, mirroring
  `EchelonForm::transform_inv_t`. -/
  transformInvT : PackedMatrix m m
  /-- The pivot columns found so far, in the order they were found, mirroring
  `EchelonForm::pivots` (Rust's `rank_profile`). -/
  pivots : List Nat

/-- The column at which the next pivot search starts: one past the last pivot found, or
`0` if none has been found yet. Recovers, purely from `S.pivots`, the column value that
`EchelonForm.new`'s loop threads through `pivot.1`. -/
def searchCol (S : EchelonForm m n) : Nat :=
  match S.pivots.getLast? with
  | some c => c + 1
  | none => 0

/-- XOR row `pivotRow` into row `row` (updating `matrix`/`transform`), and, with operands
swapped, XOR row `row` into row `pivotRow` of `transformInvT`, exactly when `matrix` has a
set bit at `(row, col)`; mirrors `xor_if_column_with_transforms` verbatim, including its
`transform_inv_t` orientation asymmetry (see the module-level trust boundary note). -/
def xorIfColumn (col : Nat) (pivotRow : Fin m) (S : EchelonForm m n) (row : Fin m) :
    EchelonForm m n :=
  bif S.matrix.get row col then
    { S with
      matrix := S.matrix.xorRow row pivotRow
      transform := S.transform.xorRow row pivotRow
      transformInvT := S.transformInvT.xorRow pivotRow row }
  else S

/-- Apply `xorIfColumn` to every row index `row, row + 1, …` for `fuel` steps, skipping
`pivotRow` itself, mirroring one of `reduce_with_transforms`'s two loops; combined at
`reduceWithTransforms` below into a single pass covering Rust's `0..from.0` and
`from.0 + 1..row_count` ranges together (see the module-level trust boundary note). New
steps are appended by peeling the last index off a `fuel + 1` unrolling, so that per-cell
reasoning about "which single step touched row `t`" is plain `Nat` arithmetic on
`row + fuel`, needing no list/`Nodup` bookkeeping. -/
def reduceFrom (S : EchelonForm m n) (pivotRow : Fin m) (col row : Nat) : Nat → EchelonForm m n
  | 0 => S
  | fuel + 1 =>
    let S' := reduceFrom S pivotRow col row fuel
    if h : row + fuel < m then
      if row + fuel = pivotRow.val then S' else xorIfColumn col pivotRow S' ⟨row + fuel, h⟩
    else S'

/-- Reduce every row other than `pivotRow` against `pivotRow` in column `col`, mirroring
`reduce_with_transforms`. -/
def reduceWithTransforms (S : EchelonForm m n) (pivotRow : Fin m) (col : Nat) : EchelonForm m n :=
  reduceFrom S pivotRow col 0 m

/-- Swap rows `i` and `j` of `matrix`, `transform`, and `transformInvT` together
(`pivots` is untouched), mirroring `EchelonForm::new`'s three parallel `swap_rows`
calls. -/
def swapState (S : EchelonForm m n) (i j : Fin m) : EchelonForm m n where
  matrix := swapRows S.matrix i j
  transform := swapRows S.transform i j
  transformInvT := swapRows S.transformInvT i j
  pivots := S.pivots

/-- One loop body of `EchelonForm::new`: swap the found pivot row into `rowIndex`, record
`pivotCol` as a pivot, and reduce every other row against it. -/
def applyPivot (S : EchelonForm m n) (rowIndex pivotRowFound : Fin m) (pivotCol : Nat) :
    EchelonForm m n :=
  let S1 := swapState S pivotRowFound rowIndex
  reduceWithTransforms { S1 with pivots := S1.pivots ++ [pivotCol] } rowIndex pivotCol

/-- The main `EchelonForm::new` loop: starting from the pivot search result
`(foundRow, foundCol)` at loop row `rowIndex`, apply it (if `foundCol` is in range) and
recurse with the next search result, for `fuel` further rows. The defensive fallback
branches (taken when `rowIndex` or `foundRow` are out of range) are never exercised along
the call path from `EchelonForm.new` (see `echelonAux_invariant`), which always supplies
`rowIndex + fuel = m` together with a `foundRow`/`foundCol` pair fresh from `pivotOf`. -/
def echelonAux (S : EchelonForm m n) (foundRow foundCol rowIndex : Nat) : Nat → EchelonForm m n
  | 0 => S
  | fuel + 1 =>
    if foundCol < n then
      if hr : rowIndex < m then
        if hfr : foundRow < m then
          let S' := applyPivot S ⟨rowIndex, hr⟩ ⟨foundRow, hfr⟩ foundCol
          let next := pivotOf S'.matrix (rowIndex + 1) (foundCol + 1)
          echelonAux S' next.1 next.2 (rowIndex + 1) fuel
        else S
      else S
    else S

/-- Build the reduced row echelon form (with transforms) of `M`, mirroring
`EchelonForm::new` exactly: start from the identity transforms and the first pivot
search, then run the main loop for up to `m` rows. -/
def EchelonForm.new (M : PackedMatrix m n) : EchelonForm m n :=
  let S0 : EchelonForm m n :=
    { matrix := M
      transform := PackedMatrix.identity m
      transformInvT := PackedMatrix.identity m
      pivots := [] }
  let initial := pivotOf M 0 0
  echelonAux S0 initial.1 initial.2 0 m

/-! ## The algebraic invariants `T * A = M` and `T * Uᵀ = 1`

A transvection's transpose swaps its two indices; not already in Mathlib's
`Transvection.lean`, so proved here as a small standalone helper. -/
theorem Matrix.transvection_transpose {n : Type*} [DecidableEq n] {R : Type*} [CommRing R]
    (i j : n) (c : R) : (Matrix.transvection i j c)ᵀ = Matrix.transvection j i c := by
  unfold Matrix.transvection
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]

/-- `xorIfColumn` preserves `T * A = M` for any fixed target `A`, since it left-multiplies
both `matrix` and `transform` by the same transvection. -/
theorem xorIfColumn_TA_eq_M {S : EchelonForm m n} {A : Matrix (Fin m) (Fin n) F2}
    (pivotRow : Fin m) (col : Nat) (row : Fin m)
    (h : S.transform.decode * A = S.matrix.decode) :
    (xorIfColumn col pivotRow S row).transform.decode * A
      = (xorIfColumn col pivotRow S row).matrix.decode := by
  unfold xorIfColumn
  rcases S.matrix.get row col with _ | _
  · simpa using h
  · simp only [Bool.cond_true]
    rw [decode_xorRow_eq_transvection_mul, decode_xorRow_eq_transvection_mul, Matrix.mul_assoc, h]

/-- `xorIfColumn` preserves `T * Uᵀ = 1`, in Rust's exact `transform_inv_t` orientation:
`transform` is updated by adding `pivotRow` into `row`, while `transformInvT` is updated
by adding `row` into `pivotRow` (operands swapped). Requires `row ≠ pivotRow`, which
always holds at `xorIfColumn`'s call sites inside `reduceFrom` (see the module-level
trust boundary note). -/
theorem xorIfColumn_TUt_eq_one {S : EchelonForm m n} (pivotRow : Fin m) (col : Nat) (row : Fin m)
    (hne : row ≠ pivotRow) (h : S.transform.decode * (S.transformInvT.decode)ᵀ = 1) :
    (xorIfColumn col pivotRow S row).transform.decode *
      ((xorIfColumn col pivotRow S row).transformInvT.decode)ᵀ = 1 := by
  unfold xorIfColumn
  rcases S.matrix.get row col with _ | _
  · simpa using h
  · simp only [Bool.cond_true]
    rw [decode_xorRow_eq_transvection_mul, decode_xorRow_eq_transvection_mul, Matrix.transpose_mul,
      Matrix.transvection_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc S.transform.decode, h,
      Matrix.one_mul, Matrix.transvection_mul_transvection_same row pivotRow hne]
    have h2 : (1 + 1 : F2) = 0 := by decide
    rw [h2, Matrix.transvection_zero]

/-- `reduceFrom` preserves `T * A = M` for any fixed target `A`. -/
theorem reduceFrom_TA_eq_M {S : EchelonForm m n} {A : Matrix (Fin m) (Fin n) F2} (pivotRow : Fin m)
    (col row fuel : Nat) (h : S.transform.decode * A = S.matrix.decode) :
    (reduceFrom S pivotRow col row fuel).transform.decode * A
      = (reduceFrom S pivotRow col row fuel).matrix.decode := by
  induction fuel with
  | zero => exact h
  | succ fuel ih =>
    have heq : reduceFrom S pivotRow col row (fuel + 1) =
        if hb : row + fuel < m then
          if row + fuel = pivotRow.val then reduceFrom S pivotRow col row fuel
          else xorIfColumn col pivotRow (reduceFrom S pivotRow col row fuel) ⟨row + fuel, hb⟩
        else reduceFrom S pivotRow col row fuel := rfl
    rw [heq]
    split
    · split
      · exact ih
      · exact xorIfColumn_TA_eq_M pivotRow col ⟨row + fuel, by omega⟩ ih
    · exact ih

/-- `reduceFrom` preserves `T * Uᵀ = 1`. -/
theorem reduceFrom_TUt_eq_one {S : EchelonForm m n} (pivotRow : Fin m) (col row fuel : Nat)
    (h : S.transform.decode * (S.transformInvT.decode)ᵀ = 1) :
    (reduceFrom S pivotRow col row fuel).transform.decode *
      ((reduceFrom S pivotRow col row fuel).transformInvT.decode)ᵀ = 1 := by
  induction fuel with
  | zero => exact h
  | succ fuel ih =>
    have heq : reduceFrom S pivotRow col row (fuel + 1) =
        if hb : row + fuel < m then
          if row + fuel = pivotRow.val then reduceFrom S pivotRow col row fuel
          else xorIfColumn col pivotRow (reduceFrom S pivotRow col row fuel) ⟨row + fuel, hb⟩
        else reduceFrom S pivotRow col row fuel := rfl
    rw [heq]
    split
    · split
      · exact ih
      · exact xorIfColumn_TUt_eq_one pivotRow col ⟨row + fuel, by omega⟩
          (by simp_all [Fin.ext_iff]) ih
    · exact ih

/-- `swapState` preserves `T * A = M` for any fixed target `A`. -/
theorem swapState_TA_eq_M {S : EchelonForm m n} {A : Matrix (Fin m) (Fin n) F2} (i j : Fin m)
    (h : S.transform.decode * A = S.matrix.decode) :
    (swapState S i j).transform.decode * A = (swapState S i j).matrix.decode := by
  show (swapRows S.transform i j).decode * A = (swapRows S.matrix i j).decode
  rw [decode_swapRows, decode_swapRows, Matrix.mul_assoc, h]

/-- `swapState` preserves `T * Uᵀ = 1`. -/
theorem swapState_TUt_eq_one {S : EchelonForm m n} (i j : Fin m)
    (h : S.transform.decode * (S.transformInvT.decode)ᵀ = 1) :
    (swapState S i j).transform.decode * ((swapState S i j).transformInvT.decode)ᵀ = 1 := by
  show (swapRows S.transform i j).decode * ((swapRows S.transformInvT i j).decode)ᵀ = 1
  rw [decode_swapRows, decode_swapRows, Matrix.transpose_mul, Matrix.transpose_swap,
    Matrix.mul_assoc, ← Matrix.mul_assoc S.transform.decode, h, Matrix.one_mul,
    Matrix.swap_mul_self]

/-! ## Raw-bit facts about `xorIfColumn` / `reduceFrom`, for the pivot/zero invariants -/

/-- Raw-bit description of `xorIfColumn`: cell `(t, c)` of `matrix` flips exactly when
`t = target` and `matrix` had a set bit at `(target, col)`; otherwise it is unchanged. -/
theorem xorIfColumn_matrix_get {S : EchelonForm m n} (pivotRow : Fin m) (col : Nat)
    (target t : Fin m) (c : Nat) :
    (xorIfColumn col pivotRow S target).matrix.get t c =
      if t = target ∧ S.matrix.get target col = true then
        S.matrix.get t c ^^ S.matrix.get pivotRow c
      else S.matrix.get t c := by
  unfold xorIfColumn
  rcases S.matrix.get target col with _ | _
  · simp
  · simp only [Bool.cond_true, and_true]
    exact PackedMatrix.get_xorRow S.matrix target pivotRow t c

/-- `reduceFrom` never modifies `pivotRow`'s own row (`xorIfColumn` always skips it). -/
theorem reduceFrom_pivotRow_get {S : EchelonForm m n} (pivotRow : Fin m) (col row fuel : Nat)
    (c : Nat) :
    (reduceFrom S pivotRow col row fuel).matrix.get pivotRow c = S.matrix.get pivotRow c := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have heq : reduceFrom S pivotRow col row (fuel + 1) =
        if hb : row + fuel < m then
          if row + fuel = pivotRow.val then reduceFrom S pivotRow col row fuel
          else xorIfColumn col pivotRow (reduceFrom S pivotRow col row fuel) ⟨row + fuel, hb⟩
        else reduceFrom S pivotRow col row fuel := rfl
    rw [heq]
    split
    · split
      · exact ih
      · rename_i hb hnep
        rw [xorIfColumn_matrix_get]
        have hne : ¬ (pivotRow = (⟨row + fuel, hb⟩ : Fin m) ∧
            (reduceFrom S pivotRow col row fuel).matrix.get (⟨row + fuel, hb⟩ : Fin m) col
              = true) :=
          fun ⟨he, _⟩ => hnep (congrArg Fin.val he).symm
        rw [ite_eq_right hne, ih]
    · exact ih

/-- `reduceFrom` never modifies a row outside the touched range `[row, row + fuel)`. -/
theorem reduceFrom_outside_get {S : EchelonForm m n} (pivotRow : Fin m) (col row fuel : Nat)
    (t : Fin m) (c : Nat) (ht : t.val < row ∨ row + fuel ≤ t.val) :
    (reduceFrom S pivotRow col row fuel).matrix.get t c = S.matrix.get t c := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have heq : reduceFrom S pivotRow col row (fuel + 1) =
        if hb : row + fuel < m then
          if row + fuel = pivotRow.val then reduceFrom S pivotRow col row fuel
          else xorIfColumn col pivotRow (reduceFrom S pivotRow col row fuel) ⟨row + fuel, hb⟩
        else reduceFrom S pivotRow col row fuel := rfl
    rw [heq]
    split
    · split
      · exact ih (by omega)
      · rename_i hb hnep
        rw [xorIfColumn_matrix_get]
        have hne : ¬ (t = (⟨row + fuel, hb⟩ : Fin m) ∧
            (reduceFrom S pivotRow col row fuel).matrix.get (⟨row + fuel, hb⟩ : Fin m) col
              = true) :=
          fun ⟨he, _⟩ => by
            have hv : t.val = row + fuel := by rw [he]
            omega
        rw [ite_eq_right hne, ih (by omega)]
    · exact ih (by omega)

/-- `reduceFrom`'s effect on a row strictly inside the touched range and different from
`pivotRow`: it XORs in `pivotRow`'s row exactly when `matrix` originally had a set bit in
column `col` of that row. -/
theorem reduceFrom_inside_get {S : EchelonForm m n} (pivotRow : Fin m) (col row fuel : Nat)
    (t : Fin m) (c : Nat) (ht1 : row ≤ t.val) (ht2 : t.val < row + fuel) (ht3 : t ≠ pivotRow) :
    (reduceFrom S pivotRow col row fuel).matrix.get t c =
      if S.matrix.get t col = true then S.matrix.get t c ^^ S.matrix.get pivotRow c
      else S.matrix.get t c := by
  induction fuel with
  | zero => omega
  | succ fuel ih =>
    have heq : reduceFrom S pivotRow col row (fuel + 1) =
        if hb : row + fuel < m then
          if row + fuel = pivotRow.val then reduceFrom S pivotRow col row fuel
          else xorIfColumn col pivotRow (reduceFrom S pivotRow col row fuel) ⟨row + fuel, hb⟩
        else reduceFrom S pivotRow col row fuel := rfl
    rw [heq]
    by_cases htv : t.val = row + fuel
    · have hb : row + fuel < m := htv ▸ t.isLt
      have hnep : row + fuel ≠ pivotRow.val := fun he => ht3 (Fin.ext (htv.trans he))
      rw [dite_eq_left hb, ite_eq_right hnep, xorIfColumn_matrix_get]
      have ht : t = (⟨row + fuel, hb⟩ : Fin m) := Fin.ext htv
      rw [← ht]
      have hcol : (reduceFrom S pivotRow col row fuel).matrix.get t col = S.matrix.get t col :=
        reduceFrom_outside_get (S := S) pivotRow col row fuel t col (Or.inr (le_of_eq htv.symm))
      have hcolc : (reduceFrom S pivotRow col row fuel).matrix.get t c = S.matrix.get t c :=
        reduceFrom_outside_get (S := S) pivotRow col row fuel t c (Or.inr (le_of_eq htv.symm))
      have hpiv := reduceFrom_pivotRow_get (S := S) pivotRow col row fuel c
      rw [hcol, hcolc, hpiv]
      simp
    · have ht2' : t.val < row + fuel := by omega
      split
      · rename_i hb
        split
        · exact ih ht2'
        · rename_i hnep
          rw [xorIfColumn_matrix_get]
          have hne : ¬ (t = (⟨row + fuel, hb⟩ : Fin m) ∧
              (reduceFrom S pivotRow col row fuel).matrix.get (⟨row + fuel, hb⟩ : Fin m) col
                = true) :=
            fun ⟨he, _⟩ => htv (congrArg Fin.val he)
          rw [ite_eq_right hne]
          exact ih ht2'
      · exact ih ht2'

/-- General consequence of the three raw-bit facts above: if the pivot row's own entry in
column `c` is already `false`, `reduceFrom` never changes column `c` anywhere, since each
conditional row-XOR is then a no-op in that column regardless of whether it fires. -/
theorem reduceFrom_col_get_of_pivotRow_false {S : EchelonForm m n} (pivotRow : Fin m)
    (col row fuel : Nat) (c : Nat) (hz : S.matrix.get pivotRow c = false) (t : Fin m) :
    (reduceFrom S pivotRow col row fuel).matrix.get t c = S.matrix.get t c := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have heq : reduceFrom S pivotRow col row (fuel + 1) =
        if hb : row + fuel < m then
          if row + fuel = pivotRow.val then reduceFrom S pivotRow col row fuel
          else xorIfColumn col pivotRow (reduceFrom S pivotRow col row fuel) ⟨row + fuel, hb⟩
        else reduceFrom S pivotRow col row fuel := rfl
    rw [heq]
    split
    · split
      · exact ih
      · rw [xorIfColumn_matrix_get, reduceFrom_pivotRow_get, hz, ih]
        simp
    · exact ih

/-- `reduceFrom` never changes `pivots` (only `matrix`/`transform`/`transformInvT` are
touched by `xorIfColumn`). -/
theorem reduceFrom_pivots (S : EchelonForm m n) (pivotRow : Fin m) (col row fuel : Nat) :
    (reduceFrom S pivotRow col row fuel).pivots = S.pivots := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have heq : reduceFrom S pivotRow col row (fuel + 1) =
        if hb : row + fuel < m then
          if row + fuel = pivotRow.val then reduceFrom S pivotRow col row fuel
          else xorIfColumn col pivotRow (reduceFrom S pivotRow col row fuel) ⟨row + fuel, hb⟩
        else reduceFrom S pivotRow col row fuel := rfl
    rw [heq]
    split
    · split
      · exact ih
      · show (xorIfColumn col pivotRow (reduceFrom S pivotRow col row fuel)
            ⟨row + fuel, by assumption⟩).pivots = S.pivots
        unfold xorIfColumn
        rcases (reduceFrom S pivotRow col row fuel).matrix.get _ _ with _ | _
        · exact ih
        · exact ih
    · exact ih

/-! ## `EchelonInvariant`: the loop invariant maintained by `EchelonForm.new`

The invariant maintained by the main loop: `S.transform`/`S.transformInvT` correctly
realize `original` as `S.matrix` in both directions, `S.pivots` is a strictly increasing,
in-range list of column indices exactly characterizing where `S.matrix` has its pivot
ones (row `i` is the unique row with a set bit at column `S.pivots[i]`, for
`i < S.pivots.length`), and no row from `S.pivots.length` onward has any set bit before
`searchCol S`. -/
structure EchelonInvariant (original : PackedMatrix m n) (S : EchelonForm m n) : Prop where
  /-- Pivot columns are recorded in strictly increasing order. -/
  pivots_sorted : S.pivots.Pairwise (· < ·)
  /-- Every pivot column is a valid column index. -/
  pivots_lt_n : ∀ c ∈ S.pivots, c < n
  /-- Every pivot column lies before the next search column. -/
  pivots_lt_search : ∀ c ∈ S.pivots, c < searchCol S
  /-- `transform` realizes `matrix` as the image of `original` under the accumulated row
  operations, mirroring `EchelonForm::transform`'s documented contract. -/
  transform_mul_eq : S.transform.decode * original.decode = S.matrix.decode
  /-- `transform` and `transformInvT` are (transpose-)inverse, mirroring
  `EchelonForm::transform_inv_t`'s documented contract, in Rust's exact orientation. -/
  transform_mul_inv : S.transform.decode * (S.transformInvT.decode)ᵀ = 1
  /-- Column `S.pivots[i]` has a set bit at row `i` and nowhere else, for every already-found
  pivot index `i`. -/
  pivot_unit : ∀ (i : Nat) (hi : i < S.pivots.length) (row : Fin m),
      S.matrix.get row (S.pivots[i]'hi) = true ↔ row.val = i
  /-- Every row from `S.pivots.length` onward is all-zero before `searchCol S`. -/
  rows_zero : ∀ (row : Fin m), S.pivots.length ≤ row.val →
      ∀ (col : Nat), col < searchCol S → S.matrix.get row col = false

/-- `EchelonInvariant` holds trivially for the starting state of `EchelonForm.new`: the
identity transforms realize `M` as itself, and there are no pivots yet to satisfy or
violate any of the pivot/zero conditions. -/
theorem echelonInvariant_S0 (M : PackedMatrix m n) :
    EchelonInvariant M
      ({ matrix := M, transform := PackedMatrix.identity m,
         transformInvT := PackedMatrix.identity m, pivots := [] } : EchelonForm m n) where
  pivots_sorted := List.Pairwise.nil
  pivots_lt_n := by simp
  pivots_lt_search := by simp
  transform_mul_eq := by
    show (PackedMatrix.identity m).decode * M.decode = M.decode
    rw [decode_identity, Matrix.one_mul]
  transform_mul_inv := by
    show (PackedMatrix.identity m).decode * ((PackedMatrix.identity m).decode)ᵀ = 1
    rw [decode_identity, Matrix.transpose_one, Matrix.one_mul]
  pivot_unit := by simp
  rows_zero := by simp [searchCol]

/-- `applyPivot` preserves `EchelonInvariant`, given a pivot freshly found by `pivotOf` at
the current loop row `rowIndex` (whose value must equal the number of pivots already
found). This is the heart of the main loop's correctness: it combines `swapState`'s row
permutation (moving the found pivot row into position `rowIndex`) with a full
`reduceWithTransforms` pass (clearing column `pivotCol` everywhere else), and shows the
result keeps every previously-established pivot column intact while making the newly
found column a fresh unit pivot at row `rowIndex`. -/
theorem applyPivot_invariant {original : PackedMatrix m n} {S : EchelonForm m n}
    (hinv : EchelonInvariant original S) (rowIndex pivotRowFound : Fin m) (pivotCol : Nat)
    (hlen : rowIndex.val = S.pivots.length) (hcolge : searchCol S ≤ pivotCol)
    (hcollt : pivotCol < n) (hpivrow : rowIndex.val ≤ pivotRowFound.val)
    (hset : S.matrix.get pivotRowFound pivotCol = true)
    (hzero : ∀ c, searchCol S ≤ c → c < pivotCol →
        ∀ r, rowIndex.val ≤ r → r < m → getTotal S.matrix r c = false) :
    EchelonInvariant original (applyPivot S rowIndex pivotRowFound pivotCol) := by
  set S1 := swapState S pivotRowFound rowIndex with hS1def
  set S2 : EchelonForm m n := { S1 with pivots := S1.pivots ++ [pivotCol] } with hS2def
  have hresult : applyPivot S rowIndex pivotRowFound pivotCol
      = reduceFrom S2 rowIndex pivotCol 0 m := rfl
  have hS2matrix : S2.matrix = S1.matrix := rfl
  have hS2pivots : S2.pivots = S.pivots ++ [pivotCol] := rfl
  have hS1matrix_get : ∀ (row : Fin m) (c : Nat),
      S1.matrix.get row c = S.matrix.get (Equiv.swap pivotRowFound rowIndex row) c := by
    intro row c
    show (swapRows S.matrix pivotRowFound rowIndex).get row c = _
    exact get_swapRows S.matrix pivotRowFound rowIndex row c
  -- Combined fact: below `pivotCol`, original rows at or after `rowIndex` are zero,
  -- whether from the old `rows_zero` invariant or from `pivotOf`'s own search gap.
  have hzero_combined : ∀ c, c < pivotCol → ∀ r : Fin m, rowIndex.val ≤ r.val →
      S.matrix.get r c = false := by
    intro c hc r hr
    by_cases hcs : c < searchCol S
    · exact hinv.rows_zero r (hlen ▸ hr) c hcs
    · simp only [not_lt] at hcs
      have hgt := hzero c hcs hc r.val hr r.isLt
      unfold getTotal at hgt
      rwa [dite_eq_left r.isLt] at hgt
  -- After the swap, every row at or after `rowIndex` is still zero below `pivotCol`.
  have hS1_ge_zero : ∀ (row : Fin m), rowIndex.val ≤ row.val → ∀ c, c < pivotCol →
      S1.matrix.get row c = false := by
    intro row hrow c hc
    rw [hS1matrix_get]
    rcases eq_or_ne row pivotRowFound with hrp | hrp
    · rw [hrp, Equiv.swap_apply_left]
      exact hzero_combined c hc rowIndex (le_refl _)
    rcases eq_or_ne row rowIndex with hri | hri
    · rw [hri, Equiv.swap_apply_right]
      exact hzero_combined c hc pivotRowFound hpivrow
    · rw [Equiv.swap_apply_of_ne_of_ne hrp hri]
      exact hzero_combined c hc row hrow
  have hS2_rowIndex_zero : ∀ c, c < pivotCol → S2.matrix.get rowIndex c = false := by
    intro c hc
    rw [hS2matrix]
    exact hS1_ge_zero rowIndex (le_refl _) c hc
  -- The swap moves the freshly found pivot bit onto row `rowIndex`.
  have hS1_rowIndex_set : S1.matrix.get rowIndex pivotCol = true := by
    rw [hS1matrix_get, Equiv.swap_apply_right]
    exact hset
  -- Old pivot rows/columns are untouched by the swap: both swapped indices are at or
  -- above the old pivot count, strictly above every old pivot row index.
  have hS1_pivot_pattern : ∀ (i : Nat) (hi : i < S.pivots.length), ∀ row : Fin m,
      S1.matrix.get row (S.pivots[i]'hi) = true ↔ row.val = i := by
    intro i hi row
    have hik : i < rowIndex.val := hlen ▸ hi
    rw [hS1matrix_get]
    rcases eq_or_ne row pivotRowFound with hrp | hrp
    · subst hrp
      rw [Equiv.swap_apply_left, hinv.pivot_unit i hi rowIndex]
      omega
    rcases eq_or_ne row rowIndex with hri | hri
    · subst hri
      rw [Equiv.swap_apply_right, hinv.pivot_unit i hi pivotRowFound]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hrp hri]
      exact hinv.pivot_unit i hi row
  have hS3pivots : (reduceFrom S2 rowIndex pivotCol 0 m).pivots = S.pivots ++ [pivotCol] :=
    (reduceFrom_pivots S2 rowIndex pivotCol 0 m).trans hS2pivots
  have hsearchS3 : searchCol (reduceFrom S2 rowIndex pivotCol 0 m) = pivotCol + 1 := by
    show (match (reduceFrom S2 rowIndex pivotCol 0 m).pivots.getLast? with
      | some c => c + 1 | none => 0) = pivotCol + 1
    rw [hS3pivots, List.getLast?_concat]
  have hnewpivot : ∀ row : Fin m,
      (reduceFrom S2 rowIndex pivotCol 0 m).matrix.get row pivotCol = true ↔ row = rowIndex := by
    intro row
    have hS2_rowIndex_set : S2.matrix.get rowIndex pivotCol = true := by
      rw [hS2matrix]; exact hS1_rowIndex_set
    rcases eq_or_ne row rowIndex with hri | hri
    · subst hri
      rw [reduceFrom_pivotRow_get, hS2matrix]
      simpa using hS1_rowIndex_set
    · have hstep := reduceFrom_inside_get (S := S2) rowIndex pivotCol 0 m row pivotCol
        (Nat.zero_le _) (by omega) hri
      rw [hstep]
      have hxor_false : (if S2.matrix.get row pivotCol = true then
          S2.matrix.get row pivotCol ^^ S2.matrix.get rowIndex pivotCol
        else S2.matrix.get row pivotCol) = false := by
        rcases S2.matrix.get row pivotCol with _ | _
        · simp
        · simp [hS2_rowIndex_set]
      rw [hxor_false]
      simp [hri]
  rw [hresult]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pivots_sorted
    rw [hS3pivots, List.pairwise_append]
    refine ⟨hinv.pivots_sorted, by simp, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb
    subst hb
    exact lt_of_lt_of_le (hinv.pivots_lt_search a ha) hcolge
  · -- pivots_lt_n
    rw [hS3pivots]
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hinv.pivots_lt_n c hc
    · simp only [List.mem_singleton] at hc; subst hc; exact hcollt
  · -- pivots_lt_search
    rw [hS3pivots, hsearchS3]
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · have h1 := hinv.pivots_lt_search c hc
      omega
    · simp only [List.mem_singleton] at hc; omega
  · -- transform_mul_eq
    exact reduceFrom_TA_eq_M rowIndex pivotCol 0 m
      (swapState_TA_eq_M pivotRowFound rowIndex hinv.transform_mul_eq)
  · -- transform_mul_inv
    exact reduceFrom_TUt_eq_one rowIndex pivotCol 0 m
      (swapState_TUt_eq_one pivotRowFound rowIndex hinv.transform_mul_inv)
  · -- pivot_unit
    intro i hi row
    rw [getElem_congr_coll hS3pivots]
    rcases Nat.lt_or_ge i S.pivots.length with hik | hik
    · rw [List.getElem_append_left hik]
      have hzcol : S2.matrix.get rowIndex (S.pivots[i]'hik) = false := by
        rw [hS2matrix, Bool.eq_false_iff]
        intro hcontra
        have hcontra' := (hS1_pivot_pattern i hik rowIndex).mp hcontra
        omega
      rw [reduceFrom_col_get_of_pivotRow_false rowIndex pivotCol 0 m (S.pivots[i]'hik) hzcol row,
        hS2matrix]
      exact hS1_pivot_pattern i hik row
    · have hi' : i < (S.pivots ++ [pivotCol]).length := hS3pivots ▸ hi
      simp only [List.length_append, List.length_singleton] at hi'
      have hieq : i = S.pivots.length := by omega
      rw [List.getElem_concat_length hieq, hnewpivot row, Fin.ext_iff]
      omega
  · -- rows_zero
    intro row hrow col hcol
    rw [hS3pivots] at hrow
    simp only [List.length_append, List.length_singleton] at hrow
    rw [hsearchS3] at hcol
    have hrow' : rowIndex.val < row.val := by omega
    by_cases hcp : col = pivotCol
    · subst hcp
      have hrne : row ≠ rowIndex := by
        intro h; rw [h] at hrow'; omega
      exact Bool.eq_false_iff.mpr (fun hc => hrne ((hnewpivot row).mp hc))
    · have hcp' : col < pivotCol := by omega
      rw [reduceFrom_col_get_of_pivotRow_false rowIndex pivotCol 0 m col
        (hS2_rowIndex_zero col hcp') row, hS2matrix]
      exact hS1_ge_zero row (by omega) col hcp'

/-! ## The main loop induction: `EchelonInvariant` holds at every step of `EchelonForm.new` -/

/-- `applyPivot`'s `pivots` field, spelled out generically (no `EchelonInvariant`
hypothesis needed): swapping rows never touches `pivots`, and the subsequent
`reduceWithTransforms` pass doesn't either, so only the explicit `++ [pivotCol]` survives. -/
theorem applyPivot_pivots (S : EchelonForm m n) (rowIndex pivotRowFound : Fin m) (pivotCol : Nat) :
    (applyPivot S rowIndex pivotRowFound pivotCol).pivots = S.pivots ++ [pivotCol] := by
  show (reduceFrom { swapState S pivotRowFound rowIndex with
      pivots := (swapState S pivotRowFound rowIndex).pivots ++ [pivotCol] } rowIndex pivotCol 0 m).pivots
    = S.pivots ++ [pivotCol]
  rw [reduceFrom_pivots]
  rfl

/-- `EchelonInvariant` holds after every iteration of `EchelonForm.new`'s main loop,
provided the loop is entered with `rowIndex` already equal to the pivot count found so
far and enough `fuel` left to reach row `m`. This drives the loop forward one step at a
time using `applyPivot_invariant`, discharging its side hypotheses from `pivotOf_success`
/ `pivotOf_col_ge` / `pivotOf_lt_zero` / `lt_of_getTotal`, and threading `searchCol`
forward via `applyPivot_pivots` and `List.getLast?_concat`. The defensive fallback
branches of `echelonAux` (taken only when `rowIndex` or the found row are out of range)
are never reached along this path, since `hfuel` always keeps `rowIndex < m`, and
`pivotOf_success` combined with `lt_of_getTotal` always keeps the found row in range too. -/
theorem echelonAux_invariant {original : PackedMatrix m n} :
    ∀ (fuel : Nat) (S : EchelonForm m n) (rowIndex : Nat),
      EchelonInvariant original S → rowIndex = S.pivots.length → rowIndex + fuel = m →
      EchelonInvariant original
        (echelonAux S (pivotOf S.matrix rowIndex (searchCol S)).1
          (pivotOf S.matrix rowIndex (searchCol S)).2 rowIndex fuel) := by
  intro fuel
  induction fuel with
  | zero => intro S rowIndex hinv _ _; exact hinv
  | succ fuel ih =>
    intro S rowIndex hinv hlen hfuel
    by_cases hfc : (pivotOf S.matrix rowIndex (searchCol S)).2 < n
    · have hr : rowIndex < m := by omega
      obtain ⟨hset, hpivrow⟩ := pivotOf_success hfc
      have hfr : (pivotOf S.matrix rowIndex (searchCol S)).1 < m := lt_of_getTotal hset
      have heq : echelonAux S (pivotOf S.matrix rowIndex (searchCol S)).1
          (pivotOf S.matrix rowIndex (searchCol S)).2 rowIndex (fuel + 1) =
        (if (pivotOf S.matrix rowIndex (searchCol S)).2 < n then
          if hr' : rowIndex < m then
            if hfr' : (pivotOf S.matrix rowIndex (searchCol S)).1 < m then
              let S' := applyPivot S ⟨rowIndex, hr'⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr'⟩
                (pivotOf S.matrix rowIndex (searchCol S)).2
              let next := pivotOf S'.matrix (rowIndex + 1) ((pivotOf S.matrix rowIndex (searchCol S)).2 + 1)
              echelonAux S' next.1 next.2 (rowIndex + 1) fuel
            else S
          else S
        else S) := rfl
      rw [heq, ite_eq_left hfc, dite_eq_left hr, dite_eq_left hfr]
      show EchelonInvariant original
        (echelonAux
          (applyPivot S ⟨rowIndex, hr⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
            (pivotOf S.matrix rowIndex (searchCol S)).2)
          (pivotOf (applyPivot S ⟨rowIndex, hr⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
              (pivotOf S.matrix rowIndex (searchCol S)).2).matrix
            (rowIndex + 1) ((pivotOf S.matrix rowIndex (searchCol S)).2 + 1)).1
          (pivotOf (applyPivot S ⟨rowIndex, hr⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
              (pivotOf S.matrix rowIndex (searchCol S)).2).matrix
            (rowIndex + 1) ((pivotOf S.matrix rowIndex (searchCol S)).2 + 1)).2
          (rowIndex + 1) fuel)
      have hnewinv : EchelonInvariant original
          (applyPivot S ⟨rowIndex, hr⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
            (pivotOf S.matrix rowIndex (searchCol S)).2) := by
        have hset' : S.matrix.get ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
            (pivotOf S.matrix rowIndex (searchCol S)).2 = true := by
          unfold getTotal at hset
          rwa [dite_eq_left hfr] at hset
        exact applyPivot_invariant hinv ⟨rowIndex, hr⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
          (pivotOf S.matrix rowIndex (searchCol S)).2 hlen
          (pivotOf_col_ge S.matrix rowIndex (searchCol S)) hfc hpivrow hset'
          (pivotOf_lt_zero S.matrix rowIndex (searchCol S))
      have hnewlen : rowIndex + 1 =
          (applyPivot S ⟨rowIndex, hr⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
            (pivotOf S.matrix rowIndex (searchCol S)).2).pivots.length := by
        rw [applyPivot_pivots, List.length_append, List.length_singleton]
        omega
      have hnewfuel : (rowIndex + 1) + fuel = m := by omega
      have hsearch' : searchCol
          (applyPivot S ⟨rowIndex, hr⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
            (pivotOf S.matrix rowIndex (searchCol S)).2)
          = (pivotOf S.matrix rowIndex (searchCol S)).2 + 1 := by
        unfold searchCol
        rw [applyPivot_pivots, List.getLast?_concat]
      rw [← hsearch']
      exact ih _ (rowIndex + 1) hnewinv hnewlen hnewfuel
    · have heq2 : echelonAux S (pivotOf S.matrix rowIndex (searchCol S)).1
          (pivotOf S.matrix rowIndex (searchCol S)).2 rowIndex (fuel + 1) = S := by
        show (if (pivotOf S.matrix rowIndex (searchCol S)).2 < n then
            if hr' : rowIndex < m then
              if hfr' : (pivotOf S.matrix rowIndex (searchCol S)).1 < m then
                let S' := applyPivot S ⟨rowIndex, hr'⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr'⟩
                  (pivotOf S.matrix rowIndex (searchCol S)).2
                let next := pivotOf S'.matrix (rowIndex + 1) ((pivotOf S.matrix rowIndex (searchCol S)).2 + 1)
                echelonAux S' next.1 next.2 (rowIndex + 1) fuel
              else S
            else S
          else S) = S
        rw [ite_eq_right hfc]
      rw [heq2]
      exact hinv

/-- `EchelonInvariant` holds for the result of `EchelonForm.new`, applying
`echelonAux_invariant` from the starting state (identity transforms, no pivots, `rowIndex
= 0`, full `fuel = m`). -/
theorem EchelonForm.new_invariant (M : PackedMatrix m n) :
    EchelonInvariant M (EchelonForm.new M) := by
  show EchelonInvariant M
    (echelonAux
      { matrix := M, transform := PackedMatrix.identity m,
        transformInvT := PackedMatrix.identity m, pivots := [] }
      (pivotOf M 0 0).1 (pivotOf M 0 0).2 0 m)
  exact echelonAux_invariant m
    { matrix := M, transform := PackedMatrix.identity m,
      transformInvT := PackedMatrix.identity m, pivots := [] }
    0 (echelonInvariant_S0 M) rfl (by omega)

/-- Companion fact to `echelonAux_invariant`, tracking the loop's termination condition:
either every row has been assigned a pivot, or the final pivot search (the one that broke
the loop) found nothing in the remaining columns, in which case `pivotOf_lt_zero` gives a
zero fact covering the "search gap" `[searchCol R, n)` for every row from `R.pivots.length`
onward. Combined with `EchelonInvariant.rows_zero` (which only covers `[0, searchCol R)`),
this lets `EchelonForm.new_rows_zero` below extend zero-coverage to every column `< n`. -/
theorem echelonAux_search_gap :
    ∀ (fuel : Nat) (S : EchelonForm m n) (rowIndex : Nat),
      rowIndex = S.pivots.length → rowIndex + fuel = m →
      (let R := echelonAux S (pivotOf S.matrix rowIndex (searchCol S)).1
        (pivotOf S.matrix rowIndex (searchCol S)).2 rowIndex fuel
       R.pivots.length = m ∨
         ∀ c, searchCol R ≤ c → c < n →
           ∀ r, R.pivots.length ≤ r → r < m → getTotal R.matrix r c = false) := by
  intro fuel
  induction fuel with
  | zero =>
    intro S rowIndex hlen hfuel
    show S.pivots.length = m ∨ _
    exact Or.inl (by omega)
  | succ fuel ih =>
    intro S rowIndex hlen hfuel
    by_cases hfc : (pivotOf S.matrix rowIndex (searchCol S)).2 < n
    · have hr : rowIndex < m := by omega
      obtain ⟨hset, hpivrow⟩ := pivotOf_success hfc
      have hfr : (pivotOf S.matrix rowIndex (searchCol S)).1 < m := lt_of_getTotal hset
      have heq : echelonAux S (pivotOf S.matrix rowIndex (searchCol S)).1
          (pivotOf S.matrix rowIndex (searchCol S)).2 rowIndex (fuel + 1) =
        (if (pivotOf S.matrix rowIndex (searchCol S)).2 < n then
          if hr' : rowIndex < m then
            if hfr' : (pivotOf S.matrix rowIndex (searchCol S)).1 < m then
              let S' := applyPivot S ⟨rowIndex, hr'⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr'⟩
                (pivotOf S.matrix rowIndex (searchCol S)).2
              let next := pivotOf S'.matrix (rowIndex + 1) ((pivotOf S.matrix rowIndex (searchCol S)).2 + 1)
              echelonAux S' next.1 next.2 (rowIndex + 1) fuel
            else S
          else S
        else S) := rfl
      rw [heq, ite_eq_left hfc, dite_eq_left hr, dite_eq_left hfr]
      have hnewlen : rowIndex + 1 =
          (applyPivot S ⟨rowIndex, hr⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
            (pivotOf S.matrix rowIndex (searchCol S)).2).pivots.length := by
        rw [applyPivot_pivots, List.length_append, List.length_singleton]
        omega
      have hnewfuel : (rowIndex + 1) + fuel = m := by omega
      have hsearch' : searchCol
          (applyPivot S ⟨rowIndex, hr⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
            (pivotOf S.matrix rowIndex (searchCol S)).2)
          = (pivotOf S.matrix rowIndex (searchCol S)).2 + 1 := by
        unfold searchCol
        rw [applyPivot_pivots, List.getLast?_concat]
      have hthis := ih
        (applyPivot S ⟨rowIndex, hr⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
          (pivotOf S.matrix rowIndex (searchCol S)).2)
        (rowIndex + 1) hnewlen hnewfuel
      rw [hsearch'] at hthis
      exact hthis
    · have heq2 : echelonAux S (pivotOf S.matrix rowIndex (searchCol S)).1
          (pivotOf S.matrix rowIndex (searchCol S)).2 rowIndex (fuel + 1) = S := by
        show (if (pivotOf S.matrix rowIndex (searchCol S)).2 < n then
            if hr' : rowIndex < m then
              if hfr' : (pivotOf S.matrix rowIndex (searchCol S)).1 < m then
                let S' := applyPivot S ⟨rowIndex, hr'⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr'⟩
                  (pivotOf S.matrix rowIndex (searchCol S)).2
                let next := pivotOf S'.matrix (rowIndex + 1) ((pivotOf S.matrix rowIndex (searchCol S)).2 + 1)
                echelonAux S' next.1 next.2 (rowIndex + 1) fuel
              else S
            else S
          else S) = S
        rw [ite_eq_right hfc]
      rw [heq2]
      refine Or.inr (fun c hc1 hc2 r hr1 hr2 => ?_)
      have hcol : c < (pivotOf S.matrix rowIndex (searchCol S)).2 := by omega
      exact pivotOf_lt_zero S.matrix rowIndex (searchCol S) c hc1 hcol r (by omega) hr2

/-- Companion bound to `echelonAux_search_gap`/`echelonAux_invariant`: the number of
pivots found never exceeds the row count `m`, since `pivots.length` tracks `rowIndex`
lockstep and `rowIndex + fuel = m` keeps `rowIndex ≤ m` throughout. Needed to view the
first `pivots.length` rows of the result as a `Fin (pivots.length) → Fin m` inclusion in
the rank argument below. -/
theorem echelonAux_pivots_length_le :
    ∀ (fuel : Nat) (S : EchelonForm m n) (rowIndex : Nat),
      rowIndex = S.pivots.length → rowIndex + fuel = m →
      (echelonAux S (pivotOf S.matrix rowIndex (searchCol S)).1
        (pivotOf S.matrix rowIndex (searchCol S)).2 rowIndex fuel).pivots.length ≤ m := by
  intro fuel
  induction fuel with
  | zero =>
    intro S rowIndex hlen hfuel
    show S.pivots.length ≤ m
    omega
  | succ fuel ih =>
    intro S rowIndex hlen hfuel
    by_cases hfc : (pivotOf S.matrix rowIndex (searchCol S)).2 < n
    · have hr : rowIndex < m := by omega
      obtain ⟨hset, hpivrow⟩ := pivotOf_success hfc
      have hfr : (pivotOf S.matrix rowIndex (searchCol S)).1 < m := lt_of_getTotal hset
      have heq : echelonAux S (pivotOf S.matrix rowIndex (searchCol S)).1
          (pivotOf S.matrix rowIndex (searchCol S)).2 rowIndex (fuel + 1) =
        (if (pivotOf S.matrix rowIndex (searchCol S)).2 < n then
          if hr' : rowIndex < m then
            if hfr' : (pivotOf S.matrix rowIndex (searchCol S)).1 < m then
              let S' := applyPivot S ⟨rowIndex, hr'⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr'⟩
                (pivotOf S.matrix rowIndex (searchCol S)).2
              let next := pivotOf S'.matrix (rowIndex + 1) ((pivotOf S.matrix rowIndex (searchCol S)).2 + 1)
              echelonAux S' next.1 next.2 (rowIndex + 1) fuel
            else S
          else S
        else S) := rfl
      rw [heq, ite_eq_left hfc, dite_eq_left hr, dite_eq_left hfr]
      show
        (let S' := applyPivot S ⟨rowIndex, hr⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
          (pivotOf S.matrix rowIndex (searchCol S)).2
         let next := pivotOf S'.matrix (rowIndex + 1) ((pivotOf S.matrix rowIndex (searchCol S)).2 + 1)
         echelonAux S' next.1 next.2 (rowIndex + 1) fuel).pivots.length ≤ m
      have hnewlen : rowIndex + 1 =
          (applyPivot S ⟨rowIndex, hr⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
            (pivotOf S.matrix rowIndex (searchCol S)).2).pivots.length := by
        rw [applyPivot_pivots, List.length_append, List.length_singleton]
        omega
      have hnewfuel : (rowIndex + 1) + fuel = m := by omega
      have hsearch' : searchCol
          (applyPivot S ⟨rowIndex, hr⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr⟩
            (pivotOf S.matrix rowIndex (searchCol S)).2)
          = (pivotOf S.matrix rowIndex (searchCol S)).2 + 1 := by
        unfold searchCol
        rw [applyPivot_pivots, List.getLast?_concat]
      rw [← hsearch']
      exact ih _ (rowIndex + 1) hnewlen hnewfuel
    · have heq2 : echelonAux S (pivotOf S.matrix rowIndex (searchCol S)).1
          (pivotOf S.matrix rowIndex (searchCol S)).2 rowIndex (fuel + 1) = S := by
        show (if (pivotOf S.matrix rowIndex (searchCol S)).2 < n then
            if hr' : rowIndex < m then
              if hfr' : (pivotOf S.matrix rowIndex (searchCol S)).1 < m then
                let S' := applyPivot S ⟨rowIndex, hr'⟩ ⟨(pivotOf S.matrix rowIndex (searchCol S)).1, hfr'⟩
                  (pivotOf S.matrix rowIndex (searchCol S)).2
                let next := pivotOf S'.matrix (rowIndex + 1) ((pivotOf S.matrix rowIndex (searchCol S)).2 + 1)
                echelonAux S' next.1 next.2 (rowIndex + 1) fuel
              else S
            else S
          else S) = S
        rw [ite_eq_right hfc]
      rw [heq2]
      show S.pivots.length ≤ m
      omega

/-- `EchelonForm.new`'s result never has more pivots than rows. -/
theorem EchelonForm.new_pivots_length_le (M : PackedMatrix m n) :
    (EchelonForm.new M).pivots.length ≤ m := by
  show
    (echelonAux
        { matrix := M, transform := PackedMatrix.identity m,
          transformInvT := PackedMatrix.identity m, pivots := [] }
        (pivotOf M 0 0).1 (pivotOf M 0 0).2 0 m).pivots.length ≤ m
  exact echelonAux_pivots_length_le m
    { matrix := M, transform := PackedMatrix.identity m,
      transformInvT := PackedMatrix.identity m, pivots := [] }
    0 rfl (by omega)

/-- Instantiates `echelonAux_search_gap` at `EchelonForm.new`'s starting state, mirroring
`EchelonForm.new_invariant`. -/
theorem EchelonForm.new_search_gap (M : PackedMatrix m n) :
    (EchelonForm.new M).pivots.length = m ∨
      ∀ c, searchCol (EchelonForm.new M) ≤ c → c < n →
        ∀ r, (EchelonForm.new M).pivots.length ≤ r → r < m →
          getTotal (EchelonForm.new M).matrix r c = false := by
  show
    (echelonAux
        { matrix := M, transform := PackedMatrix.identity m,
          transformInvT := PackedMatrix.identity m, pivots := [] }
        (pivotOf M 0 0).1 (pivotOf M 0 0).2 0 m).pivots.length = m ∨ _
  exact echelonAux_search_gap m
    { matrix := M, transform := PackedMatrix.identity m,
      transformInvT := PackedMatrix.identity m, pivots := [] }
    0 rfl (by omega)

/-- Every row from `(EchelonForm.new M).pivots.length` onward is entirely zero across
*all* `n` columns, extending `EchelonInvariant.rows_zero`'s `[0, searchCol)` coverage
with `EchelonForm.new_search_gap`'s `[searchCol, n)` coverage (vacuously true when every
row already has a pivot). This is the last ingredient `IsRREF` needs. -/
theorem EchelonForm.new_rows_zero (M : PackedMatrix m n) :
    ∀ (row : Fin m), (EchelonForm.new M).pivots.length ≤ row.val →
      ∀ (col : Nat), col < n → (EchelonForm.new M).matrix.get row col = false := by
  intro row hrow col hcol
  rcases EchelonForm.new_search_gap M with hfull | hgap
  · exfalso
    have := row.isLt
    omega
  · by_cases hcs : col < searchCol (EchelonForm.new M)
    · exact (EchelonForm.new_invariant M).rows_zero row hrow col hcs
    · simp only [not_lt] at hcs
      have := hgap col hcs hcol row.val hrow row.isLt
      unfold getTotal at this
      rwa [dite_eq_left row.isLt] at this

/-- Precise reduced-row-echelon-form predicate, matching Rust's documented `echelonize`
postcondition: `pivots` is a strictly increasing, in-range list of column indices, each
pivot column has a unit entry at its own row and nowhere else among the rows that carry
pivots, and every row past the last pivot is entirely zero. -/
structure IsRREF (R : PackedMatrix m n) (pivots : List Nat) : Prop where
  /-- Pivot columns are strictly increasing. -/
  sorted : pivots.Pairwise (· < ·)
  /-- Every pivot column is a valid column index. -/
  lt_n : ∀ c ∈ pivots, c < n
  /-- Column `pivots[i]` has a set bit at row `i` and nowhere else. -/
  pivot_unit : ∀ (i : Nat) (hi : i < pivots.length) (row : Fin m),
      R.get row (pivots[i]'hi) = true ↔ row.val = i
  /-- Every row from `pivots.length` onward is entirely zero. -/
  rows_zero : ∀ (row : Fin m), pivots.length ≤ row.val → ∀ (col : Nat), col < n →
      R.get row col = false

/-- `EchelonForm.new` produces a matrix/pivot-list pair satisfying `IsRREF`, mirroring
Rust `echelonize`'s documented postcondition. -/
theorem EchelonForm.new_isRREF (M : PackedMatrix m n) :
    IsRREF (EchelonForm.new M).matrix (EchelonForm.new M).pivots where
  sorted := (EchelonForm.new_invariant M).pivots_sorted
  lt_n := (EchelonForm.new_invariant M).pivots_lt_n
  pivot_unit := (EchelonForm.new_invariant M).pivot_unit
  rows_zero := EchelonForm.new_rows_zero M

/-- `EchelonForm.new`'s accumulated transform realizes the reduced matrix as the image
of the original under row operations, mirroring `EchelonForm::transform`'s documented
contract. -/
theorem EchelonForm.new_transform_mul_eq (M : PackedMatrix m n) :
    (EchelonForm.new M).transform.decode * M.decode = (EchelonForm.new M).matrix.decode :=
  (EchelonForm.new_invariant M).transform_mul_eq

/-- `EchelonForm.new`'s `transform` and `transformInvT` are (transpose-)inverse, in
Rust's exact documented orientation: `T * Uᵀ = 1`. -/
theorem EchelonForm.new_transform_mul_inv (M : PackedMatrix m n) :
    (EchelonForm.new M).transform.decode * ((EchelonForm.new M).transformInvT.decode)ᵀ = 1 :=
  (EchelonForm.new_invariant M).transform_mul_inv

/-! ## Row space preservation and the rank connection

`EchelonForm.new`'s row operations are invertible (`T * Uᵀ = 1`), so the reduced matrix
and the original matrix have the same row space: each row of one is a genuine `F2`-linear
combination of the rows of the other. Combined with the fact that the reduced matrix's
first `pivots.length` rows already span everything (every later row is zero) and are
linearly independent (the pivot columns restrict them to the identity matrix), this
identifies `pivots.length` with Mathlib's `Matrix.rank`, discharging requirement (4). -/

/-- Left-multiplying by any square matrix cannot enlarge the row space: every row of
`T * A` is an `F2`-linear combination of the rows of `A`. -/
theorem span_range_mul_le (T : Matrix (Fin m) (Fin m) F2) (A : Matrix (Fin m) (Fin n) F2) :
    Submodule.span F2 (Set.range (T * A)) ≤ Submodule.span F2 (Set.range A) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  have hrow : (T * A) i = ∑ j, T i j • A j := by
    funext c
    simp [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrow]
  exact Submodule.sum_mem _
    fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

/-- `EchelonForm.new`'s row operations preserve the row space: the reduced matrix and
the original matrix span the same subspace of `Fin n → F2`. -/
theorem EchelonForm.new_rowSpace_eq (M : PackedMatrix m n) :
    Submodule.span F2 (Set.range (EchelonForm.new M).matrix.decode) =
      Submodule.span F2 (Set.range M.decode) := by
  have hTA := EchelonForm.new_transform_mul_eq M
  have hTU := EchelonForm.new_transform_mul_inv M
  have hTdet : IsUnit (EchelonForm.new M).transform.decode.det :=
    Matrix.isUnit_det_of_right_inverse hTU
  have hTinv : (EchelonForm.new M).transform.decode⁻¹ = ((EchelonForm.new M).transformInvT.decode)ᵀ :=
    Matrix.inv_eq_right_inv hTU
  have hUT : ((EchelonForm.new M).transformInvT.decode)ᵀ * (EchelonForm.new M).transform.decode = 1 := by
    rw [← hTinv]
    exact Matrix.nonsing_inv_mul _ hTdet
  refine le_antisymm ?_ ?_
  · rw [← hTA]
    exact span_range_mul_le _ _
  · have hA : M.decode = ((EchelonForm.new M).transformInvT.decode)ᵀ * (EchelonForm.new M).matrix.decode := by
      rw [← hTA, ← Matrix.mul_assoc, hUT, Matrix.one_mul]
    rw [hA]
    exact span_range_mul_le _ _

/-- The number of pivots found by `EchelonForm.new` equals Mathlib's `Matrix.rank` of the
original decoded matrix. This is requirement (4): the executable, packed pivot count
computed by the Rust-mirroring algorithm agrees exactly with the abstract linear-algebra
notion of rank, for every rectangular (including zero-dimensional) matrix. -/
theorem EchelonForm.new_pivots_length_eq_rank (M : PackedMatrix m n) :
    (EchelonForm.new M).pivots.length = M.decode.rank := by
  have hrref := EchelonForm.new_isRREF M
  have hrm : (EchelonForm.new M).pivots.length ≤ m := EchelonForm.new_pivots_length_le M
  have hTdet : IsUnit (EchelonForm.new M).transform.decode.det :=
    Matrix.isUnit_det_of_right_inverse (EchelonForm.new_transform_mul_inv M)
  have hMrank : (EchelonForm.new M).matrix.decode.rank = M.decode.rank := by
    rw [← EchelonForm.new_transform_mul_eq M]
    exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ hTdet
  rw [← hMrank]
  set r := (EchelonForm.new M).pivots.length with hr_def
  set Mrows := (EchelonForm.new M).matrix.decode.submatrix (Fin.castLE hrm) id with hMrows_def
  set pivotColFn : Fin r → Fin n :=
    fun i => ⟨(EchelonForm.new M).pivots[i.1]'i.2, hrref.lt_n _ (List.getElem_mem i.2)⟩
    with hpivotColFn_def
  set Munit := Mrows.submatrix id pivotColFn with hMunit_def
  have hrank_le : Mrows.rank ≤ r := Matrix.rank_le_height Mrows
  have hone : Munit = 1 := by
    funext i j
    rw [hMunit_def, hMrows_def, Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.one_apply]
    simp only [id_eq]
    rw [PackedMatrix.decode_get]
    have hpu := hrref.pivot_unit j.1 j.2 (Fin.castLE hrm i)
    by_cases hij : i = j
    · have hval : i.val = j.1 := by rw [hij]
      have hget : (EchelonForm.new M).matrix.get (Fin.castLE hrm i) (pivotColFn j).val = true :=
        hpu.mpr hval
      rw [ite_eq_left hij, hget, Bool.toF2_true]
    · have hne : i.val ≠ j.1 := fun h => hij (Fin.eq_of_val_eq h)
      have hget : (EchelonForm.new M).matrix.get (Fin.castLE hrm i) (pivotColFn j).val = false :=
        Bool.eq_false_iff.mpr (fun h => hne (hpu.mp h))
      rw [ite_eq_right hij, hget, Bool.toF2_false]
  have hr_le_Munit : r ≤ Munit.rank := by
    simp [hone, Matrix.rank_one, Fintype.card_fin]
  have hr_le_Mrows : r ≤ Mrows.rank := by
    refine hr_le_Munit.trans ?_
    rw [hMunit_def]
    exact Matrix.rank_submatrix_le Mrows id pivotColFn
  have hMrows_rank : Mrows.rank = r := le_antisymm hrank_le hr_le_Mrows
  have hspan_le1 : Submodule.span F2 (Set.range (EchelonForm.new M).matrix.decode) ≤
      Submodule.span F2 (Set.range Mrows) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    by_cases hiv : i.val < r
    · have heq : (EchelonForm.new M).matrix.decode i = Mrows ⟨i.val, hiv⟩ := by
        rw [hMrows_def]
        rfl
      rw [heq]
      exact Submodule.subset_span (Set.mem_range_self _)
    · have hzero : (EchelonForm.new M).matrix.decode i = 0 := by
        funext c
        rw [PackedMatrix.decode_get, EchelonForm.new_rows_zero M i (by omega) c.val c.isLt]
        rfl
      rw [hzero]
      exact Submodule.zero_mem _
  have hspan_le2 : Submodule.span F2 (Set.range Mrows) ≤
      Submodule.span F2 (Set.range (EchelonForm.new M).matrix.decode) := by
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castLE hrm i, by rw [hMrows_def]; rfl⟩
  have hspan_eq : Submodule.span F2 (Set.range (EchelonForm.new M).matrix.decode) =
      Submodule.span F2 (Set.range Mrows) := le_antisymm hspan_le1 hspan_le2
  have hrank_eq : Mrows.rank = (EchelonForm.new M).matrix.decode.rank := by
    have h1 := Matrix.rank_eq_finrank_span_row Mrows
    have h2 := Matrix.rank_eq_finrank_span_row (EchelonForm.new M).matrix.decode
    unfold Matrix.row at h1 h2
    rw [h1, h2, hspan_eq]
  rw [← hrank_eq]
  exact hMrows_rank.symm

/-! ## Transform-free view (requirement 5)

Rust's `AlignedBitMatrix` also exposes transform-free entry points (`echelonize`/`rank`)
that discard the transform `T` and inverse-transpose `U` and return only the reduced
matrix / pivot count. We expose the same view here as thin projections of
`EchelonForm.new`, and restate its proofs verbatim: no new elimination algorithm or
proof is introduced, matching requirement (5). -/

/-- Transform-free packed RREF: the reduced matrix produced by `EchelonForm.new`,
discarding the transform `T` and inverse-transpose `U`. Mirrors the reduced-matrix
part of Rust's `AlignedBitMatrix::echelonize`. -/
def echelonize (M : PackedMatrix m n) : PackedMatrix m n := (EchelonForm.new M).matrix

/-- `echelonize M` is in reduced row echelon form with pivot columns
`(EchelonForm.new M).pivots`, restating `EchelonForm.new_isRREF` transform-free. -/
theorem echelonize_isRREF (M : PackedMatrix m n) :
    IsRREF (echelonize M) (EchelonForm.new M).pivots :=
  EchelonForm.new_isRREF M

/-- `echelonize` preserves row space, restating `EchelonForm.new_rowSpace_eq`
transform-free. -/
theorem echelonize_rowSpace_eq (M : PackedMatrix m n) :
    Submodule.span F2 (Set.range (echelonize M).decode) =
      Submodule.span F2 (Set.range M.decode) :=
  EchelonForm.new_rowSpace_eq M

/-- Transform-free packed rank: the number of pivots `EchelonForm.new` finds. Mirrors
Rust's `AlignedBitMatrix::rank` (`echelonize().pivots.len()`). -/
def PackedMatrix.rank (M : PackedMatrix m n) : Nat := (EchelonForm.new M).pivots.length

/-- `PackedMatrix.rank` agrees with Mathlib's `Matrix.rank`, restating requirement (4)
transform-free. -/
theorem PackedMatrix.rank_eq_decode_rank (M : PackedMatrix m n) :
    PackedMatrix.rank M = M.decode.rank :=
  EchelonForm.new_pivots_length_eq_rank M

end BinarFormal.Echelon
