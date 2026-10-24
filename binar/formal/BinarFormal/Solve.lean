import BinarFormal.Echelon
import BinarFormal.Transpose
import BinarFormal.M4RI
import Batteries.Data.BitVec.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear-algebra solving, kernels, and inverses

An executable Lean model of `binar`'s packed GF(2) linear-algebra "solve" layer, refined
against `BinarFormal.Packed.PackedMatrix` and built on top of `BinarFormal.Echelon`'s RREF
computation (`EchelonForm.new`, `IsRREF`). This mirrors, in order of composition,
`binar/src/matrix/aligned_bitmatrix.rs`:

* `impl Mul<&AlignedBitView> for &AlignedBitMatrix` (matrix × column vector) →
  `PackedMatrix.mulVec`, refining Mathlib's `Matrix.mulVec` (`decode_mulVec`).
* `AlignedBitMatrix::right_multiply` (row vector × matrix) → `PackedMatrix.rightMultiply`,
  refining Mathlib's `Matrix.vecMul` (`decode_rightMultiply`), built on
  `BinarFormal.Packed.PackedMatrix.transpose` rather than re-deriving column access.
* `AlignedBitMatrix::mul_transpose` → `PackedMatrix.mulTranspose`, refining `A * Bᵀ`
  (`decode_mulTranspose`), built by composing `BinarFormal.Packed.PackedMatrix.m4riMul` and
  `BinarFormal.Packed.PackedMatrix.transpose`.
* The private free functions `solve_rref_system`/`transpose_solve_rref_system` →
  `BinarFormal.Solve.solveRrefSystem`/`BinarFormal.Solve.transposeSolveRrefSystem`, generic
  over any `IsRREF`-satisfying matrix and pivot list (not just `EchelonForm.new`'s output),
  with soundness+completeness theorems `solveRrefSystem_eq_some_iff` and
  `transposeSolveRrefSystem_eq_some_iff`.
* `EchelonForm::solve`/`EchelonForm::transpose_solve` → `EchelonForm.solve`/
  `EchelonForm.transposeSolve`, lifting the two theorems above along the transform `T`
  (`EchelonForm.new_transform_mul_eq`/`new_transform_mul_inv`) to theorems about the
  *original* matrix `A` (`EchelonForm.solve_eq_some_iff`/`EchelonForm.transposeSolve_eq_some_iff`).
* `kernel_basis_matrix`/`complement` → `BinarFormal.Solve.freeColumns`/
  `PackedMatrix.kernelBasis`, with membership, linear independence, and span theorems
  identifying its rows with a genuine basis of `LinearMap.ker A.decode.mulVecLin`
  (`kernelBasis_mem_ker`, `kernelBasis_linearIndependent`, `kernelBasis_span_eq_ker`).
* `AlignedBitMatrix::inverted` → `PackedMatrix.inverted`, taking a full-rank *proof*
  (`PackedMatrix.rank A = n`) instead of modelling Rust's `assert_eq!`/panic, with both
  `inverted_mul_left` (`inverse * A = 1`, matching `EchelonForm::new_transform_mul_eq` at
  full rank) and `inverted_mul_right` (`A * inverse = 1`, matching `inverted`'s own
  `debug_assert_eq!(self * &echelon_form.transform, AlignedBitMatrix::identity(...))`).

## Trust boundary

* `PackedMatrix.mulVec`/`rightMultiply` are built directly from `PackedVec.dot` and
  `PackedMatrix.transpose`; no new bit-level algorithm is introduced (matching the
  `ponytail` guidance to derive from already-proven pieces rather than rebuilding).
* `solveRrefSystem`/`transposeSolveRrefSystem` mirror Rust's back-substitution/forward
  pivot-row-cancellation loops as explicit fuel-decreasing folds over the *reverse*/
  *forward* pivot order (matching Rust's `(0..pivots.len()).rev()` and
  `pivots.iter().enumerate()` respectively) using totalized helpers
  (`PackedVec.setTotal`, `BinarFormal.Solve.columnVec`) for out-of-range indices, exactly
  as `BinarFormal.Echelon.getTotal` totalizes reads there. Their defining equations are
  literal transcriptions of the Rust loop bodies; the soundness/completeness proofs are
  the new mathematical content, derived entirely from `IsRREF`'s invariants (in particular
  `pivot_unit`, which makes every individual step's effect on *other* pivot rows exactly
  zero, so the fold's final result does not depend on processing order even though the
  fold itself still literally replays Rust's order).
* `PackedMatrix.kernelBasis` reads each output bit directly off the already-computed RREF
  matrix via a closed-form `PackedVec.ofBoolFn` formula instead of Rust's two sequential
  `set` loops; since those loops write to disjoint cells (pivot columns vs. each row's own
  free column), the closed form is extensionally identical, in the same spirit as
  `BinarFormal.Transpose.transposeRowStorage` replacing Rust's write-then-read tiling.
* `PackedMatrix.inverted` takes the full-rank hypothesis as an explicit Lean `Prop` rather
  than modelling Rust's `assert_eq!`-triggered panic; Rust's own `debug_assert_eq!` inside
  `inverted` is exactly the `inverted_mul_right` theorem proved here (both are the
  correctness statement, not defensive code, from the Lean side).
-/

open scoped Matrix

namespace BinarFormal.Packed.PackedVec

open BinarFormal.Packed

variable {n : Nat}

/-- Build a packed vector from a totalized boolean function, mirroring the common pattern
(shared by `PackedMatrix.mulVec`, `PackedMatrix.rightMultiply`, and
`PackedMatrix.kernelBasis` below) of writing every output bit independently as a pure
function of its index. Bits at or beyond `n` are discarded regardless of what `f` returns
there, so callers never need to prove a padding fact about `f` itself. -/
def ofBoolFn (n : Nat) (f : Nat → Bool) : PackedVec n where
  storage := BitVec.ofFnLE (fun i : Fin (capacity n) => if i.val < n then f i.val else false)
  zero_padding := by
    intro i hi
    rcases Nat.lt_or_ge i (capacity n) with hic | hic
    · rw [BitVec.getLsbD_ofFnLE, dite_eq_left hic]
      simp only []
      rw [ite_eq_right (by omega)]
    · exact BitVec.getLsbD_of_ge _ i hic

@[simp] theorem get_ofBoolFn (n : Nat) (f : Nat → Bool) (i : Nat) (hi : i < n) :
    (ofBoolFn n f).get i = f i := by
  unfold ofBoolFn get
  rw [BitVec.getLsbD_ofFnLE, dite_eq_left (hi.trans_le (le_capacity n))]
  simp only []
  rw [ite_eq_left hi]

/-- Whether every logical bit of `v` is `false`, mirroring `Bitwise::is_zero`. -/
def isZero (v : PackedVec n) : Bool := v.storage == 0#(capacity n)

theorem isZero_iff (v : PackedVec n) : v.isZero = true ↔ v.decode = 0 := by
  unfold isZero
  rw [beq_iff_eq]
  constructor
  · intro h
    funext i
    have hbit : v.get i.val = false := by
      show v.storage.getLsbD i.val = false
      rw [h]; simp
    rw [decode_get, hbit, Bool.toF2_false]
    rfl
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rcases Nat.lt_or_ge i n with hin | hin
    · have hbit : v.get i = false := by
        have hh := congrFun h ⟨i, hin⟩
        rw [decode_get] at hh
        exact Bool.toF2_injective (hh.trans Bool.toF2_false.symm)
      show v.storage.getLsbD i = (0#(capacity n)).getLsbD i
      rw [BitVec.getLsbD_zero]
      exact hbit
    · show v.storage.getLsbD i = (0#(capacity n)).getLsbD i
      rw [BitVec.getLsbD_zero]
      exact v.zero_padding i hin

@[simp] theorem get_zero (n i : Nat) : (PackedVec.zero n).get i = false := by
  show (0#(capacity n)).getLsbD i = false
  rw [BitVec.getLsbD_zero]

/-- Bool-level restatement of `isZero_iff`, avoiding any detour through `decode`: `v.isZero`
holds iff every in-range bit reads `false`. -/
theorem isZero_iff_get (v : PackedVec n) : v.isZero = true ↔ ∀ i, i < n → v.get i = false := by
  rw [isZero_iff]
  constructor
  · intro h i hi
    have hh := congrFun h ⟨i, hi⟩
    rw [decode_get] at hh
    exact Bool.toF2_injective (hh.trans Bool.toF2_false.symm)
  · intro h
    funext i
    rw [decode_get, h i.val i.isLt, Bool.toF2_false]
    rfl

/-- Write bit `i` to `b`, totalized to a no-op for out-of-range indices, mirroring the
totalizing style of `BinarFormal.Echelon.getTotal`. Used by `solveRrefSystem`/
`transposeSolveRrefSystem` below, whose Rust originals only ever call `assign_index` at
indices already known in range (pivot columns/row indices), so the fallback branch is
never exercised along the call paths mirrored here. -/
def setTotal (v : PackedVec n) (i : Nat) (b : Bool) : PackedVec n :=
  if h : i < n then v.set i h b else v

theorem get_setTotal_self (v : PackedVec n) (i : Nat) (hi : i < n) (b : Bool) :
    (v.setTotal i b).get i = b := by
  unfold setTotal
  rw [dite_eq_left hi, get_set_self]

theorem get_setTotal_ne (v : PackedVec n) (i : Nat) (b : Bool) {j : Nat} (hij : i ≠ j) :
    (v.setTotal i b).get j = v.get j := by
  unfold setTotal
  split
  · next h => exact get_set_ne v i h b hij
  · rfl

/-- XOR at the raw-bit level: `xor` reads back as `Bool.xor` on each bit. -/
theorem get_xor (u v : PackedVec n) (i : Nat) : (u.xor v).get i = (u.get i ^^ v.get i) := by
  show (u.storage ^^^ v.storage).getLsbD i = (u.get i ^^ v.get i)
  rw [BitVec.getLsbD_xor]
  rfl

/-- A packed vector is determined by its decoded content: `decode` is injective. This lets
proofs establish `Bool`-level equality of two packed vectors by instead comparing their
`F2`-valued decodings, which is often easier to compute with (e.g. via linearity). -/
theorem ext_of_decode {u v : PackedVec n} (h : u.decode = v.decode) : u = v := by
  have hget : ∀ i, i < n → u.get i = v.get i := by
    intro i hi
    have := congrFun h ⟨i, hi⟩
    rwa [decode_get, decode_get, Bool.toF2_injective.eq_iff] at this
  have hstorage : u.storage = v.storage := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rcases Nat.lt_or_ge i n with hin | hin
    · exact hget i hin
    · rw [u.zero_padding i hin, v.zero_padding i hin]
  cases u
  cases v
  simpa using hstorage

end BinarFormal.Packed.PackedVec

namespace BinarFormal.Packed.PackedMatrix

open BinarFormal.Packed.PackedVec

variable {m n k p : Nat}

/-- Multiply a packed matrix by a packed column vector, mirroring
`impl Mul<&AlignedBitView> for &AlignedBitMatrix`: each output bit is the dot product of
the corresponding row with `v`. -/
def mulVec (M : PackedMatrix m n) (v : PackedVec n) : PackedVec m :=
  PackedVec.ofBoolFn m (fun i => if h : i < m then (M.rows ⟨i, h⟩).dot v else false)

theorem get_mulVec (M : PackedMatrix m n) (v : PackedVec n) (i : Nat) (hi : i < m) :
    (M.mulVec v).get i = (M.rows ⟨i, hi⟩).dot v := by
  rw [mulVec, PackedVec.get_ofBoolFn m _ i hi, dite_eq_left hi]

/-- `mulVec` refines Mathlib's `Matrix.mulVec`. -/
theorem decode_mulVec (M : PackedMatrix m n) (v : PackedVec n) :
    (M.mulVec v).decode = M.decode *ᵥ v.decode := by
  funext i
  rw [PackedVec.decode_get, get_mulVec M v i.val i.isLt, PackedVec.dot_eq_dotProduct,
    Matrix.mulVec_apply]
  rfl

/-- Multiply a packed row vector by a packed matrix, mirroring
`AlignedBitMatrix::right_multiply`: built from `transpose` rather than re-deriving column
access, since Rust's `result ^= self.row(row_index)` accumulation over `left.support()` is
exactly the dot product of `left` with each column, read off as a row of the transpose. -/
def rightMultiply (M : PackedMatrix m n) (v : PackedVec m) : PackedVec n :=
  PackedVec.ofBoolFn n (fun j => if h : j < n then v.dot (M.transpose.rows ⟨j, h⟩) else false)

theorem get_rightMultiply (M : PackedMatrix m n) (v : PackedVec m) (j : Nat) (hj : j < n) :
    (M.rightMultiply v).get j = v.dot (M.transpose.rows ⟨j, hj⟩) := by
  rw [rightMultiply, PackedVec.get_ofBoolFn n _ j hj, dite_eq_left hj]

/-- `rightMultiply` refines Mathlib's `Matrix.vecMul`. -/
theorem decode_rightMultiply (M : PackedMatrix m n) (v : PackedVec m) :
    (M.rightMultiply v).decode = v.decode ᵥ* M.decode := by
  funext j
  have hcol : (M.transpose.rows j).decode = M.decode.col j := by
    rw [show (M.transpose.rows j).decode = (transpose M).decode j from rfl, decode_transpose]
    funext i
    rw [Matrix.transpose_apply, Matrix.col_apply]
  rw [PackedVec.decode_get, get_rightMultiply M v j.val j.isLt, PackedVec.dot_eq_dotProduct,
    hcol, Matrix.vecMul_apply]

/-- Multiply a packed matrix by the transpose of another, mirroring
`AlignedBitMatrix::mul_transpose`: computed by composing the already-refined `m4riMul` and
`transpose` rather than deriving a new multiplication algorithm. -/
def mulTranspose (left : PackedMatrix m k) (right : PackedMatrix p k) :
    PackedMatrix m p :=
  m4riMul left right.transpose

/-- `mulTranspose` refines `A * Bᵀ`. -/
theorem decode_mulTranspose (left : PackedMatrix m k) (right : PackedMatrix p k) :
    (mulTranspose left right).decode = left.decode * right.decodeᵀ := by
  rw [mulTranspose, decode_m4riMul, decode_transpose]

end BinarFormal.Packed.PackedMatrix

namespace BinarFormal.Solve

open BinarFormal.Packed BinarFormal.Packed.PackedVec BinarFormal.Packed.PackedMatrix
open BinarFormal.Echelon

variable {m n : Nat}

/-- Column `col` of a packed matrix as a length-`m` packed vector (totalized: out-of-range
columns read as the all-zero vector), mirroring `AlignedBitMatrix::column`. Built from
`PackedMatrix.transpose` (column `col` of `M` is row `col` of `Mᵀ`) rather than a fresh
column-reading algorithm. -/
def columnVec (M : PackedMatrix m n) (col : Nat) : PackedVec m :=
  if h : col < n then M.transpose.rows ⟨col, h⟩ else PackedVec.zero m

theorem get_columnVec (M : PackedMatrix m n) (col : Nat) (hcol : col < n) (row : Fin m) :
    (columnVec M col).get row.val = M.get row col := by
  unfold columnVec
  rw [dite_eq_left hcol]
  exact transpose_get M ⟨col, hcol⟩ row.val row.isLt

/-- Row `row` of a packed matrix as a length-`n` packed vector (totalized: out-of-range
rows read as the all-zero vector), mirroring `AlignedBitMatrix::row`. Unlike `columnVec`,
`PackedMatrix.rows` already gives direct row access, so no auxiliary transpose is needed. -/
def rowVec (M : PackedMatrix m n) (row : Nat) : PackedVec n :=
  if h : row < m then M.rows ⟨row, h⟩ else PackedVec.zero n

theorem get_rowVec (M : PackedMatrix m n) (row : Nat) (hrow : row < m) (col : Nat) :
    (rowVec M row).get col = M.get ⟨row, hrow⟩ col := by
  unfold rowVec
  rw [dite_eq_left hrow]
  rfl

/-! ## `solve_rref_system`: back-substitution

Mirrors the private free function `solve_rref_system` in `binar/src/matrix/aligned_bitmatrix.rs`:
```
fn solve_rref_system(matrix: &AlignedBitMatrix, pivots: &[usize], target: &AlignedBitView)
    -> Option<AlignedBitVec> {
    let mut residual_target = AlignedBitVec::from_view(target);
    let mut solution = AlignedBitVec::zeros(matrix.column_count());
    for row_index in (0..pivots.len()).rev() {
        if residual_target.index(row_index) {
            let column_index = pivots[row_index];
            residual_target.bitxor_assign(&matrix.column(column_index));
            solution.assign_index(column_index, true);
        }
    }
    residual_target.is_zero().then_some(solution)
}
```
-/

/-- One back-substitution step at pivot-row index `idx`: if the residual is still set at row
`idx`, cancel it by XORing in that pivot's column of `rr` and record the pivot column as set
in the solution. Totalized to `idx < pivots.length` (mirroring the loop range
`(0..pivots.len()).rev()`, which never presents an out-of-range `idx`) so it can be folded
over an arbitrary index list. -/
def solveRrefStep (rr : PackedMatrix m n) (pivots : List Nat) (idx : Nat)
    (state : PackedVec m × PackedVec n) : PackedVec m × PackedVec n :=
  if h : idx < pivots.length then
    if state.1.get idx then
      (state.1.xor (columnVec rr pivots[idx]), state.2.setTotal pivots[idx] true)
    else state
  else state

theorem solveRrefStep_of_true (rr : PackedMatrix m n) (pivots : List Nat) (idx : Nat)
    (state : PackedVec m × PackedVec n) (h : idx < pivots.length)
    (hc : state.1.get idx = true) :
    solveRrefStep rr pivots idx state =
      (state.1.xor (columnVec rr (pivots[idx]'h)), state.2.setTotal (pivots[idx]'h) true) := by
  unfold solveRrefStep
  rw [dite_eq_left h, ite_eq_left hc]

theorem solveRrefStep_of_false (rr : PackedMatrix m n) (pivots : List Nat) (idx : Nat)
    (state : PackedVec m × PackedVec n) (h : idx < pivots.length)
    (hc : state.1.get idx = false) :
    solveRrefStep rr pivots idx state = state := by
  unfold solveRrefStep
  rw [dite_eq_left h, ite_eq_right (by simp [hc])]

/-- Fold `solveRrefStep` over an index list, mirroring the `for row_index in ...` loop body
applied in sequence. -/
def solveRrefFold (rr : PackedMatrix m n) (pivots : List Nat) (indices : List Nat)
    (state : PackedVec m × PackedVec n) : PackedVec m × PackedVec n :=
  indices.foldl (fun st idx => solveRrefStep rr pivots idx st) state

/-- Mirrors `solve_rref_system`: back-substitution over pivot rows in reverse order
(`(0..pivots.len()).rev()`), then reports `none` unless the residual has been driven to
zero. -/
def solveRrefSystem (rr : PackedMatrix m n) (pivots : List Nat) (target : PackedVec m) :
    Option (PackedVec n) :=
  let final := solveRrefFold rr pivots (List.range pivots.length).reverse
    (target, PackedVec.zero n)
  if final.1.isZero then some final.2 else none

theorem solveRrefFold_cons (rr : PackedMatrix m n) (pivots : List Nat) (a : Nat)
    (rest : List Nat) (state : PackedVec m × PackedVec n) :
    solveRrefFold rr pivots (a :: rest) state =
      solveRrefFold rr pivots rest (solveRrefStep rr pivots a state) :=
  List.foldl_cons

/-- Generalized correctness invariant for `solveRrefFold`, threaded through an arbitrary
starting state that already agrees with the original `target`/all-zero solution on the
pivot-row indices still in `l` (not yet processed), and with the canonical closed form on
the pivot-row indices no longer in `l` (already processed). Proved by induction on `l`,
using `IsRREF.pivot_unit`/`IsRREF.rows_zero` to show each step only ever affects its own
dedicated residual bit and solution column, so the outcome does not depend on which order
the remaining indices in `l` are processed in, even though `solveRrefFold` itself still
literally replays that order. -/
theorem solveRrefFold_spec (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (hlen : pivots.length ≤ m) (target : PackedVec m) :
    ∀ (l : List Nat), l.Nodup → (∀ k ∈ l, k < pivots.length) →
    ∀ (residual0 : PackedVec m) (solution0 : PackedVec n),
    (∀ k, k < pivots.length → k ∈ l → residual0.get k = target.get k) →
    (∀ k, k < pivots.length → k ∉ l → residual0.get k = false) →
    (∀ r : Fin m, pivots.length ≤ r.val → residual0.get r.val = target.get r.val) →
    (∀ k, (hk : k < pivots.length) → k ∈ l → solution0.get (pivots[k]'hk) = false) →
    (∀ k, (hk : k < pivots.length) → k ∉ l → solution0.get (pivots[k]'hk) = target.get k) →
    (∀ c, c < n → c ∉ pivots → solution0.get c = false) →
    (∀ k, k < pivots.length →
        (solveRrefFold rr pivots l (residual0, solution0)).1.get k = false) ∧
    (∀ r : Fin m, pivots.length ≤ r.val →
        (solveRrefFold rr pivots l (residual0, solution0)).1.get r.val = target.get r.val) ∧
    (∀ k, (hk : k < pivots.length) →
        (solveRrefFold rr pivots l (residual0, solution0)).2.get (pivots[k]'hk) = target.get k) ∧
    (∀ c, c < n → c ∉ pivots →
        (solveRrefFold rr pivots l (residual0, solution0)).2.get c = false) := by
  intro l
  induction l with
  | nil =>
    intro _ _ residual0 solution0 hmem hout htail hsmem hsout hsfree
    refine ⟨fun k hk => hout k hk (List.not_mem_nil), htail,
      fun k hk => hsout k hk (List.not_mem_nil), hsfree⟩
  | cons a rest ih =>
    intro hnodup hlt residual0 solution0 hmem hout htail hsmem hsout hsfree
    have ha_mem : a ∈ a :: rest := List.mem_cons_self
    have ha_lt : a < pivots.length := hlt a ha_mem
    have ha_notin_rest : a ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
    have hrest_lt : ∀ k ∈ rest, k < pivots.length := fun k hk => hlt k (List.mem_cons_of_mem a hk)
    have hpivnodup : pivots.Nodup := hrref.sorted.nodup
    have hcheck : residual0.get a = target.get a := hmem a ha_lt ha_mem
    rw [solveRrefFold_cons]
    rcases hfire : residual0.get a with _ | _
    · rw [solveRrefStep_of_false rr pivots a (residual0, solution0) ha_lt hfire]
      apply ih hrest_nodup hrest_lt
      · exact fun k hk hkrest => hmem k hk (List.mem_cons_of_mem a hkrest)
      · intro k hk hkrest
        rcases eq_or_ne k a with hka | hka
        · subst hka; exact hfire
        · exact hout k hk (fun h => (List.mem_cons.mp h).elim hka hkrest)
      · exact htail
      · exact fun k hk hkrest => hsmem k hk (List.mem_cons_of_mem a hkrest)
      · intro k hk hkrest
        rcases eq_or_ne k a with hka | hka
        · subst hka; rw [hsmem k ha_lt ha_mem, ← hcheck, hfire]
        · exact hsout k hk (fun h => (List.mem_cons.mp h).elim hka hkrest)
      · exact hsfree
    · rw [solveRrefStep_of_true rr pivots a (residual0, solution0) ha_lt hfire]
      apply ih hrest_nodup hrest_lt
      · intro k hk hkrest
        have hkne : k ≠ a := fun h => ha_notin_rest (h ▸ hkrest)
        show (residual0.xor (columnVec rr (pivots[a]'ha_lt))).get k = target.get k
        have hknotpivot : (columnVec rr (pivots[a]'ha_lt)).get k = false := by
          rw [get_columnVec rr (pivots[a]'ha_lt) (hrref.lt_n _ (List.getElem_mem ha_lt))
            ⟨k, hk.trans_le hlen⟩]
          apply Bool.eq_false_iff.mpr
          intro hcontra
          exact hkne ((hrref.pivot_unit a ha_lt ⟨k, hk.trans_le hlen⟩).mp hcontra)
        rw [get_xor, hknotpivot, Bool.xor_false]
        exact hmem k hk (List.mem_cons_of_mem a hkrest)
      · intro k hk hknotrest
        show (residual0.xor (columnVec rr (pivots[a]'ha_lt))).get k = false
        rcases eq_or_ne k a with hka | hka
        · have hself : (columnVec rr (pivots[a]'ha_lt)).get k = true := by
            rw [get_columnVec rr (pivots[a]'ha_lt) (hrref.lt_n _ (List.getElem_mem ha_lt))
              ⟨k, hk.trans_le hlen⟩]
            exact (hrref.pivot_unit a ha_lt ⟨k, hk.trans_le hlen⟩).mpr hka
          have hval : residual0.get k = true := by rw [hka]; exact hfire
          rw [get_xor, hself, hval]; rfl
        · have hknotpivot : (columnVec rr (pivots[a]'ha_lt)).get k = false := by
            rw [get_columnVec rr (pivots[a]'ha_lt) (hrref.lt_n _ (List.getElem_mem ha_lt))
              ⟨k, hk.trans_le hlen⟩]
            apply Bool.eq_false_iff.mpr
            intro hcontra
            exact hka ((hrref.pivot_unit a ha_lt ⟨k, hk.trans_le hlen⟩).mp hcontra)
          rw [get_xor, hknotpivot, Bool.xor_false]
          exact hout k hk (fun h => (List.mem_cons.mp h).elim hka hknotrest)
      · intro r hr
        show (residual0.xor (columnVec rr (pivots[a]'ha_lt))).get r.val = target.get r.val
        have hzerocol : (columnVec rr (pivots[a]'ha_lt)).get r.val = false := by
          rw [get_columnVec rr (pivots[a]'ha_lt) (hrref.lt_n _ (List.getElem_mem ha_lt)) r]
          exact hrref.rows_zero r hr (pivots[a]'ha_lt) (hrref.lt_n _ (List.getElem_mem ha_lt))
        rw [get_xor, hzerocol, Bool.xor_false]
        exact htail r hr
      · intro k hk hkrest
        have hkne : k ≠ a := fun h => ha_notin_rest (h ▸ hkrest)
        have hpivne : (pivots[k]'hk) ≠ (pivots[a]'ha_lt) :=
          fun heq => hkne (hpivnodup.getElem_inj_iff.mp heq)
        show (solution0.setTotal (pivots[a]'ha_lt) true).get (pivots[k]'hk) = false
        rw [get_setTotal_ne _ _ _ (Ne.symm hpivne)]
        exact hsmem k hk (List.mem_cons_of_mem a hkrest)
      · intro k hk hknotrest
        show (solution0.setTotal (pivots[a]'ha_lt) true).get (pivots[k]'hk) = target.get k
        rcases eq_or_ne k a with hka | hka
        · subst hka
          rw [get_setTotal_self _ _ (hrref.lt_n _ (List.getElem_mem ha_lt)), ← hcheck, hfire]
        · have hpivne : (pivots[k]'hk) ≠ (pivots[a]'ha_lt) :=
            fun heq => hka (hpivnodup.getElem_inj_iff.mp heq)
          rw [get_setTotal_ne _ _ _ (Ne.symm hpivne)]
          exact hsout k hk (fun h => (List.mem_cons.mp h).elim hka hknotrest)
      · intro c hc hcpiv
        show (solution0.setTotal (pivots[a]'ha_lt) true).get c = false
        have hcne : c ≠ pivots[a]'ha_lt := fun h => hcpiv (h ▸ List.getElem_mem ha_lt)
        rw [get_setTotal_ne _ _ _ (Ne.symm hcne)]
        exact hsfree c hc hcpiv

/-- `solveRrefFold_spec` specialized to `solveRrefSystem`'s actual starting state (the
literal `target`/all-zero-solution pair folded over the *full* reversed pivot-index range):
after the fold, the residual is zero on every pivot row, unchanged beyond the last pivot
row, the solution matches `target` at every pivot column (read back through `pivots`), and
the solution is zero on every non-pivot (free) column. -/
theorem solveRrefSystem_spec (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (hlen : pivots.length ≤ m) (target : PackedVec m) :
    (∀ k, k < pivots.length →
        (solveRrefFold rr pivots (List.range pivots.length).reverse
          (target, PackedVec.zero n)).1.get k = false) ∧
    (∀ r : Fin m, pivots.length ≤ r.val →
        (solveRrefFold rr pivots (List.range pivots.length).reverse
          (target, PackedVec.zero n)).1.get r.val = target.get r.val) ∧
    (∀ k, (hk : k < pivots.length) →
        (solveRrefFold rr pivots (List.range pivots.length).reverse
          (target, PackedVec.zero n)).2.get (pivots[k]'hk) = target.get k) ∧
    (∀ c, c < n → c ∉ pivots →
        (solveRrefFold rr pivots (List.range pivots.length).reverse
          (target, PackedVec.zero n)).2.get c = false) := by
  have hfull : ∀ k, k < pivots.length → k ∈ (List.range pivots.length).reverse :=
    fun k hk => List.mem_reverse.mpr (List.mem_range.mpr hk)
  exact solveRrefFold_spec rr pivots hrref hlen target (List.range pivots.length).reverse
    (List.nodup_reverse.mpr List.nodup_range)
    (fun k hk => List.mem_range.mp (List.mem_reverse.mp hk))
    target (PackedVec.zero n)
    (fun _ _ _ => rfl)
    (fun k hk hnotin => absurd (hfull k hk) hnotin)
    (fun _ _ => rfl)
    (fun k _ _ => get_zero n _)
    (fun k hk hnotin => absurd (hfull k hk) hnotin)
    (fun c _ _ => get_zero n c)

/-- For any packed vector `y` that vanishes on every non-pivot column, `rr.decode.mulVec
y.decode` at a pivot row `k` collapses to the single term at that row's own pivot column,
and vanishes entirely past the last pivot row: `pivot_unit` kills every other pivot
column's contribution (its row-`k` entry is `false`), and `hyfree` kills every non-pivot
column's contribution. This is the computational core shared by both the soundness and
completeness directions of `solveRrefSystem_eq_some_iff`. -/
theorem mulVec_apply_of_free_zero (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (y : PackedVec n)
    (hyfree : ∀ c, c < n → c ∉ pivots → y.get c = false) (row : Fin m) :
    rr.decode.mulVec y.decode row =
      if h : row.val < pivots.length then Bool.toF2 (y.get (pivots[row.val]'h)) else 0 := by
  rw [Matrix.mulVec_apply]
  show dotProduct (rr.decode row) y.decode = _
  split
  · next h =>
    have hcol_lt_n : pivots[row.val]'h < n := hrref.lt_n _ (List.getElem_mem h)
    have hother : ∀ col : Fin n, col ≠ (⟨pivots[row.val]'h, hcol_lt_n⟩ : Fin n) →
        rr.decode row col * y.decode col = 0 := by
      intro col hcolne
      by_cases hpiv : col.val ∈ pivots
      · obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hpiv
        have hkne : k ≠ row.val := by
          intro hcontra
          apply hcolne
          apply Fin.ext
          show col.val = pivots[row.val]'h
          subst hcontra
          exact hkeq.symm
        have hrrfalse : rr.get row (pivots[k]'hk) = false :=
          Bool.eq_false_iff.mpr
            (fun hcontra => hkne ((hrref.pivot_unit k hk row).mp hcontra).symm)
        rw [PackedMatrix.decode_get, PackedVec.decode_get, ← hkeq, hrrfalse, Bool.toF2_false,
          zero_mul]
      · have hyval : y.get col.val = false := hyfree col.val col.isLt hpiv
        rw [PackedMatrix.decode_get, PackedVec.decode_get, hyval, Bool.toF2_false, mul_zero]
    rw [dotProduct,
      Finset.sum_eq_single (⟨pivots[row.val]'h, hcol_lt_n⟩ : Fin n)
        (fun col _ hcolne => hother col hcolne) (fun ha => absurd (Finset.mem_univ _) ha),
      PackedMatrix.decode_get, PackedVec.decode_get]
    have hrrget : rr.get row (pivots[row.val]'h) = true :=
      (hrref.pivot_unit row.val h row).mpr rfl
    rw [hrrget, Bool.toF2_true, one_mul]
  · next h =>
    replace h : pivots.length ≤ row.val := by omega
    have hallzero : ∀ col : Fin n, rr.decode row col * y.decode col = 0 := by
      intro col
      by_cases hpiv : col.val ∈ pivots
      · obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hpiv
        have hkne : k ≠ row.val := by omega
        have hrrfalse : rr.get row (pivots[k]'hk) = false :=
          Bool.eq_false_iff.mpr
            (fun hcontra => hkne ((hrref.pivot_unit k hk row).mp hcontra).symm)
        rw [PackedMatrix.decode_get, PackedVec.decode_get, ← hkeq, hrrfalse, Bool.toF2_false,
          zero_mul]
      · have hyval : y.get col.val = false := hyfree col.val col.isLt hpiv
        rw [PackedMatrix.decode_get, PackedVec.decode_get, hyval, Bool.toF2_false, mul_zero]
    rw [dotProduct, Finset.sum_eq_zero (fun col _ => hallzero col)]

/-- **Soundness and completeness** of `solveRrefSystem`: it returns `some x` exactly when
`x` solves `A x = b` (for the RREF matrix `rr`) *and* every free (non-pivot) column of `x`
is zero — the canonical solution Rust's back-substitution produces, not an arbitrary one
selected by a choice principle. Consequently it returns `none` exactly when *no* solution
of `A x = b` exists at all: `mulVec_apply_of_free_zero` shows any candidate solution with
zeroed free columns forces `target` to vanish past the last pivot row, so if `target`
fails that condition (the `isZero`-false case), not even a non-canonical solution could
exist. -/
theorem solveRrefSystem_eq_some_iff (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (hlen : pivots.length ≤ m) (target : PackedVec m)
    (x : PackedVec n) :
    solveRrefSystem rr pivots target = some x ↔
      rr.decode.mulVec x.decode = target.decode ∧
        ∀ c, c < n → c ∉ pivots → x.get c = false := by
  obtain ⟨hzero_pivot, hzero_tail, hsol_pivot, hsol_free⟩ :=
    solveRrefSystem_spec rr pivots hrref hlen target
  set final := solveRrefFold rr pivots (List.range pivots.length).reverse
    (target, PackedVec.zero n) with hfinal_def
  have hisZero_iff : final.1.isZero = true ↔
      ∀ r : Fin m, pivots.length ≤ r.val → target.get r.val = false := by
    rw [isZero_iff_get]
    constructor
    · intro h r hr
      rw [← hzero_tail r hr]
      exact h r.val r.isLt
    · intro h i hi
      rcases Nat.lt_or_ge i pivots.length with hip | hip
      · exact hzero_pivot i hip
      · rw [hzero_tail ⟨i, hi⟩ hip]
        exact h ⟨i, hi⟩ hip
  constructor
  · intro heq
    unfold solveRrefSystem at heq
    rw [← hfinal_def] at heq
    by_cases hcond : final.1.isZero = true
    · rw [ite_eq_left hcond] at heq
      have hxeq : final.2 = x := Option.some.inj heq
      refine ⟨?_, ?_⟩
      · funext row
        rw [← hxeq, mulVec_apply_of_free_zero rr pivots hrref final.2 hsol_free row]
        split
        · next h => rw [hsol_pivot row.val h, PackedVec.decode_get]
        · next h =>
          replace h : pivots.length ≤ row.val := by omega
          rw [PackedVec.decode_get, (hisZero_iff.mp hcond) row h, Bool.toF2_false]
      · intro c hc hcp
        rw [← hxeq]
        exact hsol_free c hc hcp
    · rw [ite_eq_right hcond] at heq
      exact absurd heq (by simp)
  · rintro ⟨heqn, hxfree⟩
    have hsolvable : ∀ r : Fin m, pivots.length ≤ r.val → target.get r.val = false := by
      intro r hr
      have hthis := congrFun heqn r
      rw [mulVec_apply_of_free_zero rr pivots hrref x hxfree r,
        dite_eq_right (show ¬(r.val < pivots.length) by omega), PackedVec.decode_get] at hthis
      exact (Bool.toF2_injective (Bool.toF2_false.trans hthis)).symm
    have hcond : final.1.isZero = true := hisZero_iff.mpr hsolvable
    have hget_eq : ∀ c, c < n → x.get c = final.2.get c := by
      intro c hc
      by_cases hpiv : c ∈ pivots
      · obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hpiv
        have hkm : k < m := hk.trans_le hlen
        have hthis := congrFun heqn ⟨k, hkm⟩
        rw [mulVec_apply_of_free_zero rr pivots hrref x hxfree ⟨k, hkm⟩, dite_eq_left hk,
          PackedVec.decode_get] at hthis
        rw [← hkeq, hsol_pivot k hk]
        exact Bool.toF2_injective hthis
      · rw [hxfree c hc hpiv, hsol_free c hc hpiv]
    have hdecode_eq : x.decode = final.2.decode := by
      funext i
      rw [PackedVec.decode_get, PackedVec.decode_get, hget_eq i.val i.isLt]
    have hxeq : final.2 = x := (ext_of_decode hdecode_eq).symm
    show (if final.1.isZero then some final.2 else none) = some x
    rw [ite_eq_left hcond, hxeq]

/-- Any candidate solution's contribution vanishes past `rr`'s last pivot row, with no
constraint on the candidate at all: `IsRREF.rows_zero` makes the entire row zero, so every
term of the dot product is zero regardless of what the vector holds. This is the key fact
making the "tail" condition on `target` a genuine *necessary* condition for solvability by
*any* `x`, not just the canonical free-zero one. -/
theorem mulVec_apply_eq_zero_of_rows_zero (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (y : PackedVec n) (row : Fin m)
    (hrow : pivots.length ≤ row.val) :
    rr.decode.mulVec y.decode row = 0 := by
  rw [Matrix.mulVec_apply]
  show dotProduct (rr.decode row) y.decode = 0
  rw [dotProduct]
  refine Finset.sum_eq_zero (fun col _ => ?_)
  rw [PackedMatrix.decode_get, hrref.rows_zero row hrow col.val col.isLt, Bool.toF2_false,
    zero_mul]

/-- `target` lies in the range of `rr.decode.mulVec` iff it already vanishes past the last
pivot row: the forward direction is exactly `mulVec_apply_eq_zero_of_rows_zero` (necessity,
from *any* candidate solution), and the backward direction exhibits the canonical
free-zero solution as an explicit witness (sufficiency, reusing `solveRrefSystem_spec` and
`mulVec_apply_of_free_zero`). Phrased with the witness's free columns zero so it composes
directly with `solveRrefSystem_eq_some_iff`. -/
theorem solveRrefSystem_isSolvable_iff (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (hlen : pivots.length ≤ m) (target : PackedVec m) :
    (∀ r : Fin m, pivots.length ≤ r.val → target.get r.val = false) ↔
      ∃ x : PackedVec n, rr.decode.mulVec x.decode = target.decode ∧
        ∀ c, c < n → c ∉ pivots → x.get c = false := by
  constructor
  · intro hsolvable
    obtain ⟨hzero_pivot, hzero_tail, hsol_pivot, hsol_free⟩ :=
      solveRrefSystem_spec rr pivots hrref hlen target
    refine ⟨(solveRrefFold rr pivots (List.range pivots.length).reverse
      (target, PackedVec.zero n)).2, ?_, hsol_free⟩
    funext row
    rw [mulVec_apply_of_free_zero rr pivots hrref _ hsol_free row]
    split
    · next h => rw [hsol_pivot row.val h, PackedVec.decode_get]
    · next h =>
      replace h : pivots.length ≤ row.val := by omega
      rw [PackedVec.decode_get, hsolvable row h, Bool.toF2_false]
  · rintro ⟨x, hx, hxfree⟩ r hr
    have hthis := congrFun hx r
    rw [mulVec_apply_of_free_zero rr pivots hrref x hxfree r,
      dite_eq_right (show ¬(r.val < pivots.length) by omega), PackedVec.decode_get] at hthis
    exact (Bool.toF2_injective (Bool.toF2_false.trans hthis)).symm

/-- **Completeness of `none`**: `solveRrefSystem` reports `none` exactly when `target` is
*genuinely unsolvable*, i.e. no `x` at all (canonical or not) satisfies `A x = target`, not
merely that the canonical construction happens to fail. Combined with
`solveRrefSystem_eq_some_iff`, this pins down `solveRrefSystem` completely: it is `some x`
iff `x` is the canonical solution, and `none` iff `target` admits no solution whatsoever. -/
theorem solveRrefSystem_eq_none_iff (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (hlen : pivots.length ≤ m) (target : PackedVec m) :
    solveRrefSystem rr pivots target = none ↔
      ¬ ∃ x : PackedVec n, rr.decode.mulVec x.decode = target.decode := by
  constructor
  · intro hnone hex
    obtain ⟨x, hx⟩ := hex
    have hsolvable : ∀ r : Fin m, pivots.length ≤ r.val → target.get r.val = false := by
      intro r hr
      have hthis := congrFun hx r
      rw [mulVec_apply_eq_zero_of_rows_zero rr pivots hrref x r hr, PackedVec.decode_get] at hthis
      exact (Bool.toF2_injective (Bool.toF2_false.trans hthis)).symm
    obtain ⟨x', hx', hx'free⟩ :=
      (solveRrefSystem_isSolvable_iff rr pivots hrref hlen target).mp hsolvable
    have hsome := (solveRrefSystem_eq_some_iff rr pivots hrref hlen target x').mpr ⟨hx', hx'free⟩
    rw [hnone] at hsome
    exact absurd hsome (by simp)
  · intro hnex
    by_contra hnone
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp hnone
    exact hnex ⟨x, ((solveRrefSystem_eq_some_iff rr pivots hrref hlen target x).mp hx.symm).1⟩

/-! ## `transpose_solve_rref_system`: forward pivot-row cancellation

Mirrors the private free function `transpose_solve_rref_system` in
`binar/src/matrix/aligned_bitmatrix.rs`, which solves `matrixᵀ x = target` (not
`matrix x = target`) by scanning pivot rows in their original (not reversed) order:
```
fn transpose_solve_rref_system(matrix: &AlignedBitMatrix, pivots: &[usize],
    target: &AlignedBitView) -> Option<AlignedBitVec> {
    let mut residual_target = AlignedBitVec::from_view(target);
    let mut solution = AlignedBitVec::zeros(pivots.len());
    for (row_index, &column_index) in pivots.iter().enumerate() {
        if residual_target.index(column_index) {
            residual_target.bitxor_assign(&matrix.row(row_index));
            solution.assign_index(row_index, true);
        }
    }
    residual_target.is_zero().then_some(solution)
}
```
Unlike `solve_rref_system`, the residual is checked/cancelled at the *pivot column*
`pivots[row_index]` while the loop itself walks `row_index` forward, and cancellation XORs
in the pivot's *row* (`rowVec`) rather than its column. -/

/-- One forward pivot-cancellation step at pivot-row index `idx`: if the residual is still
set at pivot column `pivots[idx]`, cancel it by XORing in that pivot's row of `rr` and
record row `idx` as set in the solution. Totalized to `idx < pivots.length` (mirroring
`pivots.iter().enumerate()`, which never presents an out-of-range `idx`). -/
def transposeSolveRrefStep (rr : PackedMatrix m n) (pivots : List Nat) (idx : Nat)
    (state : PackedVec n × PackedVec m) : PackedVec n × PackedVec m :=
  if h : idx < pivots.length then
    if state.1.get (pivots[idx]'h) then
      (state.1.xor (rowVec rr idx), state.2.setTotal idx true)
    else state
  else state

theorem transposeSolveRrefStep_of_true (rr : PackedMatrix m n) (pivots : List Nat) (idx : Nat)
    (state : PackedVec n × PackedVec m) (h : idx < pivots.length)
    (hc : state.1.get (pivots[idx]'h) = true) :
    transposeSolveRrefStep rr pivots idx state =
      (state.1.xor (rowVec rr idx), state.2.setTotal idx true) := by
  unfold transposeSolveRrefStep
  rw [dite_eq_left h, ite_eq_left hc]

theorem transposeSolveRrefStep_of_false (rr : PackedMatrix m n) (pivots : List Nat) (idx : Nat)
    (state : PackedVec n × PackedVec m) (h : idx < pivots.length)
    (hc : state.1.get (pivots[idx]'h) = false) :
    transposeSolveRrefStep rr pivots idx state = state := by
  unfold transposeSolveRrefStep
  rw [dite_eq_left h, ite_eq_right (by simp [hc])]

/-- Fold `transposeSolveRrefStep` over an index list, mirroring
`pivots.iter().enumerate()` applied in sequence. -/
def transposeSolveRrefFold (rr : PackedMatrix m n) (pivots : List Nat) (indices : List Nat)
    (state : PackedVec n × PackedVec m) : PackedVec n × PackedVec m :=
  indices.foldl (fun st idx => transposeSolveRrefStep rr pivots idx st) state

/-- Mirrors `transpose_solve_rref_system`: forward pivot-row cancellation
(`pivots.iter().enumerate()`, i.e. `row_index = 0, 1, …`), then reports `none` unless the
residual has been driven to zero. -/
def transposeSolveRrefSystem (rr : PackedMatrix m n) (pivots : List Nat)
    (target : PackedVec n) : Option (PackedVec m) :=
  let final := transposeSolveRrefFold rr pivots (List.range pivots.length)
    (target, PackedVec.zero m)
  if final.1.isZero then some final.2 else none

theorem transposeSolveRrefFold_cons (rr : PackedMatrix m n) (pivots : List Nat) (a : Nat)
    (rest : List Nat) (state : PackedVec n × PackedVec m) :
    transposeSolveRrefFold rr pivots (a :: rest) state =
      transposeSolveRrefFold rr pivots rest (transposeSolveRrefStep rr pivots a state) :=
  List.foldl_cons

/-- Setting a previously-`false` bit to `true` acts additively on `decode`: it adds the
decoding of the corresponding standard basis vector. Unlike the original `solveRrefFold`
(where every column stays `false`/unchanged outside its own dedicated bit), the transpose
fold's residual accumulates contributions from every fired step, so tracking it bit by
bit would require re-deriving the whole accumulated XOR history; decoding to `F2` and
using additivity avoids that entirely. -/
theorem decode_setTotal_true_of_get_false (v : PackedVec n) (i : Nat) (hi : i < n)
    (hv : v.get i = false) :
    (v.setTotal i true).decode = v.decode + ((PackedVec.zero n).setTotal i true).decode := by
  funext j
  rw [Pi.add_apply]
  by_cases hij : i = j.val
  · have hij' : (⟨i, hi⟩ : Fin n) = j := Fin.ext hij
    rw [← hij', PackedVec.decode_get, PackedVec.decode_get, PackedVec.decode_get,
      get_setTotal_self _ _ hi, get_setTotal_self _ _ hi, hv]
    decide
  · rw [PackedVec.decode_get, PackedVec.decode_get, PackedVec.decode_get,
      get_setTotal_ne _ _ _ hij, get_setTotal_ne _ _ _ hij, get_zero, Bool.toF2_false, add_zero]

/-- The decoding of a single standard-basis packed vector, pushed through `rr.decode.transpose
.mulVec`, reads back as the decoding of `rr`'s own `idx`-th row: this is exactly the
algebraic reflection of `residual_target.bitxor_assign(&matrix.row(row_index))`. -/
theorem transpose_mulVec_single (rr : PackedMatrix m n) (idx : Nat) (hidx : idx < m) :
    rr.decode.transpose.mulVec ((PackedVec.zero m).setTotal idx true).decode
      = (rowVec rr idx).decode := by
  funext c
  rw [Matrix.mulVec_apply]
  show dotProduct (rr.decode.transpose c) ((PackedVec.zero m).setTotal idx true).decode = _
  have hother : ∀ row : Fin m, row ≠ (⟨idx, hidx⟩ : Fin m) →
      rr.decode.transpose c row * ((PackedVec.zero m).setTotal idx true).decode row = 0 := by
    intro row hrowne
    have hrowne' : idx ≠ row.val := fun h => hrowne (Fin.ext h.symm)
    rw [PackedVec.decode_get, get_setTotal_ne _ _ _ hrowne', get_zero, Bool.toF2_false, mul_zero]
  rw [dotProduct,
    Finset.sum_eq_single (⟨idx, hidx⟩ : Fin m)
      (fun row _ hrowne => hother row hrowne) (fun ha => absurd (Finset.mem_univ _) ha),
    Matrix.transpose_apply, PackedVec.decode_get, get_setTotal_self _ _ hidx, Bool.toF2_true,
    mul_one, PackedVec.decode_get, get_rowVec rr idx hidx c.val, PackedMatrix.decode_get]

/-- Combines `decode_setTotal_true_of_get_false` and `transpose_mulVec_single` via linearity
(`Matrix.mulVec_add`): firing a pivot-cancellation step adds `rowVec rr idx`'s decoding to
`rr.decode.transpose.mulVec solution.decode`, exactly matching how it adds `rowVec rr idx`
itself to the residual. This is the linchpin of the algebraic invariant below. -/
theorem transpose_mulVec_setTotal_of_get_false (rr : PackedMatrix m n) (solution0 : PackedVec m)
    (idx : Nat) (hidx : idx < m) (hget : solution0.get idx = false) :
    rr.decode.transpose.mulVec (solution0.setTotal idx true).decode
      = rr.decode.transpose.mulVec solution0.decode + (rowVec rr idx).decode := by
  rw [decode_setTotal_true_of_get_false solution0 idx hidx hget, Matrix.mulVec_add,
    transpose_mulVec_single rr idx hidx]

/-- For *any* `y : PackedVec m` (no hypothesis on its shape needed), `rr.decode.transpose
.mulVec y.decode` collapses at a pivot column `pivots[k]` to `y`'s own `k`-th entry:
`pivot_unit` alone forces every *other* row's contribution to vanish, regardless of `y`.
This is the transpose-side analogue of `mulVec_apply_of_free_zero`'s pivot-row case, but
needs no free/shape hypothesis since the sum ranges over `rr`'s rows (fully controlled by
`pivot_unit`) rather than its columns. -/
theorem transposeMulVec_apply_pivot (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (y : PackedVec m) (k : Nat) (hk : k < pivots.length)
    (hlen : pivots.length ≤ m) :
    rr.decode.transpose.mulVec y.decode ⟨pivots[k]'hk, hrref.lt_n _ (List.getElem_mem hk)⟩ =
      y.decode ⟨k, hk.trans_le hlen⟩ := by
  rw [Matrix.mulVec_apply]
  show dotProduct (rr.decode.transpose _) y.decode = _
  have hother : ∀ row : Fin m, row ≠ (⟨k, hk.trans_le hlen⟩ : Fin m) →
      rr.decode.transpose (⟨pivots[k]'hk, hrref.lt_n _ (List.getElem_mem hk)⟩ : Fin n) row *
        y.decode row = 0 := by
    intro row hrowne
    have hrowne' : row.val ≠ k := fun h => hrowne (Fin.ext h)
    have hrrfalse : rr.get row (pivots[k]'hk) = false :=
      Bool.eq_false_iff.mpr (fun hcontra => hrowne' ((hrref.pivot_unit k hk row).mp hcontra))
    rw [Matrix.transpose_apply, PackedMatrix.decode_get, hrrfalse, Bool.toF2_false, zero_mul]
  rw [dotProduct,
    Finset.sum_eq_single (⟨k, hk.trans_le hlen⟩ : Fin m)
      (fun row _ hrowne => hother row hrowne) (fun ha => absurd (Finset.mem_univ _) ha),
    Matrix.transpose_apply, PackedMatrix.decode_get]
  have hrrget : rr.get (⟨k, hk.trans_le hlen⟩ : Fin m) (pivots[k]'hk) = true :=
    (hrref.pivot_unit k hk _).mpr rfl
  rw [hrrget, Bool.toF2_true, one_mul]

/-- `rr.decode.transpose.mulVec y.decode` does not depend on `y`'s entries beyond
`pivots.length`: `rows_zero` makes every such row of `rr` (hence every such column of
`rr.decode.transpose`) entirely zero, so those entries of `y` never contribute. Used to
compare an arbitrary candidate solution of `Aᵀ x = b` (whose tail need not vanish) against
the canonical solution (whose tail is provably zero). -/
theorem transpose_mulVec_eq_of_agree_lt (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (y1 y2 : PackedVec m)
    (hagree : ∀ k, (hk : k < pivots.length) → y1.get k = y2.get k) :
    rr.decode.transpose.mulVec y1.decode = rr.decode.transpose.mulVec y2.decode := by
  funext col
  rw [Matrix.mulVec_apply, Matrix.mulVec_apply]
  show dotProduct (rr.decode.transpose col) y1.decode = dotProduct (rr.decode.transpose col) y2.decode
  rw [dotProduct, dotProduct]
  apply Finset.sum_congr rfl
  intro row _
  by_cases hrow : row.val < pivots.length
  · rw [PackedVec.decode_get, PackedVec.decode_get, hagree row.val hrow]
  · replace hrow : pivots.length ≤ row.val := by omega
    rw [Matrix.transpose_apply, PackedMatrix.decode_get, hrref.rows_zero row hrow col.val col.isLt,
      Bool.toF2_false, zero_mul, zero_mul]

/-- Generalized correctness invariant for `transposeSolveRrefFold`, the transpose-side
analogue of `solveRrefFold_spec`. Threaded through an arbitrary starting state, tracking:
the solution is zero past `pivots.length` (never touched); the solution matches `target`
read back through `pivots` at every already-processed index (checkpoint, forced at the
moment each index fires or is skipped, since `pivot_unit` guarantees no *other* pivot row's
cancellation can perturb the residual at this index's own pivot column); and the algebraic
invariant `residual.decode + rr.decode.transpose.mulVec solution.decode = target.decode`,
preserved by every step (firing or not) via `Matrix.mulVec_add` linearity together with
`decode_setTotal_true_of_get_false`/`transpose_mulVec_single`. Unlike `solveRrefFold_spec`,
no Boolean tracking of the residual's *non-pivot* columns is needed at all: the algebraic
invariant captures their behaviour uniformly, sidestepping the fact that (unlike the
original fold) they are not simply left unchanged. -/
theorem transposeSolveRrefFold_spec (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (hlen : pivots.length ≤ m) (target : PackedVec n) :
    ∀ (l : List Nat), l.Nodup → (∀ k ∈ l, k < pivots.length) →
    ∀ (residual0 : PackedVec n) (solution0 : PackedVec m),
    (∀ k, k < pivots.length → k ∈ l → solution0.get k = false) →
    (∀ r : Fin m, pivots.length ≤ r.val → solution0.get r.val = false) →
    (∀ k, (hk : k < pivots.length) → k ∉ l →
        solution0.get k = target.get (pivots[k]'hk)) →
    residual0.decode + rr.decode.transpose.mulVec solution0.decode = target.decode →
    (∀ r : Fin m, pivots.length ≤ r.val →
        (transposeSolveRrefFold rr pivots l (residual0, solution0)).2.get r.val = false) ∧
    (∀ k, (hk : k < pivots.length) →
        (transposeSolveRrefFold rr pivots l (residual0, solution0)).2.get k =
          target.get (pivots[k]'hk)) ∧
    (transposeSolveRrefFold rr pivots l (residual0, solution0)).1.decode +
      rr.decode.transpose.mulVec
        (transposeSolveRrefFold rr pivots l (residual0, solution0)).2.decode =
      target.decode := by
  intro l
  induction l with
  | nil =>
    intro _ _ residual0 solution0 _ htail hscheck halg
    exact ⟨htail, fun k hk => hscheck k hk List.not_mem_nil, halg⟩
  | cons a rest ih =>
    intro hnodup hlt residual0 solution0 hsmem htail hscheck halg
    have ha_mem : a ∈ a :: rest := List.mem_cons_self
    have ha_lt : a < pivots.length := hlt a ha_mem
    have ha_notin_rest : a ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
    have hrest_lt : ∀ k ∈ rest, k < pivots.length := fun k hk => hlt k (List.mem_cons_of_mem a hk)
    have hcol_lt_n : pivots[a]'ha_lt < n := hrref.lt_n _ (List.getElem_mem ha_lt)
    have hsol_a_false : solution0.get a = false := hsmem a ha_lt ha_mem
    have h0a : residual0.get (pivots[a]'ha_lt) = target.get (pivots[a]'ha_lt) := by
      have hpivot := transposeMulVec_apply_pivot rr pivots hrref solution0 a ha_lt hlen
      have hcongr := congrFun halg (⟨pivots[a]'ha_lt, hcol_lt_n⟩ : Fin n)
      rw [Pi.add_apply, hpivot, PackedVec.decode_get, PackedVec.decode_get, PackedVec.decode_get,
        hsol_a_false, Bool.toF2_false, add_zero] at hcongr
      exact Bool.toF2_injective hcongr
    rw [transposeSolveRrefFold_cons]
    rcases hfire : residual0.get (pivots[a]'ha_lt) with _ | _
    · rw [transposeSolveRrefStep_of_false rr pivots a (residual0, solution0) ha_lt hfire]
      apply ih hrest_nodup hrest_lt
      · exact fun k hk hkrest => hsmem k hk (List.mem_cons_of_mem a hkrest)
      · exact htail
      · intro k hk hknotrest
        rcases eq_or_ne k a with hka | hka
        · subst hka
          rw [hsol_a_false, ← h0a, hfire]
        · exact hscheck k hk (fun h => (List.mem_cons.mp h).elim hka hknotrest)
      · exact halg
    · rw [transposeSolveRrefStep_of_true rr pivots a (residual0, solution0) ha_lt hfire]
      apply ih hrest_nodup hrest_lt
      · intro k hk hkrest
        have hkne : a ≠ k := fun h => ha_notin_rest (h ▸ hkrest)
        show (solution0.setTotal a true).get k = false
        rw [get_setTotal_ne _ _ _ hkne]
        exact hsmem k hk (List.mem_cons_of_mem a hkrest)
      · intro r hr
        show (solution0.setTotal a true).get r.val = false
        have hrne : a ≠ r.val := by omega
        rw [get_setTotal_ne _ _ _ hrne]
        exact htail r hr
      · intro k hk hknotrest
        show (solution0.setTotal a true).get k = target.get (pivots[k]'hk)
        rcases eq_or_ne k a with hka | hka
        · subst hka
          rw [get_setTotal_self _ _ (ha_lt.trans_le hlen), ← h0a, hfire]
        · rw [get_setTotal_ne _ _ _ (Ne.symm hka)]
          exact hscheck k hk (fun h => (List.mem_cons.mp h).elim hka hknotrest)
      · show (residual0.xor (rowVec rr a)).decode +
          rr.decode.transpose.mulVec (solution0.setTotal a true).decode = target.decode
        rw [decode_xor, transpose_mulVec_setTotal_of_get_false rr solution0 a (ha_lt.trans_le hlen) hsol_a_false]
        funext c
        have hw : (rowVec rr a).decode c + (rowVec rr a).decode c = 0 :=
          CharTwo.add_self_eq_zero _
        have hxy : residual0.decode c + rr.decode.transpose.mulVec solution0.decode c =
            target.decode c := congrFun halg c
        simp only [Pi.add_apply]
        linear_combination hxy + hw

/-- `transposeSolveRrefSystem`'s canonical starting state (`residual0 := target`,
`solution0 := PackedVec.zero m`, processing order `List.range pivots.length`) instantiates
`transposeSolveRrefFold_spec`: every hypothesis is discharged trivially (the zero vector
is false everywhere; every index below `pivots.length` lies in `List.range pivots.length`,
so the checkpoint hypothesis is vacuous; the algebraic invariant holds since
`rr.decode.transpose.mulVec 0 = 0`). -/
theorem transposeSolveRrefSystem_spec (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (hlen : pivots.length ≤ m) (target : PackedVec n) :
    (∀ r : Fin m, pivots.length ≤ r.val →
        (transposeSolveRrefFold rr pivots (List.range pivots.length)
          (target, PackedVec.zero m)).2.get r.val = false) ∧
    (∀ k, (hk : k < pivots.length) →
        (transposeSolveRrefFold rr pivots (List.range pivots.length)
          (target, PackedVec.zero m)).2.get k = target.get (pivots[k]'hk)) ∧
    (transposeSolveRrefFold rr pivots (List.range pivots.length)
        (target, PackedVec.zero m)).1.decode +
      rr.decode.transpose.mulVec
        (transposeSolveRrefFold rr pivots (List.range pivots.length)
          (target, PackedVec.zero m)).2.decode = target.decode :=
  transposeSolveRrefFold_spec rr pivots hrref hlen target (List.range pivots.length)
    List.nodup_range
    (fun k hk => List.mem_range.mp hk)
    target (PackedVec.zero m)
    (fun k _ _ => get_zero m k)
    (fun r _ => get_zero m r.val)
    (fun k hk hnotin => absurd (List.mem_range.mpr hk) hnotin)
    (by rw [PackedVec.decode_zero, Matrix.mulVec_zero, add_zero])

/-- **Soundness and completeness** of `transposeSolveRrefSystem`: it returns `some x` exactly
when `x` solves `Aᵀ x = b` (for the RREF matrix `rr`) *and* every entry of `x` past
`pivots.length` is zero — the canonical solution Rust's forward pivot-cancellation produces.
Unlike `solveRrefSystem_eq_some_iff`, no case-split on pivot/non-pivot rows is needed: the
algebraic invariant `halg` from `transposeSolveRrefSystem_spec` directly characterizes
`final.1.isZero` as equivalent to the solved equation, via ordinary additive-group
cancellation (`add_eq_right`) rather than a `CharTwo`-specific argument. -/
theorem transposeSolveRrefSystem_eq_some_iff (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (hlen : pivots.length ≤ m) (target : PackedVec n)
    (x : PackedVec m) :
    transposeSolveRrefSystem rr pivots target = some x ↔
      rr.decode.transpose.mulVec x.decode = target.decode ∧
        ∀ r : Fin m, pivots.length ≤ r.val → x.get r.val = false := by
  obtain ⟨hzero_tail, hcheckpoint, halg⟩ :=
    transposeSolveRrefSystem_spec rr pivots hrref hlen target
  set final := transposeSolveRrefFold rr pivots (List.range pivots.length)
    (target, PackedVec.zero m) with hfinal_def
  have hisZero_iff : final.1.isZero = true ↔
      rr.decode.transpose.mulVec final.2.decode = target.decode := by
    rw [isZero_iff]
    constructor
    · intro h
      rw [h, zero_add] at halg
      exact halg
    · intro h
      rw [h] at halg
      exact add_eq_right.mp halg
  constructor
  · intro heq
    unfold transposeSolveRrefSystem at heq
    rw [← hfinal_def] at heq
    by_cases hcond : final.1.isZero = true
    · rw [ite_eq_left hcond] at heq
      have hxeq : final.2 = x := Option.some.inj heq
      exact ⟨hxeq ▸ hisZero_iff.mp hcond, hxeq ▸ hzero_tail⟩
    · rw [ite_eq_right hcond] at heq
      exact absurd heq (by simp)
  · rintro ⟨heqn, hxfree⟩
    have hget_eq : ∀ k, k < m → x.get k = final.2.get k := by
      intro k hk
      by_cases hpk : k < pivots.length
      · have hcongr := congrFun heqn
          (⟨pivots[k]'hpk, hrref.lt_n _ (List.getElem_mem hpk)⟩ : Fin n)
        rw [transposeMulVec_apply_pivot rr pivots hrref x k hpk hlen, PackedVec.decode_get,
          PackedVec.decode_get] at hcongr
        rw [Bool.toF2_injective hcongr, hcheckpoint k hpk]
      · replace hpk : pivots.length ≤ k := by omega
        rw [hxfree ⟨k, hk⟩ hpk, hzero_tail ⟨k, hk⟩ hpk]
    have hdecode_eq : x.decode = final.2.decode := by
      funext i
      rw [PackedVec.decode_get, PackedVec.decode_get, hget_eq i.val i.isLt]
    have hxeq : final.2 = x := (ext_of_decode hdecode_eq).symm
    have hcond : final.1.isZero = true := hisZero_iff.mpr (by rw [hxeq]; exact heqn)
    show (if final.1.isZero then some final.2 else none) = some x
    rw [ite_eq_left hcond, hxeq]

/-- **Solvability by the canonical vector iff solvability by any vector**: every entry of
`x` past `pivots.length` never influences `rr.decode.transpose.mulVec x.decode`
(`transposeMulVec_apply_pivot` pins the first `pivots.length` entries of *any* solution
of `Aᵀx=b` to `target` read back through `pivots`, matching the canonical solution's
checkpoint values there; `transpose_mulVec_eq_of_agree_lt` then transports the equation from
`x` to the canonical vector despite their possibly differing tails). The converse is
trivial: the canonical vector is itself *a* solution. -/
theorem transposeSolveRrefSystem_isSolvable_iff (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (hlen : pivots.length ≤ m) (target : PackedVec n) :
    (∃ x : PackedVec m, rr.decode.transpose.mulVec x.decode = target.decode) ↔
      ∃ x : PackedVec m, rr.decode.transpose.mulVec x.decode = target.decode ∧
        ∀ r : Fin m, pivots.length ≤ r.val → x.get r.val = false := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hzero_tail, hcheckpoint, _⟩ :=
      transposeSolveRrefSystem_spec rr pivots hrref hlen target
    set final := transposeSolveRrefFold rr pivots (List.range pivots.length)
      (target, PackedVec.zero m) with hfinal_def
    have hagree : ∀ k, (hk : k < pivots.length) → final.2.get k = x.get k := by
      intro k hk
      have hcongr := congrFun hx (⟨pivots[k]'hk, hrref.lt_n _ (List.getElem_mem hk)⟩ : Fin n)
      rw [transposeMulVec_apply_pivot rr pivots hrref x k hk hlen, PackedVec.decode_get,
        PackedVec.decode_get] at hcongr
      exact (hcheckpoint k hk).trans (Bool.toF2_injective hcongr).symm
    have hmulVec_eq :
        rr.decode.transpose.mulVec final.2.decode = rr.decode.transpose.mulVec x.decode :=
      transpose_mulVec_eq_of_agree_lt rr pivots hrref final.2 x hagree
    exact ⟨final.2, hmulVec_eq.trans hx, hzero_tail⟩
  · rintro ⟨x, hx, _⟩
    exact ⟨x, hx⟩

/-- **Completeness of `none`**: `transposeSolveRrefSystem` reports `none` exactly when
`target` is *genuinely unsolvable*, i.e. no `x` at all (canonical or not) satisfies
`Aᵀ x = target`. Combined with `transposeSolveRrefSystem_eq_some_iff`, this pins down
`transposeSolveRrefSystem` completely: it is `some x` iff `x` is the canonical solution, and
`none` iff `target` admits no solution of `Aᵀ x = target` whatsoever (equivalently, `target`
is outside the row space of `A`). -/
theorem transposeSolveRrefSystem_eq_none_iff (rr : PackedMatrix m n) (pivots : List Nat)
    (hrref : IsRREF rr pivots) (hlen : pivots.length ≤ m) (target : PackedVec n) :
    transposeSolveRrefSystem rr pivots target = none ↔
      ¬ ∃ x : PackedVec m, rr.decode.transpose.mulVec x.decode = target.decode := by
  constructor
  · intro hnone hex
    obtain ⟨x', hx', hx'zero⟩ :=
      (transposeSolveRrefSystem_isSolvable_iff rr pivots hrref hlen target).mp hex
    have hsome :=
      (transposeSolveRrefSystem_eq_some_iff rr pivots hrref hlen target x').mpr ⟨hx', hx'zero⟩
    rw [hnone] at hsome
    exact absurd hsome (by simp)
  · intro hnex
    by_contra hnone
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp hnone
    exact hnex
      ⟨x, ((transposeSolveRrefSystem_eq_some_iff rr pivots hrref hlen target x).mp hx.symm).1⟩

/-! ## `EchelonForm::solve`/`EchelonForm::transpose_solve`: lifting to the original matrix

Mirrors `EchelonForm::solve`/`EchelonForm::transpose_solve` (Lean: `EchelonForm.solve`/
`EchelonForm.transposeSolve`), which reduce to `solve_rref_system`/
`transpose_solve_rref_system` on the reduced matrix, transforming the *input* target
(respectively, the RREF-level *output* solution) by `EchelonForm.new`'s accumulated
transform `T`:
```
pub fn solve(&self, target: &AlignedBitView) -> Option<AlignedBitVec> {
    let transformed_target = &self.transform * target;
    solve_rref_system(&self.matrix, &self.pivots, &transformed_target.as_view())
}

pub fn transpose_solve(&self, target: &AlignedBitView) -> Option<AlignedBitVec> {
    let rref_solution = transpose_solve_rref_system(&self.matrix, &self.pivots, target)?;
    Some(self.transform.right_multiply(&rref_solution.as_view()))
}
```
`EchelonForm.new_transform_mul_eq` (`T * A = R`) transports both RREF-level results to `A`
directly. `EchelonForm.new_transform_mul_inv` (`T * Vᵀ = 1`, hence also `Vᵀ * T = 1`, since
a square matrix with a one-sided inverse over a field is two-sided invertible) is
additionally needed wherever a `T`-wrapped equation must be *cancelled* down to a bare
statement about `A` (`solve`'s both directions; `transposeSolve`'s `none`-completeness),
but not where a witness is merely *substituted* through the transform without inverting it
(`transposeSolve`'s `some`-case soundness/completeness). -/

/-- A right-invertible square matrix cancels under `Matrix.mulVec` on the left: the
algebraic content of `EchelonForm.new_transform_mul_inv` that lets `EchelonForm.solve`'s
correctness theorems strip the transform `T` off both sides of a `T.mulVec`-wrapped
equation. -/
theorem mulVec_left_cancel_of_mul_eq_one {k : Nat} (T U : Matrix (Fin k) (Fin k) F2)
    (hTU : T * U = 1) (p q : Fin k → F2) (h : T.mulVec p = T.mulVec q) : p = q := by
  have hUT : U * T = 1 := mul_eq_one_comm.mp hTU
  have hcong := congrArg U.mulVec h
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hUT, Matrix.one_mulVec, Matrix.one_mulVec]
    at hcong

/-- Mirrors `EchelonForm::solve`: transform `target` by the accumulated transform, then
hand off to `solveRrefSystem` on the reduced matrix/pivots. -/
def _root_.BinarFormal.Echelon.EchelonForm.solve (S : EchelonForm m n) (target : PackedVec m) :
    Option (PackedVec n) :=
  solveRrefSystem S.matrix S.pivots (S.transform.mulVec target)

/-- Mirrors `EchelonForm::transpose_solve`: solve the transpose system against the reduced
matrix/pivots, then carry the RREF-level solution back through the transform via
`rightMultiply`. -/
def _root_.BinarFormal.Echelon.EchelonForm.transposeSolve (S : EchelonForm m n)
    (target : PackedVec n) : Option (PackedVec m) :=
  (transposeSolveRrefSystem S.matrix S.pivots target).map S.transform.rightMultiply

/-- **Soundness and completeness of `EchelonForm.solve`, for the original matrix `A`**:
mirrors `solveRrefSystem_eq_some_iff` exactly (identical canonical-shape condition, since
`solve`'s only post-processing is on the *input* target, never on its output), transported
from the RREF matrix `R = T * A` to `A` itself by cancelling `T` via
`mulVec_left_cancel_of_mul_eq_one`. -/
theorem EchelonForm.solve_eq_some_iff (A : PackedMatrix m n) (target : PackedVec m)
    (x : PackedVec n) :
    (EchelonForm.new A).solve target = some x ↔
      A.decode.mulVec x.decode = target.decode ∧
        ∀ c, c < n → c ∉ (EchelonForm.new A).pivots → x.get c = false := by
  have hTA := EchelonForm.new_transform_mul_eq A
  have hTU := EchelonForm.new_transform_mul_inv A
  have hrref := EchelonForm.new_isRREF A
  have hlen := EchelonForm.new_pivots_length_le A
  show solveRrefSystem _ _ _ = some x ↔ _
  rw [solveRrefSystem_eq_some_iff _ _ hrref hlen _ x, decode_mulVec, ← hTA,
    ← Matrix.mulVec_mulVec]
  constructor
  · rintro ⟨heq, hfree⟩
    exact ⟨mulVec_left_cancel_of_mul_eq_one _ _ hTU _ _ heq, hfree⟩
  · rintro ⟨heq, hfree⟩
    exact ⟨congrArg (EchelonForm.new A).transform.decode.mulVec heq, hfree⟩

/-- **Completeness of `none` for `EchelonForm.solve`**: `A x = target` is unsolvable
(over *any* `x`, canonical or not) iff `solve` reports `none`. -/
theorem EchelonForm.solve_eq_none_iff (A : PackedMatrix m n) (target : PackedVec m) :
    (EchelonForm.new A).solve target = none ↔
      ¬ ∃ x : PackedVec n, A.decode.mulVec x.decode = target.decode := by
  have hTA := EchelonForm.new_transform_mul_eq A
  have hTU := EchelonForm.new_transform_mul_inv A
  have hrref := EchelonForm.new_isRREF A
  have hlen := EchelonForm.new_pivots_length_le A
  show solveRrefSystem _ _ _ = none ↔ _
  rw [solveRrefSystem_eq_none_iff _ _ hrref hlen _]
  constructor
  · intro hnone hex
    obtain ⟨x, hx⟩ := hex
    refine hnone ⟨x, ?_⟩
    rw [decode_mulVec, ← hTA, ← Matrix.mulVec_mulVec]
    exact congrArg (EchelonForm.new A).transform.decode.mulVec hx
  · intro hnex hex
    obtain ⟨x, hx⟩ := hex
    rw [decode_mulVec, ← hTA, ← Matrix.mulVec_mulVec] at hx
    exact hnex ⟨x, mulVec_left_cancel_of_mul_eq_one _ _ hTU _ _ hx⟩

/-- **Soundness and completeness of `EchelonForm.transposeSolve`, for the original matrix
`A`**: mirrors `transposeSolveRrefSystem_eq_some_iff`, transported along the transform `T`
(`x := T.rightMultiply y` for the RREF-level canonical `y`). Since `transposeSolve` *does*
post-process its output, the canonical-shape condition genuinely routes through `T`; it is
expressed as "some canonical-shaped RREF-level `y` produces `x`" rather than a bare
condition on `x`'s own entries, matching exactly how Rust constructs `x`. Neither direction
needs `T`'s invertibility: `x` is only ever *substituted*, never inverted. -/
theorem EchelonForm.transposeSolve_eq_some_iff (A : PackedMatrix m n) (target : PackedVec n)
    (x : PackedVec m) :
    (EchelonForm.new A).transposeSolve target = some x ↔
      A.decode.transpose.mulVec x.decode = target.decode ∧
        ∃ y : PackedVec m, x = (EchelonForm.new A).transform.rightMultiply y ∧
          ∀ r : Fin m, (EchelonForm.new A).pivots.length ≤ r.val → y.get r.val = false := by
  have hTA := EchelonForm.new_transform_mul_eq A
  have hrref := EchelonForm.new_isRREF A
  have hlen := EchelonForm.new_pivots_length_le A
  show (transposeSolveRrefSystem _ _ _).map _ = some x ↔ _
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨hyeq, hyfree⟩ := (transposeSolveRrefSystem_eq_some_iff _ _ hrref hlen _ y).mp hy
    refine ⟨?_, y, hxy.symm, hyfree⟩
    rw [← hxy, decode_rightMultiply, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
      ← Matrix.transpose_mul, hTA]
    exact hyeq
  · rintro ⟨heq, y, hxy, hyfree⟩
    refine ⟨y, ?_, hxy.symm⟩
    rw [transposeSolveRrefSystem_eq_some_iff _ _ hrref hlen]
    refine ⟨?_, hyfree⟩
    rw [← heq, hxy, decode_rightMultiply, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
      ← Matrix.transpose_mul, hTA]

/-- **Completeness of `none` for `EchelonForm.transposeSolve`**: `Aᵀ x = target` is
unsolvable (over *any* `x`) iff `transposeSolve` reports `none`. Unlike
`transposeSolve_eq_some_iff`, this needs `T`'s invertibility (`new_transform_mul_inv`) to
*construct* a preimage of any hypothetical `x` back at the RREF level. -/
theorem EchelonForm.transposeSolve_eq_none_iff (A : PackedMatrix m n) (target : PackedVec n) :
    (EchelonForm.new A).transposeSolve target = none ↔
      ¬ ∃ x : PackedVec m, A.decode.transpose.mulVec x.decode = target.decode := by
  have hTA := EchelonForm.new_transform_mul_eq A
  have hTU := EchelonForm.new_transform_mul_inv A
  have hrref := EchelonForm.new_isRREF A
  have hlen := EchelonForm.new_pivots_length_le A
  have hUT : (EchelonForm.new A).transformInvT.decode.transpose *
      (EchelonForm.new A).transform.decode = 1 := mul_eq_one_comm.mp hTU
  have hUR : (EchelonForm.new A).transformInvT.decode.transpose *
      (EchelonForm.new A).matrix.decode = A.decode := by
    rw [← hTA, ← Matrix.mul_assoc, hUT, Matrix.one_mul]
  show (transposeSolveRrefSystem _ _ _).map _ = none ↔ _
  rw [Option.map_eq_none_iff, transposeSolveRrefSystem_eq_none_iff _ _ hrref hlen]
  constructor
  · intro hnoney hex
    obtain ⟨x, hx⟩ := hex
    refine hnoney ⟨(EchelonForm.new A).transformInvT.transpose.rightMultiply x, ?_⟩
    rw [decode_rightMultiply, decode_transpose, Matrix.mulVec_transpose, Matrix.vecMul_vecMul,
      hUR, ← Matrix.mulVec_transpose]
    exact hx
  · intro hnonex hey
    obtain ⟨y, hy⟩ := hey
    refine hnonex ⟨(EchelonForm.new A).transform.rightMultiply y, ?_⟩
    rw [decode_rightMultiply, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
      ← Matrix.transpose_mul, hTA]
    exact hy

/-! ## Kernel basis

Mirrors `kernel_basis_matrix`/`complement`: for an already-RREF'd matrix `rr` with pivot
list `pivots`, each free (non-pivot) column `c` contributes one row to the kernel basis,
namely `kernelVec rr pivots c`. Rust's `kernel_basis_matrix` writes this row via two
sequential `set` loops (one copying pivot-column entries off `rr`, one setting the row's
own driving column to `true`); since those loops touch disjoint cells, `kernelVec` gives
the same content as a single closed-form `PackedVec.ofBoolFn`, matching the `ofBoolFn`
doc comment's stated rationale. -/

/-- The shared per-row closed form behind `PackedMatrix.kernelBasis`: entry `c` (this row's
own driving free column) is `true`; every pivot column reads off `rr`'s already-computed
RREF via `BinarFormal.Echelon.getTotal` at that pivot's row (mirroring
`rr[(index, col_src)]` inside `kernel_basis_matrix`'s inner loop); every other column is
`false`. -/
def kernelVec (rr : PackedMatrix m n) (pivots : List Nat) (c : Nat) : PackedVec n :=
  PackedVec.ofBoolFn n (fun j => if j = c then true else getTotal rr (pivots.idxOf j) c)

/-- `kernelVec`'s own driving free column always reads `true`. -/
theorem get_kernelVec_self (rr : PackedMatrix m n) (pivots : List Nat) (c : Nat) (hc : c < n) :
    (kernelVec rr pivots c).get c = true := by
  rw [kernelVec, get_ofBoolFn n _ c hc, ite_eq_left rfl]

/-- `kernelVec`'s value at a pivot column reads off `rr` at that pivot's row, since
`pivots.idxOf` recovers the row index of any column actually appearing in `pivots`. -/
theorem get_kernelVec_pivot {rr : PackedMatrix m n} {pivots : List Nat} (hpn : pivots.Nodup)
    (c : Nat) (i : Nat) (hi : i < pivots.length) (hne : pivots[i]'hi ≠ c)
    (hcol_lt : pivots[i]'hi < n) :
    (kernelVec rr pivots c).get (pivots[i]'hi) = getTotal rr i c := by
  rw [kernelVec, get_ofBoolFn n _ _ hcol_lt, ite_eq_right hne]
  have hidx : pivots.idxOf (pivots[i]'hi) = i := by
    have hmem : pivots[i]'hi ∈ pivots := List.getElem_mem hi
    have hlt : pivots.idxOf (pivots[i]'hi) < pivots.length := List.idxOf_lt_length_iff.mpr hmem
    have heq : pivots[pivots.idxOf (pivots[i]'hi)]'hlt = pivots[i]'hi := List.getElem_idxOf hlt
    exact (List.Nodup.getElem_inj_iff hpn).mp heq
  rw [hidx]

/-- `BinarFormal.Echelon.getTotal` always reads `false` once the row index reaches or
exceeds `pivots.length`, whether via its own out-of-range branch or via `IsRREF.rows_zero`. -/
theorem getTotal_of_ge {rr : PackedMatrix m n} {pivots : List Nat} (hrref : IsRREF rr pivots)
    (idx c : Nat) (hge : pivots.length ≤ idx) (hc : c < n) :
    getTotal rr idx c = false := by
  unfold getTotal
  split
  · next h => exact hrref.rows_zero ⟨idx, h⟩ hge c hc
  · rfl

/-- `kernelVec`'s value at any free column other than its own driving column is always
`false`: such a column is absent from `pivots`, so `pivots.idxOf` lands at or past
`pivots.length`, where `getTotal_of_ge` applies. -/
theorem get_kernelVec_free_ne {rr : PackedMatrix m n} {pivots : List Nat}
    (hrref : IsRREF rr pivots) (c : Nat) (hc : c < n)
    (j : Nat) (hjn : j < n) (hjfree : j ∉ pivots) (hjne : j ≠ c) :
    (kernelVec rr pivots c).get j = false := by
  rw [kernelVec, get_ofBoolFn n _ j hjn, ite_eq_right hjne]
  have hge : pivots.length ≤ pivots.idxOf j := by
    by_contra hlt
    push Not at hlt
    exact hjfree (List.idxOf_lt_length_iff.mp hlt)
  exact getTotal_of_ge hrref _ c hge hc

/-- Additively decomposing `kernelVec` into its free-zero part (its own driving column
cleared) plus the standard basis vector at that column; the key step for reducing
`kernelVec`'s kernel membership to the already-proven `mulVec_apply_of_free_zero`. -/
theorem decode_kernelVec_eq {rr : PackedMatrix m n} {pivots : List Nat} (c : Nat) (hc : c < n) :
    (kernelVec rr pivots c).decode
      = ((kernelVec rr pivots c).setTotal c false).decode + Pi.single (⟨c, hc⟩ : Fin n) 1 := by
  funext j
  rw [PackedVec.decode_get, Pi.add_apply, PackedVec.decode_get]
  rcases eq_or_ne j.val c with hjc | hjc
  · have hje : j = ⟨c, hc⟩ := Fin.ext hjc
    subst hje
    rw [get_setTotal_self _ c hc, Pi.single_eq_same]
    have hself : (kernelVec rr pivots c).get c = true := get_kernelVec_self rr pivots c hc
    show Bool.toF2 ((kernelVec rr pivots c).get c) = Bool.toF2 false + 1
    rw [hself]
    decide
  · rw [get_setTotal_ne _ c false (Ne.symm hjc),
      Pi.single_eq_of_ne (fun h => hjc (congrArg Fin.val h))]
    simp

/-- Clearing `kernelVec`'s own driving column leaves every free column `false`, the exact
hypothesis `mulVec_apply_of_free_zero` needs of its vector argument. -/
theorem kernelVec_setTotal_free_zero {rr : PackedMatrix m n} {pivots : List Nat}
    (hrref : IsRREF rr pivots) (c : Nat) (hc : c < n) (hcfree : c ∉ pivots) :
    ∀ c', c' < n → c' ∉ pivots → ((kernelVec rr pivots c).setTotal c false).get c' = false := by
  intro c' hc'n hc'free
  by_cases hcc' : c' = c
  · subst hcc'; exact get_setTotal_self _ _ hc'n false
  · rw [get_setTotal_ne _ c false (Ne.symm hcc')]
    exact get_kernelVec_free_ne hrref c hc c' hc'n hc'free hcc'

/-- Every `kernelVec` row lies in the kernel of the *reduced* matrix: `rr *ᵥ (kernelVec
rr pivots c).decode = 0` for every free column `c`. Combines the additive decomposition
`decode_kernelVec_eq` with Mathlib's `Matrix.mulVec_single`, reuses the already-proven
`mulVec_apply_of_free_zero` for the free-zero half, and closes the pivot-row case via
`ZMod 2`'s characteristic-2 cancellation `x + x = 0`. -/
theorem kernelVec_mem_ker {rr : PackedMatrix m n} {pivots : List Nat}
    (hrref : IsRREF rr pivots) (c : Nat) (hc : c < n) (hcfree : c ∉ pivots) :
    rr.decode.mulVec (kernelVec rr pivots c).decode = 0 := by
  rw [decode_kernelVec_eq c hc, Matrix.mulVec_add, Matrix.mulVec_single]
  have hy'free := kernelVec_setTotal_free_zero hrref c hc hcfree
  funext row
  rw [Pi.add_apply, mulVec_apply_of_free_zero rr pivots hrref
    ((kernelVec rr pivots c).setTotal c false) hy'free row]
  by_cases hrow : row.val < pivots.length
  · rw [dite_eq_left hrow]
    have hcol_lt : pivots[row.val]'hrow < n := hrref.lt_n _ (List.getElem_mem hrow)
    have hne : pivots[row.val]'hrow ≠ c := fun h => hcfree (h ▸ List.getElem_mem hrow)
    rw [get_setTotal_ne _ c false (Ne.symm hne)]
    have hpn : pivots.Nodup := List.Pairwise.imp (fun {a b} hab => Nat.ne_of_lt hab) hrref.sorted
    rw [get_kernelVec_pivot hpn c row.val hrow hne hcol_lt]
    have hgt : getTotal rr row.val c = rr.get row c := by
      unfold getTotal
      rw [dite_eq_left row.isLt]
    rw [hgt]
    show Bool.toF2 (rr.get row c) + (MulOpposite.op (1 : ZMod 2) • rr.decode.col ⟨c, hc⟩) row = 0
    rw [Pi.smul_apply, Matrix.col_apply]
    simp only [MulOpposite.op_one, one_smul]
    rw [PackedMatrix.decode_get]
    exact (show ∀ x : ZMod 2, x + x = 0 by decide) _
  · rw [dite_eq_right hrow]
    have hge : pivots.length ≤ row.val := by omega
    have hrzero : rr.get row c = false := hrref.rows_zero row hge c hc
    show (0 : ZMod 2) + (MulOpposite.op (1 : ZMod 2) • rr.decode.col ⟨c, hc⟩) row = 0
    rw [Pi.smul_apply, Matrix.col_apply]
    simp only [MulOpposite.op_one, one_smul]
    rw [PackedMatrix.decode_get, hrzero]
    simp

/-- The complement of `pivots` inside `0, ..., n - 1`, mirroring Rust's `complement` (as
called from `kernel_basis_matrix`): the sorted list of free (non-pivot) column indices. -/
def freeColumns (pivots : List Nat) (n : Nat) : List Nat :=
  (List.range n).filter (· ∉ pivots)

/-- Membership characterization for `freeColumns`. -/
theorem mem_freeColumns_iff (pivots : List Nat) (n c : Nat) :
    c ∈ freeColumns pivots n ↔ c < n ∧ c ∉ pivots := by
  unfold freeColumns
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq]

/-- `freeColumns` inherits strict sortedness from `List.range`, mirroring `complement`'s
sorted-input/sorted-output contract (`assume_sorted_by_item`/`difference`). -/
theorem freeColumns_sorted (pivots : List Nat) (n : Nat) :
    (freeColumns pivots n).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

/-- Pivots and free columns partition `0, ..., n - 1`: their counts add to `n`. This is
the counting fact underlying `kernel_basis_matrix`'s `res_row_count = num_cols -
rank_profile.len()`. -/
theorem freeColumns_length_add (pivots : List Nat) (n : Nat) (hsorted : pivots.Pairwise (· < ·))
    (hlt : ∀ c ∈ pivots, c < n) :
    pivots.length + (freeColumns pivots n).length = n := by
  have hnodup : pivots.Nodup := List.Pairwise.imp (fun {a b} hab => Nat.ne_of_lt hab) hsorted
  have hnodup2 : (freeColumns pivots n).Nodup := List.Nodup.filter _ List.nodup_range
  have hcard1 : pivots.toFinset.card = pivots.length := List.toFinset_card_of_nodup hnodup
  have hcard2 : (freeColumns pivots n).toFinset.card = (freeColumns pivots n).length :=
    List.toFinset_card_of_nodup hnodup2
  have hunion : pivots.toFinset ∪ (freeColumns pivots n).toFinset = Finset.range n := by
    ext c
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_range]
    rw [mem_freeColumns_iff]
    constructor
    · rintro (h | ⟨h1, _⟩)
      · exact hlt c h
      · exact h1
    · intro h
      by_cases hc : c ∈ pivots
      · exact Or.inl hc
      · exact Or.inr ⟨h, hc⟩
  have hdisjoint : Disjoint pivots.toFinset (freeColumns pivots n).toFinset := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    simp only [List.mem_toFinset] at hc1 hc2
    exact (mem_freeColumns_iff pivots n c).mp hc2 |>.2 hc1
  have hcardunion := Finset.card_union_of_disjoint hdisjoint
  rw [hunion, Finset.card_range] at hcardunion
  omega

/-- Mirrors `kernel_basis_matrix`: for each free column of `A`'s RREF (`EchelonForm.new
A`), in order, the corresponding kernel-basis row is `kernelVec` evaluated at that column.
The row count `(freeColumns (EchelonForm.new A).pivots n).length` is exactly Rust's
`res_row_count = num_cols - rank_profile.len()` (see `kernelBasis_rows_length_eq`). -/
def _root_.BinarFormal.Packed.PackedMatrix.kernelBasis (A : PackedMatrix m n) :
    PackedMatrix (freeColumns (EchelonForm.new A).pivots n).length n where
  rows k := kernelVec (EchelonForm.new A).matrix (EchelonForm.new A).pivots
    ((freeColumns (EchelonForm.new A).pivots n)[k.1]'k.2)

/-- The rows of `PackedMatrix.kernelBasis` are linearly independent over `F2`: evaluating
a vanishing linear combination at each row's own driving free column isolates that row's
coefficient, since `get_kernelVec_self` gives `1` there and `get_kernelVec_free_ne` gives
`0` at every other row's driving column. -/
theorem kernelBasis_linearIndependent (A : PackedMatrix m n) :
    LinearIndependent F2 (fun k => (kernelBasis A).rows k |>.decode) := by
  set pivots := (EchelonForm.new A).pivots
  set rr := (EchelonForm.new A).matrix
  set free := freeColumns pivots n with hfree_def
  have hrref := EchelonForm.new_isRREF A
  have hsorted : free.Pairwise (· < ·) := freeColumns_sorted pivots n
  have hfreenodup : free.Nodup := List.Pairwise.imp (fun {a b} hab => Nat.ne_of_lt hab) hsorted
  rw [Fintype.linearIndependent_iff]
  intro a ha0 j
  have hcol : free[j.1]'j.2 < n := (mem_freeColumns_iff pivots n _).mp (List.getElem_mem j.2) |>.1
  have hcolfree : free[j.1]'j.2 ∉ pivots :=
    (mem_freeColumns_iff pivots n _).mp (List.getElem_mem j.2) |>.2
  have hcongr := congrFun ha0 ⟨free[j.1]'j.2, hcol⟩
  rw [Finset.sum_apply] at hcongr
  simp only [Pi.smul_apply, smul_eq_mul] at hcongr
  rw [Finset.sum_eq_single j] at hcongr
  · show a j = 0
    have hself : ((kernelBasis A).rows j).decode ⟨free[j.1]'j.2, hcol⟩ = 1 := by
      show Bool.toF2 (((kernelBasis A).rows j).get (free[j.1]'j.2)) = 1
      show Bool.toF2 ((kernelVec rr pivots (free[j.1]'j.2)).get (free[j.1]'j.2)) = 1
      rw [get_kernelVec_self rr pivots _ hcol]
      rfl
    rw [hself, mul_one] at hcongr
    exact hcongr
  · intro k _ hkne
    have hk_col : free[k.1]'k.2 < n :=
      (mem_freeColumns_iff pivots n _).mp (List.getElem_mem k.2) |>.1
    have hk_free : free[k.1]'k.2 ∉ pivots :=
      (mem_freeColumns_iff pivots n _).mp (List.getElem_mem k.2) |>.2
    have hne : free[k.1]'k.2 ≠ free[j.1]'j.2 := by
      intro heq
      apply hkne
      exact Fin.ext ((List.Nodup.getElem_inj_iff hfreenodup).mp heq)
    have hother : ((kernelBasis A).rows k).decode ⟨free[j.1]'j.2, hcol⟩ = 0 := by
      show Bool.toF2 (((kernelBasis A).rows k).get (free[j.1]'j.2)) = 0
      show Bool.toF2 ((kernelVec rr pivots (free[k.1]'k.2)).get (free[j.1]'j.2)) = 0
      rw [get_kernelVec_free_ne hrref _ hk_col _ hcol hcolfree (Ne.symm hne)]
      rfl
    rw [hother, mul_zero]
  · intro hjnotin
    exact absurd (Finset.mem_univ j) hjnotin

/-- Every row of `PackedMatrix.kernelBasis A` lies in `LinearMap.ker A.decode.mulVecLin`:
`kernelVec_mem_ker`'s membership against the *reduced* matrix transports to `A` itself via
the transform's invertibility (`mulVec_left_cancel_of_mul_eq_one`), exactly as
`EchelonForm.solve`'s soundness theorems transport RREF-level facts back to `A`. -/
theorem kernelBasis_mem_ker (A : PackedMatrix m n)
    (k : Fin (freeColumns (EchelonForm.new A).pivots n).length) :
    ((kernelBasis A).rows k).decode ∈ LinearMap.ker A.decode.mulVecLin := by
  have hrref := EchelonForm.new_isRREF A
  have hTA := EchelonForm.new_transform_mul_eq A
  have hTU := EchelonForm.new_transform_mul_inv A
  have hcol : (freeColumns (EchelonForm.new A).pivots n)[k.1]'k.2 < n :=
    (mem_freeColumns_iff (EchelonForm.new A).pivots n _).mp (List.getElem_mem k.2) |>.1
  have hcolfree : (freeColumns (EchelonForm.new A).pivots n)[k.1]'k.2 ∉ (EchelonForm.new A).pivots :=
    (mem_freeColumns_iff (EchelonForm.new A).pivots n _).mp (List.getElem_mem k.2) |>.2
  have hmemrr : (EchelonForm.new A).matrix.decode.mulVec ((kernelBasis A).rows k).decode = 0 :=
    kernelVec_mem_ker hrref _ hcol hcolfree
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  apply mulVec_left_cancel_of_mul_eq_one (EchelonForm.new A).transform.decode
    (EchelonForm.new A).transformInvT.decode.transpose hTU
  rw [Matrix.mulVec_mulVec, hTA, Matrix.mulVec_zero]
  exact hmemrr

/-- Rank-nullity: the kernel of `A.decode.mulVecLin` has dimension exactly `(freeColumns
(EchelonForm.new A).pivots n).length`, combining Mathlib's rank-nullity theorem
(`LinearMap.finrank_range_add_finrank_ker`) with `Matrix.rank`'s defining equality to
`finrank (range mulVecLin)` and `EchelonForm.new_pivots_length_eq_rank`. -/
theorem finrank_ker_mulVecLin_eq_freeColumns_length (A : PackedMatrix m n) :
    Module.finrank F2 (LinearMap.ker A.decode.mulVecLin) =
      (freeColumns (EchelonForm.new A).pivots n).length := by
  have hrn := LinearMap.finrank_range_add_finrank_ker A.decode.mulVecLin
  rw [Module.finrank_pi, Fintype.card_fin] at hrn
  have hrange : Module.finrank F2 (LinearMap.range A.decode.mulVecLin) = A.decode.rank := rfl
  rw [hrange] at hrn
  have hrankpiv : A.decode.rank = (EchelonForm.new A).pivots.length :=
    (EchelonForm.new_pivots_length_eq_rank A).symm
  have hlt : ∀ c ∈ (EchelonForm.new A).pivots, c < n := (EchelonForm.new_isRREF A).lt_n
  have hsorted : (EchelonForm.new A).pivots.Pairwise (· < ·) := (EchelonForm.new_isRREF A).sorted
  have hcount := freeColumns_length_add (EchelonForm.new A).pivots n hsorted hlt
  omega

/-- **Strong basis theorem**: the kernel-basis rows exactly span `LinearMap.ker
A.decode.mulVecLin`. Combined with `kernelBasis_linearIndependent` and
`kernelBasis_mem_ker`, this establishes that `PackedMatrix.kernelBasis`'s rows are exactly
a basis of the kernel, discharging requirement (4) without any Mathlib choice oracle: the
span inclusion is by direct membership, and equality follows from matching
`Module.finrank` (via `finrank_span_eq_card` on the independent family, against
`finrank_ker_mulVecLin_eq_freeColumns_length`) rather than an explicit spanning
decomposition. -/
theorem kernelBasis_span_eq_ker (A : PackedMatrix m n) :
    Submodule.span F2 (Set.range (fun k => ((kernelBasis A).rows k).decode)) =
      LinearMap.ker A.decode.mulVecLin := by
  have hli := kernelBasis_linearIndependent A
  have hle : Submodule.span F2 (Set.range (fun k => ((kernelBasis A).rows k).decode)) ≤
      LinearMap.ker A.decode.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact kernelBasis_mem_ker A k
  have hfr_span : Module.finrank F2
      (Submodule.span F2 (Set.range (fun k => ((kernelBasis A).rows k).decode)))
      = (freeColumns (EchelonForm.new A).pivots n).length := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  exact Submodule.eq_of_le_of_finrank_eq hle
    (by rw [hfr_span, finrank_ker_mulVecLin_eq_freeColumns_length])

/-- `A * (PackedMatrix.kernelBasis A)ᵀ = 0`, the matrix-level restatement of
`kernelBasis_mem_ker` for every row simultaneously. -/
theorem decode_mul_kernelBasis_decode_transpose_eq_zero (A : PackedMatrix m n) :
    A.decode * (kernelBasis A).decode.transpose = 0 := by
  funext i k
  have hmem := kernelBasis_mem_ker A k
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hmem
  have hi := congrFun hmem i
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  exact hi

/-- The row count of `PackedMatrix.kernelBasis A` (i.e. `(freeColumns ...).length`) equals
the nullity `n - A.decode.rank`, mirroring `kernel_basis_matrix`'s `res_row_count =
num_cols - rank_profile.len()`. -/
theorem kernelBasis_rows_length_eq (A : PackedMatrix m n) :
    (freeColumns (EchelonForm.new A).pivots n).length = n - A.decode.rank := by
  have hlt : ∀ c ∈ (EchelonForm.new A).pivots, c < n := (EchelonForm.new_isRREF A).lt_n
  have hsorted : (EchelonForm.new A).pivots.Pairwise (· < ·) := (EchelonForm.new_isRREF A).sorted
  have hcount := freeColumns_length_add (EchelonForm.new A).pivots n hsorted hlt
  have hrank := EchelonForm.new_pivots_length_eq_rank A
  omega

/-! ## Matrix inversion

Mirrors `AlignedBitMatrix::inverted`: for a square, full-rank matrix `A`, the accumulated
transform from `EchelonForm.new A` is `A`'s two-sided inverse. Rust's
`assert_eq!(echelon_form.pivots.len(), self.row_count())` becomes the explicit hypothesis
`PackedMatrix.rank A = n` taken by `PackedMatrix.inverted`, giving a *total* Lean function
rather than one modelling a panic; Rust's `debug_assert_eq!(self *
&echelon_form.transform, AlignedBitMatrix::identity(...))` is exactly the theorem
`inverted_mul_right` proved below (both are the correctness statement, not defensive
code, from the Lean side). -/

/-- A strictly increasing, length-`n` list of naturals all below `n` is forced to be
`[0, 1, ..., n - 1]` read off by index: the unique increasing enumeration of `Finset.range
n` (`Finset.orderEmbOfFin_unique`) applied to the indexing function `fun i => pivots[i]`
identifies it with `(Finset.range n).orderEmbOfFin`, whose values are the identity
(`Finset.sort_range`, `List.getElem_range`). -/
theorem pivots_eq_id_of_length_eq (pivots : List Nat) (n : Nat)
    (hsorted : pivots.Pairwise (· < ·)) (hlt : ∀ c ∈ pivots, c < n) (hlen : pivots.length = n)
    (i : Nat) (hi : i < pivots.length) : pivots[i]'hi = i := by
  have hmono : StrictMono (fun i : Fin n => pivots[i.1]'(hlen ▸ i.2)) := by
    intro a b hab
    exact List.pairwise_iff_getElem.mp hsorted a.1 b.1 (hlen ▸ a.2) (hlen ▸ b.2) hab
  have hfs : ∀ x : Fin n, pivots[x.1]'(hlen ▸ x.2) ∈ Finset.range n := by
    intro x
    rw [Finset.mem_range]
    exact hlt _ (List.getElem_mem _)
  have huniq := Finset.orderEmbOfFin_unique (s := Finset.range n) (k := n) (Finset.card_range n)
    hfs hmono
  have hval := congrFun huniq ⟨i, hlen ▸ hi⟩
  simp only at hval
  rw [hval]
  simp [Finset.orderEmbOfFin_apply, Finset.sort_range]

/-- A square, full-rank matrix's RREF is exactly the identity: with `pivots.length = n`
pivot columns among `n` total columns, `pivots_eq_id_of_length_eq` forces `pivots[i] = i`
for every `i`, so `IsRREF.pivot_unit` at every column `col` reads `true` exactly at row
`col` and `false` everywhere else. -/
theorem echelonized_eq_one_of_full_rank (A : PackedMatrix n n)
    (hfullrank : PackedMatrix.rank A = n) :
    (EchelonForm.new A).matrix.decode = 1 := by
  have hrref := EchelonForm.new_isRREF A
  have hlen : (EchelonForm.new A).pivots.length = n := hfullrank
  funext row col
  have hcollt : col.1 < (EchelonForm.new A).pivots.length := by rw [hlen]; exact col.2
  have hpe : (EchelonForm.new A).pivots[col.1]'hcollt = col.1 :=
    pivots_eq_id_of_length_eq _ n hrref.sorted hrref.lt_n hlen col.1 hcollt
  have hpu := hrref.pivot_unit col.1 hcollt row
  rw [hpe] at hpu
  rw [Matrix.one_apply, PackedMatrix.decode_get]
  by_cases hcase : row.val = col.val
  · rw [ite_eq_left (Fin.ext hcase), hpu.mpr hcase, Bool.toF2_true]
  · rw [ite_eq_right (fun h => hcase (congrArg Fin.val h))]
    have hfalse : (EchelonForm.new A).matrix.get row col.1 = false := by
      by_contra hne
      rw [Bool.not_eq_false] at hne
      exact hcase (hpu.mp hne)
    rw [hfalse, Bool.toF2_false]

/-- Mirrors `AlignedBitMatrix::inverted`: the accumulated row-operation transform from
`EchelonForm.new A`, taking the full-rank hypothesis mirroring Rust's `assert_eq!` as an
explicit proof argument instead of modelling the panic. The returned matrix does not
itself depend on the proof, exactly as Rust's `inverted` computes
`EchelonForm::new(self).transform` unconditionally and only *checks* full rank
separately. -/
def _root_.BinarFormal.Packed.PackedMatrix.inverted (A : PackedMatrix n n)
    (_hfullrank : PackedMatrix.rank A = n) : PackedMatrix n n :=
  (EchelonForm.new A).transform

/-- `PackedMatrix.inverted` is a left inverse: `inverse * A = 1`, matching
`EchelonForm.new_transform_mul_eq` specialized to a full-rank (hence identity-reduced)
matrix. -/
theorem inverted_mul_left (A : PackedMatrix n n) (hfullrank : PackedMatrix.rank A = n) :
    (A.inverted hfullrank).decode * A.decode = 1 := by
  show (EchelonForm.new A).transform.decode * A.decode = 1
  rw [EchelonForm.new_transform_mul_eq]
  exact echelonized_eq_one_of_full_rank A hfullrank

/-- `PackedMatrix.inverted` is a right inverse: `A * inverse = 1`, the exact content of
Rust's `debug_assert_eq!(self * &echelon_form.transform,
AlignedBitMatrix::identity(self.row_count()))` inside `inverted`. -/
theorem inverted_mul_right (A : PackedMatrix n n) (hfullrank : PackedMatrix.rank A = n) :
    A.decode * (A.inverted hfullrank).decode = 1 :=
  mul_eq_one_comm.mp (inverted_mul_left A hfullrank)

end BinarFormal.Solve
