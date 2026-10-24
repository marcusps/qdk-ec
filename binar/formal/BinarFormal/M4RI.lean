import BinarFormal.Transpose
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Bitwise

/-!
# M4RI matrix multiplication

An executable Lean model of `binar`'s M4RI (Method of Four Russians) packed GF(2) matrix
multiplication, refined against `BinarFormal.Packed.PackedMatrix`. This mirrors, in order
of composition, `binar/src/matrix/m4ri.rs`:

* `INNER_STRIPE_BITS`/`SUPER_STRIPE_COUNT`/`SUPER_STRIPE_BITS` → the identically-named
  `BinarFormal.M4RI.INNER_STRIPE_BITS`/`SUPER_STRIPE_COUNT`/`SUPER_STRIPE_BITS`.
* `RowStripeTable::populate`'s Gray-code-ordered table fill → `tableStep`/`grayTable`,
  built from a small self-contained theory of the reflected binary Gray code
  (`grayCode`, `invGray`, `changedBit`), with lookup correctness `decode_grayTable`.
* `StripeColumnExtractor`'s per-row pattern extraction → `extractPattern`, reusing
  `BinarFormal.Transpose.transpose8x64_getLsbD` (via `readTile`) rather than re-deriving
  transpose correctness, with extraction correctness `extractPattern_testBit`.
* The shared "loop over `div_ceil`-many chunks of a bounded size, XORing in each chunk's
  contribution" control flow of both `RowStripeTable::populate`'s inner-stripe loop and
  `mul`'s outer super-stripe loop (via `multiply_stripes`) → the single shared recursive
  helper `stripeFold`, instantiated once per level.
* `mul`'s inner per-row, per-inner-stripe accumulation (`multiply_stripes`) → `innerStripe`,
  with correctness `decode_innerStripe`.
* `mul` itself, including its `inner_dimension == 0 || num_result_cols == 0` early return →
  `PackedMatrix.m4riMul`, with the top-level refinement theorem
  `PackedMatrix.decode_m4riMul`.

## Semantic trust boundary

* **The Gray-code table fill is modeled exactly, not specified away.** `tableStep`
  reproduces `RowStripeTable::populate`'s loop verbatim in control/data flow: entry
  `grayCode (pattern + 1)` is written from entry `grayCode pattern` XORed with exactly one
  selected row, chosen by `changedBit pattern`, for every `pattern` in turn. No step of
  this construction is replaced by a specification; `decode_grayTable` is proved about this
  exact executable recursion.
* **`changedBit` uses `Nat.log2` where Rust uses `trailing_zeros`.** These agree precisely
  because consecutive Gray codes differ in exactly one bit
  (`grayCode_succ_diff_eq_two_pow_changedBit`), i.e. their XOR is always exactly a power of
  two, for which `log2` and `trailing_zeros` coincide; `log2` is used only because it has
  more directly applicable Mathlib lemmas, not to change what is computed.
* **One shared `stripeFold` instead of two near-duplicate `div_ceil` loops.** Rust's
  `RowStripeTable::populate` (chunks of `INNER_STRIPE_BITS`) and `mul` (chunks of
  `SUPER_STRIPE_BITS`) are both "repeatedly take a `min(chunkSize, remaining)`-sized chunk
  and fold in its contribution" loops over the same `k`-bit range; `stripeFold` is one
  structurally recursive function capturing this shape once, instantiated at both chunk
  sizes, with one correctness lemma `decode_stripeFold` used at both call sites.
* **`extractPattern` recomputes `transpose8x64` per output row instead of caching it per
  64-column block.** `StripeColumnExtractor` caches `transpose_8x64`'s result across 64
  consecutive `current_column`s (`cached_patterns`/`load_block`) purely for performance;
  since `transpose8x64` is a pure function of its input tile, recomputing it for each
  `outputRow` (as `extractPattern` does) is extensionally identical to caching it, and
  `extractPattern_testBit` is proved directly from `Transpose.transpose8x64_getLsbD`
  without duplicating its proof.
* **Out of scope**, matching `BinarFormal.Packed`/`BinarFormal.Transpose`'s own boundary:
  raw pointer arithmetic, cache-blocking/amortization performance characteristics, and
  `BitBlock`/word-array allocation. Only the logical bit contents of tables, patterns, and
  the product matrix are modeled.
-/

namespace BinarFormal.M4RI

open BinarFormal.Packed BinarFormal.Transpose BinarFormal.Packed.PackedMatrix

/-! ## Reflected binary Gray code

A small self-contained theory of the reflected binary Gray code, factored out as the
general mathematical fact `RowStripeTable::populate` relies on: consecutive Gray codes
differ in exactly one bit, and every `Nat` below `2 ^ bits` is `grayCode`'s image of some
`p < 2 ^ bits`. -/

/-- The reflected binary Gray code of `p`, mirroring `RowStripeTable::populate`'s
`pattern ^ (pattern >> 1)`. -/
def grayCode (p : Nat) : Nat := p ^^^ (p >>> 1)

/-- The inverse of `grayCode`, used only to exhibit each table pattern `x` as `grayCode`
of some step index (`grayCode_invGray`), never executed by the model of `mul` itself. -/
def invGray (g : Nat) : Nat :=
  if g = 0 then 0 else g ^^^ invGray (g >>> 1)
termination_by g
decreasing_by omega

theorem grayCode_invGray (g : Nat) : grayCode (invGray g) = g := by
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    rcases Nat.eq_zero_or_pos g with hg0 | hgpos
    · subst hg0; simp [invGray, grayCode]
    · have hlt : g >>> 1 < g := by omega
      have hIH := ih (g >>> 1) hlt
      unfold invGray
      rw [ite_eq_right (by omega)]
      show grayCode (g ^^^ invGray (g >>> 1)) = g
      unfold grayCode
      rw [Nat.shiftRight_xor_distrib]
      have : g ^^^ invGray (g >>> 1) ^^^ (g >>> 1 ^^^ (invGray (g >>> 1) >>> 1))
           = g ^^^ (g >>> 1) ^^^ (invGray (g >>> 1) ^^^ invGray (g >>> 1) >>> 1) := by
        ac_rfl
      rw [this]
      show g ^^^ (g >>> 1) ^^^ grayCode (invGray (g >>> 1)) = g
      rw [hIH, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem grayCode_lt_two_pow {p bits : Nat} (h : p < 2 ^ bits) : grayCode p < 2 ^ bits := by
  have h1 : p >>> 1 < 2 ^ bits := by
    have : p >>> 1 ≤ p := Nat.shiftRight_le p 1
    omega
  exact Nat.xor_lt_two_pow h h1

theorem invGray_lt_two_pow {bits : Nat} : ∀ {g : Nat}, g < 2 ^ bits → invGray g < 2 ^ bits := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hg
    rcases Nat.eq_zero_or_pos g with hg0 | hgpos
    · subst hg0
      unfold invGray
      rw [ite_eq_left rfl]
      exact Nat.two_pow_pos bits
    · have hlt : g >>> 1 < g := by omega
      have hb : g >>> 1 < 2 ^ bits := by
        have : g >>> 1 ≤ g := Nat.shiftRight_le g 1
        omega
      have hIH := ih (g >>> 1) hlt hb
      unfold invGray
      rw [ite_eq_right (by omega)]
      exact Nat.xor_lt_two_pow hg hIH

theorem grayCode_succ_xor (p : Nat) :
    grayCode p ^^^ grayCode (p + 1) = grayCode (p ^^^ (p + 1)) := by
  unfold grayCode
  rw [Nat.shiftRight_xor_distrib]
  ac_rfl

theorem two_mul_xor_two_mul (a b : Nat) : 2 * a ^^^ 2 * b = 2 * (a ^^^ b) := by
  have h1 : 2 * a = a <<< 1 := by rw [Nat.shiftLeft_eq]; ring
  have h2 : 2 * b = b <<< 1 := by rw [Nat.shiftLeft_eq]; ring
  have h3 : 2 * (a ^^^ b) = (a ^^^ b) <<< 1 := by rw [Nat.shiftLeft_eq]; ring
  rw [h1, h2, h3, Nat.shiftLeft_xor_distrib]

theorem odd_succ_xor (m : Nat) :
    (2 * m + 1) ^^^ (2 * m + 2) = 2 * (m ^^^ (m + 1)) ^^^ 1 := by
  have e1 : (2 * m + 1) = 2 * m ^^^ 1 := (Nat.xor_one_of_even (even_two_mul m)).symm
  have e2 : (2 * m + 2) = 2 * (m + 1) := by ring
  rw [e1, e2, show (2 * m ^^^ 1) ^^^ (2 * (m + 1)) = (2 * m ^^^ 2 * (m + 1)) ^^^ 1 from by ac_rfl,
    two_mul_xor_two_mul]

theorem double_two_pow_sub_one_xor_one (j : Nat) :
    2 * (2 ^ j - 1) ^^^ 1 = 2 ^ (j + 1) - 1 := by
  have hpow : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [Nat.xor_one_of_even (by exact even_two_mul _)]
  rw [pow_succ]
  omega

/-- Every `p ^^^ (p + 1)` is `2 ^ j - 1` for some `j > 0`: consecutive naturals' binary
representations agree above their lowest differing bit and are all-ones below it. -/
theorem xor_succ_self_eq_two_pow_sub_one :
    ∀ p : Nat, ∃ j, 0 < j ∧ p ^^^ (p + 1) = 2 ^ j - 1 := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    rcases Nat.even_or_odd p with hev | hodd
    · refine ⟨1, by norm_num, ?_⟩
      rw [← Nat.xor_one_of_even hev, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      decide
    · obtain ⟨m, hm⟩ := hodd
      have hm_lt : m < p := by omega
      obtain ⟨j, hjpos, hjeq⟩ := ih m hm_lt
      refine ⟨j + 1, by omega, ?_⟩
      have hp2 : p + 1 = 2 * m + 2 := by omega
      rw [hp2, hm, odd_succ_xor, hjeq]
      exact double_two_pow_sub_one_xor_one j

theorem grayCode_two_pow_sub_one (j : Nat) (hj : 0 < j) :
    grayCode (2 ^ j - 1) = 2 ^ (j - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold grayCode
  simp only [Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow]
  rw [Bool.eq_iff_iff]
  simp only [Bool.xor_iff_ne, ne_eq, decide_eq_decide, decide_eq_true_eq]
  omega

/-- Consecutive Gray codes differ in exactly one bit: `grayCode p ^^^ grayCode (p + 1)` is
always exactly a power of two. -/
theorem grayCode_succ_exists_pow2 (p : Nat) : ∃ i, grayCode p ^^^ grayCode (p + 1) = 2 ^ i := by
  obtain ⟨j, hjpos, hjeq⟩ := xor_succ_self_eq_two_pow_sub_one p
  exact ⟨j - 1, by rw [grayCode_succ_xor, hjeq, grayCode_two_pow_sub_one j hjpos]⟩

/-- The single bit index that changes between `grayCode p` and `grayCode (p + 1)`,
mirroring `RowStripeTable::populate`'s `changed_bit = (previous_gray ^ current_gray)
.trailing_zeros()` (see the module trust boundary for the `log2`/`trailing_zeros` note). -/
def changedBit (p : Nat) : Nat := Nat.log2 (grayCode p ^^^ grayCode (p + 1))

theorem grayCode_succ_diff_eq_two_pow_changedBit (p : Nat) :
    grayCode p ^^^ grayCode (p + 1) = 2 ^ changedBit p := by
  obtain ⟨i, hi⟩ := grayCode_succ_exists_pow2 p
  unfold changedBit
  rw [hi, Nat.log2_two_pow]

theorem testBit_grayCode_succ (p i : Nat) :
    (grayCode (p + 1)).testBit i
      = ((grayCode p).testBit i).xor (decide (i = changedBit p)) := by
  have hkey := congrArg (fun x => Nat.testBit x i) (grayCode_succ_diff_eq_two_pow_changedBit p)
  simp only [Nat.testBit_xor, Nat.testBit_two_pow] at hkey
  have hcomm : decide (changedBit p = i) = decide (i = changedBit p) := by simp [eq_comm]
  rw [hcomm] at hkey
  cases h1 : (grayCode p).testBit i <;> cases h2 : (grayCode (p+1)).testBit i <;>
    simp_all

theorem changedBit_lt {bits p : Nat} (hp : p + 1 < 2 ^ bits) : changedBit p < bits := by
  have h1 : grayCode p < 2 ^ bits := grayCode_lt_two_pow (by omega)
  have h2 : grayCode (p + 1) < 2 ^ bits := grayCode_lt_two_pow hp
  have h3 : (2:Nat) ^ changedBit p < 2 ^ bits := by
    rw [← grayCode_succ_diff_eq_two_pow_changedBit p]
    exact Nat.xor_lt_two_pow h1 h2
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3

variable {n : Nat}

/-! ## `RowStripeTable::populate`: the Gray-code lookup table

`RowStripeTable::populate` walks `pattern` from `1` to `2 ^ inner_bits - 1` in order,
writing table entry `grayCode pattern` as table entry `grayCode (pattern - 1)` XORed with
whichever row `changedBit (pattern - 1)` selects. `tableStep rows pattern` is exactly this
table after the steps for `1, ..., pattern` have run (`tableStep rows 0` is the initial
all-zero table), and `grayTable` is the finished table after all `2 ^ bits - 1` steps. -/

/-- The Gray-code table after `pattern` fill steps, mirroring `RowStripeTable::populate`'s
loop state: `tableStep rows 0` is the initial all-zero table (`AlignedBitMatrix::zeros`,
with row/pattern `0` reinforced by the loop's own explicit zero-fill), and each successor
step writes exactly one new entry, `grayCode (pattern + 1)`, from the previous entry
`grayCode pattern` XORed with row `changedBit pattern` of `rows`. -/
def tableStep (rows : Nat → PackedVec n) : Nat → Nat → PackedVec n
  | 0 => Function.update (Function.const Nat (PackedVec.zero n)) 0 (PackedVec.zero n)
  | pattern + 1 =>
      let prev := tableStep rows pattern
      Function.update prev (grayCode (pattern + 1))
        ((prev (grayCode pattern)).xor (rows (changedBit pattern)))

/-- The GF(2) row sum selected by the low `bits` bits of `x`, i.e. the specification a
correctly-filled Gray-code table entry for pattern `x` must match. -/
def xorOfSelected (rows : Nat → PackedVec n) (bits x : Nat) : Fin n → F2 :=
  fun j => ∑ i ∈ Finset.range bits, Bool.toF2 (x.testBit i) * (rows i).decode j

/-- Immediately after step `pattern` writes entry `grayCode pattern`, that entry is the row
sum selected by `grayCode pattern`'s own bits. -/
theorem tableStep_grayCode (rows : Nat → PackedVec n) (bits pattern : Nat)
    (hp : pattern < 2 ^ bits) :
    (tableStep rows pattern (grayCode pattern)).decode
      = xorOfSelected rows bits (grayCode pattern) := by
  induction pattern with
  | zero =>
    show (Function.update (Function.const Nat (PackedVec.zero n)) 0 (PackedVec.zero n)
      (grayCode 0)).decode = xorOfSelected rows bits (grayCode 0)
    have : grayCode 0 = 0 := rfl
    rw [this, Function.update_self, PackedVec.decode_zero]
    funext j
    unfold xorOfSelected
    simp
  | succ p ih =>
    have hp' : p < 2 ^ bits := by omega
    have step : tableStep rows (p+1) (grayCode (p+1))
        = (tableStep rows p (grayCode p)).xor (rows (changedBit p)) := by
      show Function.update (tableStep rows p) (grayCode (p+1))
        ((tableStep rows p (grayCode p)).xor (rows (changedBit p))) (grayCode (p+1)) = _
      rw [Function.update_self]
    rw [step, PackedVec.decode_xor, ih hp']
    funext j
    show xorOfSelected rows bits (grayCode p) j + (rows (changedBit p)).decode j
      = xorOfSelected rows bits (grayCode (p+1)) j
    unfold xorOfSelected
    have hcb : changedBit p < bits := changedBit_lt (by omega)
    have hexpand : ∀ i, Bool.toF2 ((grayCode (p+1)).testBit i)
        = Bool.toF2 ((grayCode p).testBit i) + Bool.toF2 (decide (i = changedBit p)) := by
      intro i
      rw [testBit_grayCode_succ, Bool.toF2_xor]
    simp_rw [hexpand]
    rw [show (∀ f g : Nat → F2, ∑ i ∈ Finset.range bits, (f i + g i) * (rows i).decode j
        = (∑ i ∈ Finset.range bits, f i * (rows i).decode j)
          + ∑ i ∈ Finset.range bits, g i * (rows i).decode j) from ?_]
    · congr 1
      have : ∀ i, Bool.toF2 (decide (i = changedBit p)) * (rows i).decode j
          = if i = changedBit p then (rows i).decode j else 0 := by
        intro i; by_cases h : i = changedBit p <;> simp [h]
      simp_rw [this]
      rw [Finset.sum_ite_eq' (Finset.range bits) (changedBit p) (fun i => (rows i).decode j)]
      simp [hcb]
    · intro f g
      rw [← Finset.sum_add_distrib]
      congr 1
      funext i
      ring

/-- Once step `pattern` has correctly written entry `grayCode pattern`, later steps never
overwrite it again (Gray codes only repeat by wrapping fully around `2 ^ bits`), so its
decoded value is stable for the rest of the fill. -/
theorem tableStep_decode_stable (rows : Nat → PackedVec n) (bits pattern : Nat) :
    ∀ d, pattern + d < 2 ^ bits →
      (tableStep rows (pattern + d) (grayCode pattern)).decode
        = (tableStep rows pattern (grayCode pattern)).decode := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
      intro hd
      simp only [← Nat.add_assoc] at hd ⊢
      have hIH := ih (by omega)
      by_cases heq : grayCode pattern = grayCode (pattern + d + 1)
      · have h1 := tableStep_grayCode rows bits (pattern + d + 1) hd
        have h2 := tableStep_grayCode rows bits pattern (by omega)
        have hshow : tableStep rows (pattern + d + 1) (grayCode pattern)
            = tableStep rows (pattern + d + 1) (grayCode (pattern + d + 1)) := by rw [heq]
        rw [hshow, h1, ← heq, h2]
      · have hshow : tableStep rows (pattern + d + 1) (grayCode pattern)
            = tableStep rows (pattern + d) (grayCode pattern) := by
          show Function.update (tableStep rows (pattern + d)) (grayCode (pattern + d + 1)) _
            (grayCode pattern) = _
          rw [Function.update_of_ne heq]
        rw [hshow, hIH]

/-- The finished Gray-code table for `bits`-bit patterns, mirroring one `sub_table` after
`RowStripeTable::populate` has run its full `1 .. 2 ^ bits` loop. -/
def grayTable (rows : Nat → PackedVec n) (bits : Nat) : Nat → PackedVec n :=
  tableStep rows (2 ^ bits - 1)

/-- Every entry of the finished table is the row sum selected by its own pattern: the
Gray-code table lookup invariant. -/
theorem decode_grayTable (rows : Nat → PackedVec n) (bits x : Nat) (hx : x < 2 ^ bits) :
    (grayTable rows bits x).decode = xorOfSelected rows bits x := by
  have hgx : grayCode (invGray x) = x := grayCode_invGray x
  have hib : invGray x < 2 ^ bits := invGray_lt_two_pow hx
  have hstable := tableStep_decode_stable rows bits (invGray x) (2 ^ bits - 1 - invGray x)
    (by omega)
  have hcorrect := tableStep_grayCode rows bits (invGray x) hib
  rw [show invGray x + (2 ^ bits - 1 - invGray x) = 2 ^ bits - 1 from by omega, hgx] at hstable
  rw [hgx] at hcorrect
  show (tableStep rows (2^bits - 1) x).decode = xorOfSelected rows bits x
  rw [hstable, hcorrect]

/-! ## A shared stripe-chunking loop

Both `RowStripeTable::populate`'s inner-stripe loop (chunks of `INNER_STRIPE_BITS`) and
`mul`'s outer super-stripe loop (chunks of `SUPER_STRIPE_BITS`, via `multiply_stripes`)
repeatedly XOR in the contribution of a `min(chunkSize, remaining)`-sized chunk until the
full `k`-bit range is exhausted; `stripeFold` is that shape, defined once and instantiated
at each chunk size (`innerStripe`, `PackedMatrix.m4riMul`). -/

/-- Folds `chunkLookup colStart' chunkLen'` XOR-accumulated over successive
`chunkSize`-or-smaller chunks covering `[colStart, colStart + totalBits)`, mirroring the
"repeatedly XOR in the next chunk's contribution" shape shared by `RowStripeTable::populate`
and `mul`/`multiply_stripes`, generic over the chunk size. -/
def stripeFold (chunkSize : Nat) (hchunk : 0 < chunkSize) (chunkLookup : Nat → Nat → PackedVec n) :
    Nat → Nat → PackedVec n
  | _, 0 => PackedVec.zero n
  | colStart, totalBits + 1 =>
      let thisChunk := min chunkSize (totalBits + 1)
      (chunkLookup colStart thisChunk).xor
        (stripeFold chunkSize hchunk chunkLookup (colStart + thisChunk) (totalBits + 1 - thisChunk))
  termination_by _ totalBits => totalBits
  decreasing_by
    all_goals (simp only [Nat.succ_eq_add_one]; omega)

/-- The GF(2) partial dot product of `rows`/`bitAt` over the index window
`[colStart, colStart + totalBits)`, the specification target for `stripeFold` at both the
inner- and outer-stripe level. -/
def xorOfChunks (rows : Nat → PackedVec n) (bitAt : Nat → Bool) (colStart totalBits : Nat) :
    Fin n → F2 :=
  fun j => ∑ i ∈ Finset.range totalBits, Bool.toF2 (bitAt (colStart + i)) * (rows (colStart + i)).decode j

theorem xorOfChunks_add (rows : Nat → PackedVec n) (bitAt : Nat → Bool) (colStart a b : Nat) :
    xorOfChunks rows bitAt colStart (a + b)
      = fun j => xorOfChunks rows bitAt colStart a j + xorOfChunks rows bitAt (colStart + a) b j := by
  funext j
  unfold xorOfChunks
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show colStart + (a + i) = colStart + a + i from by ring]

/-- `stripeFold`'s general correctness lemma: if every chunk lookup of length at most
`chunkSize` matches the partial dot product over its window, then so does the fold over
any window, of any total length. Used once with `chunkSize = INNER_STRIPE_BITS` (discharged
by `decode_grayTable`/`extractPattern_testBit`, via `decode_innerStripe`) and once with
`chunkSize = SUPER_STRIPE_BITS` (discharged by `decode_innerStripe`, via
`PackedMatrix.decode_m4riMul`). -/
theorem decode_stripeFold (chunkSize : Nat) (hchunk : 0 < chunkSize)
    (chunkLookup : Nat → Nat → PackedVec n) (rows : Nat → PackedVec n) (bitAt : Nat → Bool)
    (hchunk_correct : ∀ colStart chunkLen, chunkLen ≤ chunkSize →
      (chunkLookup colStart chunkLen).decode = xorOfChunks rows bitAt colStart chunkLen) :
    ∀ colStart totalBits,
      (stripeFold chunkSize hchunk chunkLookup colStart totalBits).decode
        = xorOfChunks rows bitAt colStart totalBits := by
  intro colStart totalBits
  induction totalBits using Nat.strong_induction_on generalizing colStart with
  | _ totalBits ih =>
    match totalBits with
    | 0 =>
      simp only [stripeFold]
      rw [PackedVec.decode_zero]
      funext j
      unfold xorOfChunks
      simp
    | totalBits' + 1 =>
      simp only [stripeFold]
      rw [PackedVec.decode_xor]
      set thisChunk := min chunkSize (totalBits' + 1) with hthisChunk
      have hpos : 0 < thisChunk := by simp [hthisChunk]; omega
      have hle : thisChunk ≤ chunkSize := by simp [hthisChunk]
      have hlt : totalBits' + 1 - thisChunk < totalBits' + 1 := by omega
      have h1 := hchunk_correct colStart thisChunk hle
      have h2 := ih (totalBits' + 1 - thisChunk) hlt (colStart + thisChunk)
      rw [h1, h2]
      have hsplit : thisChunk + (totalBits' + 1 - thisChunk) = totalBits' + 1 := by omega
      have heq := xorOfChunks_add rows bitAt colStart thisChunk (totalBits' + 1 - thisChunk)
      rw [hsplit] at heq
      funext j
      rw [congrFun heq j]
      rfl

variable {m k : Nat}

/-! ## `StripeColumnExtractor`: per-row pattern extraction

`StripeColumnExtractor` yields, for each output row in turn, one `inner_bits`-wide pattern
per inner stripe, extracted from the *transposed* left matrix via `transpose_8x64`.
`extractPattern` computes the same pattern for one fixed output row directly (see the
module trust boundary for the caching-vs-recompute note), reusing
`Transpose.transpose8x64_getLsbD` rather than re-deriving transpose correctness. -/

/-- The `innerBits`-wide pattern for output row `outputRow`, over columns
`[colStart, colStart + innerBits)` of `left`, mirroring `StripeColumnExtractor`'s
`current_patterns` (`col_in_block`/`word_index`/`shift` become `byteIdx`/`j` here) applied
to a fresh `transpose_8x64` of the relevant rows of `left.transpose` (in place of
`StripeColumnExtractor`'s cached `load_block`). -/
def extractPattern (left : PackedMatrix m k) (colStart innerBits outputRow : Nat) : Nat :=
  let blockIdx := outputRow / 64
  let byteIdx := outputRow % 64 / 8
  let j := outputRow % 64 % 8
  let w : Tile64 := fun row =>
    if row < innerBits then
      readTile left.transpose ((colStart + row) / 64) blockIdx ((colStart + row) % 64)
    else 0#64
  ((transpose8x64 w byteIdx).extractLsb' (8 * j) 8).toNat

/-- Extraction correctness: bit `row` of the extracted pattern is exactly `left`'s entry
`(outputRow, colStart + row)` when `row < innerBits`, and `false` otherwise. Holds
unconditionally (no bound on `colStart + innerBits` vs. `k` is needed), since
`PackedVec.zero_padding` already makes both the in-range and out-of-range cases agree. -/
theorem extractPattern_testBit (left : PackedMatrix m k) (colStart innerBits outputRow row : Nat)
    (hrow : row < 8) (houtRow : outputRow < m) :
    (extractPattern left colStart innerBits outputRow).testBit row
      = (decide (row < innerBits) && left.get ⟨outputRow, houtRow⟩ (colStart + row)) := by
  unfold extractPattern
  simp only
  rw [BitVec.testBit_toNat, BitVec.getLsbD_extractLsb']
  rw [decide_eq_true hrow, Bool.true_and]
  set byteIdx := outputRow % 64 / 8 with hbyteIdx
  set j := outputRow % 64 % 8 with hj
  have hj8 : j < 8 := by simp only [hj]; omega
  rw [transpose8x64_getLsbD _ byteIdx row j hrow hj8]
  have hbj : 8 * byteIdx + j = outputRow % 64 := by simp only [hbyteIdx, hj]; omega
  by_cases hri : row < innerBits
  · rw [ite_eq_left hri, hbj]
    have hb64 : outputRow % 64 < 64 := Nat.mod_lt _ (by norm_num)
    rw [readTile_getLsbD left.transpose ((colStart + row) / 64) (outputRow / 64)
      ((colStart + row) % 64) (outputRow % 64) hb64]
    have heq1 : (colStart + row) / 64 * 64 + (colStart + row) % 64 = colStart + row := by omega
    have heq2 : outputRow / 64 * 64 + outputRow % 64 = outputRow := by omega
    rw [heq1, heq2, decide_eq_true hri, Bool.true_and]
    by_cases hk : colStart + row < k
    · rw [dite_eq_left hk, transpose_get left ⟨colStart + row, hk⟩ outputRow houtRow]
    · rw [dite_eq_right hk]
      symm
      show (left.rows ⟨outputRow, houtRow⟩).get (colStart + row) = false
      exact (left.rows ⟨outputRow, houtRow⟩).zero_padding (colStart + row) (by omega)
  · rw [ite_eq_right hri, BitVec.getLsbD_zero, decide_eq_false hri, Bool.false_and]

theorem lt_two_pow_of_testBit_ge {x n : Nat} (h : ∀ i, n ≤ i → x.testBit i = false) :
    x < 2 ^ n := by
  have heq : x = x % 2 ^ n := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    rcases Nat.lt_or_ge i n with hi | hi
    · simp [hi]
    · simp [Nat.not_lt.mpr hi, h i hi]
  rw [heq]
  exact Nat.mod_lt x (Nat.two_pow_pos n)

/-- Every extracted pattern is a valid `innerBits`-wide index, as needed to invoke
`decode_grayTable` on it. -/
theorem extractPattern_lt (left : PackedMatrix m k) (colStart innerBits outputRow : Nat)
    (houtRow : outputRow < m) :
    extractPattern left colStart innerBits outputRow < 2 ^ innerBits := by
  apply lt_two_pow_of_testBit_ge
  intro i hi
  rcases Nat.lt_or_ge i 8 with hi8 | hi8
  · rw [extractPattern_testBit left colStart innerBits outputRow i hi8 houtRow]
    rw [decide_eq_false (by omega), Bool.false_and]
  · exact Nat.testBit_lt_two_pow (by
      calc extractPattern left colStart innerBits outputRow
          < 2 ^ 8 := by
            unfold extractPattern
            simp only
            exact BitVec.isLt _
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi8)

/-! ## `mul`: assembling stripes into the full product -/

/-- Mirrors `INNER_STRIPE_BITS` in `binar/src/matrix/m4ri.rs`: the width of each Gray-code
lookup table's pattern (bits consumed per `grayTable` lookup). -/
def INNER_STRIPE_BITS : Nat := 8

/-- Mirrors `SUPER_STRIPE_COUNT` in `binar/src/matrix/m4ri.rs`: the number of inner stripes
(and hence Gray-code tables) processed together per super-stripe. -/
def SUPER_STRIPE_COUNT : Nat := 4

/-- Mirrors `SUPER_STRIPE_BITS` in `binar/src/matrix/m4ri.rs`: the width of each outer
accumulation chunk, `INNER_STRIPE_BITS * SUPER_STRIPE_COUNT = 32`. -/
def SUPER_STRIPE_BITS : Nat := INNER_STRIPE_BITS * SUPER_STRIPE_COUNT

/-- `right`'s rows as a total function of a `Nat` index, zero past `right`'s row count,
mirroring how `matrix.row(i)` is only ever called by `RowStripeTable::populate` for `i` in
the current stripe (always in range) while letting `stripeFold`/`xorOfChunks` stay generic
`Nat`-indexed specifications. -/
def rowsTotal (right : PackedMatrix k n) : Nat → PackedVec n :=
  fun i => if h : i < k then right.rows ⟨i, h⟩ else PackedVec.zero n

/-- The contribution of columns `[colStart, colStart + totalBits)` of `right` to output row
`r` of the product, mirroring `mul`'s per-super-stripe body: `RowStripeTable::populate`
followed by `StripeColumnExtractor`/`multiply_stripes` restricted to row `r`. Each
`INNER_STRIPE_BITS`-or-smaller chunk's contribution is a single `grayTable` lookup, keyed by
`extractPattern left colStart' chunkLen' r.val`, XOR-accumulated by the shared
`stripeFold`. -/
def innerStripe (left : PackedMatrix m k) (right : PackedMatrix k n) (r : Fin m)
    (colStart totalBits : Nat) : PackedVec n :=
  stripeFold INNER_STRIPE_BITS (by decide)
    (fun colStart' chunkLen' =>
      grayTable (fun i => rowsTotal right (colStart' + i)) chunkLen'
        (extractPattern left colStart' chunkLen' r.val))
    colStart totalBits

/-- `innerStripe`'s contribution matches the partial dot product it stands for, for any
window and any total length (covering the `INNER_STRIPE_BITS`-exact and partial-final-chunk
cases alike). -/
theorem decode_innerStripe (left : PackedMatrix m k) (right : PackedMatrix k n) (r : Fin m)
    (colStart totalBits : Nat) :
    (innerStripe left right r colStart totalBits).decode
      = xorOfChunks (rowsTotal right) (fun i => left.get r i) colStart totalBits := by
  unfold innerStripe
  apply decode_stripeFold
  intro colStart' chunkLen' hchunkLen'
  have hconst : INNER_STRIPE_BITS = 8 := rfl
  have hlt : extractPattern left colStart' chunkLen' r.val < 2 ^ chunkLen' :=
    extractPattern_lt left colStart' chunkLen' r.val r.isLt
  rw [decode_grayTable _ chunkLen' _ hlt]
  funext j
  unfold xorOfSelected xorOfChunks
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have hi8 : i < 8 := by omega
  have := extractPattern_testBit left colStart' chunkLen' r.val i hi8 r.isLt
  rw [this, decide_eq_true hi, Bool.true_and]

end BinarFormal.M4RI

namespace BinarFormal.Packed.PackedMatrix

open BinarFormal.M4RI

/-- Computes `left * right` using M4RI (Method of Four Russians), mirroring `mul` in
`binar/src/matrix/m4ri.rs`: the `k = 0 ∨ n = 0` branch mirrors `mul`'s
`inner_dimension == 0 || num_result_cols == 0` early return, and otherwise each output row
is the shared `stripeFold`, at `SUPER_STRIPE_BITS`-sized chunks, of `innerStripe`'s
super-stripe contributions over the full `k`-bit inner dimension. -/
def m4riMul (left : PackedMatrix m k) (right : PackedMatrix k n) : PackedMatrix m n :=
  if _ : k = 0 ∨ n = 0 then PackedMatrix.zero m n
  else { rows := fun r => stripeFold SUPER_STRIPE_BITS (by decide) (innerStripe left right r) 0 k }

/-- `m4riMul` refines Mathlib's matrix multiplication: decoding the M4RI product gives
exactly the product of the decoded matrices, for any shapes `m`, `k`, `n` (including
`k = 0`, `n = 0`, and any mix of exact/partial `INNER_STRIPE_BITS`/`SUPER_STRIPE_BITS`
boundaries). -/
theorem decode_m4riMul (left : PackedMatrix m k) (right : PackedMatrix k n) :
    (m4riMul left right).decode = left.decode * right.decode := by
  unfold m4riMul
  split
  next hzero =>
    rw [PackedMatrix.decode_zero]
    rcases hzero with hk0 | hn0
    · subst hk0
      funext r j
      simp [Matrix.mul_apply]
    · subst hn0
      funext r j
      exact j.elim0
  next hnz =>
    rw [not_or] at hnz
    obtain ⟨hk0, hn0⟩ := hnz
    funext r j
    show (stripeFold SUPER_STRIPE_BITS (by decide) (innerStripe left right r) 0 k).decode j
      = (left.decode * right.decode) r j
    rw [decode_stripeFold SUPER_STRIPE_BITS (by decide) (innerStripe left right r) (rowsTotal right)
      (fun i => left.get r i) (fun colStart' chunkLen' _ => decode_innerStripe left right r colStart' chunkLen') 0 k]
    unfold xorOfChunks
    calc ∑ i ∈ Finset.range k, Bool.toF2 (left.get r (0 + i)) * (rowsTotal right (0 + i)).decode j
        = ∑ i ∈ Finset.range k, Bool.toF2 (left.get r i) * Bool.toF2 ((rowsTotal right i).get j.val) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [PackedVec.decode_get]
      _ = ∑ i : Fin k, Bool.toF2 (left.get r i.val) * Bool.toF2 ((rowsTotal right i.val).get j.val) :=
          (Fin.sum_univ_eq_sum_range
            (fun i => Bool.toF2 (left.get r i) * Bool.toF2 ((rowsTotal right i).get j.val)) k).symm
      _ = ∑ i : Fin k, left.decode r i * right.decode i j := by
          apply Finset.sum_congr rfl
          intro i _
          have : (rowsTotal right i.val).get j.val = right.get i j.val := by
            unfold rowsTotal
            rw [dite_eq_left i.isLt]
            rfl
          rw [this]
          rfl
      _ = (left.decode * right.decode) r j := Matrix.mul_apply.symm

end BinarFormal.Packed.PackedMatrix
