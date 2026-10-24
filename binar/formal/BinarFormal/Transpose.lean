import BinarFormal.Packed
import Batteries.Data.BitVec.Lemmas
import Mathlib.Tactic.Ring

/-!
# Packed transpose

An executable Lean model of `binar`'s bit-matrix transpose, refined against
`BinarFormal.Packed.PackedMatrix`. This mirrors, in order of composition:

* `binar/src/matrix/transpose_kernel.rs`:
  * `delta_swap`/`transpose_8x64` → `deltaSwap`/`transpose8x64`, the 8×8-per-lane kernel
    used by M4RI-style byte transposition.
  * `swap_blocks_64`/`transpose_64x64_inplace` → `swapBlocks`/`transpose64x64`, the
    six-stage (`BLOCK_SIZE` = 1, 2, 4, 8, 16, 32) in-place 64×64 word-matrix transpose.
* `binar/src/matrix/aligned_bitmatrix.rs`'s `transposed()` (and its `read_64x64_tile`,
  `read_64x64_tile_partial`, `write_64x64_tile`, `write_64x64_tile_partial` helpers) →
  `readTile` and `PackedMatrix.transpose`, tiling `transpose64x64` over a packed matrix
  of any shape.

## Semantic trust boundary

* **Simultaneous-read functional model of in-place swaps.** `swap_blocks_64`'s inner loop
  mutates a shared `&mut [u64; 64]` array, but for each `row_offset` it reads both
  `row_id_from` and `row_id_to` into locals *before* writing either back, and different
  `row_offset`/`block_top_row` iterations touch disjoint row pairs. `swapBlockRow`,
  `swapBlocks`, and `packByte` instead model this as a pure function of the *original*
  tile (`Tile64 := Nat → BitVec 64`): every output row/lane is computed directly from the
  input rows, never from a partially-updated intermediate state. This is extensionally
  identical to the imperative loop precisely because the updates it performs are
  index-disjoint, and it is the only respect in which this file departs from a literal
  transcription of the Rust control flow.
* **One tiling formula instead of four tiling branches.** `AlignedBitMatrix::transposed`
  dispatches on whether the row/column count is an exact multiple of 64, giving four
  separate branches (full/full, full/remainder, remainder/full, and the remainder/remainder
  corner) built from `read_64x64_tile` vs. `read_64x64_tile_partial` and `write_64x64_tile`
  vs. `write_64x64_tile_partial`. `readTile` folds the two read variants into one total
  function (a row past the source matrix's row count reads as the all-zero word), and
  `PackedMatrix.transpose` computes every destination bit directly from `readTile` and
  `transpose64x64`, so `PackedMatrix.decode_transpose` covers all four shapes (including
  `m = 0` or `n = 0`) via a single generic proof rather than one lemma per branch. The
  destination-side bound check that distinguishes the write helpers is still present,
  as the `dif`/zero-padding case split inside `readTile`, `transposeRowStorage`, and
  `PackedMatrix.transpose_get`.
* **Out of scope**, matching `BinarFormal.Packed`'s own boundary: raw pointer arithmetic,
  `row_words`/`row_words_mut` slice construction, `BitBlock`/word-array allocation and
  alignment. Only the logical bit contents of a tile and their packed encoding are
  modeled.
-/

namespace BinarFormal.Transpose

open BinarFormal.Packed

/-! ## 64-row tiles

A tile is modeled as a total function from row index to a 64-bit word, matching the
`[u64; 64]` arrays `swap_blocks_64`/`transpose_64x64_inplace` mutate in place. -/

/-- A 64-row tile of 64-bit words, mirroring the `[u64; 64]` arrays operated on by
`swap_blocks_64` and `transpose_64x64_inplace`. -/
abbrev Tile64 := Nat → BitVec 64

/-! ## `swap_blocks_64`: one transpose stage

`swap_blocks_64<BLOCK_SIZE, BLOCK_MASK>` pairs up row `row_id_from` with
`row_id_to = row_id_from + BLOCK_SIZE` for every `BLOCK_SIZE`-sized block, and swaps the
masked bits between the shifted halves via the 3-XOR trick. -/

/-- The new value of a `swap_blocks_64` row pair `(row_id_from, row_id_to)`, mirroring
the loop body's `diff`/XOR-swap computation. Reads both original rows before either output
is formed, matching the trust-boundary note above. -/
def swapBlockRow (blockSize : Nat) (mask : BitVec 64) (rows : Tile64) (rowFrom : Nat) :
    BitVec 64 × BitVec 64 :=
  let rowTo := rowFrom + blockSize
  let diff := ((rows rowFrom >>> blockSize) ^^^ rows rowTo) &&& mask
  (rows rowFrom ^^^ (diff <<< blockSize), rows rowTo ^^^ diff)

/-- One `swap_blocks_64<blockSize, mask>` stage: row `r` reads from the `swapBlockRow` pair
rooted at whichever of `r`, `r - blockSize` is the pair's `rowFrom`. -/
def swapBlocks (blockSize : Nat) (mask : BitVec 64) (rows : Tile64) : Tile64 :=
  fun r =>
    if r % (2 * blockSize) < blockSize then
      (swapBlockRow blockSize mask rows r).1
    else
      (swapBlockRow blockSize mask rows (r - blockSize)).2

/-- The `(row, col)` coordinate that stage `blockSize` reads from to produce its output at
`(row, col)`: unchanged if `row` and `col` fall in the same `blockSize`-sized half of their
`2 * blockSize` period, otherwise swapped into the other half. -/
def stageStep (blockSize : Nat) (p : Nat × Nat) : Nat × Nat :=
  let (r, c) := p
  if (r % (2 * blockSize) < blockSize) = (c % (2 * blockSize) < blockSize) then (r, c)
  else if r % (2 * blockSize) < blockSize then (r + blockSize, c - blockSize)
  else (r - blockSize, c + blockSize)

theorem mod_shift_up (r B : Nat) (h : r % (2 * B) < B) :
    (r + B) % (2 * B) = r % (2 * B) + B := by
  have key : r + B = (2 * B) * (r / (2 * B)) + (r % (2 * B) + B) := by
    have := Nat.div_add_mod r (2 * B)
    omega
  rw [key, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem mod_shift_down (r B : Nat) (hpos : 0 < B) (h : B ≤ r % (2 * B)) :
    (r - B) % (2 * B) = r % (2 * B) - B := by
  have hlt : r % (2 * B) < 2 * B := Nat.mod_lt r (by omega)
  have key : r - B = (2 * B) * (r / (2 * B)) + (r % (2 * B) - B) := by
    have := Nat.div_add_mod r (2 * B)
    omega
  rw [key, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem mod_shift_down_wrap (c B : Nat) (hB : 0 < B) (hcB : B ≤ c) (h : c % (2 * B) < B) :
    (c - B) % (2 * B) = c % (2 * B) + B := by
  have hge2B : 2 * B ≤ c := by
    by_contra hlt
    have hlt' : c < 2 * B := by omega
    have := Nat.mod_eq_of_lt hlt'
    omega
  have hqpos : 0 < c / (2 * B) := Nat.div_pos hge2B (by omega)
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_lt hqpos
  have hq' : c / (2 * B) = q + 1 := by omega
  have hd := Nat.div_add_mod c (2 * B)
  rw [hq'] at hd
  have hexpand : 2 * B * (q + 1) = 2 * B * q + 2 * B := by ring
  rw [hexpand] at hd
  have key : c - B = (2 * B) * q + (c % (2 * B) + B) := by omega
  rw [key, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- Coordinate correctness of a single `swap_blocks_64` stage: reading bit `c` of the
stage's output row `r` gives exactly the input bit at the `stageStep`-transformed
coordinate. Generic over `blockSize`, so this one proof serves all six stages of
`transpose64x64`. -/
theorem swapBlocks_getLsbD (blockSize : Nat) (hB : 0 < blockSize) (mask : BitVec 64)
    (hmask : ∀ x, x < 64 → mask.getLsbD x = decide (x % (2 * blockSize) < blockSize))
    (rows : Tile64) (r c : Nat) (hc : c < 64) :
    (swapBlocks blockSize mask rows r).getLsbD c =
      (rows (stageStep blockSize (r, c)).1).getLsbD (stageStep blockSize (r, c)).2 := by
  by_cases hcase1 : r % (2 * blockSize) < blockSize
  · by_cases hcase2 : c % (2 * blockSize) < blockSize
    · have hstep : stageStep blockSize (r, c) = (r, c) := by simp [stageStep, hcase1, hcase2]
      rw [hstep]
      simp only [swapBlocks, hcase1, ite_true, swapBlockRow]
      by_cases hcb : c < blockSize
      · simp [hc, hcb]
      · have hcb' : blockSize ≤ c := by omega
        have hwrap : (c - blockSize) % (2 * blockSize) = c % (2 * blockSize) + blockSize :=
          mod_shift_down_wrap c blockSize hB hcb' hcase2
        have hmval : mask.getLsbD (c - blockSize) = false := by
          rw [hmask (c - blockSize) (by omega), hwrap]
          simp
        simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
          BitVec.getLsbD_ushiftRight, hc, decide_true, Bool.true_and, hcb, decide_false,
          Bool.not_false, hmval, Bool.and_false, Bool.xor_false]
    · have hstep : stageStep blockSize (r, c) = (r + blockSize, c - blockSize) := by
        simp [stageStep, hcase1, hcase2]
      rw [hstep]
      simp only [swapBlocks, hcase1, ite_true, swapBlockRow]
      have hcge : blockSize ≤ c % (2 * blockSize) := Nat.le_of_not_lt hcase2
      have hcb2 : ¬ c < blockSize := by
        intro hlt
        have heq2 : c % (2 * blockSize) = c := Nat.mod_eq_of_lt (by omega)
        omega
      have hval : (c - blockSize) % (2 * blockSize) = c % (2 * blockSize) - blockSize :=
        mod_shift_down c blockSize hB hcge
      have hlt2B : c % (2 * blockSize) < 2 * blockSize := Nat.mod_lt c (by omega)
      have hmval : mask.getLsbD (c - blockSize) = true := by
        rw [hmask (c - blockSize) (by omega), hval]
        simp; omega
      have heq : blockSize + (c - blockSize) = c := by omega
      simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_ushiftRight, hc, decide_true, Bool.true_and, hcb2, decide_false,
        Bool.not_false, hmval, Bool.and_true, heq]
      generalize (rows r).getLsbD c = a
      generalize (rows (r + blockSize)).getLsbD (c - blockSize) = b
      cases a <;> cases b <;> rfl
  · by_cases hcase2 : c % (2 * blockSize) < blockSize
    · have hstep : stageStep blockSize (r, c) = (r - blockSize, c + blockSize) := by
        simp [stageStep, hcase1, hcase2]
      rw [hstep, Nat.add_comm c blockSize]
      simp only [swapBlocks, hcase1, ite_false, swapBlockRow]
      have hrge : blockSize ≤ r := by
        have := Nat.mod_le r (2 * blockSize)
        omega
      have hrb : r - blockSize + blockSize = r := by omega
      rw [hrb]
      have hmval : mask.getLsbD c = true := by
        rw [hmask c hc]
        simp [hcase2]
      simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
        hmval, Bool.and_true]
      generalize (rows r).getLsbD c = a
      generalize (rows (r - blockSize)).getLsbD (blockSize + c) = b
      cases a <;> cases b <;> rfl
    · have hstep : stageStep blockSize (r, c) = (r, c) := by
        simp [stageStep, hcase1, hcase2]
      rw [hstep]
      simp only [swapBlocks, hcase1, ite_false, swapBlockRow]
      have hrge : blockSize ≤ r := by
        have := Nat.mod_le r (2 * blockSize)
        omega
      have hrb : r - blockSize + blockSize = r := by omega
      rw [hrb]
      have hmval : mask.getLsbD c = false := by
        rw [hmask c hc]
        simp [hcase2]
      simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, hmval, Bool.and_false, Bool.xor_false]

/-! ## `transpose_64x64_inplace`: the full six-stage kernel

The six `BLOCK_MASKS` and `BLOCK_SIZE`s (`1 << 0` through `1 << 5`) from
`transpose_64x64_inplace`, applied in the same order as the six sequential
`swap_blocks_64` calls. -/

/-- The six `BLOCK_MASKS` literals from `transpose_64x64_inplace`, indexed in the same
order as the six `swap_blocks_64` calls. -/
def transposeMasks : Fin 6 → BitVec 64
  | 0 => 0x5555555555555555#64
  | 1 => 0x3333333333333333#64
  | 2 => 0x0F0F0F0F0F0F0F0F#64
  | 3 => 0x00FF00FF00FF00FF#64
  | 4 => 0x0000FFFF0000FFFF#64
  | 5 => 0x00000000FFFFFFFF#64

/-- The six `BLOCK_SIZE`s (`1 << 0` through `1 << 5`) from `transpose_64x64_inplace`. -/
def transposeBlockSizes : Fin 6 → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32

theorem transposeMasks_getLsbD :
    ∀ (k : Fin 6) (x : Fin 64),
      (transposeMasks k).getLsbD x.val =
        decide (x.val % (2 * transposeBlockSizes k) < transposeBlockSizes k) := by
  decide

/-- The full `transpose_64x64_inplace` kernel: six `swapBlocks` stages composed in the same
order as the six sequential `swap_blocks_64` calls on the shared array. -/
def transpose64x64 (rows : Tile64) : Tile64 :=
  swapBlocks 32 (transposeMasks 5)
    (swapBlocks 16 (transposeMasks 4)
      (swapBlocks 8 (transposeMasks 3)
        (swapBlocks 4 (transposeMasks 2)
          (swapBlocks 2 (transposeMasks 1)
            (swapBlocks 1 (transposeMasks 0) rows)))))

theorem transposeIndex_eq : ∀ i j : Fin 64,
    stageStep 1 (stageStep 2 (stageStep 4 (stageStep 8 (stageStep 16
      (stageStep 32 (i.val, j.val)))))) = (j.val, i.val) := by
  decide

theorem stageStep32_lt : ∀ r c : Fin 64,
    (stageStep 32 (r.val, c.val)).1 < 64 ∧ (stageStep 32 (r.val, c.val)).2 < 64 := by decide

theorem stageStep16_lt : ∀ r c : Fin 64,
    (stageStep 16 (r.val, c.val)).1 < 64 ∧ (stageStep 16 (r.val, c.val)).2 < 64 := by decide

theorem stageStep8_lt : ∀ r c : Fin 64,
    (stageStep 8 (r.val, c.val)).1 < 64 ∧ (stageStep 8 (r.val, c.val)).2 < 64 := by decide

theorem stageStep4_lt : ∀ r c : Fin 64,
    (stageStep 4 (r.val, c.val)).1 < 64 ∧ (stageStep 4 (r.val, c.val)).2 < 64 := by decide

theorem stageStep2_lt : ∀ r c : Fin 64,
    (stageStep 2 (r.val, c.val)).1 < 64 ∧ (stageStep 2 (r.val, c.val)).2 < 64 := by decide

/-- Coordinate correctness of the full 64×64 in-place kernel: output row `j` bit `i` equals
input row `i` bit `j`, i.e. `transpose64x64` really is a transpose. -/
theorem transpose64x64_getLsbD (rows : Tile64) (i j : Fin 64) :
    (transpose64x64 rows i.val).getLsbD j.val = (rows j.val).getLsbD i.val := by
  unfold transpose64x64
  rw [swapBlocks_getLsbD 32 (by norm_num) (transposeMasks 5)
        (fun x hx => transposeMasks_getLsbD 5 ⟨x, hx⟩) _ i.val j.val j.isLt]
  obtain ⟨h1_5, h2_5⟩ := stageStep32_lt i j
  generalize hg5 : stageStep 32 (i.val, j.val) = p5 at h1_5 h2_5 ⊢
  obtain ⟨r5, c5⟩ := p5
  rw [swapBlocks_getLsbD 16 (by norm_num) (transposeMasks 4)
        (fun x hx => transposeMasks_getLsbD 4 ⟨x, hx⟩) _ r5 c5 h2_5]
  obtain ⟨h1_4, h2_4⟩ := stageStep16_lt ⟨r5, h1_5⟩ ⟨c5, h2_5⟩
  generalize hg4 : stageStep 16 (r5, c5) = p4 at h1_4 h2_4 ⊢
  obtain ⟨r4, c4⟩ := p4
  rw [swapBlocks_getLsbD 8 (by norm_num) (transposeMasks 3)
        (fun x hx => transposeMasks_getLsbD 3 ⟨x, hx⟩) _ r4 c4 h2_4]
  obtain ⟨h1_3, h2_3⟩ := stageStep8_lt ⟨r4, h1_4⟩ ⟨c4, h2_4⟩
  generalize hg3 : stageStep 8 (r4, c4) = p3 at h1_3 h2_3 ⊢
  obtain ⟨r3, c3⟩ := p3
  rw [swapBlocks_getLsbD 4 (by norm_num) (transposeMasks 2)
        (fun x hx => transposeMasks_getLsbD 2 ⟨x, hx⟩) _ r3 c3 h2_3]
  obtain ⟨h1_2, h2_2⟩ := stageStep4_lt ⟨r3, h1_3⟩ ⟨c3, h2_3⟩
  generalize hg2 : stageStep 4 (r3, c3) = p2 at h1_2 h2_2 ⊢
  obtain ⟨r2, c2⟩ := p2
  rw [swapBlocks_getLsbD 2 (by norm_num) (transposeMasks 1)
        (fun x hx => transposeMasks_getLsbD 1 ⟨x, hx⟩) _ r2 c2 h2_2]
  obtain ⟨h1_1, h2_1⟩ := stageStep2_lt ⟨r2, h1_2⟩ ⟨c2, h2_2⟩
  generalize hg1 : stageStep 2 (r2, c2) = p1 at h1_1 h2_1 ⊢
  obtain ⟨r1, c1⟩ := p1
  rw [swapBlocks_getLsbD 1 (by norm_num) (transposeMasks 0)
        (fun x hx => transposeMasks_getLsbD 0 ⟨x, hx⟩) _ r1 c1 h2_1]
  have hfinal := transposeIndex_eq i j
  rw [hg5, hg4, hg3, hg2, hg1] at hfinal
  rw [hfinal]

/-! ## `delta_swap`/`transpose_8x64`: the M4RI-facing 8×8 kernel

`delta_swap x mask delta` swaps, within `x`, every masked bit at position `p` with the bit
at `p + delta`. `transpose_8x64` packs one byte from each of 8 input words into a single
`u64` lane and runs three delta swaps (`delta` = 7, 14, 28) to transpose the resulting 8×8
bit matrix, producing 64 transposed 8-bit column patterns as used by M4RI. -/

/-- Mirrors `delta_swap`: XOR-swap, within `x`, every masked bit at position `p` with the
bit at `p + delta`. -/
def deltaSwap (mask : BitVec 64) (delta : Nat) (x : BitVec 64) : BitVec 64 :=
  let t := ((x >>> delta) ^^^ x) &&& mask
  x ^^^ t ^^^ (t <<< delta)

/-- The bit position `deltaSwap (mask := 0x00AA00AA00AA00AA) 7` reads from to produce its
output at position `p`. -/
def deltaStep7 (p : Nat) : Nat :=
  if p % 2 = 1 ∧ p / 8 % 2 = 0 then 7 + p
  else if p % 2 = 0 ∧ p / 8 % 2 = 1 then p - 7
  else p

/-- The bit position `deltaSwap (mask := 0x0000CCCC0000CCCC) 14` reads from to produce its
output at position `p`. -/
def deltaStep14 (p : Nat) : Nat :=
  if p / 2 % 2 = 1 ∧ p / 16 % 2 = 0 then 14 + p
  else if p / 2 % 2 = 0 ∧ p / 16 % 2 = 1 then p - 14
  else p

/-- The bit position `deltaSwap (mask := 0x00000000F0F0F0F0) 28` reads from to produce its
output at position `p`. -/
def deltaStep28 (p : Nat) : Nat :=
  if p / 4 % 2 = 1 ∧ p / 32 % 2 = 0 then 28 + p
  else if p / 4 % 2 = 0 ∧ p / 32 % 2 = 1 then p - 28
  else p

theorem deltaSwap7_getLsbD (mask : BitVec 64)
    (hmask : ∀ x, x < 64 → mask.getLsbD x = decide (x % 2 = 1 ∧ x / 8 % 2 = 0))
    (x : BitVec 64) (p : Nat) (hp : p < 64) :
    (deltaSwap mask 7 x).getLsbD p = x.getLsbD (deltaStep7 p) := by
  simp only [deltaSwap, deltaStep7]
  have hmp : mask.getLsbD p = decide (p % 2 = 1 ∧ p / 8 % 2 = 0) := hmask p hp
  have hmpd : mask.getLsbD (p - 7) = decide ((p - 7) % 2 = 1 ∧ (p - 7) / 8 % 2 = 0) :=
    hmask (p - 7) (by omega)
  split_ifs with h1 h2
  · have hmpT : mask.getLsbD p = true := by rw [hmp]; simp [h1]
    have hmpdF : mask.getLsbD (p - 7) = false := by
      rw [hmpd]; simp; omega
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hp, decide_true, Bool.true_and, hmpT, Bool.and_true,
      hmpdF, Bool.and_false, Bool.xor_false]
    generalize x.getLsbD p = a
    generalize x.getLsbD (7 + p) = b
    cases a <;> cases b <;> rfl
  · have hnot1 : ¬ p < 7 := by omega
    have hmpF : mask.getLsbD p = false := by rw [hmp]; simp; omega
    have hmpdT : mask.getLsbD (p - 7) = true := by
      rw [hmpd]; simp; omega
    have heq : 7 + (p - 7) = p := by omega
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hp, decide_true, Bool.true_and, hmpF, Bool.and_false,
      Bool.xor_false, hnot1, decide_false, Bool.not_false, hmpdT, Bool.and_true, heq]
    generalize x.getLsbD p = a
    generalize x.getLsbD (p - 7) = b
    cases a <;> cases b <;> rfl
  · have hmpF : mask.getLsbD p = false := by rw [hmp]; simp; omega
    have hmpdF : mask.getLsbD (p - 7) = false := by rw [hmpd]; simp; omega
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hp, decide_true, Bool.true_and, hmpF, Bool.and_false,
      Bool.xor_false, hmpdF]

theorem deltaSwap14_getLsbD (mask : BitVec 64)
    (hmask : ∀ x, x < 64 → mask.getLsbD x = decide (x / 2 % 2 = 1 ∧ x / 16 % 2 = 0))
    (x : BitVec 64) (p : Nat) (hp : p < 64) :
    (deltaSwap mask 14 x).getLsbD p = x.getLsbD (deltaStep14 p) := by
  simp only [deltaSwap, deltaStep14]
  have hmp : mask.getLsbD p = decide (p / 2 % 2 = 1 ∧ p / 16 % 2 = 0) := hmask p hp
  have hmpd : mask.getLsbD (p - 14) = decide ((p - 14) / 2 % 2 = 1 ∧ (p - 14) / 16 % 2 = 0) :=
    hmask (p - 14) (by omega)
  split_ifs with h1 h2
  · have hmpT : mask.getLsbD p = true := by rw [hmp]; simp [h1]
    have hmpdF : mask.getLsbD (p - 14) = false := by
      rw [hmpd]; simp; omega
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hp, decide_true, Bool.true_and, hmpT, Bool.and_true,
      hmpdF, Bool.and_false, Bool.xor_false]
    generalize x.getLsbD p = a
    generalize x.getLsbD (14 + p) = b
    cases a <;> cases b <;> rfl
  · have hnot1 : ¬ p < 14 := by omega
    have hmpF : mask.getLsbD p = false := by rw [hmp]; simp; omega
    have hmpdT : mask.getLsbD (p - 14) = true := by
      rw [hmpd]; simp; omega
    have heq : 14 + (p - 14) = p := by omega
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hp, decide_true, Bool.true_and, hmpF, Bool.and_false,
      Bool.xor_false, hnot1, decide_false, Bool.not_false, hmpdT, Bool.and_true, heq]
    generalize x.getLsbD p = a
    generalize x.getLsbD (p - 14) = b
    cases a <;> cases b <;> rfl
  · have hmpF : mask.getLsbD p = false := by rw [hmp]; simp; omega
    have hmpdF : mask.getLsbD (p - 14) = false := by rw [hmpd]; simp; omega
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hp, decide_true, Bool.true_and, hmpF, Bool.and_false,
      Bool.xor_false, hmpdF]

theorem deltaSwap28_getLsbD (mask : BitVec 64)
    (hmask : ∀ x, x < 64 → mask.getLsbD x = decide (x / 4 % 2 = 1 ∧ x / 32 % 2 = 0))
    (x : BitVec 64) (p : Nat) (hp : p < 64) :
    (deltaSwap mask 28 x).getLsbD p = x.getLsbD (deltaStep28 p) := by
  simp only [deltaSwap, deltaStep28]
  have hmp : mask.getLsbD p = decide (p / 4 % 2 = 1 ∧ p / 32 % 2 = 0) := hmask p hp
  have hmpd : mask.getLsbD (p - 28) = decide ((p - 28) / 4 % 2 = 1 ∧ (p - 28) / 32 % 2 = 0) :=
    hmask (p - 28) (by omega)
  split_ifs with h1 h2
  · have hmpT : mask.getLsbD p = true := by rw [hmp]; simp [h1]
    have hmpdF : mask.getLsbD (p - 28) = false := by
      rw [hmpd]; simp; omega
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hp, decide_true, Bool.true_and, hmpT, Bool.and_true,
      hmpdF, Bool.and_false, Bool.xor_false]
    generalize x.getLsbD p = a
    generalize x.getLsbD (28 + p) = b
    cases a <;> cases b <;> rfl
  · have hnot1 : ¬ p < 28 := by omega
    have hmpF : mask.getLsbD p = false := by rw [hmp]; simp; omega
    have hmpdT : mask.getLsbD (p - 28) = true := by
      rw [hmpd]; simp; omega
    have heq : 28 + (p - 28) = p := by omega
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hp, decide_true, Bool.true_and, hmpF, Bool.and_false,
      Bool.xor_false, hnot1, decide_false, Bool.not_false, hmpdT, Bool.and_true, heq]
    generalize x.getLsbD p = a
    generalize x.getLsbD (p - 28) = b
    cases a <;> cases b <;> rfl
  · have hmpF : mask.getLsbD p = false := by rw [hmp]; simp; omega
    have hmpdF : mask.getLsbD (p - 28) = false := by rw [hmpd]; simp; omega
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, hp, decide_true, Bool.true_and, hmpF, Bool.and_false,
      Bool.xor_false, hmpdF]

theorem deltaTransposeIndex_eq :
    ∀ p : Fin 64, deltaStep7 (deltaStep14 (deltaStep28 p.val)) = 8 * (p.val % 8) + p.val / 8 := by
  decide

/-- The three delta swaps (`delta` = 7, 14, 28) from `transpose_8x64`'s loop body, composed
in the same order, transposing an 8×8 bit matrix packed one row per byte lane. -/
def transpose8x8Word (x : BitVec 64) : BitVec 64 :=
  deltaSwap 0x00000000F0F0F0F0#64 28
    (deltaSwap 0x0000CCCC0000CCCC#64 14
      (deltaSwap 0x00AA00AA00AA00AA#64 7 x))

theorem transpose8x8Word_getLsbD (x : BitVec 64) (p : Nat) (hp : p < 64) :
    (transpose8x8Word x).getLsbD p = x.getLsbD (8 * (p % 8) + p / 8) := by
  have hm7 : ∀ y, y < 64 → (0x00AA00AA00AA00AA#64).getLsbD y =
      decide (y % 2 = 1 ∧ y / 8 % 2 = 0) := by decide
  have hm14 : ∀ y, y < 64 → (0x0000CCCC0000CCCC#64).getLsbD y =
      decide (y / 2 % 2 = 1 ∧ y / 16 % 2 = 0) := by decide
  have hm28 : ∀ y, y < 64 → (0x00000000F0F0F0F0#64).getLsbD y =
      decide (y / 4 % 2 = 1 ∧ y / 32 % 2 = 0) := by decide
  show (deltaSwap 0x00000000F0F0F0F0#64 28
    (deltaSwap 0x0000CCCC0000CCCC#64 14
      (deltaSwap 0x00AA00AA00AA00AA#64 7 x))).getLsbD p = x.getLsbD (8 * (p % 8) + p / 8)
  rw [deltaSwap28_getLsbD _ hm28 _ p hp]
  have b1 : deltaStep28 p < 64 := by unfold deltaStep28; split_ifs <;> omega
  generalize hgen1 : deltaStep28 p = p1 at b1 ⊢
  rw [deltaSwap14_getLsbD _ hm14 _ p1 b1]
  have b2 : deltaStep14 p1 < 64 := by unfold deltaStep14; split_ifs <;> omega
  generalize hgen2 : deltaStep14 p1 = p2 at b2 ⊢
  rw [deltaSwap7_getLsbD _ hm7 _ p2 b2]
  have hfinal : deltaStep7 p2 = 8 * (p % 8) + p / 8 := by
    rw [← hgen2, ← hgen1]
    exact deltaTransposeIndex_eq ⟨p, hp⟩
  rw [hfinal]

/-- Packs byte `byteIdx` from each of the 8 words `w 0, ..., w 7` into one `u64`, mirroring
`transpose_8x64`'s `x |= ((word >> (byte_idx * 8)) & 0xFF) << (word_idx * 8)` loop. Built as
a direct concatenation (rather than an explicit `Nat`-indexed fold) since the 8 byte
extractions land in disjoint 8-bit lanes, so the two forms are extensionally identical. -/
def packByte (w : Tile64) (byteIdx : Nat) : BitVec 64 :=
  (w 7).extractLsb' (byteIdx * 8) 8 ++
    ((w 6).extractLsb' (byteIdx * 8) 8 ++
      ((w 5).extractLsb' (byteIdx * 8) 8 ++
        ((w 4).extractLsb' (byteIdx * 8) 8 ++
          ((w 3).extractLsb' (byteIdx * 8) 8 ++
            ((w 2).extractLsb' (byteIdx * 8) 8 ++
              ((w 1).extractLsb' (byteIdx * 8) 8 ++ (w 0).extractLsb' (byteIdx * 8) 8))))))

theorem packByte_getLsbD (w : Tile64) (byteIdx wordIdx k : Nat) (hw : wordIdx < 8) (hk : k < 8) :
    (packByte w byteIdx).getLsbD (8 * wordIdx + k) = (w wordIdx).getLsbD (byteIdx * 8 + k) := by
  simp only [packByte, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · have hv : wordIdx = 0 := by omega
    subst hv
    have hcond : 8 * 0 + k < 8 := by omega
    simp only [hcond, decide_true, Bool.true_and]; congr 1; omega
  · have hv : wordIdx = 1 := by omega
    subst hv
    have hcond : 8 * 1 + k - 8 < 8 := by omega
    simp only [hcond, decide_true, Bool.true_and]; congr 1; omega
  · have hv : wordIdx = 2 := by omega
    subst hv
    have hcond : 8 * 2 + k - 16 < 8 := by omega
    simp only [hcond, decide_true, Bool.true_and]; congr 1; omega
  · have hv : wordIdx = 3 := by omega
    subst hv
    have hcond : 8 * 3 + k - 24 < 8 := by omega
    simp only [hcond, decide_true, Bool.true_and]; congr 1; omega
  · have hv : wordIdx = 4 := by omega
    subst hv
    have hcond : 8 * 4 + k - 32 < 8 := by omega
    simp only [hcond, decide_true, Bool.true_and]; congr 1; omega
  · have hv : wordIdx = 5 := by omega
    subst hv
    have hcond : 8 * 5 + k - 40 < 8 := by omega
    simp only [hcond, decide_true, Bool.true_and]; congr 1; omega
  · have hv : wordIdx = 6 := by omega
    subst hv
    have hcond : 8 * 6 + k - 48 < 8 := by omega
    simp only [hcond, decide_true, Bool.true_and]; congr 1; omega
  · have hv : wordIdx = 7 := by omega
    subst hv
    have hcond : 8 * 7 + k - 56 < 8 := by omega
    simp only [hcond, decide_true, Bool.true_and]; congr 1; omega

/-- Mirrors `transpose_8x64`: for each `byteIdx`, packs byte `byteIdx` of all 8 input words
and transposes the resulting 8×8 bit matrix via `transpose8x8Word`. -/
def transpose8x64 (w : Tile64) (byteIdx : Nat) : BitVec 64 :=
  transpose8x8Word (packByte w byteIdx)

/-- The M4RI-facing correctness theorem: for row `row` and column `j` within an 8×8 block,
output word `byteIdx`'s byte `row` equals column `8 * byteIdx + j`'s original bit `row` at
lane position `j`; equivalently, `transpose8x64 w byteIdx` really does hold the transposed
8-bit patterns of columns `8 * byteIdx` through `8 * byteIdx + 7` of `w`, matching the
docstring of `transpose_8x64`. -/
theorem transpose8x64_getLsbD (w : Tile64) (byteIdx row j : Nat) (hrow : row < 8) (hj : j < 8) :
    (transpose8x64 w byteIdx).getLsbD (8 * j + row) = (w row).getLsbD (8 * byteIdx + j) := by
  have hp : 8 * j + row < 64 := by omega
  simp only [transpose8x64]
  rw [transpose8x8Word_getLsbD _ _ hp]
  have hmod : (8 * j + row) % 8 = row := by omega
  have hdiv : (8 * j + row) / 8 = j := by omega
  rw [hmod, hdiv]
  rw [packByte_getLsbD w byteIdx row j hrow hj]
  congr 1
  omega

/-! ## Bridging tiles to `PackedMatrix`

`readTile` extracts a `Tile64` from a `PackedMatrix`, reading through the packed `get` API.
Row `blockRow * 64 + offset` past the matrix's row count reads as the zero word, playing
the role of `read_64x64_tile_partial`'s explicit zero-initialization; a column past the
matrix's column count is handled "for free" by `PackedVec.get`'s own zero padding, so a
single `readTile` covers what Rust splits into `read_64x64_tile`/`read_64x64_tile_partial`. -/

/-- Reads the 64×64 tile of `M` whose rows are `blockRow * 64 .. blockRow * 64 + 63` and
whose columns are `blockCol * 64 .. blockCol * 64 + 63`, mirroring `read_64x64_tile` (and,
via its zero default for out-of-range rows, `read_64x64_tile_partial`). -/
def readTile (M : PackedMatrix m n) (blockRow blockCol : Nat) : Tile64 :=
  fun offset =>
    if h : blockRow * 64 + offset < m then
      BitVec.ofFnLE (fun b : Fin 64 => M.get ⟨blockRow * 64 + offset, h⟩ (blockCol * 64 + b.val))
    else
      0#64

theorem readTile_getLsbD (M : PackedMatrix m n) (blockRow blockCol offset b : Nat)
    (hb : b < 64) :
    (readTile M blockRow blockCol offset).getLsbD b =
      if h : blockRow * 64 + offset < m then
        M.get ⟨blockRow * 64 + offset, h⟩ (blockCol * 64 + b)
      else false := by
  unfold readTile
  split
  · rw [BitVec.getLsbD_ofFnLE]
    simp [hb]
  · simp

/-- The packed storage for row `R` of the transposed matrix: bit `C` is read directly from
the tile covering source row block `R / 64` and source column block `C / 64`, avoiding a
separate write-then-read tiling pass. -/
def transposeRowStorage (M : PackedMatrix m n) (R : Nat) : BitVec (capacity m) :=
  BitVec.ofFnLE (fun c : Fin (capacity m) =>
    (transpose64x64 (readTile M (c.val / 64) (R / 64)) (R % 64)).getLsbD (c.val % 64))

theorem transposeRowStorage_getLsbD (M : PackedMatrix m n) (R C : Nat) (hC : C < capacity m) :
    (transposeRowStorage M R).getLsbD C =
      (transpose64x64 (readTile M (C / 64) (R / 64)) (R % 64)).getLsbD (C % 64) := by
  unfold transposeRowStorage
  rw [BitVec.getLsbD_ofFnLE]
  simp [hC]

theorem transposeRowStorage_zero_padding (M : PackedMatrix m n) (R : Nat) :
    ∀ j, m ≤ j → (transposeRowStorage M R).getLsbD j = false := by
  intro j hj
  rcases Nat.lt_or_ge j (capacity m) with hjc | hjc
  · rw [transposeRowStorage_getLsbD M R j hjc,
      transpose64x64_getLsbD (readTile M (j / 64) (R / 64)) ⟨R % 64, by omega⟩ ⟨j % 64, by omega⟩,
      readTile_getLsbD M (j / 64) (R / 64) (j % 64) (R % 64) (by omega)]
    have hdm : j / 64 * 64 + j % 64 = j := by omega
    rw [dite_eq_right (by omega)]
  · exact BitVec.getLsbD_of_ge _ j hjc

end BinarFormal.Transpose

namespace BinarFormal.Packed.PackedMatrix

open BinarFormal.Transpose

/-- Transposes a packed GF(2) matrix, mirroring `AlignedBitMatrix::transposed`'s tiled
64×64-kernel algorithm: every destination bit is read directly from the source tile
covering it, via `readTile` and `transpose64x64`. -/
def transpose (M : PackedMatrix m n) : PackedMatrix n m where
  rows := fun R => {
    storage := transposeRowStorage M R.val
    zero_padding := transposeRowStorage_zero_padding M R.val
  }

/-- Coordinate correctness of `transpose`, at the packed `get` level: entry `(R, C)` of the
transposed matrix is entry `(C, R)` of the original. -/
theorem transpose_get (M : PackedMatrix m n) (R : Fin n) (C : Nat) (hC : C < m) :
    (transpose M).get R C = M.get ⟨C, hC⟩ R.val := by
  show (transposeRowStorage M R.val).getLsbD C = M.get ⟨C, hC⟩ R.val
  rw [transposeRowStorage_getLsbD M R.val C (hC.trans_le (le_capacity m)),
    transpose64x64_getLsbD (readTile M (C / 64) (R.val / 64)) ⟨R.val % 64, by omega⟩
      ⟨C % 64, by omega⟩,
    readTile_getLsbD M (C / 64) (R.val / 64) (C % 64) (R.val % 64) (by omega)]
  have hdm : C / 64 * 64 + C % 64 = C := by omega
  rw [dite_eq_left (by omega)]
  congr 2
  omega

/-- `transpose` refines `Matrix.transpose`: decoding the packed transpose gives exactly the
logical transpose of the decoded matrix, for any shape `m n` (including `m = 0`, `n = 0`,
exact multiples of 64, and partial tiles). -/
theorem decode_transpose (M : PackedMatrix m n) :
    (transpose M).decode = Matrix.transpose M.decode := by
  funext R C
  rw [Matrix.transpose_apply, PackedMatrix.decode_get, PackedMatrix.decode_get,
    transpose_get M R C.val C.isLt]

end BinarFormal.Packed.PackedMatrix
