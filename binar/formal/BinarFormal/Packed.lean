import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.Data.Fintype.BigOperators
import Batteries.Data.BitVec.Lemmas

/-!
# Packed GF(2) storage

An executable Lean model of `binar`'s packed bit storage, refined against Mathlib's
`ZMod 2`-valued vectors and matrices. This covers:

* `binar/src/bit/bitblock.rs` (`Word`, `BIT_BLOCK_WORD_COUNT`, `BitBlock`): fixed-width
  512-bit storage blocks built from eight 64-bit words.
* `binar/src/bit/bitwise*.rs` (the `Bitwise`/`BitwiseMut`/`BitwisePair`/`BitwisePairMut`
  traits): read, write, XOR, and dot/parity operations on packed bits.
* `binar/src/vec/aligned_vec.rs` (`AlignedBitVec`): a packed bit vector whose capacity is
  its logical length rounded up to a whole number of `BitBlock`s, with the tail bits
  (the "padding") always zero.
* `binar/src/matrix/aligned_bitmatrix.rs` (`AlignedBitMatrix`): a row-major packed bit
  matrix, i.e. one independently block-padded `AlignedBitVec` per row.

Raw pointer arithmetic, allocation, alignment, and other unsafe Rust storage details are
outside this semantic model; only the logical bit contents and their packed encoding are
represented.
-/

/- `capacity` (below) rounds a logical length up to a whole block via `Nat.div`/`Nat.mod`.
Using that expression as a structure field's type index (e.g. `BitVec (capacity n)`)
requires the elaborator to unfold well-founded `Nat` division deeper than the default
limit while checking the structure's constructor; raising the recursion depth here is
the standard, purely elaboration-side workaround (it affects no proof term). -/
set_option maxRecDepth 4000

namespace BinarFormal.Packed

/-! ## `F2`: bits as ring elements

The finite field with two elements, used throughout as the semantic target for a single
bit. -/

/-- The finite field with two elements, i.e. the coefficient ring for GF(2) linear
algebra. -/
abbrev F2 := ZMod 2

namespace Bool

/-- Interpret a `Bool` as an element of `F2`, sending `false ↦ 0` and `true ↦ 1`. -/
def toF2 (b : Bool) : F2 := bif b then 1 else 0

@[simp] theorem toF2_false : toF2 false = 0 := rfl

@[simp] theorem toF2_true : toF2 true = 1 := rfl

/-- Boolean XOR maps to addition in `F2`, i.e. `toF2` is additive. -/
@[simp] theorem toF2_xor (a b : Bool) : toF2 (a ^^ b) = toF2 a + toF2 b := by
  cases a <;> cases b <;> decide

/-- Boolean AND maps to multiplication in `F2`, i.e. `toF2` is multiplicative. -/
@[simp] theorem toF2_and (a b : Bool) : toF2 (a && b) = toF2 a * toF2 b := by
  cases a <;> cases b <;> decide

/-- `toF2` distinguishes `false` from `true`, so decoded equalities determine the bit. -/
theorem toF2_injective : Function.Injective toF2 := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

end Bool

/-! ## Packed storage sizes

These mirror `binar`'s fixed-width storage layout exactly: a `Word` is a 64-bit machine
word (`binar/src/bit/bitblock.rs`), a `BitBlock` packs `BIT_BLOCK_WORD_COUNT = 8` words
into 512 bits, and the capacity of a packed vector of logical length `n` is `n` rounded up
to a whole number of blocks (`AlignedBitVec::block_count`,
`binar/src/vec/aligned_vec.rs`). -/

/-- Bits in a single Rust `Word` (`u64`). -/
def wordBits : Nat := 64

/-- Words packed into a single `BitBlock` (`BIT_BLOCK_WORD_COUNT`). -/
def wordsPerBlock : Nat := 8

/-- Bits packed into a single `BitBlock`. -/
def blockBits : Nat := wordsPerBlock * wordBits

/-- Number of whole `BitBlock`s needed to store `n` logical bits, i.e. `⌈n / blockBits⌉`,
mirroring `AlignedBitVec::block_count`. -/
def blockCount (n : Nat) : Nat := n / blockBits + (if n % blockBits = 0 then 0 else 1)

/-- Packed storage width for `n` logical bits: `n` rounded up to a whole number of
blocks, mirroring `AlignedBitVec::capacity`. -/
def capacity (n : Nat) : Nat := blockCount n * blockBits

/-- The empty vector needs no storage at all. -/
example : capacity 0 = 0 := by decide

/-- An exact multiple of the block size needs no padding. -/
example : capacity 512 = 512 := by decide

/-- A length one bit past a full block rounds up to a whole extra block. -/
example : capacity 513 = 1024 := by decide

/-- The packed capacity always covers the logical length; the difference is exactly the
zero-padded tail. -/
theorem le_capacity (n : Nat) : n ≤ capacity n := by
  unfold capacity blockCount blockBits wordsPerBlock wordBits
  have := Nat.div_add_mod n 512
  split <;> omega

/-! ## Bit-level helpers on `BitVec`

Small helpers on fixed-width `BitVec`s that are not already in Lean core/Mathlib but are
needed to state and prove the packed refinement contracts below. Kept in the
`BinarFormal.Packed` namespace (rather than extending the root `BitVec` namespace) so they
stay scoped to this model. -/

variable {w : Nat}

/-- Write a single bit of a fixed-width `BitVec`, leaving all other bits unchanged. -/
def setBit (x : BitVec w) (i : Nat) (b : Bool) : BitVec w :=
  bif b then x ||| BitVec.twoPow w i else x &&& ~~~(BitVec.twoPow w i)

/-- Reading back any bit of `setBit x i b` at an in-range index `i`: bit `j` is `b` at
`i = j` and unchanged otherwise. -/
theorem getLsbD_setBit {x : BitVec w} {i : Nat} (hi : i < w) (b : Bool) (j : Nat) :
    (setBit x i b).getLsbD j = if i = j then b else x.getLsbD j := by
  rcases Nat.lt_or_ge j w with hj | hj
  · unfold setBit
    cases b <;>
      simp only [Bool.cond_true, Bool.cond_false, BitVec.getLsbD_or, BitVec.getLsbD_and,
        BitVec.getLsbD_not, BitVec.getLsbD_twoPow, hi, hj] <;>
      split_ifs with hji <;> simp_all
  · have hxj : x.getLsbD j = false := BitVec.getLsbD_of_ge x j hj
    rw [BitVec.getLsbD_of_ge (setBit x i b) j hj]
    split_ifs with hji
    · exfalso; omega
    · exact hxj.symm

@[simp] theorem getLsbD_setBit_self {x : BitVec w} {i : Nat} (hi : i < w) (b : Bool) :
    (setBit x i b).getLsbD i = b := by
  rw [getLsbD_setBit hi b i, ite_eq_left rfl]

theorem getLsbD_setBit_ne {x : BitVec w} {i : Nat} (hi : i < w) {j : Nat} (h : i ≠ j)
    (b : Bool) : (setBit x i b).getLsbD j = x.getLsbD j := by
  rw [getLsbD_setBit hi b j, ite_eq_right h]

/-- XOR-fold of the low `k` bits of `x`, i.e. their parity. A direct structural recursion
on the bit count, used to connect packed dot/parity operations to `Finset` sums. -/
def bitParityAux (x : BitVec w) : Nat → Bool
  | 0 => false
  | k + 1 => bitParityAux x k ^^ x.getLsbD k

/-- The parity (XOR) of every bit of a fixed-width `BitVec`. -/
def bitParity (x : BitVec w) : Bool := bitParityAux x w

theorem toF2_bitParityAux (x : BitVec w) (k : Nat) :
    Bool.toF2 (bitParityAux x k) = ∑ i ∈ Finset.range k, Bool.toF2 (x.getLsbD i) := by
  induction k with
  | zero => simp [bitParityAux]
  | succ k ih => rw [bitParityAux, Bool.toF2_xor, ih, Finset.sum_range_succ]

/-- Bits at or beyond `n` do not affect the parity of the low `n + extra` bits, provided
they are all zero: this lets a padded packed representation compute the same parity as
its logical (unpadded) length. -/
theorem bitParityAux_eq_of_getLsbD_false {x : BitVec w} {n : Nat}
    (hpad : ∀ j, n ≤ j → x.getLsbD j = false) (extra : Nat) :
    bitParityAux x (n + extra) = bitParityAux x n := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    show (bitParityAux x (n + extra) ^^ x.getLsbD (n + extra)) = bitParityAux x n
    rw [ih, hpad (n + extra) (Nat.le_add_right n extra), Bool.xor_false]

/-! ## `PackedVec`: packed bit vectors

A packed GF(2) vector of logical length `n`, refining `binar`'s `AlignedBitVec`
(`binar/src/vec/aligned_vec.rs`). The underlying storage is a single fixed-width
`BitVec (capacity n)`; since the padding invariant is a field of the structure itself,
every operation below that returns a `PackedVec n` preserves it by construction. -/

/-- A packed GF(2) vector of logical length `n`, backed by a `capacity n`-bit `BitVec`
with an always-zero padded tail (`binar/src/vec/aligned_vec.rs`). -/
structure PackedVec (n : Nat) where
  /-- The packed fixed-width storage, `n` rounded up to a whole number of `BitBlock`s. -/
  storage : BitVec (capacity n)
  /-- Padding invariant: bits at or beyond the logical length are always zero. -/
  zero_padding : ∀ i, n ≤ i → storage.getLsbD i = false

namespace PackedVec

variable {n : Nat}

/-- The all-zero packed vector, mirroring `AlignedBitVec::zeros`. -/
def zero (n : Nat) : PackedVec n where
  storage := 0#(capacity n)
  zero_padding := by intro i _; simp

/-- Read bit `i`, mirroring `Bitwise::index`. Total: out-of-range indices read as
`false`, matching the zero-padded tail. -/
def get (v : PackedVec n) (i : Nat) : Bool := v.storage.getLsbD i

/-- Build a packed vector from a Boolean function, discarding out-of-range bits. -/
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

/-- Write bit `i` to `b`, for an in-range index, mirroring
`BitwiseMut::assign_index`. -/
def set (v : PackedVec n) (i : Nat) (h : i < n) (b : Bool) : PackedVec n where
  storage := setBit v.storage i b
  zero_padding := by
    intro j hj
    have hij : i ≠ j := by omega
    rw [getLsbD_setBit_ne (h.trans_le (le_capacity n)) hij]
    exact v.zero_padding j hj

/-- Bitwise XOR of two packed vectors of the same logical length, mirroring
`BitwisePairMut::bitxor_assign`. -/
def xor (u v : PackedVec n) : PackedVec n where
  storage := u.storage ^^^ v.storage
  zero_padding := by
    intro i hi
    rw [BitVec.getLsbD_xor, u.zero_padding i hi, v.zero_padding i hi]
    rfl

/-- Parity (XOR) of all logical bits, mirroring `Bitwise::parity`. -/
def parity (v : PackedVec n) : Bool := bitParity v.storage

/-- Dot product (parity of the bitwise AND) of two packed vectors, mirroring
`BitwisePair::dot`. -/
def dot (u v : PackedVec n) : Bool := bitParity (u.storage &&& v.storage)

/-- Decode a packed vector to its logical `F2`-valued content. -/
def decode (v : PackedVec n) : Fin n → F2 := fun i => Bool.toF2 (v.get i.val)

@[simp] theorem get_set_self (v : PackedVec n) (i : Nat) (h : i < n) (b : Bool) :
    (v.set i h b).get i = b :=
  getLsbD_setBit_self (h.trans_le (le_capacity n)) b

theorem get_set_ne (v : PackedVec n) (i : Nat) (h : i < n) (b : Bool) {j : Nat}
    (hij : i ≠ j) : (v.set i h b).get j = v.get j :=
  getLsbD_setBit_ne (h.trans_le (le_capacity n)) hij b

@[simp] theorem decode_get (v : PackedVec n) (i : Fin n) :
    v.decode i = Bool.toF2 (v.get i.val) := rfl

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

@[simp] theorem decode_zero (n : Nat) : (PackedVec.zero n).decode = 0 := by
  funext i
  show Bool.toF2 ((PackedVec.zero n).get i.val) = 0
  simp [get, zero]

/-- Setting an in-range index decodes to updating that entry, i.e. `set` refines
`Function.update`. -/
theorem decode_set (v : PackedVec n) (i : Nat) (h : i < n) (b : Bool) :
    (v.set i h b).decode = Function.update v.decode ⟨i, h⟩ (Bool.toF2 b) := by
  funext j
  rcases eq_or_ne j ⟨i, h⟩ with hj | hj
  · subst hj
    rw [Function.update_self, decode_get, get_set_self]
  · rw [Function.update_of_ne hj, decode_get, decode_get,
      get_set_ne v i h b (fun heq => hj (Fin.ext heq.symm))]

/-- XOR decodes to vector addition. -/
theorem decode_xor (u v : PackedVec n) : (u.xor v).decode = u.decode + v.decode := by
  funext i
  show Bool.toF2 ((u.storage ^^^ v.storage).getLsbD i.val) = u.decode i + v.decode i
  rw [BitVec.getLsbD_xor, Bool.toF2_xor]
  rfl

/-- Parity equals the sum of the decoded entries over `F2`. -/
theorem parity_eq_sum_decode (v : PackedVec n) :
    Bool.toF2 v.parity = ∑ i : Fin n, v.decode i := by
  have htail : bitParityAux v.storage (capacity n) = bitParityAux v.storage n := by
    have hk : n + (capacity n - n) = capacity n := Nat.add_sub_of_le (le_capacity n)
    calc bitParityAux v.storage (capacity n)
        = bitParityAux v.storage (n + (capacity n - n)) := by rw [hk]
      _ = bitParityAux v.storage n :=
          bitParityAux_eq_of_getLsbD_false v.zero_padding (capacity n - n)
  calc Bool.toF2 v.parity
      = Bool.toF2 (bitParityAux v.storage (capacity n)) := rfl
    _ = Bool.toF2 (bitParityAux v.storage n) := by rw [htail]
    _ = ∑ i ∈ Finset.range n, Bool.toF2 (v.storage.getLsbD i) := toF2_bitParityAux v.storage n
    _ = ∑ i : Fin n, Bool.toF2 (v.storage.getLsbD i.val) :=
        (Fin.sum_univ_eq_sum_range (fun i => Bool.toF2 (v.storage.getLsbD i)) n).symm
    _ = ∑ i : Fin n, v.decode i := by
        apply Finset.sum_congr rfl
        intro i _
        rfl

/-- The dot product (parity of the bitwise AND) equals Mathlib's `dotProduct` over the
decoded vectors. -/
theorem dot_eq_dotProduct (u v : PackedVec n) :
    Bool.toF2 (u.dot v) = dotProduct u.decode v.decode := by
  have hpad : ∀ j, n ≤ j → (u.storage &&& v.storage).getLsbD j = false := by
    intro j hj
    rw [BitVec.getLsbD_and, u.zero_padding j hj, Bool.false_and]
  have htail : bitParityAux (u.storage &&& v.storage) (capacity n)
      = bitParityAux (u.storage &&& v.storage) n := by
    have hk : n + (capacity n - n) = capacity n := Nat.add_sub_of_le (le_capacity n)
    calc bitParityAux (u.storage &&& v.storage) (capacity n)
        = bitParityAux (u.storage &&& v.storage) (n + (capacity n - n)) := by rw [hk]
      _ = bitParityAux (u.storage &&& v.storage) n :=
          bitParityAux_eq_of_getLsbD_false hpad (capacity n - n)
  calc Bool.toF2 (u.dot v)
      = Bool.toF2 (bitParityAux (u.storage &&& v.storage) (capacity n)) := rfl
    _ = Bool.toF2 (bitParityAux (u.storage &&& v.storage) n) := by rw [htail]
    _ = ∑ i ∈ Finset.range n, Bool.toF2 ((u.storage &&& v.storage).getLsbD i) :=
        toF2_bitParityAux _ n
    _ = ∑ i : Fin n, Bool.toF2 ((u.storage &&& v.storage).getLsbD i.val) :=
        (Fin.sum_univ_eq_sum_range
          (fun i => Bool.toF2 ((u.storage &&& v.storage).getLsbD i)) n).symm
    _ = ∑ i : Fin n, u.decode i * v.decode i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [BitVec.getLsbD_and, Bool.toF2_and]
        rfl
    _ = dotProduct u.decode v.decode := rfl

end PackedVec

/-! ## `PackedMatrix`: packed row-major bit matrices

A packed GF(2) matrix of `m` rows and `n` columns, refining `binar`'s
`AlignedBitMatrix` (`binar/src/matrix/aligned_bitmatrix.rs`) as `m` independently
block-padded packed rows, each a `PackedVec n`. This mirrors `AlignedBitMatrix`'s actual
row-major, per-row-padded layout while leaving the flat-buffer/raw-row-pointer storage
details (also outside this semantic model) unspecified. -/

/-- A packed GF(2) matrix of `m` rows and `n` columns: `m` independently block-padded
packed rows (`binar/src/matrix/aligned_bitmatrix.rs`). -/
structure PackedMatrix (m n : Nat) where
  /-- The packed rows, each a length-`n` packed vector. -/
  rows : Fin m → PackedVec n

namespace PackedMatrix

variable {m n : Nat}

/-- The all-zero packed matrix, mirroring `AlignedBitMatrix::zeros`. -/
def zero (m n : Nat) : PackedMatrix m n where
  rows _ := PackedVec.zero n

/-- Read entry `(i, j)`, mirroring `AlignedBitMatrix::get`. -/
def get (M : PackedMatrix m n) (i : Fin m) (j : Nat) : Bool := (M.rows i).get j

/-- Write entry `(i, j)` for an in-range column, mirroring `AlignedBitMatrix::set`. -/
def set (M : PackedMatrix m n) (i : Fin m) (j : Nat) (h : j < n) (b : Bool) :
    PackedMatrix m n where
  rows := Function.update M.rows i ((M.rows i).set j h b)

/-- XOR packed row `src` into packed row `dst`, mirroring
`AlignedBitMatrix::add_into_row`. -/
def xorRow (M : PackedMatrix m n) (dst src : Fin m) : PackedMatrix m n where
  rows := Function.update M.rows dst ((M.rows dst).xor (M.rows src))

/-- Decode a packed matrix to its logical `F2`-valued content. -/
def decode (M : PackedMatrix m n) : Matrix (Fin m) (Fin n) F2 :=
  Matrix.of fun i => (M.rows i).decode

@[simp] theorem decode_get (M : PackedMatrix m n) (i : Fin m) (j : Fin n) :
    M.decode i j = Bool.toF2 (M.get i j.val) := rfl

@[simp] theorem decode_zero (m n : Nat) : (PackedMatrix.zero m n).decode = 0 := by
  funext i j
  show (PackedVec.zero n).decode j = (0 : Matrix (Fin m) (Fin n) F2) i j
  rw [PackedVec.decode_zero]
  rfl

/-- Setting an in-range entry decodes to updating that row, i.e. `set` refines
`Matrix.updateRow`/`Function.update`. -/
theorem decode_set (M : PackedMatrix m n) (i : Fin m) (j : Nat) (h : j < n) (b : Bool) :
    (M.set i j h b).decode = Matrix.updateRow M.decode i
      (Function.update (M.decode i) ⟨j, h⟩ (Bool.toF2 b)) := by
  funext i' j'
  rcases eq_or_ne i' i with hi | hi
  · subst hi
    rw [Matrix.updateRow_self]
    show ((Function.update M.rows i' ((M.rows i').set j h b)) i').decode j' = _
    rw [Function.update_self, PackedVec.decode_set]
    rfl
  · rw [Matrix.updateRow_ne hi]
    show ((Function.update M.rows i ((M.rows i).set j h b)) i').decode j' = M.decode i' j'
    rw [Function.update_of_ne hi]
    rfl

/-- XOR-ing row `src` into row `dst` decodes to adding the decoded rows, i.e. `xorRow`
refines `Matrix.updateRow`. -/
theorem decode_xorRow (M : PackedMatrix m n) (dst src : Fin m) :
    (M.xorRow dst src).decode
      = Matrix.updateRow M.decode dst (M.decode dst + M.decode src) := by
  funext i' j'
  rcases eq_or_ne i' dst with hi | hi
  · subst hi
    rw [Matrix.updateRow_self]
    show ((Function.update M.rows i' ((M.rows i').xor (M.rows src))) i').decode j' = _
    rw [Function.update_self, PackedVec.decode_xor]
    rfl
  · rw [Matrix.updateRow_ne hi]
    show ((Function.update M.rows dst ((M.rows dst).xor (M.rows src))) i').decode j'
      = M.decode i' j'
    rw [Function.update_of_ne hi]
    rfl

end PackedMatrix

end BinarFormal.Packed
