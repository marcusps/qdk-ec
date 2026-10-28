import BinarFormal
import PaulimerFormal.Pauli
import PaulimerFormal.PackedEncoding

/-!
# Executable Pauli representations

Dense Paulis use BinarFormal's packed vectors. Sparse Paulis use finite sets of
X and Z positions. Both representations decode to `PaulimerFormal.Pauli`, so
their operations can be compared through one storage-independent semantics.
-/

namespace PaulimerFormal

open BinarFormal.Packed

/-- Rust's raw wrapping byte phase, modelled as arithmetic modulo 256. -/
abbrev RawPauliPhase := ZMod 256

/-- Reduction of a raw byte phase to its semantic exponent modulo four. -/
def decodeRawPauliPhase (phase : RawPauliPhase) : PauliPhase :=
  ZMod.castHom (show 4 ∣ 256 by norm_num) (ZMod 4) phase

@[simp]
theorem decodeRawPauliPhase_zero :
    decodeRawPauliPhase 0 = 0 := by
  simp [decodeRawPauliPhase]

@[simp]
theorem decodeRawPauliPhase_add (left right : RawPauliPhase) :
    decodeRawPauliPhase (left + right) =
      decodeRawPauliPhase left + decodeRawPauliPhase right := by
  exact map_add
    (ZMod.castHom (show 4 ∣ 256 by norm_num) (ZMod 4))
    left right

@[simp]
theorem decodeRawPauliPhase_neg (phase : RawPauliPhase) :
    decodeRawPauliPhase (-phase) =
      -decodeRawPauliPhase phase := by
  exact map_neg
    (ZMod.castHom (show 4 ∣ 256 by norm_num) (ZMod 4))
    phase

/-- Rust's stored result for `complex_conjugate_in_place`. -/
def rawComplexConjugate (phase : RawPauliPhase) : RawPauliPhase :=
  (4 - phase.val % 4 : ℕ)

@[simp]
theorem decodeRawPauliPhase_complexConjugate
    (phase : RawPauliPhase) :
    decodeRawPauliPhase (rawComplexConjugate phase) =
      -decodeRawPauliPhase phase := by
  fin_cases phase <;> decide

/-! ## Dense packed Paulis -/

@[ext]
structure DensePauli (m : ℕ) where
  xBits : PackedVec m
  zBits : PackedVec m
  phase : PauliPhase

namespace DensePauli

variable {m : ℕ}

/-- Decode packed storage into canonical phase-aware semantics. -/
def decode (pauli : DensePauli m) : Pauli m where
  x := pauli.xBits.decode
  z := pauli.zBits.decode
  phase := pauli.phase

/-- Pack a canonical Pauli. -/
def ofPauli (pauli : Pauli m) : DensePauli m where
  xBits := packVector pauli.x
  zBits := packVector pauli.z
  phase := pauli.phase

@[simp]
theorem decode_ofPauli (pauli : Pauli m) :
    decode (ofPauli pauli) = pauli := by
  ext <;> simp [decode, ofPauli]

@[simp]
theorem ofPauli_decode (pauli : DensePauli m) :
    ofPauli pauli.decode = pauli := by
  ext <;> simp [decode, ofPauli]

theorem decode_injective :
    Function.Injective (decode : DensePauli m → Pauli m) := by
  intro left right equal
  rw [← ofPauli_decode left, equal, ofPauli_decode]

theorem eq_iff_decode_eq (left right : DensePauli m) :
    left = right ↔ left.decode = right.decode :=
  decode_injective.eq_iff.symm

/-- Packed identity. -/
def identity : DensePauli m where
  xBits := PackedVec.zero m
  zBits := PackedVec.zero m
  phase := 0

/-- Packed right multiplication, matching Paulimer's `mul_assign_right`. -/
def multiply (left right : DensePauli m) : DensePauli m where
  xBits := left.xBits.xor right.xBits
  zBits := left.zBits.xor right.zBits
  phase :=
    left.phase + right.phase +
      Pauli.parityPhase (Bool.toF2 (left.zBits.dot right.xBits))

/-- Packed inversion, matching Paulimer's phase update. -/
def inverse (pauli : DensePauli m) : DensePauli m where
  xBits := pauli.xBits
  zBits := pauli.zBits
  phase :=
    -pauli.phase +
      Pauli.parityPhase (Bool.toF2 (pauli.zBits.dot pauli.xBits))

instance : One (DensePauli m) := ⟨identity⟩

instance : Mul (DensePauli m) := ⟨multiply⟩

instance : Inv (DensePauli m) := ⟨inverse⟩

@[simp]
theorem decode_one :
    decode (1 : DensePauli m) = 1 := by
  change decode identity = Pauli.identity
  ext <;> simp [decode, identity, Pauli.identity]

@[simp]
theorem decode_mul (left right : DensePauli m) :
    decode (left * right) = decode left * decode right := by
  apply Pauli.ext
  · exact PackedVec.decode_xor left.xBits right.xBits
  · exact PackedVec.decode_xor left.zBits right.zBits
  · change
      left.phase + right.phase +
          Pauli.parityPhase (Bool.toF2 (left.zBits.dot right.xBits)) =
        left.phase + right.phase +
          Pauli.parityPhase
            (dotProduct left.zBits.decode right.xBits.decode)
    rw [PackedVec.dot_eq_dotProduct]

@[simp]
theorem decode_inv (pauli : DensePauli m) :
    decode pauli⁻¹ = (decode pauli)⁻¹ := by
  apply Pauli.ext
  · rfl
  · rfl
  · change
      -pauli.phase +
          Pauli.parityPhase (Bool.toF2 (pauli.zBits.dot pauli.xBits)) =
        -pauli.phase +
          Pauli.parityPhase
            (dotProduct pauli.zBits.decode pauli.xBits.decode)
    rw [PackedVec.dot_eq_dotProduct]

instance : Group (DensePauli m) where
  mul_assoc left middle right := by
    apply decode_injective
    simp only [decode_mul]
    exact mul_assoc _ _ _
  one_mul pauli := by
    apply decode_injective
    simp only [decode_mul, decode_one]
    exact one_mul _
  mul_one pauli := by
    apply decode_injective
    simp only [decode_mul, decode_one]
    exact mul_one _
  inv_mul_cancel pauli := by
    apply decode_injective
    simp only [decode_mul, decode_inv, decode_one]
    exact inv_mul_cancel _

/-- Assign the phase exponent without changing the packed coordinates. -/
def assignPhase (pauli : DensePauli m) (phase : PauliPhase) :
    DensePauli m :=
  { pauli with phase }

/-- Add to the phase exponent without changing the packed coordinates. -/
def addPhase (pauli : DensePauli m) (phase : PauliPhase) :
    DensePauli m :=
  { pauli with phase := pauli.phase + phase }

/-- Symbolic complex conjugation of the represented Pauli. -/
def complexConjugate (pauli : DensePauli m) : DensePauli m :=
  { pauli with phase := -pauli.phase }

/-- Multiplication by the scalar phase `-1`. -/
def negate (pauli : DensePauli m) : DensePauli m :=
  { pauli with phase := pauli.phase + 2 }

@[simp]
theorem decode_assignPhase (pauli : DensePauli m) (phase : PauliPhase) :
    decode (assignPhase pauli phase) =
      Pauli.ofProjective pauli.decode.projective phase := by
  rfl

@[simp]
theorem decode_addPhase (pauli : DensePauli m) (phase : PauliPhase) :
    decode (addPhase pauli phase) =
      Pauli.ofProjective pauli.decode.projective
        (pauli.decode.phase + phase) := by
  rfl

@[simp]
theorem decode_complexConjugate (pauli : DensePauli m) :
    decode pauli.complexConjugate =
      pauli.decode.complexConjugate := by
  rfl

@[simp]
theorem decode_negate (pauli : DensePauli m) :
    decode pauli.negate = -pauli.decode := by
  rfl

/-- Packed constructor for a single X. -/
def singleX (index : Fin m) : DensePauli m :=
  ofPauli (Pauli.ofProjective (ProjectivePauli.singleX index) 0)

/-- Packed constructor for a single Z. -/
def singleZ (index : Fin m) : DensePauli m :=
  ofPauli (Pauli.ofProjective (ProjectivePauli.singleZ index) 0)

/-- Packed constructor for the positive single-qubit Y representative. -/
def singleY (index : Fin m) : DensePauli m :=
  ofPauli
    (Pauli.positiveRepresentative
      (ProjectivePauli.singleX index + ProjectivePauli.singleZ index))

@[simp]
theorem decode_singleX (index : Fin m) :
    decode (singleX index) =
      Pauli.ofProjective (ProjectivePauli.singleX index) 0 := by
  simp [singleX]

@[simp]
theorem decode_singleZ (index : Fin m) :
    decode (singleZ index) =
      Pauli.ofProjective (ProjectivePauli.singleZ index) 0 := by
  simp [singleZ]

@[simp]
theorem decode_singleY (index : Fin m) :
    decode (singleY index) =
      Pauli.positiveRepresentative
        (ProjectivePauli.singleX index + ProjectivePauli.singleZ index) := by
  simp [singleY]

/-- Right multiplication by a single X. -/
def multiplyRightX (pauli : DensePauli m) (index : Fin m) :
    DensePauli m :=
  pauli * singleX index

/-- Left multiplication by a single X. -/
def multiplyLeftX (pauli : DensePauli m) (index : Fin m) :
    DensePauli m :=
  singleX index * pauli

/-- Right multiplication by a single Y. -/
def multiplyRightY (pauli : DensePauli m) (index : Fin m) :
    DensePauli m :=
  pauli * singleY index

/-- Left multiplication by a single Y. -/
def multiplyLeftY (pauli : DensePauli m) (index : Fin m) :
    DensePauli m :=
  singleY index * pauli

/-- Right multiplication by a single Z. -/
def multiplyRightZ (pauli : DensePauli m) (index : Fin m) :
    DensePauli m :=
  pauli * singleZ index

/-- Left multiplication by a single Z. -/
def multiplyLeftZ (pauli : DensePauli m) (index : Fin m) :
    DensePauli m :=
  singleZ index * pauli

@[simp]
theorem decode_multiplyRightX (pauli : DensePauli m) (index : Fin m) :
    decode (multiplyRightX pauli index) =
      pauli.decode *
        Pauli.ofProjective (ProjectivePauli.singleX index) 0 := by
  simp [multiplyRightX]

@[simp]
theorem decode_multiplyLeftX (pauli : DensePauli m) (index : Fin m) :
    decode (multiplyLeftX pauli index) =
      Pauli.ofProjective (ProjectivePauli.singleX index) 0 *
        pauli.decode := by
  simp [multiplyLeftX]

@[simp]
theorem decode_multiplyRightY (pauli : DensePauli m) (index : Fin m) :
    decode (multiplyRightY pauli index) =
      pauli.decode *
        Pauli.positiveRepresentative
          (ProjectivePauli.singleX index +
            ProjectivePauli.singleZ index) := by
  simp [multiplyRightY]

@[simp]
theorem decode_multiplyLeftY (pauli : DensePauli m) (index : Fin m) :
    decode (multiplyLeftY pauli index) =
      Pauli.positiveRepresentative
          (ProjectivePauli.singleX index +
            ProjectivePauli.singleZ index) *
        pauli.decode := by
  simp [multiplyLeftY]

@[simp]
theorem decode_multiplyRightZ (pauli : DensePauli m) (index : Fin m) :
    decode (multiplyRightZ pauli index) =
      pauli.decode *
        Pauli.ofProjective (ProjectivePauli.singleZ index) 0 := by
  simp [multiplyRightZ]

@[simp]
theorem decode_multiplyLeftZ (pauli : DensePauli m) (index : Fin m) :
    decode (multiplyLeftZ pauli index) =
      Pauli.ofProjective (ProjectivePauli.singleZ index) 0 *
        pauli.decode := by
  simp [multiplyLeftZ]

def support (pauli : DensePauli m) : Finset (Fin m) :=
  Finset.univ.filter fun index : Fin m =>
    pauli.xBits.get index.val = true ∨
      pauli.zBits.get index.val = true

def weight (pauli : DensePauli m) : ℕ :=
  pauli.support.card

def ySupport (pauli : DensePauli m) : Finset (Fin m) :=
  Finset.univ.filter fun index : Fin m =>
    pauli.xBits.get index.val = true ∧
      pauli.zBits.get index.val = true

def yWeight (pauli : DensePauli m) : ℕ :=
  pauli.ySupport.card

@[simp]
theorem support_eq_decode (pauli : DensePauli m) :
    pauli.support = Pauli.support pauli.decode.projective := by
  change
    (Finset.univ.filter fun index : Fin m =>
      pauli.xBits.get index.val = true ∨
        pauli.zBits.get index.val = true) =
      Finset.univ.filter fun index : Fin m =>
        Bool.toF2 (pauli.xBits.get index.val) ≠ 0 ∨
          Bool.toF2 (pauli.zBits.get index.val) ≠ 0
  ext index
  cases x_value : pauli.xBits.get index.val <;>
    cases z_value : pauli.zBits.get index.val <;>
    simp [x_value, z_value]

@[simp]
theorem weight_eq_decode (pauli : DensePauli m) :
    pauli.weight = Pauli.weight pauli.decode.projective := by
  rw [weight, Pauli.weight, support_eq_decode]

@[simp]
theorem ySupport_eq_decode (pauli : DensePauli m) :
    pauli.ySupport = Pauli.ySupport pauli.decode.projective := by
  change
    (Finset.univ.filter fun index : Fin m =>
      pauli.xBits.get index.val = true ∧
        pauli.zBits.get index.val = true) =
      Finset.univ.filter fun index : Fin m =>
        Bool.toF2 (pauli.xBits.get index.val) ≠ 0 ∧
          Bool.toF2 (pauli.zBits.get index.val) ≠ 0
  ext index
  cases x_value : pauli.xBits.get index.val <;>
    cases z_value : pauli.zBits.get index.val <;>
    simp [x_value, z_value]

@[simp]
theorem yWeight_eq_decode (pauli : DensePauli m) :
    pauli.yWeight = Pauli.yWeight pauli.decode.projective := by
  rw [yWeight, Pauli.yWeight, ySupport_eq_decode]

end DensePauli

/-! ## Sparse finite-support Paulis -/

/-- Decode a finite support as a binary indicator vector. -/
def vectorOfSupport {m : ℕ} (support : Finset (Fin m)) :
    Fin m → F2 :=
  fun index => if index ∈ support then 1 else 0

/-- Extract the nonzero positions of a binary vector. -/
def supportOfVector {m : ℕ} (vector : Fin m → F2) :
    Finset (Fin m) :=
  Finset.univ.filter fun index => vector index ≠ 0

@[simp]
theorem indicatorF2 (bit : F2) :
    (if bit ≠ 0 then 1 else 0) = bit := by
  rcases Pauli.f2_eq_zero_or_one bit with equals_zero | equals_one
  · simp [equals_zero]
  · simp [equals_one]

@[simp]
theorem zeroIndicatorF2 (bit : F2) :
    (if bit = 0 then 0 else 1) = bit := by
  rcases Pauli.f2_eq_zero_or_one bit with equals_zero | equals_one
  · simp [equals_zero]
  · simp [equals_one]

@[simp]
theorem vectorOfSupport_supportOfVector {m : ℕ}
    (vector : Fin m → F2) :
    vectorOfSupport (supportOfVector vector) = vector := by
  funext index
  simp [vectorOfSupport, supportOfVector]

@[simp]
theorem supportOfVector_vectorOfSupport {m : ℕ}
    (support : Finset (Fin m)) :
    supportOfVector (vectorOfSupport support) = support := by
  ext index
  simp [supportOfVector, vectorOfSupport]

/-- Symmetric difference, represented directly as a finite filter. -/
def xorSupport {m : ℕ}
    (left right : Finset (Fin m)) : Finset (Fin m) :=
  (left \ right) ∪ (right \ left)

@[simp]
theorem vectorOfSupport_xorSupport {m : ℕ}
    (left right : Finset (Fin m)) :
    vectorOfSupport (xorSupport left right) =
      vectorOfSupport left + vectorOfSupport right := by
  funext index
  by_cases left_mem : index ∈ left <;>
    by_cases right_mem : index ∈ right <;>
    simp [xorSupport, vectorOfSupport, left_mem, right_mem]

/-- Parity of a finite support, represented in the binary field. -/
def supportParity {m : ℕ} (support : Finset (Fin m)) : F2 :=
  support.card

theorem supportParity_inter_eq_dotProduct {m : ℕ}
    (left right : Finset (Fin m)) :
    supportParity (left ∩ right) =
      dotProduct (vectorOfSupport left) (vectorOfSupport right) := by
  classical
  rw [supportParity, dotProduct]
  calc
    ((left ∩ right).card : F2) =
        ∑ index : Fin m,
          if index ∈ left ∩ right then (1 : F2) else 0 := by
      symm
      calc
        (∑ index : Fin m,
            if index ∈ left ∩ right then (1 : F2) else 0) =
            ((Finset.univ.filter fun index : Fin m =>
              index ∈ left ∩ right).card : F2) :=
          Finset.sum_boole
            (R := F2)
            (fun index : Fin m => index ∈ left ∩ right)
            Finset.univ
        _ = ((left ∩ right).card : F2) := by
          have filtered :
              Finset.univ.filter
                  (fun index : Fin m => index ∈ left ∩ right) =
                left ∩ right := by
            ext index
            simp
          rw [filtered]
    _ = ∑ index : Fin m,
          vectorOfSupport left index *
            vectorOfSupport right index := by
      apply Finset.sum_congr rfl
      intro index _
      by_cases left_mem : index ∈ left <;>
        by_cases right_mem : index ∈ right <;>
        simp [vectorOfSupport, left_mem, right_mem]

@[ext]
structure SparsePauli (m : ℕ) where
  xSupport : Finset (Fin m)
  zSupport : Finset (Fin m)
  phase : PauliPhase

namespace SparsePauli

variable {m : ℕ}

/-- Decode finite supports into canonical phase-aware semantics. -/
def decode (pauli : SparsePauli m) : Pauli m where
  x := vectorOfSupport pauli.xSupport
  z := vectorOfSupport pauli.zSupport
  phase := pauli.phase

/-- Extract a sparse representation from canonical semantics. -/
def ofPauli (pauli : Pauli m) : SparsePauli m where
  xSupport := supportOfVector pauli.x
  zSupport := supportOfVector pauli.z
  phase := pauli.phase

@[simp]
theorem decode_ofPauli (pauli : Pauli m) :
    decode (ofPauli pauli) = pauli := by
  ext <;> simp [decode, ofPauli]

@[simp]
theorem ofPauli_decode (pauli : SparsePauli m) :
    ofPauli pauli.decode = pauli := by
  ext <;> simp [decode, ofPauli]

theorem decode_injective :
    Function.Injective (decode : SparsePauli m → Pauli m) := by
  intro left right equal
  rw [← ofPauli_decode left, equal, ofPauli_decode]

theorem eq_iff_decode_eq (left right : SparsePauli m) :
    left = right ↔ left.decode = right.decode :=
  decode_injective.eq_iff.symm

def identity : SparsePauli m where
  xSupport := ∅
  zSupport := ∅
  phase := 0

def multiply (left right : SparsePauli m) : SparsePauli m where
  xSupport := xorSupport left.xSupport right.xSupport
  zSupport := xorSupport left.zSupport right.zSupport
  phase :=
    left.phase + right.phase +
      Pauli.parityPhase
        (supportParity (left.zSupport ∩ right.xSupport))

def inverse (pauli : SparsePauli m) : SparsePauli m where
  xSupport := pauli.xSupport
  zSupport := pauli.zSupport
  phase :=
    -pauli.phase +
      Pauli.parityPhase
        (supportParity (pauli.zSupport ∩ pauli.xSupport))

instance : One (SparsePauli m) := ⟨identity⟩

instance : Mul (SparsePauli m) := ⟨multiply⟩

instance : Inv (SparsePauli m) := ⟨inverse⟩

@[simp]
theorem decode_one :
    decode (1 : SparsePauli m) = 1 := by
  change decode identity = Pauli.identity
  ext <;> simp [decode, identity, Pauli.identity, vectorOfSupport]

@[simp]
theorem decode_mul (left right : SparsePauli m) :
    decode (left * right) = decode left * decode right := by
  apply Pauli.ext
  · exact vectorOfSupport_xorSupport left.xSupport right.xSupport
  · exact vectorOfSupport_xorSupport left.zSupport right.zSupport
  · change
      left.phase + right.phase +
          Pauli.parityPhase
            (supportParity (left.zSupport ∩ right.xSupport)) =
        left.phase + right.phase +
          Pauli.parityPhase
            (dotProduct
              (vectorOfSupport left.zSupport)
              (vectorOfSupport right.xSupport))
    rw [supportParity_inter_eq_dotProduct]

@[simp]
theorem decode_inv (pauli : SparsePauli m) :
    decode pauli⁻¹ = (decode pauli)⁻¹ := by
  apply Pauli.ext
  · rfl
  · rfl
  · change
      -pauli.phase +
          Pauli.parityPhase
            (supportParity (pauli.zSupport ∩ pauli.xSupport)) =
        -pauli.phase +
          Pauli.parityPhase
            (dotProduct
              (vectorOfSupport pauli.zSupport)
              (vectorOfSupport pauli.xSupport))
    rw [supportParity_inter_eq_dotProduct]

instance : Group (SparsePauli m) where
  mul_assoc left middle right := by
    apply decode_injective
    simp only [decode_mul]
    exact mul_assoc _ _ _
  one_mul pauli := by
    apply decode_injective
    simp only [decode_mul, decode_one]
    exact one_mul _
  mul_one pauli := by
    apply decode_injective
    simp only [decode_mul, decode_one]
    exact mul_one _
  inv_mul_cancel pauli := by
    apply decode_injective
    simp only [decode_mul, decode_inv, decode_one]
    exact inv_mul_cancel _

def support (pauli : SparsePauli m) : Finset (Fin m) :=
  pauli.xSupport ∪ pauli.zSupport

def weight (pauli : SparsePauli m) : ℕ :=
  pauli.support.card

def ySupport (pauli : SparsePauli m) : Finset (Fin m) :=
  pauli.xSupport ∩ pauli.zSupport

def yWeight (pauli : SparsePauli m) : ℕ :=
  pauli.ySupport.card

@[simp]
theorem decode_support (pauli : SparsePauli m) :
    Pauli.support pauli.decode.projective = pauli.support := by
  change
    (Finset.univ.filter fun index =>
      vectorOfSupport pauli.xSupport index ≠ 0 ∨
        vectorOfSupport pauli.zSupport index ≠ 0) =
      pauli.xSupport ∪ pauli.zSupport
  ext index
  by_cases x_mem : index ∈ pauli.xSupport <;>
    by_cases z_mem : index ∈ pauli.zSupport <;>
    simp [vectorOfSupport, x_mem, z_mem]

@[simp]
theorem decode_ySupport (pauli : SparsePauli m) :
    Pauli.ySupport pauli.decode.projective = pauli.ySupport := by
  change
    (Finset.univ.filter fun index =>
      vectorOfSupport pauli.xSupport index ≠ 0 ∧
        vectorOfSupport pauli.zSupport index ≠ 0) =
      pauli.xSupport ∩ pauli.zSupport
  ext index
  by_cases x_mem : index ∈ pauli.xSupport <;>
    by_cases z_mem : index ∈ pauli.zSupport <;>
    simp [vectorOfSupport, x_mem, z_mem]

@[simp]
theorem decode_weight (pauli : SparsePauli m) :
    Pauli.weight pauli.decode.projective = pauli.weight := by
  rw [Pauli.weight, weight, decode_support]

@[simp]
theorem decode_yWeight (pauli : SparsePauli m) :
    Pauli.yWeight pauli.decode.projective = pauli.yWeight := by
  rw [Pauli.yWeight, yWeight, decode_ySupport]

end SparsePauli

/-! ## Dense/sparse conversion -/

namespace DensePauli

variable {m : ℕ}

def toSparse (pauli : DensePauli m) : SparsePauli m :=
  SparsePauli.ofPauli pauli.decode

@[simp]
theorem decode_toSparse (pauli : DensePauli m) :
    pauli.toSparse.decode = pauli.decode := by
  simp [toSparse]

@[simp]
theorem toSparse_support (pauli : DensePauli m) :
    pauli.toSparse.support = pauli.support := by
  calc
    pauli.toSparse.support =
        Pauli.support pauli.toSparse.decode.projective :=
      (SparsePauli.decode_support pauli.toSparse).symm
    _ = Pauli.support pauli.decode.projective := by
      rw [decode_toSparse]
    _ = pauli.support := (support_eq_decode pauli).symm

@[simp]
theorem toSparse_weight (pauli : DensePauli m) :
    pauli.toSparse.weight = pauli.weight := by
  change pauli.toSparse.support.card = pauli.support.card
  rw [toSparse_support]

end DensePauli

namespace SparsePauli

variable {m : ℕ}

def toDense (pauli : SparsePauli m) : DensePauli m :=
  DensePauli.ofPauli pauli.decode

@[simp]
theorem decode_toDense (pauli : SparsePauli m) :
    pauli.toDense.decode = pauli.decode := by
  simp [toDense]

@[simp]
theorem toDense_toSparse (pauli : SparsePauli m) :
    pauli.toDense.toSparse = pauli := by
  apply SparsePauli.decode_injective
  simp

end SparsePauli

@[simp]
theorem DensePauli.toSparse_toDense {m : ℕ}
    (pauli : DensePauli m) :
    pauli.toSparse.toDense = pauli := by
  apply DensePauli.decode_injective
  simp

/-! ## Projective storage -/

@[ext]
structure DenseProjectivePauli (m : ℕ) where
  xBits : PackedVec m
  zBits : PackedVec m

namespace DenseProjectivePauli

variable {m : ℕ}

def decode (pauli : DenseProjectivePauli m) : ProjectivePauli m where
  x := pauli.xBits.decode
  z := pauli.zBits.decode

def ofProjective (pauli : ProjectivePauli m) : DenseProjectivePauli m where
  xBits := packVector pauli.x
  zBits := packVector pauli.z

@[simp]
theorem decode_ofProjective (pauli : ProjectivePauli m) :
    decode (ofProjective pauli) = pauli := by
  ext <;> simp [decode, ofProjective]

@[simp]
theorem ofProjective_decode (pauli : DenseProjectivePauli m) :
    ofProjective pauli.decode = pauli := by
  ext <;> simp [decode, ofProjective]

def multiply (left right : DenseProjectivePauli m) :
    DenseProjectivePauli m where
  xBits := left.xBits.xor right.xBits
  zBits := left.zBits.xor right.zBits

@[simp]
theorem decode_multiply (left right : DenseProjectivePauli m) :
    decode (multiply left right) = left.decode + right.decode := by
  apply ProjectivePauli.ext
  · exact PackedVec.decode_xor left.xBits right.xBits
  · exact PackedVec.decode_xor left.zBits right.zBits

def withPhase (pauli : DenseProjectivePauli m) (phase : PauliPhase) :
    DensePauli m where
  xBits := pauli.xBits
  zBits := pauli.zBits
  phase := phase

@[simp]
theorem decode_withPhase
    (pauli : DenseProjectivePauli m) (phase : PauliPhase) :
    (withPhase pauli phase).decode =
      Pauli.ofProjective pauli.decode phase := by
  rfl

end DenseProjectivePauli

namespace DensePauli

variable {m : ℕ}

def projectiveStorage (pauli : DensePauli m) :
    DenseProjectivePauli m where
  xBits := pauli.xBits
  zBits := pauli.zBits

@[simp]
theorem decode_projectiveStorage (pauli : DensePauli m) :
    pauli.projectiveStorage.decode = pauli.decode.projective := by
  rfl

end DensePauli

@[ext]
structure SparseProjectivePauli (m : ℕ) where
  xSupport : Finset (Fin m)
  zSupport : Finset (Fin m)

namespace SparseProjectivePauli

variable {m : ℕ}

def decode (pauli : SparseProjectivePauli m) : ProjectivePauli m where
  x := vectorOfSupport pauli.xSupport
  z := vectorOfSupport pauli.zSupport

def ofProjective (pauli : ProjectivePauli m) :
    SparseProjectivePauli m where
  xSupport := supportOfVector pauli.x
  zSupport := supportOfVector pauli.z

@[simp]
theorem decode_ofProjective (pauli : ProjectivePauli m) :
    decode (ofProjective pauli) = pauli := by
  ext <;> simp [decode, ofProjective]

@[simp]
theorem ofProjective_decode (pauli : SparseProjectivePauli m) :
    ofProjective pauli.decode = pauli := by
  ext <;> simp [decode, ofProjective]

def multiply (left right : SparseProjectivePauli m) :
    SparseProjectivePauli m where
  xSupport := xorSupport left.xSupport right.xSupport
  zSupport := xorSupport left.zSupport right.zSupport

@[simp]
theorem decode_multiply (left right : SparseProjectivePauli m) :
    decode (multiply left right) = left.decode + right.decode := by
  apply ProjectivePauli.ext
  · exact vectorOfSupport_xorSupport left.xSupport right.xSupport
  · exact vectorOfSupport_xorSupport left.zSupport right.zSupport

def withPhase (pauli : SparseProjectivePauli m) (phase : PauliPhase) :
    SparsePauli m where
  xSupport := pauli.xSupport
  zSupport := pauli.zSupport
  phase := phase

@[simp]
theorem decode_withPhase
    (pauli : SparseProjectivePauli m) (phase : PauliPhase) :
    (withPhase pauli phase).decode =
      Pauli.ofProjective pauli.decode phase := by
  rfl

def toDense (pauli : SparseProjectivePauli m) :
    DenseProjectivePauli m :=
  DenseProjectivePauli.ofProjective pauli.decode

@[simp]
theorem decode_toDense (pauli : SparseProjectivePauli m) :
    pauli.toDense.decode = pauli.decode := by
  simp [toDense]

end SparseProjectivePauli

namespace DenseProjectivePauli

variable {m : ℕ}

def toSparse (pauli : DenseProjectivePauli m) :
    SparseProjectivePauli m :=
  SparseProjectivePauli.ofProjective pauli.decode

@[simp]
theorem decode_toSparse (pauli : DenseProjectivePauli m) :
    pauli.toSparse.decode = pauli.decode := by
  simp [toSparse]

end DenseProjectivePauli

@[simp]
theorem SparseProjectivePauli.toDense_toSparse {m : ℕ}
    (pauli : SparseProjectivePauli m) :
    pauli.toDense.toSparse = pauli := by
  ext <;> simp [DenseProjectivePauli.toSparse,
    SparseProjectivePauli.toDense]

@[simp]
theorem DenseProjectivePauli.toSparse_toDense {m : ℕ}
    (pauli : DenseProjectivePauli m) :
    pauli.toSparse.toDense = pauli := by
  ext <;> simp [DenseProjectivePauli.toSparse,
    SparseProjectivePauli.toDense]

namespace SparsePauli

variable {m : ℕ}

def projectiveStorage (pauli : SparsePauli m) :
    SparseProjectivePauli m where
  xSupport := pauli.xSupport
  zSupport := pauli.zSupport

@[simp]
theorem decode_projectiveStorage (pauli : SparsePauli m) :
    pauli.projectiveStorage.decode = pauli.decode.projective := by
  rfl

end SparsePauli

/-! ## Queries matching the Rust representation API -/

/-- Whether a phase exponent is even. -/
def phaseEven (phase : PauliPhase) : Bool :=
  decide (phase + phase = 0)

theorem orderTwoBoolean_iff (phase : PauliPhase) (yParity : Bool) :
    (yParity ^^ phaseEven phase) = true ↔
      phase + phase =
        Pauli.parityPhase (Bool.toF2 yParity) := by
  fin_cases yParity <;> fin_cases phase <;> decide

namespace DensePauli

variable {m : ℕ}

def yParity (pauli : DensePauli m) : Bool :=
  pauli.xBits.dot pauli.zBits

def isOrderTwo (pauli : DensePauli m) : Bool :=
  pauli.yParity ^^ phaseEven pauli.phase

theorem isOrderTwo_eq_true_iff (pauli : DensePauli m) :
    pauli.isOrderTwo = true ↔ Pauli.IsOrderTwo pauli.decode := by
  rw [isOrderTwo, orderTwoBoolean_iff,
    Pauli.isOrderTwo_iff_phase]
  change
    pauli.phase + pauli.phase =
        Pauli.parityPhase (Bool.toF2 (pauli.xBits.dot pauli.zBits)) ↔
      pauli.phase + pauli.phase =
        Pauli.parityPhase
          (dotProduct pauli.zBits.decode pauli.xBits.decode)
  rw [PackedVec.dot_eq_dotProduct, dotProduct_comm]

end DensePauli

namespace SparsePauli

variable {m : ℕ}

def yParity (pauli : SparsePauli m) : Bool :=
  boolOfF2
    (supportParity (pauli.xSupport ∩ pauli.zSupport))

def isOrderTwo (pauli : SparsePauli m) : Bool :=
  pauli.yParity ^^ phaseEven pauli.phase

theorem isOrderTwo_eq_true_iff (pauli : SparsePauli m) :
    pauli.isOrderTwo = true ↔ Pauli.IsOrderTwo pauli.decode := by
  rw [isOrderTwo, orderTwoBoolean_iff,
    Pauli.isOrderTwo_iff_phase]
  change
    pauli.phase + pauli.phase =
        Pauli.parityPhase
          (Bool.toF2
            (boolOfF2
              (supportParity
                (pauli.xSupport ∩ pauli.zSupport)))) ↔
      pauli.phase + pauli.phase =
        Pauli.parityPhase
          (dotProduct
            (vectorOfSupport pauli.zSupport)
            (vectorOfSupport pauli.xSupport))
  rw [toF2_boolOfF2, supportParity_inter_eq_dotProduct,
    dotProduct_comm]

def singleX (index : Fin m) : SparsePauli m :=
  ofPauli (Pauli.ofProjective (ProjectivePauli.singleX index) 0)

def singleZ (index : Fin m) : SparsePauli m :=
  ofPauli (Pauli.ofProjective (ProjectivePauli.singleZ index) 0)

def singleY (index : Fin m) : SparsePauli m :=
  ofPauli
    (Pauli.positiveRepresentative
      (ProjectivePauli.singleX index + ProjectivePauli.singleZ index))

@[simp]
theorem decode_singleX (index : Fin m) :
    decode (singleX index) =
      Pauli.ofProjective (ProjectivePauli.singleX index) 0 := by
  simp [singleX]

@[simp]
theorem decode_singleZ (index : Fin m) :
    decode (singleZ index) =
      Pauli.ofProjective (ProjectivePauli.singleZ index) 0 := by
  simp [singleZ]

@[simp]
theorem decode_singleY (index : Fin m) :
    decode (singleY index) =
      Pauli.positiveRepresentative
        (ProjectivePauli.singleX index + ProjectivePauli.singleZ index) := by
  simp [singleY]

def assignPhase (pauli : SparsePauli m) (phase : PauliPhase) :
    SparsePauli m :=
  { pauli with phase }

def addPhase (pauli : SparsePauli m) (phase : PauliPhase) :
    SparsePauli m :=
  { pauli with phase := pauli.phase + phase }

def complexConjugate (pauli : SparsePauli m) : SparsePauli m :=
  { pauli with phase := -pauli.phase }

def negate (pauli : SparsePauli m) : SparsePauli m :=
  { pauli with phase := pauli.phase + 2 }

@[simp]
theorem decode_assignPhase (pauli : SparsePauli m) (phase : PauliPhase) :
    decode (assignPhase pauli phase) =
      Pauli.ofProjective pauli.decode.projective phase := by
  rfl

@[simp]
theorem decode_addPhase (pauli : SparsePauli m) (phase : PauliPhase) :
    decode (addPhase pauli phase) =
      Pauli.ofProjective pauli.decode.projective
        (pauli.decode.phase + phase) := by
  rfl

@[simp]
theorem decode_complexConjugate (pauli : SparsePauli m) :
    decode pauli.complexConjugate =
      pauli.decode.complexConjugate := by
  rfl

@[simp]
theorem decode_negate (pauli : SparsePauli m) :
    decode pauli.negate = -pauli.decode := by
  rfl

end SparsePauli

/-! ## Offset assignment and index remapping -/

/-- Replace a contiguous target range by the initial coordinates of a source vector. -/
def assignVectorWithOffset {sourceSize targetSize : ℕ}
    (target : Fin targetSize → F2) (source : Fin sourceSize → F2)
    (start count : ℕ) (source_fits : count ≤ sourceSize)
    (_target_fits : start + count ≤ targetSize) :
    Fin targetSize → F2 :=
  fun index =>
    if in_range : start ≤ index.val ∧ index.val < start + count then
      source
        ⟨index.val - start, by omega⟩
    else
      target index

def assignPauliWithOffset {sourceSize targetSize : ℕ}
    (target : Pauli targetSize) (source : Pauli sourceSize)
    (start count : ℕ) (source_fits : count ≤ sourceSize)
    (target_fits : start + count ≤ targetSize) :
    Pauli targetSize where
  x :=
    assignVectorWithOffset target.x source.x start count
      source_fits target_fits
  z :=
    assignVectorWithOffset target.z source.z start count
      source_fits target_fits
  phase := source.phase

/-- Packed closed form of Rust's per-bit offset-assignment loop. -/
def assignPackedWithOffset {sourceSize targetSize : ℕ}
    (target : PackedVec targetSize) (source : PackedVec sourceSize)
    (start count : ℕ) (_source_fits : count ≤ sourceSize)
    (_target_fits : start + count ≤ targetSize) :
    PackedVec targetSize :=
  PackedVec.ofBoolFn targetSize fun index =>
    if _in_range : start ≤ index ∧ index < start + count then
      source.get (index - start)
    else
      target.get index

@[simp]
theorem decode_assignPackedWithOffset {sourceSize targetSize : ℕ}
    (target : PackedVec targetSize) (source : PackedVec sourceSize)
    (start count : ℕ) (source_fits : count ≤ sourceSize)
    (target_fits : start + count ≤ targetSize) :
    (assignPackedWithOffset target source start count
      source_fits target_fits).decode =
      assignVectorWithOffset target.decode source.decode start count
        source_fits target_fits := by
  funext index
  unfold assignPackedWithOffset
  rw [PackedVec.decode_get,
    PackedVec.get_ofBoolFn targetSize _ index.val index.isLt]
  unfold assignVectorWithOffset
  split_ifs with in_range
  · rfl
  · rfl

namespace DensePauli

def assignWithOffset {sourceSize targetSize : ℕ}
    (target : DensePauli targetSize) (source : DensePauli sourceSize)
    (start count : ℕ) (source_fits : count ≤ sourceSize)
    (target_fits : start + count ≤ targetSize) :
    DensePauli targetSize where
  xBits :=
    assignPackedWithOffset target.xBits source.xBits start count
      source_fits target_fits
  zBits :=
    assignPackedWithOffset target.zBits source.zBits start count
      source_fits target_fits
  phase := source.phase

@[simp]
theorem decode_assignWithOffset {sourceSize targetSize : ℕ}
    (target : DensePauli targetSize) (source : DensePauli sourceSize)
    (start count : ℕ) (source_fits : count ≤ sourceSize)
    (target_fits : start + count ≤ targetSize) :
    (assignWithOffset target source start count
      source_fits target_fits).decode =
      assignPauliWithOffset target.decode source.decode start count
        source_fits target_fits := by
  apply Pauli.ext
  · exact
      decode_assignPackedWithOffset target.xBits source.xBits
        start count source_fits target_fits
  · exact
      decode_assignPackedWithOffset target.zBits source.zBits
        start count source_fits target_fits
  · rfl

end DensePauli

namespace SparsePauli

def assignWithOffset {sourceSize targetSize : ℕ}
    (target : SparsePauli targetSize) (source : SparsePauli sourceSize)
    (start count : ℕ) (source_fits : count ≤ sourceSize)
    (target_fits : start + count ≤ targetSize) :
    SparsePauli targetSize :=
  ofPauli
    (assignPauliWithOffset target.decode source.decode start count
      source_fits target_fits)

@[simp]
theorem decode_assignWithOffset {sourceSize targetSize : ℕ}
    (target : SparsePauli targetSize) (source : SparsePauli sourceSize)
    (start count : ℕ) (source_fits : count ≤ sourceSize)
    (target_fits : start + count ≤ targetSize) :
    (assignWithOffset target source start count
      source_fits target_fits).decode =
      assignPauliWithOffset target.decode source.decode start count
        source_fits target_fits := by
  simp [assignWithOffset]

/-- Remap sparse support through an injective qubit map. -/
def remap {sourceSize targetSize : ℕ}
    (pauli : SparsePauli sourceSize)
    (mapping : Fin sourceSize ↪ Fin targetSize) :
    SparsePauli targetSize where
  xSupport := pauli.xSupport.map mapping
  zSupport := pauli.zSupport.map mapping
  phase := pauli.phase

@[simp]
theorem remap_x_mem {sourceSize targetSize : ℕ}
    (pauli : SparsePauli sourceSize)
    (mapping : Fin sourceSize ↪ Fin targetSize)
    (index : Fin sourceSize) :
    mapping index ∈ (remap pauli mapping).xSupport ↔
      index ∈ pauli.xSupport := by
  simp [remap]

@[simp]
theorem remap_z_mem {sourceSize targetSize : ℕ}
    (pauli : SparsePauli sourceSize)
    (mapping : Fin sourceSize ↪ Fin targetSize)
    (index : Fin sourceSize) :
    mapping index ∈ (remap pauli mapping).zSupport ↔
      index ∈ pauli.zSupport := by
  simp [remap]

@[simp]
theorem decode_remap_x {sourceSize targetSize : ℕ}
    (pauli : SparsePauli sourceSize)
    (mapping : Fin sourceSize ↪ Fin targetSize)
    (index : Fin sourceSize) :
    (remap pauli mapping).decode.x (mapping index) =
      pauli.decode.x index := by
  simp [remap, decode, vectorOfSupport]

@[simp]
theorem decode_remap_z {sourceSize targetSize : ℕ}
    (pauli : SparsePauli sourceSize)
    (mapping : Fin sourceSize ↪ Fin targetSize)
    (index : Fin sourceSize) :
    (remap pauli mapping).decode.z (mapping index) =
      pauli.decode.z index := by
  simp [remap, decode, vectorOfSupport]

theorem decode_remap_x_eq_zero_of_not_mem_range
    {sourceSize targetSize : ℕ}
    (pauli : SparsePauli sourceSize)
    (mapping : Fin sourceSize ↪ Fin targetSize)
    (index : Fin targetSize)
    (outside : ∀ source, mapping source ≠ index) :
    (remap pauli mapping).decode.x index = 0 := by
  simp [remap, decode, vectorOfSupport, outside]

theorem decode_remap_z_eq_zero_of_not_mem_range
    {sourceSize targetSize : ℕ}
    (pauli : SparsePauli sourceSize)
    (mapping : Fin sourceSize ↪ Fin targetSize)
    (index : Fin targetSize)
    (outside : ∀ source, mapping source ≠ index) :
    (remap pauli mapping).decode.z index = 0 := by
  simp [remap, decode, vectorOfSupport, outside]

@[simp]
theorem remap_mul {sourceSize targetSize : ℕ}
    (left right : SparsePauli sourceSize)
    (mapping : Fin sourceSize ↪ Fin targetSize) :
    remap (left * right) mapping =
      remap left mapping * remap right mapping := by
  change
    remap (multiply left right) mapping =
      multiply (remap left mapping) (remap right mapping)
  apply SparsePauli.ext
  · change
      Finset.map mapping
          (xorSupport left.xSupport right.xSupport) =
        xorSupport
          (Finset.map mapping left.xSupport)
          (Finset.map mapping right.xSupport)
    simp [xorSupport, Finset.map_union, Finset.map_sdiff]
  · change
      Finset.map mapping
          (xorSupport left.zSupport right.zSupport) =
        xorSupport
          (Finset.map mapping left.zSupport)
          (Finset.map mapping right.zSupport)
    simp [xorSupport, Finset.map_union, Finset.map_sdiff]
  · change
      left.phase + right.phase +
          Pauli.parityPhase
            (supportParity (left.zSupport ∩ right.xSupport)) =
        left.phase + right.phase +
          Pauli.parityPhase
            (supportParity
              (Finset.map mapping left.zSupport ∩
                Finset.map mapping right.xSupport))
    rw [← Finset.map_inter]
    simp [supportParity]

@[simp]
theorem remap_inv {sourceSize targetSize : ℕ}
    (pauli : SparsePauli sourceSize)
    (mapping : Fin sourceSize ↪ Fin targetSize) :
    remap pauli⁻¹ mapping = (remap pauli mapping)⁻¹ := by
  change
    remap (inverse pauli) mapping =
      inverse (remap pauli mapping)
  apply SparsePauli.ext
  · rfl
  · rfl
  · change
      -pauli.phase +
          Pauli.parityPhase
            (supportParity (pauli.zSupport ∩ pauli.xSupport)) =
        -pauli.phase +
          Pauli.parityPhase
            (supportParity
              (Finset.map mapping pauli.zSupport ∩
                Finset.map mapping pauli.xSupport))
    rw [← Finset.map_inter]
    simp [supportParity]

end SparsePauli

/-- Coordinate projection along an injective ordered map. -/
def pullbackPauli {sourceSize targetSize : ℕ}
    (pauli : Pauli targetSize)
    (support : Fin sourceSize ↪ Fin targetSize) :
    Pauli sourceSize where
  x index := pauli.x (support index)
  z index := pauli.z (support index)
  phase := pauli.phase

namespace DensePauli

def projectAlong {sourceSize targetSize : ℕ}
    (pauli : DensePauli targetSize)
    (support : Fin sourceSize ↪ Fin targetSize) :
    DensePauli sourceSize :=
  ofPauli (pullbackPauli pauli.decode support)

@[simp]
theorem decode_projectAlong {sourceSize targetSize : ℕ}
    (pauli : DensePauli targetSize)
    (support : Fin sourceSize ↪ Fin targetSize) :
    (projectAlong pauli support).decode =
      pullbackPauli pauli.decode support := by
  simp [projectAlong]

@[simp]
theorem projectAlong_remap {sourceSize targetSize : ℕ}
    (pauli : SparsePauli sourceSize)
    (support : Fin sourceSize ↪ Fin targetSize) :
    projectAlong (pauli.remap support).toDense support =
      pauli.toDense := by
  apply decode_injective
  apply Pauli.ext
  · funext index
    simp [pullbackPauli]
  · funext index
    simp [pullbackPauli]
  · rfl

end DensePauli

namespace SparsePauli

/-- Every nonidentity coordinate is named by the ordered support map. -/
def SupportedOn {sourceSize targetSize : ℕ}
    (pauli : SparsePauli targetSize)
    (support : Fin sourceSize ↪ Fin targetSize) : Prop :=
  pauli.support ⊆ Finset.univ.map support

/-- Semantic `condense_from`: pull a fully covered sparse Pauli into packed
coordinates ordered by `support`. -/
def condense {sourceSize targetSize : ℕ}
    (pauli : SparsePauli targetSize)
    (support : Fin sourceSize ↪ Fin targetSize)
    (_coverage : SupportedOn pauli support) :
    DensePauli sourceSize :=
  DensePauli.ofPauli (pullbackPauli pauli.decode support)

@[simp]
theorem decode_condense {sourceSize targetSize : ℕ}
    (pauli : SparsePauli targetSize)
    (support : Fin sourceSize ↪ Fin targetSize)
    (coverage : SupportedOn pauli support) :
    (condense pauli support coverage).decode =
      pullbackPauli pauli.decode support := by
  simp [condense]

end SparsePauli

namespace DensePauli

/-- Semantic `remapped_sparse`: scatter packed coordinates through an
injective ordered support map. -/
def remap {sourceSize targetSize : ℕ}
    (pauli : DensePauli sourceSize)
    (support : Fin sourceSize ↪ Fin targetSize) :
    SparsePauli targetSize :=
  pauli.toSparse.remap support

@[simp]
theorem decode_remap_x {sourceSize targetSize : ℕ}
    (pauli : DensePauli sourceSize)
    (support : Fin sourceSize ↪ Fin targetSize)
    (index : Fin sourceSize) :
    (remap pauli support).decode.x (support index) =
      pauli.decode.x index := by
  simp [remap]

@[simp]
theorem decode_remap_z {sourceSize targetSize : ℕ}
    (pauli : DensePauli sourceSize)
    (support : Fin sourceSize ↪ Fin targetSize)
    (index : Fin sourceSize) :
    (remap pauli support).decode.z (support index) =
      pauli.decode.z index := by
  simp [remap]

theorem decode_remap_x_eq_zero_of_not_mem_range
    {sourceSize targetSize : ℕ}
    (pauli : DensePauli sourceSize)
    (support : Fin sourceSize ↪ Fin targetSize)
    (index : Fin targetSize)
    (outside : ∀ source, support source ≠ index) :
    (remap pauli support).decode.x index = 0 := by
  exact
    SparsePauli.decode_remap_x_eq_zero_of_not_mem_range
      pauli.toSparse support index outside

theorem decode_remap_z_eq_zero_of_not_mem_range
    {sourceSize targetSize : ℕ}
    (pauli : DensePauli sourceSize)
    (support : Fin sourceSize ↪ Fin targetSize)
    (index : Fin targetSize)
    (outside : ∀ source, support source ≠ index) :
    (remap pauli support).decode.z index = 0 := by
  exact
    SparsePauli.decode_remap_z_eq_zero_of_not_mem_range
      pauli.toSparse support index outside

theorem remap_injective {sourceSize targetSize : ℕ}
    (support : Fin sourceSize ↪ Fin targetSize) :
    Function.Injective fun pauli : DensePauli sourceSize =>
      remap pauli support := by
  intro left right equal
  have pulled :=
    congrArg
      (fun pauli : SparsePauli targetSize =>
        projectAlong pauli.toDense support)
      equal
  simpa [remap] using pulled

end DensePauli

@[simp]
theorem SparsePauli.remap_condense {sourceSize targetSize : ℕ}
    (pauli : SparsePauli targetSize)
    (support : Fin sourceSize ↪ Fin targetSize)
    (coverage : pauli.SupportedOn support) :
    (pauli.condense support coverage).remap support = pauli := by
  apply SparsePauli.decode_injective
  apply Pauli.ext
  · funext index
    by_cases in_range : ∃ source, support source = index
    · rcases in_range with ⟨source, rfl⟩
      simp [SparsePauli.condense, DensePauli.remap,
        pullbackPauli]
    · rw [DensePauli.decode_remap_x_eq_zero_of_not_mem_range
          _ support index (fun source equal => in_range ⟨source, equal⟩)]
      have not_mem : index ∉ pauli.xSupport := by
        intro member
        have support_member : index ∈ pauli.support := by
          simp [SparsePauli.support, member]
        rcases Finset.mem_map.mp (coverage support_member) with
          ⟨source, _, equal⟩
        exact in_range ⟨source, equal⟩
      simp [SparsePauli.decode, vectorOfSupport, not_mem]
  · funext index
    by_cases in_range : ∃ source, support source = index
    · rcases in_range with ⟨source, rfl⟩
      simp [SparsePauli.condense, DensePauli.remap,
        pullbackPauli]
    · rw [DensePauli.decode_remap_z_eq_zero_of_not_mem_range
          _ support index (fun source equal => in_range ⟨source, equal⟩)]
      have not_mem : index ∉ pauli.zSupport := by
        intro member
        have support_member : index ∈ pauli.support := by
          simp [SparsePauli.support, member]
        rcases Finset.mem_map.mp (coverage support_member) with
          ⟨source, _, equal⟩
        exact in_range ⟨source, equal⟩
      simp [SparsePauli.decode, vectorOfSupport, not_mem]
  · rfl

@[simp]
theorem DensePauli.toSparse_mul {m : ℕ}
    (left right : DensePauli m) :
    (left * right).toSparse = left.toSparse * right.toSparse := by
  apply SparsePauli.decode_injective
  simp

@[simp]
theorem DensePauli.toSparse_inv {m : ℕ}
    (pauli : DensePauli m) :
    pauli⁻¹.toSparse = pauli.toSparse⁻¹ := by
  apply SparsePauli.decode_injective
  simp

@[simp]
theorem SparsePauli.toDense_mul {m : ℕ}
    (left right : SparsePauli m) :
    (left * right).toDense = left.toDense * right.toDense := by
  apply DensePauli.decode_injective
  simp

@[simp]
theorem SparsePauli.toDense_inv {m : ℕ}
    (pauli : SparsePauli m) :
    pauli⁻¹.toDense = pauli.toDense⁻¹ := by
  apply DensePauli.decode_injective
  simp

@[simp]
theorem DensePauli.remap_mul {sourceSize targetSize : ℕ}
    (left right : DensePauli sourceSize)
    (support : Fin sourceSize ↪ Fin targetSize) :
    (left * right).remap support =
      left.remap support * right.remap support := by
  simp [DensePauli.remap]

@[simp]
theorem DensePauli.remap_inv {sourceSize targetSize : ℕ}
    (pauli : DensePauli sourceSize)
    (support : Fin sourceSize ↪ Fin targetSize) :
    pauli⁻¹.remap support = (pauli.remap support)⁻¹ := by
  simp [DensePauli.remap]

theorem SparsePauli.SupportedOn.mul
    {sourceSize targetSize : ℕ}
    {left right : SparsePauli targetSize}
    {support : Fin sourceSize ↪ Fin targetSize}
    (left_supported : left.SupportedOn support)
    (right_supported : right.SupportedOn support) :
    (left * right).SupportedOn support := by
  intro index member
  have member_union :
      index ∈ left.support ∪ right.support := by
    change
      index ∈
        xorSupport left.xSupport right.xSupport ∪
          xorSupport left.zSupport right.zSupport at member
    change
      index ∈
        (left.xSupport ∪ left.zSupport) ∪
          (right.xSupport ∪ right.zSupport)
    simp [xorSupport] at member ⊢
    tauto
  rcases Finset.mem_union.mp member_union with
    left_member | right_member
  · exact left_supported left_member
  · exact right_supported right_member

theorem SparsePauli.SupportedOn.inv
    {sourceSize targetSize : ℕ}
    {pauli : SparsePauli targetSize}
    {support : Fin sourceSize ↪ Fin targetSize}
    (supported : pauli.SupportedOn support) :
    pauli⁻¹.SupportedOn support := by
  change pauli.SupportedOn support
  exact supported

@[simp]
theorem SparsePauli.condense_mul
    {sourceSize targetSize : ℕ}
    (left right : SparsePauli targetSize)
    (support : Fin sourceSize ↪ Fin targetSize)
    (left_supported : left.SupportedOn support)
    (right_supported : right.SupportedOn support) :
    (left * right).condense support
        (left_supported.mul right_supported) =
      left.condense support left_supported *
        right.condense support right_supported := by
  apply DensePauli.remap_injective support
  simp

@[simp]
theorem SparsePauli.condense_inv
    {sourceSize targetSize : ℕ}
    (pauli : SparsePauli targetSize)
    (support : Fin sourceSize ↪ Fin targetSize)
    (supported : pauli.SupportedOn support) :
    pauli⁻¹.condense support supported.inv =
      (pauli.condense support supported)⁻¹ := by
  apply DensePauli.remap_injective support
  simp

end PaulimerFormal
