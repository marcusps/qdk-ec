import BinarFormal.Packed
import PaulimerFormal.Symplectic

/-! Binary-vector encoding shared by Pauli storage and matrix algorithms. -/

namespace PaulimerFormal

open BinarFormal.Packed

/-- The Boolean representative of a binary field element. -/
def boolOfF2 (bit : F2) : Bool :=
  if bit = 0 then false else true

@[simp]
theorem toF2_boolOfF2 (bit : F2) :
    Bool.toF2 (boolOfF2 bit) = bit := by
  fin_cases bit <;> rfl

/-- Pack a binary vector into BinarFormal's zero-padded representation. -/
def packVector {m : ℕ} (vector : Fin m → F2) : PackedVec m :=
  PackedVec.ofBoolFn m fun index =>
    if in_range : index < m then
      boolOfF2 (vector ⟨index, in_range⟩)
    else
      false

@[simp]
theorem decode_packVector {m : ℕ} (vector : Fin m → F2) :
    (packVector vector).decode = vector := by
  funext index
  simp [packVector]

@[simp]
theorem packVector_decode {m : ℕ} (vector : PackedVec m) :
    packVector vector.decode = vector := by
  apply PackedVec.ext_of_decode
  simp

end PaulimerFormal
