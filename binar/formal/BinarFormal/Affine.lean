import BinarFormal.Solve

/-!
# Packed affine maps

This module mirrors `AffineMap::apply` and `AffineMap::dot` from
`binar/src/affine_map.rs`. It proves their packed implementations refine affine
maps over `F2`; Rust allocation and representation safety remain outside the
semantic model.
-/

namespace BinarFormal.Packed

open Matrix

/-- A packed affine map `x ↦ A x + b`. -/
structure AffineMap (inputDimension outputDimension : Nat) where
  matrix : PackedMatrix outputDimension inputDimension
  shift : PackedVec outputDimension

namespace AffineMap

variable {input middle output : Nat}

/-- Evaluate a packed affine map, mirroring `AffineMap::apply`. -/
def apply (map : AffineMap input output) (value : PackedVec input) :
    PackedVec output :=
  (map.matrix.mulVec value).xor map.shift

/-- Decode a packed affine map to its Mathlib semantics. -/
def decode (map : AffineMap input output) (value : Fin input → F2) :
    Fin output → F2 :=
  map.matrix.decode *ᵥ value + map.shift.decode

/-- Packed application refines the decoded affine map. -/
theorem decode_apply (map : AffineMap input output) (value : PackedVec input) :
    (map.apply value).decode = map.decode value.decode := by
  rw [apply, PackedVec.decode_xor, PackedMatrix.decode_mulVec]
  rfl

/-- Composition `outer ∘ inner`, mirroring `AffineMap::dot`. -/
def compose (outer : AffineMap middle output)
    (inner : AffineMap input middle) : AffineMap input output where
  matrix := outer.matrix.m4riMul inner.matrix
  shift := (outer.matrix.mulVec inner.shift).xor outer.shift

/-- Decoding composition gives ordinary affine-function composition. -/
theorem decode_compose (outer : AffineMap middle output)
    (inner : AffineMap input middle) (value : Fin input → F2) :
    (outer.compose inner).decode value = outer.decode (inner.decode value) := by
  simp only [compose, decode, PackedMatrix.decode_m4riMul,
    PackedVec.decode_xor, PackedMatrix.decode_mulVec]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  ac_rfl

/-- The executable packed composition has the Rust `self(other(x))` orientation. -/
theorem apply_compose (outer : AffineMap middle output)
    (inner : AffineMap input middle) (value : PackedVec input) :
    (outer.compose inner).apply value = outer.apply (inner.apply value) := by
  apply PackedVec.ext_of_decode
  rw [decode_apply, decode_compose, decode_apply, decode_apply]

end AffineMap

end BinarFormal.Packed
