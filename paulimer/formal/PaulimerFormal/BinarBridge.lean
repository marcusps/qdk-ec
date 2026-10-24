import BinarFormal
import Mathlib.Logic.Equiv.Fin.Basic
import PaulimerFormal.Symplectic

/-!
# Bridges to BinarFormal

Paulimer orders binary Pauli coordinates as `X` followed by `Z`. BinarFormal
uses ordinary `Fin` indices. This module records that convention explicitly
and reuses BinarFormal's packed decoders without duplicating its algorithms.
-/

namespace PaulimerFormal.BinarBridge

open BinarFormal.Packed

abbrev PackedPhaseVector (m : ℕ) := PackedVec (m + m)

abbrev PackedActionMatrix (m : ℕ) := PackedMatrix (m + m) (m + m)

/-- Paulimer's `X`-then-`Z` coordinate order as a contiguous finite index. -/
def phaseIndexEquiv (m : ℕ) : PhaseIndex m ≃ Fin (m + m) :=
  finSumFinEquiv

@[simp]
theorem phaseIndexEquiv_inl {m : ℕ} (index : Fin m) :
    phaseIndexEquiv m (Sum.inl index) = Fin.castAdd m index :=
  finSumFinEquiv_apply_left index

@[simp]
theorem phaseIndexEquiv_inr {m : ℕ} (index : Fin m) :
    phaseIndexEquiv m (Sum.inr index) = Fin.natAdd m index :=
  finSumFinEquiv_apply_right index

/-- Reindex a contiguous binary vector into Paulimer's phase-space order. -/
def ofFinVector {m : ℕ} (vector : Fin (m + m) → F2) : PhaseVector m :=
  vector ∘ phaseIndexEquiv m

/-- Reindex a Paulimer phase vector into contiguous `X`-then-`Z` order. -/
def toFinVector {m : ℕ} (vector : PhaseVector m) : Fin (m + m) → F2 :=
  vector ∘ (phaseIndexEquiv m).symm

@[simp]
theorem ofFinVector_toFinVector {m : ℕ} (vector : PhaseVector m) :
    ofFinVector (toFinVector vector) = vector := by
  funext index
  simp [ofFinVector, toFinVector]

@[simp]
theorem toFinVector_ofFinVector {m : ℕ}
    (vector : Fin (m + m) → F2) :
    toFinVector (ofFinVector vector) = vector := by
  funext index
  simp [ofFinVector, toFinVector]

/-- Decode a packed Binar vector as a Paulimer phase vector. -/
def decodePhaseVector {m : ℕ} (vector : PackedPhaseVector m) :
    PhaseVector m :=
  ofFinVector vector.decode

@[simp]
theorem decodePhaseVector_apply {m : ℕ}
    (vector : PackedPhaseVector m) (index : PhaseIndex m) :
    decodePhaseVector vector index =
      vector.decode (phaseIndexEquiv m index) := rfl

@[simp]
theorem decodePhaseVector_x {m : ℕ}
    (vector : PackedPhaseVector m) (index : Fin m) :
    decodePhaseVector vector (Sum.inl index) =
      vector.decode (Fin.castAdd m index) := by
  rw [decodePhaseVector_apply, phaseIndexEquiv_inl]

@[simp]
theorem decodePhaseVector_z {m : ℕ}
    (vector : PackedPhaseVector m) (index : Fin m) :
    decodePhaseVector vector (Sum.inr index) =
      vector.decode (Fin.natAdd m index) := by
  rw [decodePhaseVector_apply, phaseIndexEquiv_inr]

/-- Decode a packed Binar matrix in Paulimer's phase-space row/column order. -/
def decodeActionMatrix {m : ℕ} (matrix : PackedActionMatrix m) :
    ActionMatrix m :=
  (Matrix.reindex (phaseIndexEquiv m).symm
    (phaseIndexEquiv m).symm) matrix.decode

@[simp]
theorem decodeActionMatrix_apply {m : ℕ}
    (matrix : PackedActionMatrix m) (row column : PhaseIndex m) :
    decodeActionMatrix matrix row column =
      matrix.decode (phaseIndexEquiv m row) (phaseIndexEquiv m column) := by
  simp [decodeActionMatrix, Matrix.reindex_apply]

theorem decodeActionMatrix_transpose {m : ℕ}
    (matrix : PackedActionMatrix m) :
    decodeActionMatrix matrix.transpose =
      Matrix.transpose (decodeActionMatrix matrix) := by
  rw [decodeActionMatrix, PackedMatrix.decode_transpose]
  exact
    (Matrix.transpose_reindex (phaseIndexEquiv m).symm
      (phaseIndexEquiv m).symm matrix.decode).symm

/-- Binar's packed matrix-vector multiplication refines Paulimer's phase-space action. -/
theorem decodePhaseVector_mulVec {m : ℕ}
    (matrix : PackedActionMatrix m) (vector : PackedPhaseVector m) :
    decodePhaseVector (matrix.mulVec vector) =
      (decodeActionMatrix matrix).mulVec (decodePhaseVector vector) := by
  rw [decodePhaseVector, PackedMatrix.decode_mulVec]
  funext row
  simp only [ofFinVector, Function.comp_apply, decodeActionMatrix,
    Matrix.mulVec, Matrix.reindex_apply, dotProduct]
  exact
    ((phaseIndexEquiv m).sum_comp
      (fun column =>
        matrix.decode (phaseIndexEquiv m row) column *
          vector.decode column)).symm

/-- Binar's packed right action refines Paulimer's row-vector action convention. -/
theorem decodePhaseVector_rightMultiply {m : ℕ}
    (matrix : PackedActionMatrix m) (vector : PackedPhaseVector m) :
    decodePhaseVector (matrix.rightMultiply vector) =
      rowAction (decodePhaseVector vector) (decodeActionMatrix matrix) := by
  rw [decodePhaseVector, PackedMatrix.decode_rightMultiply]
  funext column
  simp only [ofFinVector, Function.comp_apply, rowAction,
    decodeActionMatrix, Matrix.vecMul, Matrix.reindex_apply, dotProduct]
  exact
    ((phaseIndexEquiv m).sum_comp
      (fun row =>
        vector.decode row *
          matrix.decode row (phaseIndexEquiv m column))).symm

theorem phaseVector_zero_unique (vector : PhaseVector 0) :
    vector = 0 :=
  Subsingleton.elim _ _

end PaulimerFormal.BinarBridge
