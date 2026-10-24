import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Physlib.Relativity.PauliMatrices.Basic
import PaulimerFormal.Symplectic

/-!
# Phase-aware Pauli algebra

This module gives storage-independent semantics for Paulimer's Pauli operators.
The phase convention is the Rust `xz` convention:

`i^phase X^x Z^z`.

The binary coordinates are ordered separately as X and Z vectors. Their
concatenation agrees with `PhaseVector` and the existing symplectic
formalization.
-/

namespace PaulimerFormal

open scoped BigOperators

abbrev PauliPhase := ZMod 4

@[ext]
structure ProjectivePauli (m : ℕ) where
  x : Fin m → F2
  z : Fin m → F2

namespace ProjectivePauli

variable {m : ℕ}

private def coordinateEquiv :
    ProjectivePauli m ≃ (Fin m → F2) × (Fin m → F2) where
  toFun pauli := (pauli.x, pauli.z)
  invFun coordinates := ⟨coordinates.1, coordinates.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (ProjectivePauli m) :=
  coordinateEquiv.addCommGroup

@[simp]
theorem x_zero : (0 : ProjectivePauli m).x = 0 := rfl

@[simp]
theorem z_zero : (0 : ProjectivePauli m).z = 0 := rfl

@[simp]
theorem x_add (left right : ProjectivePauli m) :
    (left + right).x = left.x + right.x := rfl

@[simp]
theorem z_add (left right : ProjectivePauli m) :
    (left + right).z = left.z + right.z := rfl

@[simp]
theorem x_neg (pauli : ProjectivePauli m) :
    (-pauli).x = -pauli.x := rfl

@[simp]
theorem z_neg (pauli : ProjectivePauli m) :
    (-pauli).z = -pauli.z := rfl

/-- Convert separate X/Z coordinates to the shared X-then-Z phase vector. -/
def toPhaseVector (pauli : ProjectivePauli m) : PhaseVector m
  | Sum.inl index => pauli.x index
  | Sum.inr index => pauli.z index

@[simp]
theorem toPhaseVector_inl (pauli : ProjectivePauli m) (index : Fin m) :
    pauli.toPhaseVector (Sum.inl index) = pauli.x index := rfl

@[simp]
theorem toPhaseVector_inr (pauli : ProjectivePauli m) (index : Fin m) :
    pauli.toPhaseVector (Sum.inr index) = pauli.z index := rfl

@[simp]
theorem toPhaseVector_comp_inl (pauli : ProjectivePauli m) :
    pauli.toPhaseVector ∘ Sum.inl = pauli.x := rfl

@[simp]
theorem toPhaseVector_comp_inr (pauli : ProjectivePauli m) :
    pauli.toPhaseVector ∘ Sum.inr = pauli.z := rfl

/-- Split an X-then-Z phase vector into projective Pauli coordinates. -/
def ofPhaseVector (vector : PhaseVector m) : ProjectivePauli m where
  x index := vector (Sum.inl index)
  z index := vector (Sum.inr index)

@[simp]
theorem ofPhaseVector_toPhaseVector (pauli : ProjectivePauli m) :
    ofPhaseVector pauli.toPhaseVector = pauli := by
  ext <;> rfl

@[simp]
theorem toPhaseVector_ofPhaseVector (vector : PhaseVector m) :
    (ofPhaseVector vector).toPhaseVector = vector := by
  funext index
  cases index <;> rfl

@[simp]
theorem toPhaseVector_zero :
    (0 : ProjectivePauli m).toPhaseVector = 0 := by
  funext index
  cases index <;> rfl

@[simp]
theorem toPhaseVector_add (left right : ProjectivePauli m) :
    (left + right).toPhaseVector =
      left.toPhaseVector + right.toPhaseVector := by
  funext index
  cases index <;> rfl

/-- The ordered sign contribution in
`(X^x Z^z) (X^x' Z^z') = (-1)^(z·x') X^(x+x') Z^(z+z')`. -/
def xzCross (left right : ProjectivePauli m) : F2 :=
  left.z ⬝ᵥ right.x

/-- The binary symplectic commutation pairing. -/
def commutationPairing (left right : ProjectivePauli m) : F2 :=
  xzCross left right + xzCross right left

@[simp]
theorem xzCross_zero_left (pauli : ProjectivePauli m) :
    xzCross 0 pauli = 0 := by
  simp [xzCross]

@[simp]
theorem xzCross_zero_right (pauli : ProjectivePauli m) :
    xzCross pauli 0 = 0 := by
  simp [xzCross]

theorem xzCross_add_left (first second right : ProjectivePauli m) :
    xzCross (first + second) right =
      xzCross first right + xzCross second right := by
  simp [xzCross, add_dotProduct]

theorem xzCross_add_right (left first second : ProjectivePauli m) :
    xzCross left (first + second) =
      xzCross left first + xzCross left second := by
  simp [xzCross, dotProduct_add]

@[simp]
theorem commutationPairing_self (pauli : ProjectivePauli m) :
    commutationPairing pauli pauli = 0 := by
  simp [commutationPairing]

theorem commutationPairing_comm (left right : ProjectivePauli m) :
    commutationPairing left right = commutationPairing right left := by
  simp [commutationPairing, add_comm]

theorem commutationPairing_add_left
    (first second right : ProjectivePauli m) :
    commutationPairing (first + second) right =
      commutationPairing first right +
        commutationPairing second right := by
  simp [commutationPairing, xzCross_add_left, xzCross_add_right]
  abel

theorem commutationPairing_add_right
    (left first second : ProjectivePauli m) :
    commutationPairing left (first + second) =
      commutationPairing left first +
        commutationPairing left second := by
  rw [commutationPairing_comm, commutationPairing_add_left]
  simp only [commutationPairing_comm]

theorem commutationPairing_eq_pairing
    (left right : ProjectivePauli m) :
    commutationPairing left right =
      pairing left.toPhaseVector right.toPhaseVector := by
  simp [commutationPairing, xzCross, pairing, omega, Matrix.J,
    Matrix.fromBlocks_mulVec, Matrix.dotProduct_block,
    Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_comm]
  rw [dotProduct_comm right.x left.z]
  abel

/-- A single X coordinate. -/
def singleX (index : Fin m) : ProjectivePauli m where
  x := Pi.single index 1
  z := 0

/-- A single Z coordinate. -/
def singleZ (index : Fin m) : ProjectivePauli m where
  x := 0
  z := Pi.single index 1

@[simp]
theorem commutationPairing_singleZ (pauli : ProjectivePauli m)
    (index : Fin m) :
    commutationPairing pauli (singleZ index) = pauli.x index := by
  simp [commutationPairing, xzCross, singleZ]

@[simp]
theorem commutationPairing_singleX (pauli : ProjectivePauli m)
    (index : Fin m) :
    commutationPairing pauli (singleX index) = pauli.z index := by
  simp [commutationPairing, xzCross, singleX, mul_comm]

theorem pairing_eq_zero_forall_iff (pauli : ProjectivePauli m) :
    (∀ other, commutationPairing pauli other = 0) ↔ pauli = 0 := by
  constructor
  · intro orthogonal
    ext index
    · simpa using orthogonal (singleZ index)
    · simpa using orthogonal (singleX index)
  · rintro rfl other
    simp [commutationPairing]

end ProjectivePauli

@[ext]
structure Pauli (m : ℕ) extends ProjectivePauli m where
  phase : PauliPhase

namespace Pauli

variable {m : ℕ}

/-- Forget the scalar phase. -/
def projective (pauli : Pauli m) : ProjectivePauli m :=
  pauli.toProjectivePauli

/-- Lift a projective Pauli with a chosen `xz` phase exponent. -/
def ofProjective (pauli : ProjectivePauli m) (phase : PauliPhase := 0) :
    Pauli m where
  toProjectivePauli := pauli
  phase := phase

@[simp]
theorem projective_ofProjective (pauli : ProjectivePauli m)
    (phase : PauliPhase) :
    (ofProjective pauli phase).projective = pauli := rfl

/-- Interpret an `F2` bit as `0` or `1` in the phase ring. -/
def bitPhase (bit : F2) : PauliPhase :=
  if bit = 0 then 0 else 1

/-- Interpret a binary parity as the sign exponent `0` or `2`. -/
def parityPhase (bit : F2) : PauliPhase :=
  2 * bitPhase bit

@[simp]
theorem bitPhase_zero : bitPhase 0 = 0 := by
  simp [bitPhase]

@[simp]
theorem bitPhase_one : bitPhase 1 = 1 := by
  simp [bitPhase]

@[simp]
theorem parityPhase_zero : parityPhase 0 = 0 := by
  simp [parityPhase]

@[simp]
theorem parityPhase_one : parityPhase 1 = 2 := by
  simp [parityPhase]

@[simp]
theorem parityPhase_add (left right : F2) :
    parityPhase (left + right) =
      parityPhase left + parityPhase right := by
  fin_cases left <;> fin_cases right <;> decide

theorem parityPhase_injective : Function.Injective parityPhase := by
  decide

@[simp]
theorem parityPhase_add_self (bit : F2) :
    parityPhase bit + parityPhase bit = 0 := by
  fin_cases bit <;> decide

@[simp]
theorem neg_parityPhase (bit : F2) :
    -parityPhase bit = parityPhase bit := by
  fin_cases bit <;> decide

theorem parityPhase_sum {index : Type*} [Fintype index]
    (bits : index → F2) :
    parityPhase (∑ position, bits position) =
      2 * ∑ position, bitPhase (bits position) := by
  classical
  induction (Finset.univ : Finset index) using Finset.induction_on with
  | empty => simp
  | @insert position positions not_mem induction =>
      rw [Finset.sum_insert not_mem, Finset.sum_insert not_mem,
        parityPhase_add, induction]
      simp [parityPhase, mul_add]

/-- Number of Y coordinates, represented modulo four. -/
def yCountPhase (pauli : ProjectivePauli m) : PauliPhase :=
  ∑ index, bitPhase (pauli.x index * pauli.z index)

theorem bitPhase_mul_eq_indicator (left right : F2) :
    bitPhase (left * right) =
      if left ≠ 0 ∧ right ≠ 0 then 1 else 0 := by
  fin_cases left <;> fin_cases right <;> decide

/-- Coordinates on which the Pauli acts nontrivially. -/
def support (pauli : ProjectivePauli m) : Finset (Fin m) :=
  Finset.univ.filter fun index =>
    pauli.x index ≠ 0 ∨ pauli.z index ≠ 0

/-- Coordinates carrying Y. -/
def ySupport (pauli : ProjectivePauli m) : Finset (Fin m) :=
  Finset.univ.filter fun index =>
    pauli.x index ≠ 0 ∧ pauli.z index ≠ 0

def weight (pauli : ProjectivePauli m) : ℕ :=
  (support pauli).card

def yWeight (pauli : ProjectivePauli m) : ℕ :=
  (ySupport pauli).card

theorem yCountPhase_eq_yWeight (pauli : ProjectivePauli m) :
    yCountPhase pauli = (yWeight pauli : PauliPhase) := by
  classical
  rw [yCountPhase, yWeight, ySupport]
  calc
    (∑ index, bitPhase (pauli.x index * pauli.z index)) =
        ∑ index, if pauli.x index ≠ 0 ∧ pauli.z index ≠ 0
          then (1 : PauliPhase) else 0 := by
      apply Finset.sum_congr rfl
      intro index _
      exact bitPhase_mul_eq_indicator _ _
    _ = ((Finset.univ.filter fun index =>
          pauli.x index ≠ 0 ∧ pauli.z index ≠ 0).card : PauliPhase) := by
      simp

theorem parityPhase_self_xzCross (pauli : ProjectivePauli m) :
    parityPhase (ProjectivePauli.xzCross pauli pauli) =
      2 * yCountPhase pauli := by
  simpa [ProjectivePauli.xzCross, dotProduct, yCountPhase, mul_comm] using
    parityPhase_sum (fun index => pauli.z index * pauli.x index)

/-- Rust's `xyz` phase exponent, where each Y already contributes one factor of `i`. -/
def xyzPhase (pauli : Pauli m) : PauliPhase :=
  pauli.phase + 3 * yCountPhase pauli.projective

/-- Construct an `xz`-encoded Pauli from an `xyz` phase exponent. -/
def ofXYZPhase (pauli : ProjectivePauli m) (phase : PauliPhase) :
    Pauli m :=
  ofProjective pauli (phase + yCountPhase pauli)

@[simp]
theorem xyzPhase_ofXYZPhase (pauli : ProjectivePauli m)
    (phase : PauliPhase) :
    xyzPhase (ofXYZPhase pauli phase) = phase := by
  change phase + yCountPhase pauli + 3 * yCountPhase pauli = phase
  have four_zero : (4 : PauliPhase) = 0 := by decide
  calc
    phase + yCountPhase pauli + 3 * yCountPhase pauli =
        phase + 4 * yCountPhase pauli := by ring
    _ = phase := by rw [four_zero, zero_mul, add_zero]

theorem phase_eq_xyzPhase_add_yCountPhase (pauli : Pauli m) :
    pauli.phase = pauli.xyzPhase + yCountPhase pauli.projective := by
  rw [xyzPhase]
  have four_zero : (4 : PauliPhase) = 0 := by decide
  calc
    pauli.phase =
        pauli.phase + 4 * yCountPhase pauli.projective := by
          rw [four_zero, zero_mul, add_zero]
    _ = pauli.phase + 3 * yCountPhase pauli.projective +
        yCountPhase pauli.projective := by ring

/-- Identity Pauli. -/
def identity : Pauli m where
  x := 0
  z := 0
  phase := 0

/-- Multiplication in Paulimer's `xz` phase convention. -/
def multiply (left right : Pauli m) : Pauli m where
  x := left.x + right.x
  z := left.z + right.z
  phase :=
    left.phase + right.phase +
      parityPhase
        (ProjectivePauli.xzCross left.projective right.projective)

/-- Group inverse in the `xz` phase convention. -/
def inverse (pauli : Pauli m) : Pauli m where
  x := pauli.x
  z := pauli.z
  phase :=
    -pauli.phase +
      parityPhase
        (ProjectivePauli.xzCross pauli.projective pauli.projective)

instance : One (Pauli m) := ⟨identity⟩

instance : Mul (Pauli m) := ⟨multiply⟩

instance : Inv (Pauli m) := ⟨inverse⟩

@[simp]
theorem projective_one : (1 : Pauli m).projective = 0 := rfl

@[simp]
theorem projective_mul (left right : Pauli m) :
    (left * right).projective =
      left.projective + right.projective := rfl

@[simp]
theorem projective_inv (pauli : Pauli m) :
    pauli⁻¹.projective = pauli.projective := rfl

@[simp]
theorem phase_one : (1 : Pauli m).phase = 0 := rfl

@[simp]
theorem phase_mul (left right : Pauli m) :
    (left * right).phase =
      left.phase + right.phase +
        parityPhase
          (ProjectivePauli.xzCross left.projective right.projective) := rfl

@[simp]
theorem phase_inv (pauli : Pauli m) :
    pauli⁻¹.phase =
      -pauli.phase +
        parityPhase
          (ProjectivePauli.xzCross pauli.projective pauli.projective) := rfl

instance : Group (Pauli m) where
  mul_assoc left middle right := by
    apply Pauli.ext
    · exact add_assoc left.x middle.x right.x
    · exact add_assoc left.z middle.z right.z
    · simp only [phase_mul, projective_mul,
        ProjectivePauli.xzCross_add_left,
        ProjectivePauli.xzCross_add_right, parityPhase_add]
      abel
  one_mul pauli := by
    apply Pauli.ext
    · exact zero_add pauli.x
    · exact zero_add pauli.z
    · simp
  mul_one pauli := by
    apply Pauli.ext
    · exact add_zero pauli.x
    · exact add_zero pauli.z
    · simp
  inv_mul_cancel pauli := by
    apply Pauli.ext
    · funext index
      exact f2_add_self (pauli.x index)
    · funext index
      exact f2_add_self (pauli.z index)
    · change
        (-pauli.phase +
            parityPhase
              (ProjectivePauli.xzCross pauli.projective pauli.projective)) +
          pauli.phase +
          parityPhase
            (ProjectivePauli.xzCross pauli.projective pauli.projective) = 0
      calc
        _ = parityPhase
              (ProjectivePauli.xzCross pauli.projective pauli.projective) +
            parityPhase
              (ProjectivePauli.xzCross pauli.projective pauli.projective) := by
              abel
        _ = 0 := parityPhase_add_self _

/-- Multiplication forgets to addition of projective binary coordinates. -/
def projectiveHom : Pauli m →* Multiplicative (ProjectivePauli m) where
  toFun pauli := Multiplicative.ofAdd pauli.projective
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Multiplication by the scalar phase `-1`. -/
def negate (pauli : Pauli m) : Pauli m :=
  ofProjective pauli.projective (pauli.phase + 2)

instance : Neg (Pauli m) := ⟨negate⟩

@[simp]
theorem projective_neg (pauli : Pauli m) :
    (-pauli).projective = pauli.projective := rfl

@[simp]
theorem phase_neg (pauli : Pauli m) :
    (-pauli).phase = pauli.phase + 2 := rfl

@[simp]
theorem neg_neg (pauli : Pauli m) :
    -(-pauli) = pauli := by
  apply Pauli.ext
  · rfl
  · rfl
  · change pauli.phase + 2 + 2 = pauli.phase
    have two_add_two : (2 : PauliPhase) + 2 = 0 := by decide
    rw [add_assoc, two_add_two, add_zero]

/-- Symbolic complex conjugation in the `xz` convention, where X and Z are real. -/
def complexConjugate (pauli : Pauli m) : Pauli m :=
  ofProjective pauli.projective (-pauli.phase)

@[simp]
theorem projective_complexConjugate (pauli : Pauli m) :
    pauli.complexConjugate.projective = pauli.projective := rfl

@[simp]
theorem phase_complexConjugate (pauli : Pauli m) :
    pauli.complexConjugate.phase = -pauli.phase := rfl

@[simp]
theorem complexConjugate_complexConjugate (pauli : Pauli m) :
    pauli.complexConjugate.complexConjugate = pauli := by
  apply Pauli.ext
  · rfl
  · rfl
  · simp

/-- Rust's `invert` implementation: conjugate the phase and negate exactly
when the X/Z overlap has odd parity. -/
theorem inverse_eq_complexConjugate_mul_sign (pauli : Pauli m) :
    pauli⁻¹ =
      ofProjective pauli.projective
        (pauli.complexConjugate.phase +
          parityPhase
            (ProjectivePauli.xzCross
              pauli.projective pauli.projective)) := by
  rfl

/-- Two phase sign contributions agree exactly when their binary parities agree. -/
theorem parityPhase_eq_iff (left right : F2) :
    parityPhase left = parityPhase right ↔ left = right :=
  parityPhase_injective.eq_iff

theorem f2_add_eq_zero_iff_eq (left right : F2) :
    left + right = 0 ↔ left = right := by
  constructor
  · intro sum_zero
    have equal_negative := eq_neg_of_add_eq_zero_left sum_zero
    simpa using equal_negative
  · intro equal
    subst right
    exact f2_add_self left

theorem f2_eq_zero_or_one (bit : F2) :
    bit = 0 ∨ bit = 1 := by
  fin_cases bit
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Algebraic commutation is exactly vanishing symplectic pairing. -/
theorem mul_comm_iff_commutationPairing_eq_zero
    (left right : Pauli m) :
    left * right = right * left ↔
      ProjectivePauli.commutationPairing
        left.projective right.projective = 0 := by
  constructor
  · intro products_equal
    have phases_equal := congrArg Pauli.phase products_equal
    have signs_equal :
        parityPhase
            (ProjectivePauli.xzCross left.projective right.projective) =
          parityPhase
            (ProjectivePauli.xzCross right.projective left.projective) := by
      apply add_left_cancel
        (a := left.phase + right.phase)
      simpa [add_assoc, add_comm, add_left_comm] using phases_equal
    apply (f2_add_eq_zero_iff_eq _ _).mpr
    exact parityPhase_injective signs_equal
  · intro pairing_zero
    have crosses_equal :
        ProjectivePauli.xzCross left.projective right.projective =
          ProjectivePauli.xzCross right.projective left.projective := by
      exact (f2_add_eq_zero_iff_eq _ _).mp pairing_zero
    apply Pauli.ext
    · exact add_comm left.x right.x
    · exact add_comm left.z right.z
    · simp only [phase_mul, crosses_equal]
      abel

theorem commute_iff_commutationPairing_eq_zero
    (left right : Pauli m) :
    Commute left right ↔
      ProjectivePauli.commutationPairing
        left.projective right.projective = 0 :=
  mul_comm_iff_commutationPairing_eq_zero left right

theorem parityPhase_eq_add_two_iff (left right : F2) :
    parityPhase left = parityPhase right + 2 ↔ left + right = 1 := by
  fin_cases left <;> fin_cases right <;> decide

/-- Paulis anticommute exactly when their symplectic pairing is one. -/
theorem mul_eq_neg_mul_iff_commutationPairing_eq_one
    (left right : Pauli m) :
    left * right = -(right * left) ↔
      ProjectivePauli.commutationPairing
        left.projective right.projective = 1 := by
  constructor
  · intro products_equal
    have phases_equal := congrArg Pauli.phase products_equal
    apply (parityPhase_eq_add_two_iff _ _).mp
    apply add_left_cancel
      (a := left.phase + right.phase)
    simpa [add_assoc, add_comm, add_left_comm] using phases_equal
  · intro pairing_one
    have signs_equal :
        parityPhase
            (ProjectivePauli.xzCross left.projective right.projective) =
          parityPhase
              (ProjectivePauli.xzCross right.projective left.projective) +
            2 :=
      (parityPhase_eq_add_two_iff _ _).mpr pairing_one
    apply Pauli.ext
    · exact add_comm left.x right.x
    · exact add_comm left.z right.z
    · simp only [phase_mul, phase_neg, signs_equal]
      abel

/-- The center consists exactly of scalar phases. -/
theorem mem_center_iff_projective_eq_zero (pauli : Pauli m) :
    pauli ∈ Subgroup.center (Pauli m) ↔ pauli.projective = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro central
    apply
      (ProjectivePauli.pairing_eq_zero_forall_iff
        pauli.projective).mp
    intro other
    apply
      (mul_comm_iff_commutationPairing_eq_zero
        pauli (ofProjective other 0)).mp
    exact (central (ofProjective other 0)).symm
  · intro projective_zero other
    apply
      (mul_comm_iff_commutationPairing_eq_zero
        other pauli).mpr
    rw [projective_zero]
    simp [ProjectivePauli.commutationPairing]

/-- The semantic property tested by Rust's `is_order_two`. -/
def IsOrderTwo (pauli : Pauli m) : Prop :=
  pauli * pauli = 1

/-- The self-inverse criterion corresponding to Hermiticity for unitary Paulis. -/
def IsHermitian (pauli : Pauli m) : Prop :=
  pauli⁻¹ = pauli

theorem isHermitian_iff_isOrderTwo (pauli : Pauli m) :
    IsHermitian pauli ↔ IsOrderTwo pauli := by
  exact inv_eq_iff_mul_eq_one

theorem add_self_add_parityPhase_eq_zero_iff
    (phase : PauliPhase) (bit : F2) :
    phase + phase + parityPhase bit = 0 ↔
      phase + phase = parityPhase bit := by
  constructor
  · intro equals_zero
    exact
      (eq_neg_of_add_eq_zero_left equals_zero).trans
        (neg_parityPhase bit)
  · intro equals_parity
    rw [equals_parity, parityPhase_add_self]

theorem isOrderTwo_iff_phase (pauli : Pauli m) :
    IsOrderTwo pauli ↔
      pauli.phase + pauli.phase =
        parityPhase
          (ProjectivePauli.xzCross
            pauli.projective pauli.projective) := by
  rw [IsOrderTwo]
  constructor
  · intro square_one
    have phase_equal := congrArg Pauli.phase square_one
    apply
      (add_self_add_parityPhase_eq_zero_iff
        pauli.phase
        (ProjectivePauli.xzCross
          pauli.projective pauli.projective)).mp
    simpa using phase_equal
  · intro phase_condition
    apply Pauli.ext
    · funext index
      exact f2_add_self (pauli.x index)
    · funext index
      exact f2_add_self (pauli.z index)
    · apply
        (add_self_add_parityPhase_eq_zero_iff
          pauli.phase
          (ProjectivePauli.xzCross
            pauli.projective pauli.projective)).mpr
      exact phase_condition

/-- The canonical representative with zero `xyz` phase. -/
def positiveRepresentative (pauli : ProjectivePauli m) : Pauli m :=
  ofXYZPhase pauli 0

@[simp]
theorem projective_positiveRepresentative (pauli : ProjectivePauli m) :
    (positiveRepresentative pauli).projective = pauli := rfl

@[simp]
theorem phase_positiveRepresentative (pauli : ProjectivePauli m) :
    (positiveRepresentative pauli).phase = yCountPhase pauli := by
  simp [positiveRepresentative, ofXYZPhase, ofProjective]

@[simp]
theorem xyzPhase_positiveRepresentative (pauli : ProjectivePauli m) :
    xyzPhase (positiveRepresentative pauli) = 0 :=
  xyzPhase_ofXYZPhase pauli 0

theorem positiveRepresentative_isOrderTwo (pauli : ProjectivePauli m) :
    IsOrderTwo (positiveRepresentative pauli) := by
  apply (isOrderTwo_iff_phase _).mpr
  simp only [phase_positiveRepresentative,
    projective_positiveRepresentative]
  rw [parityPhase_self_xzCross]
  ring

theorem positiveRepresentative_unique
    (pauli : Pauli m) (projective : ProjectivePauli m)
    (same_projective : pauli.projective = projective)
    (positive : pauli.xyzPhase = 0) :
    pauli = positiveRepresentative projective := by
  apply Pauli.ext
  · exact congrArg ProjectivePauli.x same_projective
  · exact congrArg ProjectivePauli.z same_projective
  · rw [phase_eq_xyzPhase_add_yCountPhase, positive, zero_add,
      same_projective]
    rw [phase_positiveRepresentative]

@[simp]
theorem neg_mul (left right : Pauli m) :
    (-left) * right = -(left * right) := by
  apply Pauli.ext
  · rfl
  · rfl
  · simp only [phase_mul, phase_neg, projective_neg]
    abel

@[simp]
theorem mul_neg (left right : Pauli m) :
    left * (-right) = -(left * right) := by
  apply Pauli.ext
  · rfl
  · rfl
  · simp only [phase_mul, phase_neg, projective_neg]
    abel

/-- Conjugation by a phase-aware Pauli. -/
def conjugate (conjugator target : Pauli m) : Pauli m :=
  conjugator * target * conjugator⁻¹

theorem conjugate_eq_of_commutationPairing_eq_zero
    (conjugator target : Pauli m)
    (commutes :
      ProjectivePauli.commutationPairing
        conjugator.projective target.projective = 0) :
    conjugate conjugator target = target := by
  rw [conjugate,
    (mul_comm_iff_commutationPairing_eq_zero
      conjugator target).mpr commutes]
  simp

theorem conjugate_eq_neg_of_commutationPairing_eq_one
    (conjugator target : Pauli m)
    (anticommutes :
      ProjectivePauli.commutationPairing
        conjugator.projective target.projective = 1) :
    conjugate conjugator target = -target := by
  rw [conjugate,
    (mul_eq_neg_mul_iff_commutationPairing_eq_one
      conjugator target).mpr anticommutes,
    neg_mul]
  simp

theorem conjugate_eq_if (conjugator target : Pauli m) :
    conjugate conjugator target =
      if ProjectivePauli.commutationPairing
          conjugator.projective target.projective = 0
      then target
      else -target := by
  by_cases commutes :
      ProjectivePauli.commutationPairing
        conjugator.projective target.projective = 0
  · rw [ite_eq_left commutes,
      conjugate_eq_of_commutationPairing_eq_zero
        conjugator target commutes]
  · have anticommutes :
        ProjectivePauli.commutationPairing
          conjugator.projective target.projective = 1 := by
      generalize
        ProjectivePauli.commutationPairing
          conjugator.projective target.projective = pairing at commutes ⊢
      fin_cases pairing
      · exact (commutes rfl).elim
      · rfl
    rw [ite_eq_right commutes,
      conjugate_eq_neg_of_commutationPairing_eq_one
        conjugator target anticommutes]

theorem four_add_phase (phase : PauliPhase) :
    phase + phase + phase + phase = 0 := by
  fin_cases phase <;> decide

theorem mul_self_mul_self_eq_one (pauli : Pauli m) :
    (pauli * pauli) * (pauli * pauli) = 1 := by
  have square_projective :
      (pauli * pauli).projective = 0 := by
    apply ProjectivePauli.ext
    · funext index
      exact f2_add_self (pauli.x index)
    · funext index
      exact f2_add_self (pauli.z index)
  apply Pauli.ext
  · rw [show ((pauli * pauli) * (pauli * pauli)).x =
        (pauli * pauli).x + (pauli * pauli).x from rfl]
    funext index
    exact f2_add_self ((pauli * pauli).x index)
  · rw [show ((pauli * pauli) * (pauli * pauli)).z =
        (pauli * pauli).z + (pauli * pauli).z from rfl]
    funext index
    exact f2_add_self ((pauli * pauli).z index)
  · simp only [phase_mul, square_projective,
      ProjectivePauli.xzCross_zero_left, parityPhase_zero, add_zero]
    calc
      (pauli.phase + pauli.phase +
            parityPhase
              (ProjectivePauli.xzCross
                pauli.projective pauli.projective)) +
          (pauli.phase + pauli.phase +
            parityPhase
              (ProjectivePauli.xzCross
                pauli.projective pauli.projective)) =
          (pauli.phase + pauli.phase + pauli.phase + pauli.phase) +
            (parityPhase
                (ProjectivePauli.xzCross
                  pauli.projective pauli.projective) +
              parityPhase
                (ProjectivePauli.xzCross
                  pauli.projective pauli.projective)) := by
            abel
      _ = 0 := by
        rw [four_add_phase, parityPhase_add_self, add_zero]

theorem pow_four_eq_one (pauli : Pauli m) :
    pauli ^ 4 = 1 := by
  simpa [pow_succ, mul_assoc] using mul_self_mul_self_eq_one pauli

theorem orderOf_dvd_four (pauli : Pauli m) :
    orderOf pauli ∣ 4 :=
  orderOf_dvd_of_pow_eq_one (pow_four_eq_one pauli)

/-! ## Concrete one-qubit bridge -/

/-- The complex scalar represented by a phase exponent. -/
noncomputable def phaseScalar (phase : PauliPhase) : ℂ :=
  AddChar.zmodChar 4 Complex.I_pow_four phase

@[simp]
theorem phaseScalar_zero : phaseScalar 0 = 1 := by
  exact AddChar.map_zero_eq_one
    (AddChar.zmodChar 4 Complex.I_pow_four)

@[simp]
theorem phaseScalar_one : phaseScalar 1 = Complex.I := by
  simpa [phaseScalar] using
    (AddChar.zmodChar_apply'
      (n := 4) Complex.I_pow_four 1)

@[simp]
theorem phaseScalar_two : phaseScalar 2 = -1 := by
  calc
    phaseScalar 2 = Complex.I ^ 2 := by
      simpa [phaseScalar] using
        (AddChar.zmodChar_apply'
          (n := 4) Complex.I_pow_four 2)
    _ = -1 := Complex.I_sq

@[simp]
theorem phaseScalar_three : phaseScalar 3 = -Complex.I := by
  calc
    phaseScalar 3 = Complex.I ^ 3 := by
      simpa [phaseScalar] using
        (AddChar.zmodChar_apply'
          (n := 4) Complex.I_pow_four 3)
    _ = -Complex.I := by
      rw [pow_succ, Complex.I_sq, neg_one_mul]

theorem phaseScalar_add (left right : PauliPhase) :
    phaseScalar (left + right) =
      phaseScalar left * phaseScalar right := by
  exact AddChar.map_add_eq_mul
    (AddChar.zmodChar 4 Complex.I_pow_four) left right

/-- The X/Z matrix word for a projective one-qubit Pauli. -/
noncomputable def oneQubitProjectiveMatrix
    (pauli : ProjectivePauli 1) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (if pauli.x 0 = 0 then
      1
    else
      PauliMatrix.pauliMatrix (Sum.inr 0)) *
    (if pauli.z 0 = 0 then
      1
    else
      PauliMatrix.pauliMatrix (Sum.inr 2))

/-- Matrix semantics for one qubit, using Physlib's audited Pauli matrices. -/
noncomputable def oneQubitMatrix (pauli : Pauli 1) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  phaseScalar pauli.phase • oneQubitProjectiveMatrix pauli.projective

theorem oneQubitProjectiveMatrix_add
    (left right : ProjectivePauli 1) :
    oneQubitProjectiveMatrix left *
        oneQubitProjectiveMatrix right =
      phaseScalar
          (parityPhase (ProjectivePauli.xzCross left right)) •
        oneQubitProjectiveMatrix (left + right) := by
  rcases f2_eq_zero_or_one (left.x 0) with left_x | left_x <;>
    rcases f2_eq_zero_or_one (left.z 0) with left_z | left_z <;>
    rcases f2_eq_zero_or_one (right.x 0) with right_x | right_x <;>
    rcases f2_eq_zero_or_one (right.z 0) with right_z | right_z <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    norm_num [oneQubitProjectiveMatrix,
      ProjectivePauli.xzCross, dotProduct,
      left_x, left_z, right_x, right_z,
      parityPhase, bitPhase, PauliMatrix.pauliMatrix,
      Matrix.mul_apply, Complex.I_mul_I]

@[simp]
theorem oneQubitMatrix_one :
    oneQubitMatrix (1 : Pauli 1) = 1 := by
  simp [oneQubitMatrix, oneQubitProjectiveMatrix]

theorem oneQubitMatrix_mul (left right : Pauli 1) :
    oneQubitMatrix (left * right) =
      oneQubitMatrix left * oneQubitMatrix right := by
  rw [oneQubitMatrix, oneQubitMatrix, oneQubitMatrix,
    smul_mul_smul, oneQubitProjectiveMatrix_add, smul_smul]
  congr 1
  simp [phaseScalar_add, mul_assoc]

/-- The phase-aware one-qubit Pauli representation in Physlib matrices. -/
noncomputable def oneQubitMatrixHom :
    Pauli 1 →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := oneQubitMatrix
  map_one' := oneQubitMatrix_one
  map_mul' := oneQubitMatrix_mul

/-- Symbolic one-qubit X. -/
def oneQubitX : Pauli 1 :=
  ofProjective (ProjectivePauli.singleX 0) 0

/-- Symbolic one-qubit Z. -/
def oneQubitZ : Pauli 1 :=
  ofProjective (ProjectivePauli.singleZ 0) 0

/-- Symbolic positive one-qubit Y (`Y = iXZ`). -/
def oneQubitY : Pauli 1 where
  x := 1
  z := 1
  phase := 1

theorem oneQubitMatrix_x :
    oneQubitMatrix oneQubitX =
      PauliMatrix.pauliMatrix (Sum.inr 0) := by
  simp [oneQubitMatrix, oneQubitX, ofProjective,
    oneQubitProjectiveMatrix, ProjectivePauli.singleX, projective]

theorem oneQubitMatrix_z :
    oneQubitMatrix oneQubitZ =
      PauliMatrix.pauliMatrix (Sum.inr 2) := by
  simp [oneQubitMatrix, oneQubitZ, ofProjective,
    oneQubitProjectiveMatrix, ProjectivePauli.singleZ, projective]

theorem oneQubitMatrix_y :
    oneQubitMatrix oneQubitY =
      PauliMatrix.pauliMatrix (Sum.inr 1) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [oneQubitMatrix, oneQubitY,
      oneQubitProjectiveMatrix, projective,
      PauliMatrix.pauliMatrix, Matrix.mul_apply]

end Pauli

end PaulimerFormal
