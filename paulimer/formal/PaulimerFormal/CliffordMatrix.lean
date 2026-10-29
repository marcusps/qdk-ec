import PaulimerFormal.PauliQuarterTurn
import PaulimerFormal.CliffordUniqueness

/-! Concrete unitary realization of signed Clifford actions and valid tableaux. -/

namespace PaulimerFormal.CliffordMatrix

open Pauli CliffordAction

variable {m : ℕ}

def Represents (unitary : OperatorMatrix m) (action : CliffordAction m) : Prop :=
  ∀ pauli, unitary * matrix pauli * unitary.conjTranspose = matrix (image action pauli)

theorem represents_one : Represents (1 : OperatorMatrix m) 1 := by
  intro pauli
  simp [image_one]

theorem represents_mul {left right : OperatorMatrix m} {first second : CliffordAction m}
    (left_represents : Represents left first) (right_represents : Represents right second) :
    Represents (left * right) (first * second) := by
  intro pauli
  rw [Matrix.conjTranspose_mul]
  calc
    (left * right) * matrix pauli * (right.conjTranspose * left.conjTranspose) =
        left * (right * matrix pauli * right.conjTranspose) * left.conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = matrix (image (first * second) pauli) := by
      rw [right_represents, left_represents, image_comp]

theorem represents_quarterTurn (exponent : Pauli m) (hermitian : exponent.IsOrderTwo) :
    Represents (quarterMatrix exponent) (quarterTurn exponent hermitian) :=
  fun pauli => quarterMatrix_conjugation pauli exponent hermitian

theorem represents_pauliConjugation (correction : Pauli m) :
    Represents (matrix correction) (pauliConjugation correction) := by
  intro pauli
  change matrix correction * matrix pauli * (matrix correction).conjTranspose =
    matrix (correction * pauli * correction⁻¹)
  rw [matrix_mul, matrix_mul, matrix_inv]

noncomputable def rotationMatrix : List (PhaseVector m) → OperatorMatrix m
  | [] => 1
  | center :: centers =>
      rotationMatrix centers * quarterMatrix (positiveRepresentative (ProjectivePauli.ofPhaseVector center))

theorem rotationMatrix_spec (centers : List (PhaseVector m)) :
    rotationMatrix centers ∈ Matrix.unitaryGroup (ComputationalBasis m) ℂ ∧
      Represents (rotationMatrix centers) (rotations centers) := by
  induction centers with
  | nil => exact ⟨(Matrix.unitaryGroup _ _).one_mem, represents_one⟩
  | cons center centers induction =>
    exact ⟨(Matrix.unitaryGroup _ _).mul_mem induction.1
      (quarterMatrix_unitary _ (positiveRepresentative_isOrderTwo _)),
      represents_mul induction.2 (represents_quarterTurn _ (positiveRepresentative_isOrderTwo _))⟩

noncomputable def realize (action : CliffordAction m) : OperatorMatrix m :=
  let centers := ResidueFixSearch.minimalDecomposition (binaryAction action)
  let correction := TransvectionSigns.finalPauliCorrection
    (CliffordTableau.preimages action) (CliffordTableau.preimages (rotations centers))
  matrix correction * rotationMatrix centers

theorem realization_spec (action : CliffordAction m) :
    realize action ∈ Matrix.unitaryGroup (ComputationalBasis m) ℂ ∧
      Represents (realize action) action ∧
      TransvectionRefinement.IsShortest (binaryAction action)
        (ResidueFixSearch.minimalDecomposition (binaryAction action)) ∧
      ∀ center ∈ ResidueFixSearch.minimalDecomposition (binaryAction action), center ≠ 0 := by
  obtain ⟨reconstruction, shortest, _, _, nonzero⟩ := CliffordTableau.signedDecomposition_spec action
  refine ⟨?_, ?_, shortest, nonzero⟩
  · exact (Matrix.unitaryGroup _ _).mul_mem (matrix_unitary _)
      (rotationMatrix_spec _).1
  · let centers := ResidueFixSearch.minimalDecomposition (binaryAction action)
    have represented := represents_mul (represents_pauliConjugation
      (TransvectionSigns.finalPauliCorrection (CliffordTableau.preimages action)
        (CliffordTableau.preimages (rotations centers))))
      (rotationMatrix_spec centers).2
    dsimp only [centers] at represented
    rw [reconstruction] at represented
    exact represented

theorem represents_preimage {unitary : OperatorMatrix m} {action : CliffordAction m}
    (is_unitary : unitary ∈ Matrix.unitaryGroup (ComputationalBasis m) ℂ)
    (represented : Represents unitary action) (pauli : Pauli m) :
    unitary.conjTranspose * matrix pauli * unitary = matrix (preimage action pauli) := by
  have inverse := Matrix.mem_unitaryGroup_iff'.mp is_unitary
  change unitary.conjTranspose * unitary = 1 at inverse
  calc
    unitary.conjTranspose * matrix pauli * unitary =
        unitary.conjTranspose *
          (unitary * matrix (preimage action pauli) * unitary.conjTranspose) * unitary := by
      rw [represented, image_preimage]
    _ = (unitary.conjTranspose * unitary) * matrix (preimage action pauli) *
        (unitary.conjTranspose * unitary) := by simp only [Matrix.mul_assoc]
    _ = matrix (preimage action pauli) := by rw [inverse, one_mul, mul_one]

theorem tableau_realization_spec (tableau : CliffordTableau.Tableau m)
    (valid : CliffordTableau.IsValid tableau) :
    let unitary := realize (CliffordTableau.realize tableau valid)
    unitary ∈ Matrix.unitaryGroup (ComputationalBasis m) ℂ ∧
      ∀ index, unitary.conjTranspose * matrix (CliffordTableau.standardPauli index) * unitary =
        matrix (tableau index) := by
  have realized := realization_spec (CliffordTableau.realize tableau valid)
  refine ⟨realized.1, fun index => ?_⟩
  rw [represents_preimage realized.1 realized.2.1]
  exact congrArg matrix (congrFun (CliffordTableau.preimages_realize tableau valid) index)

end PaulimerFormal.CliffordMatrix
