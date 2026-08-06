import PaulimerFormal.Minimality

/-! Factorizations obtained from a one-dimensional border of the residue core. -/

open Matrix

namespace PaulimerFormal

def IsBorderedTriangularization {n k : ℕ}
    (core : Matrix (Fin n) (Fin n) F2)
    (coefficients : Matrix (Fin k) (Fin n) F2)
    (relation : Fin k → F2) : Prop :=
  IsUnitLowerTriangular
      (coefficients * core * Matrix.transpose coefficients +
        Matrix.vecMulVec relation relation) ∧
    Matrix.mulVec (Matrix.transpose coefficients) relation = 0 ∧
    dotProduct relation relation = 1 ∧
    Function.Injective coefficients.mulVec

theorem borderedEqPairing
    {m n k : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (coefficients : Matrix (Fin k) (Fin n) F2)
    (relation : Fin k → F2)
    (bordered :
      IsBorderedTriangularization presentation.core
        coefficients relation) :
    let centers : Fin k → PhaseVector m :=
      coefficients * presentation.basis
    coefficients * presentation.core *
          Matrix.transpose coefficients +
        Matrix.vecMulVec relation relation =
      Matrix.transpose (pairingUpperFin centers) := by
  dsimp only
  have relation_twice :
        Matrix.vecMulVec relation relation +
            Matrix.vecMulVec relation relation =
          0 := by
      ext row column
      exact f2_add_self _
  apply isUnitLowerTriangular_ext
    bordered.1
    (pairingUpperFin_transpose_isUnitLowerTriangular
      (coefficients * presentation.basis))
  calc
    (coefficients * presentation.core *
          Matrix.transpose coefficients +
        Matrix.vecMulVec relation relation) +
        Matrix.transpose
          (coefficients * presentation.core *
              Matrix.transpose coefficients +
            Matrix.vecMulVec relation relation) =
      coefficients *
          (presentation.core +
            Matrix.transpose presentation.core) *
        Matrix.transpose coefficients := by
          simp only [Matrix.transpose_mul, Matrix.transpose_add,
            Matrix.transpose_transpose, Matrix.transpose_vecMulVec,
            Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
          abel_nf
          rw [two_smul, relation_twice, zero_add]
    _ = centerMatrixFin
          (coefficients * presentation.basis) * omega m *
        Matrix.transpose
          (centerMatrixFin
            (coefficients * presentation.basis)) := by
      rw [presentation.core_add_transpose, centerMatrixFin_eq]
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = pairingUpperFin
          (coefficients * presentation.basis) +
        Matrix.transpose
          (pairingUpperFin
            (coefficients * presentation.basis)) :=
      (pairingUpperFin_add_transpose
        (coefficients * presentation.basis)).symm
    _ = Matrix.transpose
          (pairingUpperFin
            (coefficients * presentation.basis)) +
        Matrix.transpose
          (Matrix.transpose
            (pairingUpperFin
              (coefficients * presentation.basis))) := by
      rw [Matrix.transpose_transpose, add_comm]

theorem borderedCoefficientEq
    {m n k : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (coefficients : Matrix (Fin k) (Fin n) F2)
    (relation : Fin k → F2)
    (bordered :
      IsBorderedTriangularization presentation.core
        coefficients relation) :
    let centers : Fin k → PhaseVector m :=
      coefficients * presentation.basis
    presentation.coefficient =
      Matrix.transpose coefficients * pathMatrixFin centers *
        coefficients := by
  dsimp only
  have bordered_eq :
      coefficients * presentation.core *
            Matrix.transpose coefficients +
          Matrix.vecMulVec relation relation =
        Matrix.transpose
          (pairingUpperFin
            (coefficients * presentation.basis)) := by
    simpa using
      borderedEqPairing presentation coefficients relation bordered
  have pairing_eq :
      pairingUpperFin (coefficients * presentation.basis) =
        coefficients * Matrix.transpose presentation.core *
            Matrix.transpose coefficients +
          Matrix.vecMulVec relation relation := by
    have transposed := congrArg Matrix.transpose bordered_eq
    simpa [Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.mul_assoc] using transposed.symm
  have core_part_mul_relation :
      (coefficients * Matrix.transpose presentation.core *
          Matrix.transpose coefficients) *ᵥ relation = 0 := by
    rw [← Matrix.mulVec_mulVec, bordered.2.1]
    simp
  have pairing_mul_relation :
      pairingUpperFin (coefficients * presentation.basis) *ᵥ
        relation = relation := by
    rw [pairing_eq, Matrix.add_mulVec, core_part_mul_relation,
      Matrix.vecMulVec_mulVec, bordered.2.2.1]
    simp
  have path_mul_relation :
      pathMatrixFin (coefficients * presentation.basis) *ᵥ
        relation = relation := by
    calc
      pathMatrixFin (coefficients * presentation.basis) *ᵥ
          relation =
        pathMatrixFin (coefficients * presentation.basis) *ᵥ
          (pairingUpperFin (coefficients * presentation.basis) *ᵥ
            relation) := by
            rw [pairing_mul_relation]
      _ = (pathMatrixFin (coefficients * presentation.basis) *
          pairingUpperFin (coefficients * presentation.basis)) *ᵥ
            relation := by
            rw [Matrix.mulVec_mulVec]
      _ = relation := by
            rw [pathMatrixFin_mul_pairingUpperFin]
            simp
  have relation_twice :
      Matrix.vecMulVec relation relation +
          Matrix.vecMulVec relation relation =
        0 := by
    ext row column
    exact f2_add_self _
  have core_transpose_congruence :
      coefficients * Matrix.transpose presentation.core *
          Matrix.transpose coefficients =
        pairingUpperFin (coefficients * presentation.basis) +
          Matrix.vecMulVec relation relation := by
    rw [pairing_eq]
    abel_nf
    rw [two_smul, relation_twice, add_zero]
  have candidate_times_core_times_coefficients :
      (Matrix.transpose coefficients *
          pathMatrixFin (coefficients * presentation.basis) *
            coefficients * Matrix.transpose presentation.core) *
          Matrix.transpose coefficients =
        (1 : Matrix (Fin n) (Fin n) F2) *
          Matrix.transpose coefficients := by
    calc
      (Matrix.transpose coefficients *
          pathMatrixFin (coefficients * presentation.basis) *
            coefficients * Matrix.transpose presentation.core) *
          Matrix.transpose coefficients =
        Matrix.transpose coefficients *
          pathMatrixFin (coefficients * presentation.basis) *
          (coefficients * Matrix.transpose presentation.core *
            Matrix.transpose coefficients) := by
              simp [Matrix.mul_assoc]
      _ = Matrix.transpose coefficients *
          pathMatrixFin (coefficients * presentation.basis) *
          (pairingUpperFin (coefficients * presentation.basis) +
            Matrix.vecMulVec relation relation) := by
              rw [core_transpose_congruence]
      _ = Matrix.transpose coefficients *
            (pathMatrixFin (coefficients * presentation.basis) *
              pairingUpperFin (coefficients * presentation.basis)) +
          Matrix.transpose coefficients *
            (pathMatrixFin (coefficients * presentation.basis) *
              Matrix.vecMulVec relation relation) := by
              simp [Matrix.mul_add, Matrix.mul_assoc]
      _ = Matrix.transpose coefficients *
            (1 : Matrix (Fin k) (Fin k) F2) +
          Matrix.transpose coefficients *
            (pathMatrixFin (coefficients * presentation.basis) *
              Matrix.vecMulVec relation relation) := by
              rw [pathMatrixFin_mul_pairingUpperFin]
      _ = Matrix.transpose coefficients *
            (1 : Matrix (Fin k) (Fin k) F2) +
          Matrix.transpose coefficients *
            Matrix.vecMulVec relation relation := by
              rw [Matrix.mul_vecMulVec, path_mul_relation]
      _ = Matrix.transpose coefficients + 0 := by
              rw [Matrix.mul_one, Matrix.mul_vecMulVec,
                bordered.2.1]
              simp
      _ = (1 : Matrix (Fin n) (Fin n) F2) *
          Matrix.transpose coefficients := by simp
  have transpose_coefficients_vecMul_injective :
      Function.Injective
        (Matrix.transpose coefficients).vecMul := by
    intro first second equal
    apply bordered.2.2.2
    simpa only [Matrix.vecMul_transpose] using equal
  have candidate_times_core :
      (Matrix.transpose coefficients *
          pathMatrixFin (coefficients * presentation.basis) *
            coefficients) *
          Matrix.transpose presentation.core =
        1 := by
    exact mul_right_cancel_of_vecMul_injective
      (Matrix.transpose coefficients)
      ((Matrix.transpose coefficients *
          pathMatrixFin (coefficients * presentation.basis) *
            coefficients) * Matrix.transpose presentation.core)
      1
      transpose_coefficients_vecMul_injective
      candidate_times_core_times_coefficients
  symm
  calc
    Matrix.transpose coefficients *
          pathMatrixFin (coefficients * presentation.basis) *
        coefficients =
      (Matrix.transpose coefficients *
          pathMatrixFin (coefficients * presentation.basis) *
        coefficients) * 1 := by
          simp
    _ = (Matrix.transpose coefficients *
          pathMatrixFin (coefficients * presentation.basis) *
        coefficients) *
        (Matrix.transpose presentation.core *
          presentation.coefficient) := by
            rw [presentation.core_transpose_mul_coefficient]
    _ = ((Matrix.transpose coefficients *
          pathMatrixFin (coefficients * presentation.basis) *
        coefficients) *
          Matrix.transpose presentation.core) *
        presentation.coefficient := by simp [Matrix.mul_assoc]
    _ = presentation.coefficient := by
          rw [candidate_times_core, Matrix.one_mul]

theorem factorizationOfBordered
    {m n k : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (coefficients : Matrix (Fin k) (Fin n) F2)
    (relation : Fin k → F2)
    (bordered :
      IsBorderedTriangularization presentation.core
        coefficients relation) :
    IsFactorization target
      (List.ofFn
        (coefficients * presentation.basis :
          Fin k → PhaseVector m)) := by
  let centers : Fin k → PhaseVector m :=
    coefficients * presentation.basis
  have coefficient_eq :
      presentation.coefficient =
        Matrix.transpose coefficients * pathMatrixFin centers *
          coefficients := by
    simpa [centers] using
      borderedCoefficientEq presentation coefficients relation bordered
  apply target_eq_of_residueMatrix_eq target
    (productTransvections (List.ofFn centers))
  rw [residueMatrix_product_ofFn_eq, presentation.residue_eq,
    coefficient_eq, centerMatrixFin_eq]
  simp [centers, Matrix.transpose_mul, Matrix.mul_assoc]

end PaulimerFormal
