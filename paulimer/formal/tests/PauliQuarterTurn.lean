import PaulimerFormal.PauliQuarterTurn

open PaulimerFormal PaulimerFormal.Pauli

example : quarterMatrix oneQubitX * matrix oneQubitZ * (quarterMatrix oneQubitX).conjTranspose =
    matrix oneQubitY := by
  rw [quarterMatrix_conjugation _ _ (by apply Pauli.ext <;> decide)]
  congr 1
  apply Pauli.ext <;> decide

example : quarterMatrix oneQubitZ * matrix oneQubitX * (quarterMatrix oneQubitZ).conjTranspose =
    -matrix oneQubitY := by
  rw [quarterMatrix_conjugation _ _ (by apply Pauli.ext <;> decide), ← matrix_neg]
  congr 1
  apply Pauli.ext <;> decide

example : quarterMatrix oneQubitY * matrix oneQubitX * (quarterMatrix oneQubitY).conjTranspose =
    matrix oneQubitZ := by
  rw [quarterMatrix_conjugation _ _ (by apply Pauli.ext <;> decide)]
  congr 1
  apply Pauli.ext <;> decide

example : quarterMatrix (-oneQubitX) * matrix oneQubitZ * (quarterMatrix (-oneQubitX)).conjTranspose =
    -matrix oneQubitY := by
  rw [quarterMatrix_conjugation _ _ (by apply Pauli.ext <;> decide), ← matrix_neg]
  congr 1
  apply Pauli.ext <;> decide

example : quarterMatrix oneQubitX * matrix oneQubitX * (quarterMatrix oneQubitX).conjTranspose =
    matrix oneQubitX := by
  rw [quarterMatrix_conjugation _ _ (by apply Pauli.ext <;> decide)]
  congr 1

example : quarterMatrix (1 : Pauli 0) * matrix (ofProjective 0 1) *
    (quarterMatrix (1 : Pauli 0)).conjTranspose = matrix (ofProjective 0 1) := by
  rw [quarterMatrix_conjugation _ _ (by change (1 : Pauli 0) * 1 = 1; simp)]
  rw [exponentAction_scalar]
