import PaulimerFormal.CliffordMatrix

open PaulimerFormal PaulimerFormal.Pauli CliffordAction CliffordMatrix

example :
    let centers := [oneQubitX.projective.toPhaseVector, oneQubitZ.projective.toPhaseVector]
    rotationMatrix centers * matrix oneQubitZ * (rotationMatrix centers).conjTranspose =
      matrix oneQubitX := by
  dsimp only
  rw [(rotationMatrix_spec _).2]
  congr 1
  apply Pauli.ext <;> decide

example :
    let centers := [oneQubitZ.projective.toPhaseVector, oneQubitX.projective.toPhaseVector]
    rotationMatrix centers * matrix oneQubitZ * (rotationMatrix centers).conjTranspose =
      matrix oneQubitY := by
  dsimp only
  rw [(rotationMatrix_spec _).2]
  congr 1
  apply Pauli.ext <;> decide

example :
    let unitary := CliffordMatrix.realize (pauliConjugation oneQubitX)
    unitary * matrix oneQubitZ * unitary.conjTranspose = -matrix oneQubitZ := by
  dsimp only
  rw [(CliffordMatrix.realization_spec _).2.1, ← matrix_neg]
  congr 1
  apply Pauli.ext <;> decide

example (phase : PauliPhase) :
    let unitary := CliffordMatrix.realize (1 : CliffordAction 0)
    unitary * matrix (ofProjective 0 phase) * unitary.conjTranspose =
      matrix (ofProjective 0 phase) :=
  (CliffordMatrix.realization_spec (1 : CliffordAction 0)).2.1 _

example :
    let tableau := CliffordTableau.preimages (pauliConjugation oneQubitX)
    let unitary := CliffordMatrix.realize
      (CliffordTableau.realize tableau (CliffordTableau.preimages_valid _))
    unitary.conjTranspose * matrix oneQubitZ * unitary = -matrix oneQubitZ := by
  dsimp only
  have preimage := (tableau_realization_spec
    (CliffordTableau.preimages (pauliConjugation oneQubitX))
    (CliffordTableau.preimages_valid _)).2 (Sum.inr 0)
  change _ * matrix oneQubitZ * _ = _ at preimage
  rw [preimage, ← matrix_neg]
  congr 1
  apply Pauli.ext <;> decide
