import PaulimerFormal.PauliMatrix

open PaulimerFormal PaulimerFormal.Pauli

example : matrix (ofProjective (0 : ProjectivePauli 0) 1) 0 0 = Complex.I := by
  simp [matrix, ofProjective]

example : matrix (ofProjective (0 : ProjectivePauli 0) 2) 0 0 = -1 := by
  simp [matrix, ofProjective]

example : matrix oneQubitY (fun _ => 0) (fun _ => 1) = -Complex.I := by
  norm_num [matrix, oneQubitY, ofProjective, ProjectivePauli.singleX,
    ProjectivePauli.singleZ, dotProduct, funext_iff, phaseScalar_add]

example : matrix oneQubitY (fun _ => 1) (fun _ => 0) = Complex.I := by
  norm_num [matrix, oneQubitY, ofProjective, ProjectivePauli.singleX,
    ProjectivePauli.singleZ, dotProduct, funext_iff, phaseScalar_add]

def yy : Pauli 2 := ⟨⟨![1, 1], ![1, 1]⟩, 2⟩

example : matrix yy ![1, 1] ![0, 0] = -1 := by
  norm_num [matrix, yy, dotProduct, Fin.sum_univ_two, funext_iff, Fin.forall_fin_two]

example : matrix yy ![1, 0] ![0, 1] = 1 := by
  norm_num [matrix, yy, dotProduct, Fin.sum_univ_two, funext_iff, Fin.forall_fin_two]
  exact phaseScalar_zero
