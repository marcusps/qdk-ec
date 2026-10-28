import PaulimerFormal.CliffordFixedSpace

open PaulimerFormal PaulimerFormal.CliffordFixedSpace

def check {size : ℕ} (action : ActionMatrix size) (expected : ℕ) : IO Unit := do
  IO.println s!"Checking {size}-qubit fixed space of dimension {expected}"
  (← IO.getStdout).flush
  unless dimension action = expected do
    throw (IO.userError "Incorrect fixed-space dimension")
  for row in List.finRange (dimension action) do
    let pauli := paulis action row
    unless pauli.xyzPhase = 0 do
      throw (IO.userError "Non-positive generator")
    unless rowAction pauli.projective.toPhaseVector action = pauli.projective.toPhaseVector do
      throw (IO.userError "Non-fixed generator")
  IO.println "PASS"
  (← IO.getStdout).flush

def main : IO Unit := do
  check (1 : ActionMatrix 0) 0
  check (1 : ActionMatrix 1) 2
  check (transvection (Sum.elim (fun _ : Fin 1 => 1) (fun _ => 0))) 1
  check (transvection (Sum.elim (fun _ : Fin 1 => 0) (fun _ => 1))) 1
