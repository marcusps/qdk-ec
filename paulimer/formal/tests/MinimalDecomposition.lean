import PaulimerFormal.ResidueFixSearch

open PaulimerFormal PaulimerFormal.ResidueFixSearch

def swapAction : SymplecticAction 2 :=
  ⟨fun row column => if column = Sum.map (fun index : Fin 2 => index + 1)
      (fun index : Fin 2 => index + 1) row then 1 else 0, by
    let xx : PhaseVector 2 := Sum.elim (fun _ => 1) (fun _ => 0)
    let zz : PhaseVector 2 := Sum.elim (fun _ => 0) (fun _ => 1)
    have same : (fun row column => if column = Sum.map (fun index : Fin 2 => index + 1)
        (fun index : Fin 2 => index + 1) row then 1 else 0) =
        (productTransvections [xx, zz, xx + zz] : ActionMatrix 2) := by
      funext row column
      fin_cases row <;> fin_cases column <;> decide
    rw [same]
    exact (productTransvections [xx, zz, xx + zz]).property⟩

def check {size : ℕ} (label : String) (target : SymplecticAction size) (expected : ℕ)
    (solve : SymplecticAction size → List (PhaseVector size)) : IO Unit := do
  IO.println s!"Checking {label}"
  (← IO.getStdout).flush
  let started ← IO.monoMsNow
  let centers := solve target
  unless centers.length = expected do
    throw (IO.userError s!"{label}: incorrect minimal length")
  unless productTransvections centers = target do
    throw (IO.userError s!"{label}: incorrect ordered replay")
  unless centers.all (fun center => decide (center ≠ 0)) do
    throw (IO.userError s!"{label}: zero factor")
  IO.println s!"PASS: {label} ({(← IO.monoMsNow) - started} ms)"
  (← IO.getStdout).flush

def main : IO Unit := do
  check "zero qubits" (1 : SymplecticAction 0) 0 minimalDecomposition
  let singleX : PhaseVector 1 := Sum.elim (fun _ => 1) (fun _ => 0)
  let singleZ : PhaseVector 1 := Sum.elim (fun _ => 0) (fun _ => 1)
  check "one-qubit identity" (1 : SymplecticAction 1) 0 minimalDecomposition
  for center in [singleX, singleZ, singleX + singleZ] do
    check "one-qubit transvection" (transvectionAction center) 1 minimalDecomposition
  for centers in [[singleX, singleZ], [singleZ, singleX]] do
    check "one-qubit length two" (productTransvections centers) 2 minimalDecomposition
  check "SWAP recursive fallback" swapAction 3 minimalDecomposition
  check "SWAP absent candidate" swapAction 3 (fun target => checkedDecomposition target none)
  check "SWAP rejected candidate" swapAction 3 (fun target => checkedDecomposition target (some []))
  let xx : PhaseVector 2 := Sum.elim (fun _ => 1) (fun _ => 0)
  let zz : PhaseVector 2 := Sum.elim (fun _ => 0) (fun _ => 1)
  check "SWAP accepted candidate" swapAction 3
    (fun target => checkedDecomposition target (some [xx, zz, xx + zz]))
  unless minimalDecomposition swapAction = [zz, xx + zz, xx] do
    throw (IO.userError "SWAP first-success selection or factor order changed")
  IO.println "PASS: exact SWAP first-success output"
