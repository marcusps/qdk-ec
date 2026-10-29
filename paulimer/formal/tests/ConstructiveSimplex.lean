import PaulimerFormal.ConstructiveSimplex

open PaulimerFormal PaulimerFormal.ConstructiveSimplex

def check {size : ℕ} (label : String) (core : Matrix (Fin size) (Fin size) F2)
    (expected : Option (List (Fin size → F2))) : IO Unit := do
  let actual := (simplex core.toBilin' (1 : Matrix (Fin size) (Fin size) F2)).map List.ofFn
  unless actual = expected do
    throw (IO.userError s!"{label}: incorrect ordered simplex")
  IO.println s!"PASS: {label}"

def main : IO Unit := do
  check "empty alternating form" (0 : Matrix (Fin 0) (Fin 0) F2) (some [0])
  check "singular one-dimensional alternating form" !![0] none
  check "singular two-dimensional alternating form" (0 : Matrix (Fin 2) (Fin 2) F2) none
  check "one hyperbolic pair" !![0, 1; 1, 0] (some [![0, 1], ![1, 1], ![1, 0]])
  check "nonadjacent partner and recursive pair" !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
    (some [![0, 0, 1, 0], ![1, 0, 1, 0], ![1, 0, 0, 1], ![1, 1, 0, 1], ![1, 1, 0, 0]])
  check "nontrivial projected complement" !![0, 1, 1, 0; 1, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
    (some [![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, 0, 1], ![0, 1, 1, 1], ![1, 1, 1, 0]])
