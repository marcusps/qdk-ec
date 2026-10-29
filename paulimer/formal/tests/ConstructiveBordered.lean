import PaulimerFormal.ConstructiveBordered

open PaulimerFormal PaulimerFormal.ConstructiveBordered
open scoped BigOperators Matrix

def check {size : ℕ} (label : String) (core : Matrix (Fin size) (Fin size) F2)
    (vectors : List (Fin size → F2)) (relation : List F2) : IO Unit := do
  let some family := matrixFamily core
    | throw (IO.userError s!"{label}: construction failed")
  unless List.ofFn family.vectors = vectors ∧ List.ofFn family.relation = relation do
    throw (IO.userError s!"{label}: incorrect ordered family")
  let coefficients : Matrix (Fin (size + 1)) (Fin size) F2 := family.vectors
  let bordered := coefficients * core * coefficients.transpose +
    Matrix.vecMulVec family.relation family.relation
  unless ∀ index, bordered index index = 1 do
    throw (IO.userError s!"{label}: nonunit diagonal")
  for row in List.finRange (size + 1) do
    for column in List.finRange (size + 1) do
      if row < column ∧ bordered row column ≠ 0 then
        throw (IO.userError s!"{label}: nonzero upper triangle")
  unless (∑ index, family.relation index • family.vectors index) = 0 do
    throw (IO.userError s!"{label}: nonzero relation")
  unless dotProduct family.relation family.relation = 1 do
    throw (IO.userError s!"{label}: even relation")
  unless ∀ vector : Fin size → F2, ∃ weights : Fin (size + 1) → F2,
      weights ᵥ* coefficients = vector do
    throw (IO.userError s!"{label}: incomplete span")
  IO.println s!"PASS: {label}"
  (← IO.getStdout).flush

def main : IO Unit := do
  check "empty core" (0 : Matrix (Fin 0) (Fin 0) F2) [0] [1]
  check "one singleton" !![1] [![1], ![0]] [0, 1]
  check "two singleton peels" (1 : Matrix (Fin 2) (Fin 2) F2)
    [![1, 0], ![0, 1], ![0, 0]] [0, 0, 1]
  check "alternating core" !![0, 1; 1, 0] [![0, 1], ![1, 1], ![1, 0]] [1, 1, 1]
  check "singleton then alternating restriction" !![1, 0, 0; 0, 0, 1; 0, 1, 0]
    [![1, 0, 0], ![0, 0, 1], ![0, 1, 1], ![0, 1, 0]] [0, 1, 1, 1]
  check "pair-only nonisotropic selection" !![0, 1, 0; 0, 0, 1; 1, 0, 0]
    [![1, 1, 0], ![0, 1, 1], ![1, 1, 1], ![0, 0, 0]] [0, 0, 0, 1]
  check "nonadjacent alternating partner" !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
    [![0, 0, 1, 0], ![1, 0, 1, 0], ![1, 0, 0, 1], ![1, 1, 0, 1], ![1, 1, 0, 0]]
    [1, 1, 1, 1, 1]
  unless (matrixFamily !![(0 : F2)]).isNone do
    throw (IO.userError "singular core was not rejected")
  IO.println "PASS: singular core rejection"
  (← IO.getStdout).flush
  let xx : PhaseVector 2 := Sum.elim (fun _ => 1) (fun _ => 0)
  let zz : PhaseVector 2 := Sum.elim (fun _ => 0) (fun _ => 1)
  let action := ResidueExtraction.storeAction (productTransvections [xx, zz, xx + zz] : ActionMatrix 2)
  let target : SymplecticAction 2 := ⟨ResidueExtraction.readAction action, by
    simpa [action] using (productTransvections [xx, zz, xx + zz]).property⟩
  IO.println "Checking constructed SWAP candidate"
  (← IO.getStdout).flush
  let some centers := candidate (target : ActionMatrix 2)
    | throw (IO.userError "SWAP candidate construction failed")
  IO.println "Checking constructed SWAP replay"
  (← IO.getStdout).flush
  unless centers.length = 3 ∧ productTransvections centers = target ∧
      centers.all (fun center => decide (center ≠ 0)) do
    throw (IO.userError "SWAP candidate failed replay or nonzero-factor checks")
  unless ResidueExtraction.rankDecomposition (target : ActionMatrix 2) = none ∧
      TransvectionRefinement.checkCandidate (target : ActionMatrix 2) 2 centers do
    throw (IO.userError "SWAP rank rejection or candidate acceptance failed")
  unless ResidueFixSearch.checkedDecomposition target (some centers) = centers do
    throw (IO.userError "SWAP checked path changed the accepted candidate")
  IO.println "PASS: constructed SWAP candidate accepted and replayed"
