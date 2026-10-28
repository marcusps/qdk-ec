import PaulimerFormal.PauliGroupIntersection
import PaulimerFormal.PauliGroupEnumeration
import PaulimerFormal.PauliIntersectionCounterexample

open PaulimerFormal PaulimerFormal.PauliIntersection
open PaulimerFormal.PauliIntersectionCounterexample (xx zz generators points)

def checkIntersection {size : ℕ} (name : String) (first second : List (DensePauli size))
    (expected : List (Pauli size)) : IO Unit := do
  let some output := intersect first second
    | throw (IO.userError s!"{name}: intersection unexpectedly failed")
  let actual := PauliGroupEnumeration.elements (output.map DensePauli.ofPauli)
  unless actual.toFinset = expected.toFinset do
    throw (IO.userError s!"{name}: wrong intersection elements")
  IO.println s!"PASS: {name}"
  (← IO.getStdout).flush

def main : IO Unit := do
  let first := generators false
  let second := generators true
  checkIntersection "sign cancellation" first second [1, xx * zz]
  checkIntersection "identical groups" first first (points false)
  checkIntersection "dependent input" (first ++ first) first (points false)
  checkIntersection "empty left" [] first [1]
  checkIntersection "empty right" first [] [1]
  checkIntersection "empty zero-qubit groups" ([] : List (DensePauli 0)) [] [1]
  let imaginary := [DensePauli.ofPauli { xx with phase := 1 }, DensePauli.ofPauli { zz with phase := 1 }]
  checkIntersection "imaginary phase cancellation" first imaginary [1, xx * zz]
  checkIntersection "zero-qubit scalar groups"
    [DensePauli.ofPauli (Pauli.scalar (m := 0) 1)]
    [DensePauli.ofPauli (Pauli.scalar 2)] [1, Pauli.scalar 2]
  let singleX := DensePauli.singleX (m := 1) 0
  let singleZ := DensePauli.singleZ (m := 1) 0
  checkIntersection "full-rank stacked matrix, disjoint rows" [singleX] [singleZ] [1]
  checkIntersection "noncommuting full projective space" [singleX, singleZ] [singleZ, singleX]
    ([1, singleX.decode, singleZ.decode, singleX.decode * singleZ.decode].flatMap
      fun pauli => [pauli, pauli * Pauli.scalar 2])
  let left : BinarFormal.Packed.PackedMatrix 3 3 :=
    ⟨fun index => packVector (![![1, 0, 0], ![0, 1, 0], ![1, 1, 0]] index)⟩
  let right : BinarFormal.Packed.PackedMatrix 2 3 :=
    ⟨fun index => packVector (![![0, 1, 0], ![0, 0, 1]] index)⟩
  let basis := IntersectionExtraction.basis left right
  let rows := List.ofFn fun index => List.ofFn fun column : Fin 3 => (basis.rows index).get column
  unless rows = [[false, true, false]] do
    throw (IO.userError "rectangular dependency projection: wrong extracted basis")
  IO.println "PASS: rectangular dependency projection"
