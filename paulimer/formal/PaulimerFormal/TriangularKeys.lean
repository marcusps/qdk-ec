import PaulimerFormal.TriangularMemo
import BinarFormal.Echelon
import PaulimerFormal.PackedEncoding

/-!
# Collision-safe subspace keys

Reuse Binar's verified reduction, discard zero rows, and flatten logical bits.
Equal keys imply equal spans; canonical-RREF uniqueness is not assumed.
-/

namespace PaulimerFormal.Triangularization

open BinarFormal.Packed
open BinarFormal.Echelon

def packedRows {n d : ℕ} (basis : Fin n → Fin d → F2) : PackedMatrix n d :=
  ⟨fun row => packVector (basis row)⟩

@[simp]
theorem decode_packedRows {n d : ℕ} (basis : Fin n → Fin d → F2) :
    (packedRows basis).decode = basis := by
  funext row
  exact decode_packVector (basis row)

def reducedRows {n d : ℕ} (basis : Fin n → Fin d → F2) : List (Fin d → F2) :=
  (List.ofFn (echelonize (packedRows basis)).decode).filter fun row => decide (row ≠ 0)

theorem reducedRows_span {n d : ℕ} (basis : Fin n → Fin d → F2) :
    Submodule.span F2 {row | row ∈ reducedRows basis} = familySpan basis := by
  have rows_eq : {row | row ∈ reducedRows basis} =
      Set.range (echelonize (packedRows basis)).decode \ {0} := by
    ext row
    simp [reducedRows]
    intro _
    exact List.mem_ofFn' (echelonize (packedRows basis)).decode row
  rw [rows_eq, Submodule.span_sdiff_singleton_zero, echelonize_rowSpace_eq, decode_packedRows]

def flattenRows {d : ℕ} (rows : List (Fin d → F2)) : List F2 :=
  rows.flatMap List.ofFn

theorem flattenRows_injective {d : ℕ} (positive : 0 < d) :
    Function.Injective (flattenRows (d := d)) := by
  intro first second equal
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons row rest =>
          have lengths := congrArg List.length equal
          simp [flattenRows] at lengths
          omega
  | cons row rest induction =>
      cases second with
      | nil =>
          have lengths := congrArg List.length equal
          simp [flattenRows] at lengths
          omega
      | cons other tail =>
          change List.ofFn row ++ flattenRows rest = List.ofFn other ++ flattenRows tail at equal
          have parts := List.append_inj equal (by simp)
          have rows_equal := List.ofFn_injective parts.1
          exact congrArg₂ List.cons rows_equal (induction parts.2)

def subspaceKey {d n : ℕ} (basis : Fin n → Fin d → F2) : List Bool :=
  (flattenRows (reducedRows basis)).map boolOfF2

theorem subspaceKey_noFalseCollisions (d : ℕ) :
    NoFalseCollisions (subspaceKey (d := d)) := by
  intro n m first second equal
  cases d with
  | zero =>
      apply le_antisymm <;> intro vector _ <;>
        have zero : vector = 0 := Subsingleton.elim _ _ <;>
        rw [zero] <;> exact Submodule.zero_mem _
  | succ d =>
      have decoded := congrArg (List.map Bool.toF2) equal
      simp only [subspaceKey, List.map_map, Function.comp_def, toF2_boolOfF2,
        List.map_id_fun'] at decoded
      have rows_equal := flattenRows_injective (by omega : 0 < d + 1) decoded
      calc
        familySpan first = Submodule.span F2 {row | row ∈ reducedRows first} :=
          (reducedRows_span first).symm
        _ = Submodule.span F2 {row | row ∈ reducedRows second} := by rw [rows_equal]
        _ = familySpan second := reducedRows_span second

theorem subspaceKey_eq_implies_span_eq {d n m : ℕ}
    (first : Fin n → Fin d → F2) (second : Fin m → Fin d → F2)
    (equal : subspaceKey first = subspaceKey second) :
    familySpan first = familySpan second :=
  subspaceKey_noFalseCollisions d first second equal

def memoizedTriangularize {n : ℕ} (core : Matrix (Fin n) (Fin n) F2) :
    Option (Matrix (Fin n) (Fin n) F2) :=
  (memoSearch core.toBilin' subspaceKey (1 : Matrix (Fin n) (Fin n) F2) []).1

theorem memoizedTriangularize_eq {n : ℕ} (core : Matrix (Fin n) (Fin n) F2) :
    memoizedTriangularize core = congruenceTriangularize core :=
  memoSearch_empty_eq_search core.toBilin' subspaceKey (subspaceKey_noFalseCollisions n)
    (1 : Matrix (Fin n) (Fin n) F2) (Matrix.linearIndependent_rows_iff_isUnit.mpr isUnit_one)

theorem memoized_core_none_iff {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n) :
    memoizedTriangularize presentation.core = none ↔ ¬presentation.IsTriangularizable := by
  rw [memoizedTriangularize_eq]
  exact core_search_none_iff presentation

example : subspaceKey (n := 2) (d := 0) (fun _ _ => 0) = [] := by decide

example :
    memoizedTriangularize (!![1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F2) =
      some !![1, 1, 0; 1, 0, 1; 1, 1, 1] := by
  rw [memoizedTriangularize_eq]
  decide

end PaulimerFormal.Triangularization
