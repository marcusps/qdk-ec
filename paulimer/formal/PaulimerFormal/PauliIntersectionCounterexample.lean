import PaulimerFormal.PauliGroupMembership

/-! Independent phase filtering of a projective intersection basis is incomplete. -/

namespace PaulimerFormal.PauliIntersectionCounterexample

def xx : Pauli 2 where
  x _ := 1
  z _ := 0
  phase := 0

def zz : Pauli 2 where
  x _ := 0
  z _ := 1
  phase := 0

def signed (negative : Bool) (pauli : Pauli 2) : Pauli 2 :=
  if negative then -pauli else pauli

def generators (negative : Bool) : List (DensePauli 2) :=
  [DensePauli.ofPauli (signed negative xx), DensePauli.ofPauli (signed negative zz)]

def points (negative : Bool) : List (Pauli 2) :=
  [1, signed negative xx, signed negative zz, xx * zz]

def finiteGroup (negative : Bool) : Subgroup (Pauli 2) where
  carrier := { pauli | pauli ∈ points negative }
  one_mem' := by simp [points]
  mul_mem' := by
    intro first second first_mem second_mem
    simp only [Set.mem_ofPred_eq, points, List.mem_cons, List.not_mem_nil, or_false] at *
    rcases first_mem with rfl | rfl | rfl | rfl <;>
      rcases second_mem with rfl | rfl | rfl | rfl <;>
      cases negative <;> decide +kernel
  inv_mem' := by
    intro pauli member
    simp only [Set.mem_ofPred_eq, points, List.mem_cons, List.not_mem_nil, or_false] at *
    rcases member with rfl | rfl | rfl | rfl <;> cases negative <;> decide +kernel

theorem generated_eq (negative : Bool) :
    generatedPauliGroup (generators negative) = finiteGroup negative := by
  apply le_antisymm
  · rw [generatedPauliGroup, Subgroup.closure_le]
    rintro pauli ⟨index, rfl⟩
    fin_cases index <;> simp [generators, finiteGroup, points]
  · intro pauli member
    have first_mem := DensePauli.decode_mem_generatedPauliGroup (generators negative) ⟨0, by simp [generators]⟩
    have second_mem := DensePauli.decode_mem_generatedPauliGroup (generators negative) ⟨1, by simp [generators]⟩
    simp [generators] at first_mem second_mem
    change pauli ∈ points negative at member
    simp only [points, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact (generatedPauliGroup _).one_mem
    · exact first_mem
    · exact second_mem
    · have product : signed negative xx * signed negative zz = xx * zz := by
        cases negative <;> decide +kernel
      rw [← product]
      exact (generatedPauliGroup _).mul_mem first_mem second_mem

def accepted (pauli : Pauli 2) : Bool :=
  decide (pauli ∈ points false ∧ pauli ∈ points true)

def independentlyFiltered : List (Pauli 2) :=
  [xx, zz].filterMap (fun pauli =>
    ([0, 1, 2, 3].find? fun phase => accepted { pauli with phase }).map
      fun phase => { pauli with phase }) ++
  ([0, 1, 2, 3].filter fun phase => accepted (Pauli.scalar phase)).map Pauli.scalar

theorem accepted_iff (pauli : Pauli 2) :
    accepted pauli = true ↔
      pauli ∈ generatedPauliGroup (generators false) ⊓ generatedPauliGroup (generators true) := by
  simp [accepted, generated_eq, finiteGroup]

theorem rejects_basis :
    ∀ phase : PauliPhase,
      accepted { xx with phase } = false ∧ accepted { zz with phase } = false := by
  decide +kernel

theorem filtered_eq : independentlyFiltered = [1] := by decide +kernel

theorem common_mem :
    xx * zz ∈ generatedPauliGroup (generators false) ⊓ generatedPauliGroup (generators true) :=
  (accepted_iff _).mp (by decide +kernel)

theorem common_missing :
    xx * zz ∉ generatedPauliGroup (independentlyFiltered.map DensePauli.ofPauli) := by
  have trivial : generatedPauliGroup (independentlyFiltered.map DensePauli.ofPauli) ≤ ⊥ := by
    rw [filtered_eq]
    rw [generatedPauliGroup, Subgroup.closure_le]
    rintro pauli ⟨index, rfl⟩
    fin_cases index
    simp
  intro member
  have identity : xx * zz = 1 := trivial member
  have nonidentity : xx * zz ≠ 1 := by decide +kernel
  exact nonidentity identity

theorem counterexample :
    (∀ phase : PauliPhase,
      accepted { xx with phase } = false ∧ accepted { zz with phase } = false) ∧
    xx * zz ∈ generatedPauliGroup (generators false) ⊓ generatedPauliGroup (generators true) ∧
    xx * zz ∉ generatedPauliGroup (independentlyFiltered.map DensePauli.ofPauli) ∧
    generatedPauliGroup (independentlyFiltered.map DensePauli.ofPauli) ≠
      generatedPauliGroup (generators false) ⊓ generatedPauliGroup (generators true) :=
  ⟨rejects_basis, common_mem, common_missing, fun equal => common_missing (equal ▸ common_mem)⟩

end PaulimerFormal.PauliIntersectionCounterexample
