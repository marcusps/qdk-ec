import PaulimerFormal.Triangularization
import Mathlib.Data.List.Nodup

/-!
# The lazy binary span iterator

`advance` models PR #217's carry loop, including its running XOR vector.
`binaryStates` describes its finite trace in least-significant-bit-first
order; it is not an enumeration of candidate factorizations.
-/

namespace PaulimerFormal.Triangularization

open scoped BigOperators

def zeroBits (n : ℕ) : Fin n → Bool := fun _ => false

def nextBits : {n : ℕ} → (Fin n → Bool) → Option (Fin n → Bool)
  | 0, _ => none
  | n + 1, bits =>
      if bits 0 then
        (nextBits (n := n) (Fin.tail bits)).map (Fin.cons false)
      else
        some (Fin.cons true (Fin.tail bits))

def liftStates {n : ℕ} (states : List (Fin n → Bool)) :
    List (Fin (n + 1) → Bool) :=
  states.flatMap fun bits => [Fin.cons false bits, Fin.cons true bits]

def binaryStates : (n : ℕ) → List (Fin n → Bool)
  | 0 => [Fin.elim0]
  | n + 1 => liftStates (binaryStates n)

def CounterTrace {n : ℕ} : List (Fin n → Bool) → Prop
  | [] => False
  | [bits] => nextBits bits = none
  | bits :: following :: rest =>
      nextBits bits = some following ∧ CounterTrace (following :: rest)

theorem liftStates_trace {n : ℕ} (states : List (Fin n → Bool))
    (trace : CounterTrace states) : CounterTrace (liftStates states) := by
  induction states with
  | nil => exact trace.elim
  | cons bits rest induction =>
      cases rest with
      | nil =>
          simpa [liftStates, CounterTrace, nextBits] using trace
      | cons following rest =>
          change nextBits bits = some following ∧ CounterTrace (following :: rest) at trace
          change nextBits (Fin.cons false bits) = some (Fin.cons true bits) ∧
            nextBits (Fin.cons true bits) = some (Fin.cons false following) ∧
            CounterTrace (liftStates (following :: rest))
          exact ⟨rfl, by simp [nextBits, trace.1], induction trace.2⟩

theorem binaryStates_trace (n : ℕ) : CounterTrace (binaryStates n) := by
  induction n with
  | zero => rfl
  | succ n induction => exact liftStates_trace _ induction

theorem mem_binaryStates {n : ℕ} (bits : Fin n → Bool) :
    bits ∈ binaryStates n := by
  induction n with
  | zero =>
      have equal : bits = Fin.elim0 := by ext index; exact Fin.elim0 index
      simp [binaryStates, equal]
  | succ n induction =>
      rw [binaryStates, liftStates, List.mem_flatMap]
      refine ⟨Fin.tail bits, induction _, ?_⟩
      have equal : bits = Fin.cons (bits 0) (Fin.tail bits) := by
        ext index
        cases index using Fin.cases <;> rfl
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      cases head : bits 0
      · exact Or.inl (equal.trans (by rw [head]))
      · exact Or.inr (equal.trans (by rw [head]))

theorem binaryStates_nodup (n : ℕ) : (binaryStates n).Nodup := by
  induction n with
  | zero => simp [binaryStates]
  | succ n induction =>
      apply List.nodup_flatMap.mpr
      constructor
      · intro bits _
        refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
        simp only [List.mem_singleton]
        intro equal
        have impossible := congrFun equal 0
        simp at impossible
      · apply induction.imp
        intro left right different vector in_left in_right
        simp only [List.mem_cons, List.not_mem_nil, or_false] at in_left in_right
        rcases in_left with left_eq | left_eq <;>
          rcases in_right with right_eq | right_eq <;>
          exact different (congrArg Fin.tail (left_eq.symm.trans right_eq))

theorem liftStates_length {n : ℕ} (states : List (Fin n → Bool)) :
    (liftStates states).length = 2 * states.length := by
  induction states with
  | nil => rfl
  | cons bits rest induction =>
      change (liftStates rest).length + 1 + 1 = 2 * (rest.length + 1)
      rw [induction]
      omega

theorem binaryStates_length (n : ℕ) : (binaryStates n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n induction =>
      rw [binaryStates, liftStates_length, induction, pow_succ, Nat.mul_comm]

theorem binaryStates_starts_zero (n : ℕ) :
    ∃ rest, binaryStates n = zeroBits n :: rest := by
  induction n with
  | zero =>
      have equal : (Fin.elim0 : Fin 0 → Bool) = zeroBits 0 := by
        funext index
        exact Fin.elim0 index
      exact ⟨[], congrArg (fun bits => [bits]) equal⟩
  | succ n induction =>
      obtain ⟨rest, equal⟩ := induction
      refine ⟨Fin.cons true (zeroBits n) :: liftStates rest, ?_⟩
      have zeros : Fin.cons false (zeroBits n) = zeroBits (n + 1) := by
        ext index
        cases index using Fin.cases <;> rfl
      simp [binaryStates, equal, liftStates, zeros]

def spanCoefficients (n : ℕ) : List (Fin n → Bool) :=
  (binaryStates n).tail

theorem mem_spanCoefficients_iff {n : ℕ} (bits : Fin n → Bool) :
    bits ∈ spanCoefficients n ↔ bits ≠ zeroBits n := by
  obtain ⟨rest, equal⟩ := binaryStates_starts_zero n
  have unique := binaryStates_nodup n
  rw [equal, List.nodup_cons] at unique
  have complete := mem_binaryStates bits
  rw [equal, List.mem_cons] at complete
  simp only [spanCoefficients, equal, List.tail_cons]
  constructor
  · intro member same
    exact unique.1 (same ▸ member)
  · intro nonzero
    exact complete.resolve_left nonzero

variable {V : Type*} [AddCommGroup V] [Module F2 V]

def selectedSum {n : ℕ} (basis : Fin n → V) (bits : Fin n → Bool) : V :=
  ∑ index, (if bits index then (1 : F2) else 0) • basis index

@[simp]
theorem selectedSum_zero {n : ℕ} (basis : Fin n → V) :
    selectedSum basis (zeroBits n) = 0 := by
  simp [selectedSum, zeroBits]

theorem selectedSum_succ {n : ℕ} (basis : Fin (n + 1) → V)
    (bits : Fin (n + 1) → Bool) :
    selectedSum basis bits =
      (if bits 0 then basis 0 else 0) + selectedSum (Fin.tail basis) (Fin.tail bits) := by
  rw [selectedSum, Fin.sum_univ_succ]
  change (if bits 0 then (1 : F2) else 0) • basis 0 +
      selectedSum (Fin.tail basis) (Fin.tail bits) = _
  congr 1
  cases bits 0 <;> simp

/-- Prefix carry recursion is structurally bounded by the number of bits.
Its vector updates are the same XORs as `SpanVectors::next`. -/
def advance : {n : ℕ} → (Fin n → V) → (Fin n → Bool) → V →
    Option ((Fin n → Bool) × V)
  | 0, _, _, _ => none
  | n + 1, basis, bits, current =>
      if bits 0 then
        (advance (n := n) (Fin.tail basis) (Fin.tail bits) (current + basis 0)).map
          (fun result => (Fin.cons false result.1, result.2))
      else
        some (Fin.cons true (Fin.tail bits), current + basis 0)

theorem advance_spec {n : ℕ} (basis : Fin n → V) (bits : Fin n → Bool) :
    advance basis bits (selectedSum basis bits) =
      (nextBits bits).map (fun following => (following, selectedSum basis following)) := by
  induction n with
  | zero => rfl
  | succ n induction =>
      cases head : bits 0
      · simp [advance, nextBits, head, selectedSum_succ, add_comm]
      · have toggled :
            selectedSum basis bits + basis 0 =
              selectedSum (Fin.tail basis) (Fin.tail bits) := by
          rw [selectedSum_succ, head]
          change (basis 0 + selectedSum (Fin.tail basis) (Fin.tail bits)) + basis 0 = _
          calc
            (basis 0 + selectedSum (Fin.tail basis) (Fin.tail bits)) + basis 0 =
                selectedSum (Fin.tail basis) (Fin.tail bits) + (basis 0 + basis 0) := by abel
            _ = _ := by rw [add_self_eq_zero_f2, add_zero]
        simp only [advance, head, ↓reduceIte, toggled]
        rw [induction]
        cases following : nextBits (Fin.tail bits) <;>
          simp [nextBits, head, following, selectedSum_succ]

def spanVectors {n : ℕ} (basis : Fin n → V) : List V :=
  (spanCoefficients n).map (selectedSum basis)

theorem selectedSum_mem {n : ℕ} (basis : Fin n → V) (bits : Fin n → Bool) :
    selectedSum basis bits ∈ familySpan basis := by
  apply Submodule.sum_mem
  intro index _
  exact (familySpan basis).smul_mem _ (member_familySpan basis index)

theorem selectedSum_injective {n : ℕ} (basis : Fin n → V)
    (independent : LinearIndependent F2 basis) :
    Function.Injective (selectedSum basis) := by
  intro bits other equal
  have coefficients_equal :=
    Fintype.linearIndependent_iffₛ.mp independent _ _ equal
  ext index
  have coefficient_equal := coefficients_equal index
  cases left : bits index <;> cases right : other index <;> simp_all

theorem selectedSum_eq_zero_iff {n : ℕ} (basis : Fin n → V)
    (independent : LinearIndependent F2 basis) (bits : Fin n → Bool) :
    selectedSum basis bits = 0 ↔ bits = zeroBits n := by
  constructor
  · intro equal
    apply selectedSum_injective basis independent
    simpa using equal
  · rintro rfl
    exact selectedSum_zero basis

theorem spanVectors_nodup {n : ℕ} (basis : Fin n → V)
    (independent : LinearIndependent F2 basis) : (spanVectors basis).Nodup :=
  (binaryStates_nodup n).tail.map (selectedSum_injective basis independent)

theorem spanVectors_length {n : ℕ} (basis : Fin n → V) :
    (spanVectors basis).length = 2 ^ n - 1 := by
  simp [spanVectors, spanCoefficients, binaryStates_length]

theorem mem_spanVectors_iff {n : ℕ} (basis : Fin n → V)
    (independent : LinearIndependent F2 basis) (vector : V) :
    vector ∈ spanVectors basis ↔ vector ∈ familySpan basis ∧ vector ≠ 0 := by
  constructor
  · intro member
    change vector ∈ (spanCoefficients n).map (selectedSum basis) at member
    obtain ⟨bits, coefficients_member, rfl⟩ := List.mem_map.mp member
    refine ⟨selectedSum_mem basis bits, ?_⟩
    intro zero
    exact (mem_spanCoefficients_iff bits).mp coefficients_member
      ((selectedSum_eq_zero_iff basis independent bits).mp zero)
  · rintro ⟨member, nonzero⟩
    obtain ⟨coefficients, representation⟩ :=
      (Submodule.mem_span_range_iff_exists_fun F2).mp member
    let bits : Fin n → Bool := fun index => decide (coefficients index ≠ 0)
    have bit_coefficient (index : Fin n) :
        (if bits index then (1 : F2) else 0) = coefficients index := by
      by_cases zero : coefficients index = 0
      · simp [bits, zero]
      · simp [bits, f2_eq_one_of_ne_zero _ zero]
    have selected : selectedSum basis bits = vector := by
      simpa only [selectedSum, bit_coefficient] using representation
    apply List.mem_map.mpr
    refine ⟨bits, (mem_spanCoefficients_iff bits).mpr ?_, selected⟩
    intro zero
    rw [zero, selectedSum_zero] at selected
    exact nonzero selected.symm

theorem spanEnumeration_spec {n : ℕ} (basis : Fin n → V)
    (independent : LinearIndependent F2 basis) :
    (∃ rest, binaryStates n = zeroBits n :: rest) ∧
      CounterTrace (binaryStates n) ∧
      (spanVectors basis).Nodup ∧
      (spanVectors basis).length = 2 ^ n - 1 ∧
      ∀ vector, vector ∈ spanVectors basis ↔ vector ∈ familySpan basis ∧ vector ≠ 0 :=
  ⟨binaryStates_starts_zero n, binaryStates_trace n, spanVectors_nodup basis independent,
    spanVectors_length basis,
    mem_spanVectors_iff basis independent⟩

example : (binaryStates 2).map (fun bits => [bits 0, bits 1]) =
    [[false, false], [true, false], [false, true], [true, true]] := by decide

end PaulimerFormal.Triangularization
