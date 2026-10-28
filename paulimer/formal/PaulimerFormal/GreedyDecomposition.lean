import PaulimerFormal.GreedySearch
import PaulimerFormal.Product
import PaulimerFormal.Pauli

/-! A terminating greedy decomposition with binary replay and positive Hermitian factors. -/

namespace PaulimerFormal.GreedyDecomposition

open GreedyReduction GreedySearch

noncomputable def potential {m : ℕ} (action : ActionMatrix m) : ℕ := by
  classical
  exact 2 * residueRank action + if IsHyperbolic action then 1 else 0

theorem potential_bound {m : ℕ} (action : ActionMatrix m) :
    potential action ≤ 4 * m + 1 := by
  have dimension := residueRank_add_finrank_fixedSpace action
  unfold potential
  split_ifs <;> omega

theorem step_decreases {m : ℕ} (target : SymplecticAction m) (vector : PhaseVector m)
    (returned : nextVector (target : ActionMatrix m) = some vector) :
    potential ((target : ActionMatrix m) *
      transvection (residueVector (target : ActionMatrix m) vector)) <
      potential (target : ActionMatrix m) := by
  have selected := nextVector_some (target : ActionMatrix m) vector returned
  rcases selected.2 with active | hyperbolic
  · have drop := lowering_rank target vector active
    have not_hyperbolic : ¬ IsHyperbolic (target : ActionMatrix m) := by
      intro hyperbolic
      rw [hyperbolic vector] at active
      exact zero_ne_one active
    simp only [potential, ite_eq_right not_hyperbolic]
    split_ifs <;> omega
  · have same_rank := hyperbolic_rank target hyperbolic vector
    have escaped := hyperbolic_escape target hyperbolic vector selected.1
    simp [potential, hyperbolic, escaped, same_rank]

def decodeRows {m : ℕ} (rows : Vector (Vector F2 (m + m)) (m + m)) : ActionMatrix m :=
  fun row column => rows[BinarBridge.phaseIndexEquiv m row][BinarBridge.phaseIndexEquiv m column]

structure StoredAction (m : ℕ) where
  rows : Vector (Vector F2 (m + m)) (m + m)
  valid : IsSymplectic (decodeRows rows)

def StoredAction.action {m : ℕ} (stored : StoredAction m) : SymplecticAction m :=
  ⟨decodeRows stored.rows, stored.valid⟩

def store {m : ℕ} (target : SymplecticAction m) : StoredAction m :=
  let rows := Vector.ofFn fun row : Fin (m + m) =>
    Vector.ofFn fun column : Fin (m + m) =>
      (target : ActionMatrix m) ((BinarBridge.phaseIndexEquiv m).symm row)
        ((BinarBridge.phaseIndexEquiv m).symm column)
  ⟨rows, by
    have same : decodeRows rows = (target : ActionMatrix m) := by
      funext row column
      simp [decodeRows, rows]
    rw [same]
    exact target.property⟩

theorem action_store {m : ℕ} (target : SymplecticAction m) : (store target).action = target := by
  apply Subtype.ext
  funext row column
  simp [StoredAction.action, store, decodeRows]

def storedDecomposition {m : ℕ} (stored : StoredAction m) : List (PhaseVector m) :=
  match _returned : nextVector (stored.action : ActionMatrix m) with
  | none => []
  | some vector =>
      storedDecomposition
        (store (stored.action * transvectionAction (residueVector (stored.action : ActionMatrix m) vector))) ++
        [residueVector (stored.action : ActionMatrix m) vector]
termination_by potential (stored.action : ActionMatrix m)
decreasing_by
  rw [action_store]
  exact step_decreases stored.action vector _returned

def decomposition {m : ℕ} (target : SymplecticAction m) : List (PhaseVector m) :=
  storedDecomposition (store target)

theorem decomposition_of_none {m : ℕ} (target : SymplecticAction m)
    (returned : nextVector (target : ActionMatrix m) = none) : decomposition target = [] := by
  rw [decomposition, storedDecomposition]
  split <;> simp_all [action_store]

theorem decomposition_of_some {m : ℕ} (target : SymplecticAction m) (vector : PhaseVector m)
    (returned : nextVector (target : ActionMatrix m) = some vector) :
    decomposition target =
      decomposition (target * transvectionAction (residueVector (target : ActionMatrix m) vector)) ++
        [residueVector (target : ActionMatrix m) vector] := by
  unfold decomposition
  rw [storedDecomposition]
  split <;> simp_all [action_store]

theorem decomposition_spec {m : ℕ} (target : SymplecticAction m) :
    IsFactorization target (decomposition target) ∧
    (decomposition target).length ≤ potential (target : ActionMatrix m) ∧
    ∀ center ∈ decomposition target, center ≠ 0 := by
  cases returned : nextVector (target : ActionMatrix m) with
  | none =>
      have identity : target = 1 := Subtype.ext ((nextVector_none_iff _).mp returned)
      rw [decomposition_of_none target returned]
      simp [IsFactorization, identity]
  | some vector =>
      have recursive := decomposition_spec
        (target * transvectionAction (residueVector (target : ActionMatrix m) vector))
      have selected := nextVector_some (target : ActionMatrix m) vector returned
      have decrease := step_decreases target vector returned
      rw [decomposition_of_some target vector returned]
      refine ⟨?_, ?_, ?_⟩
      · change productTransvections _ = target
        rw [productTransvections_append, recursive.1, productTransvections_cons,
          productTransvections_nil, mul_one, mul_assoc]
        have squared : transvectionAction (residueVector (target : ActionMatrix m) vector) *
            transvectionAction (residueVector (target : ActionMatrix m) vector) = 1 :=
          Subtype.ext (transvection_squared _)
        rw [squared, mul_one]
      · simp only [List.length_append, List.length_singleton]
        exact Nat.le_trans (Nat.add_le_add_right recursive.2.1 1) (Nat.succ_le_of_lt decrease)
      · intro center member
        rcases List.mem_append.mp member with earlier | last
        · exact recursive.2.2 center earlier
        · have same := List.mem_singleton.mp last
          simpa only [same] using selected.1
termination_by potential (target : ActionMatrix m)
decreasing_by exact step_decreases target vector returned

def paulis {m : ℕ} (target : SymplecticAction m) : List (Pauli m) :=
  (decomposition target).map fun center => Pauli.positiveRepresentative (ProjectivePauli.ofPhaseVector center)

theorem paulis_projective {m : ℕ} (target : SymplecticAction m) :
    (paulis target).map (fun pauli => pauli.projective.toPhaseVector) = decomposition target := by
  simp [paulis, Function.comp_def]

theorem full_spec {m : ℕ} (target : SymplecticAction m) :
    IsFactorization target ((paulis target).map (fun pauli => pauli.projective.toPhaseVector)) ∧
    residueRank (target : ActionMatrix m) ≤ (paulis target).length ∧
    (paulis target).length ≤ 4 * m + 1 ∧
    ∀ pauli ∈ paulis target, pauli.xyzPhase = 0 ∧ pauli.IsHermitian ∧
      pauli.projective.toPhaseVector ≠ 0 := by
  have valid := decomposition_spec target
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [paulis_projective]
    exact valid.1
  · have lower := residueRank_product_le_length (decomposition target)
    rw [valid.1] at lower
    simpa only [paulis, List.length_map] using lower
  · simpa only [paulis, List.length_map] using valid.2.1.trans (potential_bound (target : ActionMatrix m))
  · intro pauli member
    rw [paulis, List.mem_map] at member
    obtain ⟨center, member, rfl⟩ := member
    refine ⟨Pauli.xyzPhase_positiveRepresentative _,
      (Pauli.isHermitian_iff_isOrderTwo _).mpr (Pauli.positiveRepresentative_isOrderTwo _), ?_⟩
    simpa using valid.2.2 center member

end PaulimerFormal.GreedyDecomposition
