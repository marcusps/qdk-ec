import PaulimerFormal.TriangularSearch

/-!
# Failure caching and complement deduplication

Keys need only have no false collisions. The two finite key lists model
Rust's membership sets; their order and duplicate entries are unobservable.
-/

namespace PaulimerFormal.Triangularization

variable {V : Type*} [AddCommGroup V] [Module F2 V]
variable {Key : Type*}

def NoFalseCollisions (key : {n : ℕ} → (Fin n → V) → Key) : Prop :=
  ∀ {n m} (first : Fin n → V) (second : Fin m → V),
    key first = key second → familySpan first = familySpan second

theorem search_none_of_span_eq {n m : ℕ} (form : LinearMap.BilinForm F2 V)
    (first : Fin n → V) (second : Fin m → V)
    (first_independent : LinearIndependent F2 first)
    (second_independent : LinearIndependent F2 second)
    (same_span : familySpan first = familySpan second)
    (failed : search form first = none) : search form second = none := by
  have first_rank : Module.finrank F2 (familySpan first) = n := by
    simpa only [familySpan, Fintype.card_fin] using finrank_span_eq_card first_independent
  have second_rank : Module.finrank F2 (familySpan second) = m := by
    simpa only [familySpan, Fintype.card_fin] using finrank_span_eq_card second_independent
  have same_length : n = m := by
    rw [same_span, second_rank] at first_rank
    exact first_rank.symm
  subst m
  apply (search_none_iff form second second_independent).mpr
  rw [← same_span]
  exact (search_none_iff form first first_independent).mp failed

def CacheSound (form : LinearMap.BilinForm F2 V)
    (key : {n : ℕ} → (Fin n → V) → Key) (cache : List Key) : Prop :=
  ∀ (n : ℕ) (basis : Fin n → V), LinearIndependent F2 basis →
    key basis ∈ cache → search form basis = none

theorem cacheSound_nil (form : LinearMap.BilinForm F2 V)
    (key : {n : ℕ} → (Fin n → V) → Key) : CacheSound form key [] := by
  intro n basis independent member
  simp at member

theorem cacheSound_insert {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (key : {n : ℕ} → (Fin n → V) → Key) (keys_sound : NoFalseCollisions key)
    (basis : Fin n → V) (independent : LinearIndependent F2 basis)
    (failed : search form basis = none) (cache : List Key)
    (sound : CacheSound form key cache) : CacheSound form key (key basis :: cache) := by
  intro m other other_independent member
  rcases List.mem_cons.mp member with equal | member
  · exact search_none_of_span_eq form basis other independent other_independent
      (keys_sound basis other equal.symm) failed
  · exact sound _ other other_independent member

variable [DecidableEq Key]

def scanCandidates {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (key : {n : ℕ} → (Fin n → V) → Key) (basis : Fin (n + 1) → V)
    (recurse : (Fin n → V) → List Key → Option (Fin n → V) × List Key) :
    List V → List Key → List Key → Option (Fin (n + 1) → V) × List Key
  | [], failures, _ => (none, failures)
  | pick :: remaining, failures, explored =>
      if form pick pick = 1 then
        match couplingPivot (form pick) basis with
        | none => scanCandidates form key basis recurse remaining failures explored
        | some pivot =>
            let complement := complementVectors (form pick) basis pivot
            if key complement ∈ explored then
              scanCandidates form key basis recurse remaining failures explored
            else
              match recurse complement failures with
              | (none, updated) =>
                  scanCandidates form key basis recurse remaining updated (key complement :: explored)
              | (some rest, updated) => (some (Fin.cons pick rest), updated)
      else scanCandidates form key basis recurse remaining failures explored

def memoSearch (form : LinearMap.BilinForm F2 V)
    (key : {n : ℕ} → (Fin n → V) → Key) :
    {n : ℕ} → (Fin n → V) → List Key → Option (Fin n → V) × List Key
  | 0, basis, failures => (some basis, failures)
  | n + 1, basis, failures =>
      if key basis ∈ failures then (none, failures)
      else if alternatingCheck form basis then (none, key basis :: failures)
      else
        match scanCandidates form key basis (memoSearch form key (n := n))
            (spanVectors basis) failures [] with
        | (none, updated) => (none, key basis :: updated)
        | (some result, updated) => (some result, updated)

theorem scanCandidates_spec {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (key : {n : ℕ} → (Fin n → V) → Key) (keys_sound : NoFalseCollisions key)
    (basis : Fin (n + 1) → V) (independent : LinearIndependent F2 basis)
    (recurse : (Fin n → V) → List Key → Option (Fin n → V) × List Key)
    (recursive_spec : ∀ basis, LinearIndependent F2 basis →
      ∀ failures, CacheSound form key failures →
        (recurse basis failures).1 = search form basis ∧
          CacheSound form key (recurse basis failures).2)
    (candidates : List V) (failures explored : List Key)
    (failures_sound : CacheSound form key failures)
    (explored_sound : CacheSound form key explored) :
    (scanCandidates form key basis recurse candidates failures explored).1 =
        candidates.findSome? (tryPick form basis (search form (n := n))) ∧
      CacheSound form key (scanCandidates form key basis recurse candidates failures explored).2 := by
  induction candidates generalizing failures explored with
  | nil => exact ⟨rfl, failures_sound⟩
  | cons pick remaining induction =>
      by_cases self_pairing : form pick pick = 1
      · cases found : couplingPivot (form pick) basis with
        | none =>
            simpa [scanCandidates, self_pairing, found, List.findSome?_cons, tryPick] using
              induction failures explored failures_sound explored_sound
        | some pivot =>
            let complement := complementVectors (form pick) basis pivot
            have complement_independent : LinearIndependent F2 complement :=
              Triangularization.complement_independent _ _ _ independent
            by_cases seen : key complement ∈ explored
            · have failed := explored_sound _ complement complement_independent seen
              simpa [scanCandidates, self_pairing, found, show
                complementVectors (form pick) basis pivot = complement from rfl,
                seen, List.findSome?_cons, tryPick, failed] using
                induction failures explored failures_sound explored_sound
            · have recursive := recursive_spec complement complement_independent failures failures_sound
              cases recursed : recurse complement failures with
              | mk answer updated =>
                  rw [recursed] at recursive
                  cases answer with
                  | none =>
                      have failed : search form complement = none := recursive.1.symm
                      have extended := cacheSound_insert form key keys_sound complement
                        complement_independent failed explored explored_sound
                      simpa [scanCandidates, self_pairing, found, show
                        complementVectors (form pick) basis pivot = complement from rfl,
                        seen, recursed, List.findSome?_cons, tryPick, failed] using
                        induction updated (key complement :: explored) recursive.2 extended
                  | some rest =>
                      have succeeded : search form complement = some rest := recursive.1.symm
                      simpa [scanCandidates, self_pairing, found, show
                        complementVectors (form pick) basis pivot = complement from rfl,
                        seen, recursed, List.findSome?_cons, tryPick, succeeded] using
                        (show (some (Fin.cons pick rest) : Option (Fin (n + 1) → V)) =
                            some (Fin.cons pick rest) ∧ CacheSound form key updated from
                          ⟨rfl, recursive.2⟩)
      · simpa [scanCandidates, self_pairing, List.findSome?_cons, tryPick] using
          induction failures explored failures_sound explored_sound

theorem memoSearch_spec {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (key : {n : ℕ} → (Fin n → V) → Key) (keys_sound : NoFalseCollisions key)
    (basis : Fin n → V) (independent : LinearIndependent F2 basis)
    (failures : List Key) (sound : CacheSound form key failures) :
    (memoSearch form key basis failures).1 = search form basis ∧
      CacheSound form key (memoSearch form key basis failures).2 := by
  induction n generalizing failures with
  | zero => exact ⟨rfl, sound⟩
  | succ n induction =>
      by_cases known : key basis ∈ failures
      · have failed := sound _ basis independent known
        simpa [memoSearch, known, failed] using
          (show (none : Option (Fin (n + 1) → V)) = none ∧ CacheSound form key failures from
            ⟨rfl, sound⟩)
      · by_cases alternating : alternatingCheck form basis = true
        · have failed : search form basis = none := by simp [search, alternating]
          have extended := cacheSound_insert form key keys_sound basis independent failed failures sound
          simpa [memoSearch, known, alternating, failed] using
            And.intro (rfl : none = (none : Option (Fin (n + 1) → V))) extended
        · have scanned := scanCandidates_spec form key keys_sound basis independent
            (memoSearch form key (n := n)) induction (spanVectors basis) failures [] sound
            (cacheSound_nil form key)
          cases result : scanCandidates form key basis (memoSearch form key (n := n))
              (spanVectors basis) failures [] with
          | mk answer updated =>
              rw [result] at scanned
              have agrees : answer = search form basis := by
                simpa [search, alternating] using scanned.1
              cases answer with
              | none =>
                  have extended := cacheSound_insert form key keys_sound basis independent
                    agrees.symm updated scanned.2
                  simpa [memoSearch, known, alternating, result] using And.intro agrees extended
              | some solution =>
                  simpa [memoSearch, known, alternating, result] using
                    (show some solution = search form basis ∧ CacheSound form key updated from
                      ⟨agrees, scanned.2⟩)

theorem memoSearch_empty_eq_search {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (key : {n : ℕ} → (Fin n → V) → Key) (keys_sound : NoFalseCollisions key)
    (basis : Fin n → V) (independent : LinearIndependent F2 basis) :
    (memoSearch form key basis []).1 = search form basis :=
  (memoSearch_spec form key keys_sound basis independent [] (cacheSound_nil form key)).1

end PaulimerFormal.Triangularization
