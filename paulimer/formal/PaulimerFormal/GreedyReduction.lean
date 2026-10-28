import PaulimerFormal.Triangularization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Rank reduction and hyperbolic escape for the greedy transvection algorithm. -/

namespace PaulimerFormal.GreedyReduction

def residueVector {m : ℕ} (action : ActionMatrix m) (vector : PhaseVector m) : PhaseVector m :=
  vector + rowAction vector action

def IsHyperbolic {m : ℕ} (action : ActionMatrix m) : Prop :=
  ∀ vector, pairing vector (rowAction vector action) = 0

def imageForm {m : ℕ} (action : ActionMatrix m) : LinearMap.BilinForm F2 (PhaseVector m) :=
  (omega m * action.transpose).toBilin'

theorem imageForm_apply {m : ℕ} (action : ActionMatrix m) (left right : PhaseVector m) :
    imageForm action left right = pairing left (rowAction right action) := by
  rw [imageForm, Matrix.toBilin'_apply', ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]
  rfl

theorem hyperbolic_iff_isAlt {m : ℕ} (action : ActionMatrix m) :
    IsHyperbolic action ↔ (imageForm action).IsAlt := by
  simp only [IsHyperbolic, LinearMap.BilinForm.IsAlt, LinearMap.IsAlt, imageForm_apply]

theorem hyperbolic_pairing {m : ℕ} (action : ActionMatrix m)
    (hyperbolic : IsHyperbolic action) (left right : PhaseVector m) :
    pairing (rowAction left action) right = pairing left (rowAction right action) := by
  have symmetry := (LinearMap.BilinForm.IsAlt.isSymm_f2
    ((hyperbolic_iff_isAlt action).mp hyperbolic)).eq left right
  rw [imageForm_apply, imageForm_apply] at symmetry
  rw [pairing_comm (rowAction left action) right]
  exact symmetry.symm

theorem exists_pairing_one {m : ℕ} (vector : PhaseVector m) (nonzero : vector ≠ 0) :
    ∃ other, pairing other vector = 1 := by
  classical
  by_contra missing
  have all_zero (other : PhaseVector m) : pairing other vector = 0 := by
    by_contra nonzero_pairing
    exact missing ⟨other, f2_eq_one_of_ne_zero _ nonzero_pairing⟩
  have image_zero : (omega m).mulVec vector = 0 := by
    funext index
    simpa [pairing] using all_zero (Pi.single index 1)
  apply nonzero
  have double_image := congrArg (omega m).mulVec image_zero
  simpa [Matrix.mulVec_mulVec] using double_image

theorem fixedSpace_le_updated {m : ℕ} (target : SymplecticAction m) (vector : PhaseVector m) :
    fixedSpace (target : ActionMatrix m) ≤
      fixedSpace ((target : ActionMatrix m) * transvection (residueVector (target : ActionMatrix m) vector)) := by
  intro fixed member
  have fixed_eq := (mem_fixedSpace_iff _ _).mp member
  have preserved := pairing_rowAction target.property fixed vector
  rw [fixed_eq] at preserved
  have orthogonal : pairing fixed (residueVector (target : ActionMatrix m) vector) = 0 := by
    rw [residueVector, pairing_add_right, preserved, f2_add_self]
  rw [mem_fixedSpace_iff, ← rowAction_mul, rowAction_transvection, fixed_eq, orthogonal,
    zero_smul, add_zero]

theorem lowering_vector_fixed {m : ℕ} (target : SymplecticAction m) (vector : PhaseVector m)
    (active : pairing vector (rowAction vector (target : ActionMatrix m)) = 1) :
    vector ∈ fixedSpace
      ((target : ActionMatrix m) * transvection (residueVector (target : ActionMatrix m) vector)) := by
  rw [mem_fixedSpace_iff, ← rowAction_mul, rowAction_transvection, residueVector,
    pairing_add_right, pairing_self, add_zero, pairing_comm, active, one_smul]
  simp [add_left_comm, ZModModule.add_self]

theorem lowering_vector_not_fixed {m : ℕ} (target : SymplecticAction m) (vector : PhaseVector m)
    (active : pairing vector (rowAction vector (target : ActionMatrix m)) = 1) :
    vector ∉ fixedSpace (target : ActionMatrix m) := by
  intro member
  rw [(mem_fixedSpace_iff _ _).mp member, pairing_self] at active
  exact zero_ne_one active

theorem lowering_fixedSpace {m : ℕ} (target : SymplecticAction m) (vector : PhaseVector m)
    (active : pairing vector (rowAction vector (target : ActionMatrix m)) = 1) :
    fixedSpace ((target : ActionMatrix m) * transvection (residueVector (target : ActionMatrix m) vector)) =
      fixedSpace (target : ActionMatrix m) ⊔ Submodule.span F2 {vector} := by
  apply le_antisymm
  · intro other member
    have fixed_eq := (mem_fixedSpace_iff _ _).mp member
    rw [← rowAction_mul, rowAction_transvection] at fixed_eq
    by_cases zero : pairing (rowAction other (target : ActionMatrix m))
        (residueVector (target : ActionMatrix m) vector) = 0
    · rw [zero, zero_smul, add_zero] at fixed_eq
      exact Submodule.mem_sup_left ((mem_fixedSpace_iff _ _).mpr fixed_eq)
    · have one := f2_eq_one_of_ne_zero _ zero
      rw [one, one_smul] at fixed_eq
      have sum_fixed : other + vector ∈ fixedSpace (target : ActionMatrix m) := by
        rw [mem_fixedSpace_iff, rowAction_add]
        calc
          rowAction other (target : ActionMatrix m) + rowAction vector (target : ActionMatrix m) =
              (rowAction other (target : ActionMatrix m) +
                residueVector (target : ActionMatrix m) vector) + vector := by
            simp only [residueVector, add_comm vector (rowAction vector (target : ActionMatrix m)),
              add_assoc, ZModModule.add_self, add_zero]
          _ = other + vector := congrArg (fun value => value + vector) fixed_eq
      apply Submodule.mem_sup.mpr
      refine ⟨other + vector, sum_fixed, vector, Submodule.subset_span (Set.mem_singleton vector), ?_⟩
      simp [add_assoc, ZModModule.add_self]
  · apply sup_le (fixedSpace_le_updated target vector)
    rw [Submodule.span_singleton_le_iff_mem]
    exact lowering_vector_fixed target vector active

theorem lowering_rank {m : ℕ} (target : SymplecticAction m) (vector : PhaseVector m)
    (active : pairing vector (rowAction vector (target : ActionMatrix m)) = 1) :
    residueRank
      ((target : ActionMatrix m) * transvection (residueVector (target : ActionMatrix m) vector)) + 1 =
      residueRank (target : ActionMatrix m) := by
  have dimension := Submodule.finrank_sup_span_singleton (lowering_vector_not_fixed target vector active)
  rw [← lowering_fixedSpace target vector active] at dimension
  have old_rank := residueRank_add_finrank_fixedSpace (target : ActionMatrix m)
  have new_rank := residueRank_add_finrank_fixedSpace
    ((target : ActionMatrix m) * transvection (residueVector (target : ActionMatrix m) vector))
  omega

theorem hyperbolic_fixedSpace {m : ℕ} (target : SymplecticAction m)
    (hyperbolic : IsHyperbolic (target : ActionMatrix m)) (vector : PhaseVector m) :
    fixedSpace ((target : ActionMatrix m) * transvection (residueVector (target : ActionMatrix m) vector)) =
      fixedSpace (target : ActionMatrix m) := by
  apply le_antisymm
  · intro other member
    have fixed_eq := (mem_fixedSpace_iff _ _).mp member
    rw [← rowAction_mul, rowAction_transvection] at fixed_eq
    by_cases zero : pairing (rowAction other (target : ActionMatrix m))
        (residueVector (target : ActionMatrix m) vector) = 0
    · rw [zero, zero_smul, add_zero] at fixed_eq
      exact (mem_fixedSpace_iff _ _).mpr fixed_eq
    · have one := f2_eq_one_of_ne_zero _ zero
      rw [one, one_smul] at fixed_eq
      have residue_eq :
          residueVector (target : ActionMatrix m) vector = rowAction other (target : ActionMatrix m) + other := by
        simpa only [← add_assoc, ZModModule.add_self, zero_add] using
          congrArg (fun value => rowAction other (target : ActionMatrix m) + value) fixed_eq
      rw [residue_eq, pairing_add_right, pairing_self, zero_add, pairing_comm, hyperbolic other] at one
      exact (zero_ne_one one).elim
  · exact fixedSpace_le_updated target vector

theorem hyperbolic_rank {m : ℕ} (target : SymplecticAction m)
    (hyperbolic : IsHyperbolic (target : ActionMatrix m)) (vector : PhaseVector m) :
    residueRank
      ((target : ActionMatrix m) * transvection (residueVector (target : ActionMatrix m) vector)) =
      residueRank (target : ActionMatrix m) := by
  have old_rank := residueRank_add_finrank_fixedSpace (target : ActionMatrix m)
  have new_rank := residueRank_add_finrank_fixedSpace
    ((target : ActionMatrix m) * transvection (residueVector (target : ActionMatrix m) vector))
  rw [hyperbolic_fixedSpace target hyperbolic vector] at new_rank
  omega

theorem hyperbolic_residue_pairing {m : ℕ} (target : SymplecticAction m)
    (hyperbolic : IsHyperbolic (target : ActionMatrix m)) (vector other : PhaseVector m) :
    pairing (rowAction other (target : ActionMatrix m)) (residueVector (target : ActionMatrix m) vector) =
      pairing other (residueVector (target : ActionMatrix m) vector) := by
  rw [residueVector, pairing_add_right, pairing_add_right,
    hyperbolic_pairing _ hyperbolic, pairing_rowAction target.property, add_comm]

theorem hyperbolic_escape {m : ℕ} (target : SymplecticAction m)
    (hyperbolic : IsHyperbolic (target : ActionMatrix m)) (vector : PhaseVector m)
    (nonzero : residueVector (target : ActionMatrix m) vector ≠ 0) :
    ¬ IsHyperbolic
      ((target : ActionMatrix m) * transvection (residueVector (target : ActionMatrix m) vector)) := by
  obtain ⟨other, paired⟩ := exists_pairing_one _ nonzero
  have active : pairing other (rowAction other
      ((target : ActionMatrix m) * transvection (residueVector (target : ActionMatrix m) vector))) = 1 := by
    rw [← rowAction_mul, rowAction_transvection, pairing_add_right, pairing_smul_right,
      hyperbolic other, hyperbolic_residue_pairing target hyperbolic, paired]
    rfl
  intro remains_hyperbolic
  rw [remains_hyperbolic other] at active
  exact zero_ne_one active

theorem reduction_spec {m : ℕ} (target : SymplecticAction m) (vector : PhaseVector m) :
    (pairing vector (rowAction vector (target : ActionMatrix m)) = 1 →
      residueRank
        ((target : ActionMatrix m) * transvection (residueVector (target : ActionMatrix m) vector)) + 1 =
        residueRank (target : ActionMatrix m)) ∧
    (IsHyperbolic (target : ActionMatrix m) →
      residueRank
        ((target : ActionMatrix m) * transvection (residueVector (target : ActionMatrix m) vector)) =
        residueRank (target : ActionMatrix m)) ∧
    (IsHyperbolic (target : ActionMatrix m) →
      residueVector (target : ActionMatrix m) vector ≠ 0 →
      ¬ IsHyperbolic
        ((target : ActionMatrix m) * transvection (residueVector (target : ActionMatrix m) vector))) := by
  exact ⟨lowering_rank target vector, fun hyperbolic => hyperbolic_rank target hyperbolic vector,
    fun hyperbolic => hyperbolic_escape target hyperbolic vector⟩

end PaulimerFormal.GreedyReduction
