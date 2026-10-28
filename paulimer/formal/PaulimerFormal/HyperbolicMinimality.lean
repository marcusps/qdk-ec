import PaulimerFormal.GreedyReduction
import PaulimerFormal.UpperBound
import PaulimerFormal.TransvectionImplementation

/-! Nonidentity hyperbolic actions have minimum transvection length rank plus one. -/

namespace PaulimerFormal.HyperbolicMinimality

open Matrix GreedyReduction TransvectionRefinement

theorem residue_alternating {size : ℕ} (target : ActionMatrix size)
    (hyperbolic : IsHyperbolic target) : (residueMatrix target).toBilin'.IsAlt := by
  intro vector
  have zero := hyperbolic ((omega size).mulVec vector)
  rw [pairing_comm, pairing, rowAction, Matrix.mulVec_mulVec, omega_squared, Matrix.one_mulVec,
    ← Matrix.dotProduct_mulVec] at zero
  rw [← omega_transpose size, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec] at zero
  rw [Matrix.toBilin'_apply', residueMatrix, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_add, dotProduct_add]
  change pairing vector vector + _ = 0
  rw [pairing_self, zero_add]
  exact zero

theorem sandwich_diagonal {size dimension : ℕ} (target : ActionMatrix size)
    (hyperbolic : IsHyperbolic target) (rows : Matrix (Fin dimension) (PhaseIndex size) F2)
    (index : Fin dimension) :
    (rows * residueMatrix target * rows.transpose) index index = 0 := by
  have zero := residue_alternating target hyperbolic (rows index)
  rw [Matrix.toBilin'_apply', Matrix.dotProduct_mulVec] at zero
  exact zero

theorem positive_dimension {size dimension : ℕ} {target : SymplecticAction size}
    (presentation : CorePresentation target dimension) (nonidentity : target ≠ 1) : 0 < dimension := by
  by_contra not_positive
  have empty : dimension = 0 := by omega
  subst dimension
  have zero : residueMatrix target.val = 0 := by
    simpa [Matrix.mul_apply] using presentation.residue_eq
  apply nonidentity
  apply Subtype.ext
  apply residueMatrix_injective
  rw [zero]
  simp [residueMatrix, ZModModule.add_self]

theorem not_triangularizable {size dimension : ℕ} {target : SymplecticAction size}
    (presentation : CorePresentation target dimension) (nonidentity : target ≠ 1)
    (hyperbolic : IsHyperbolic target.val) : ¬presentation.IsTriangularizable := by
  have containment : Submodule.span F2 (Set.range presentation.basis.row) ≤
      Submodule.span F2 (Set.range (residueMatrix target.val).row) := by
    rw [← residueSpace_eq_span_rows_residueMatrix]
    change Submodule.span F2 (Set.range presentation.basis) ≤ residueSpace target.val
    rw [presentation.basis_span]
  obtain ⟨transform, reduced⟩ :=
    exists_mul_eq_of_span_rows_le presentation.basis (residueMatrix target.val) containment
  intro ⟨change, _, lower⟩
  have representation : change * presentation.core * change.transpose =
      (change * transform) * residueMatrix target.val * (change * transform).transpose := by
    rw [presentation.core_eq_of_row_reduction transform reduced, ← reduced, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have diagonal := lower.2 ⟨0, positive_dimension presentation nonidentity⟩
  rw [representation, sandwich_diagonal target.val hyperbolic] at diagonal
  exact zero_ne_one diagonal

theorem minimum_spec {size : ℕ} (target : SymplecticAction size) (nonidentity : target ≠ 1)
    (hyperbolic : IsHyperbolic target.val) :
    (∃ centers, IsShortest target centers ∧ centers.length = residueRank target.val + 1) ∧
    ∀ centers, IsShortest target centers → centers.length = residueRank target.val + 1 := by
  let presentation := canonicalCorePresentation target
  obtain ⟨centers, replay, minimal, lengths, at_rank⟩ := presentation.exists_minimal_factorization
  have not_at_rank := not_triangularizable presentation nonidentity hyperbolic
  have length : centers.length = residueRank target.val + 1 := by
    rcases lengths with equal | equal
    · exact (not_at_rank (at_rank.mp equal)).elim
    · exact equal
  refine ⟨⟨centers, ⟨replay, minimal⟩, length⟩, ?_⟩
  intro other shortest
  have equal : other.length = centers.length :=
    Nat.le_antisymm (shortest.2 centers replay) (minimal other shortest.1)
  exact equal.trans length

end PaulimerFormal.HyperbolicMinimality
