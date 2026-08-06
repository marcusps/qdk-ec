import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import PaulimerFormal.Symplectic

/-! Symplectic simplices for nondegenerate alternating forms over `F2`. -/

namespace PaulimerFormal

open Module
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module F2 V]
  [FiniteDimensional F2 V]

theorem f2_eq_one_of_ne_zero (value : F2) (nonzero : value ≠ 0) :
    value = 1 := by
  fin_cases value
  · exact (nonzero rfl).elim
  · rfl

omit [FiniteDimensional F2 V] in
theorem add_self_eq_zero_f2 (vector : V) : vector + vector = 0 := by
  rw [← one_smul F2 vector, ← add_smul, f2_add_self, zero_smul]

omit [FiniteDimensional F2 V] in
theorem two_nsmul_eq_zero_f2 (vector : V) : 2 • vector = 0 := by
  simpa [two_nsmul] using add_self_eq_zero_f2 vector

omit [FiniteDimensional F2 V] in
theorem nsmul_eq_self_of_odd_f2 (vector : V) {count : ℕ}
    (odd : Odd count) :
    count • vector = vector := by
  obtain ⟨half, rfl⟩ := odd
  rw [add_nsmul, mul_nsmul, two_nsmul_eq_zero_f2, nsmul_zero,
    zero_add, one_nsmul]

omit [FiniteDimensional F2 V] in
theorem LinearMap.BilinForm.IsAlt.isSymm_f2
    {form : LinearMap.BilinForm F2 V} (alternating : form.IsAlt) :
    form.IsSymm := by
  constructor
  intro first second
  rw [← alternating.neg_eq first second, f2_neg]

structure SymplecticSimplex (form : LinearMap.BilinForm F2 V) where
  points : Finset V
  card_eq : points.card = Module.finrank F2 V + 1
  card_odd : Odd points.card
  sum_eq_zero : ∑ point ∈ points, point = 0
  spans : Submodule.span F2 (points : Set V) = ⊤
  pair_eq_one :
    ∀ ⦃first⦄, first ∈ points →
      ∀ ⦃second⦄, second ∈ points →
        first ≠ second → form first second = 1

noncomputable def symplecticSimplexOfFinrankZero
    (form : LinearMap.BilinForm F2 V)
    (dimension_zero : Module.finrank F2 V = 0) :
    SymplecticSimplex form := by
  refine
    { points := {0}
      card_eq := by simp [dimension_zero]
      card_odd := by simp
      sum_eq_zero := by simp
      spans := ?_
      pair_eq_one := ?_ }
  · apply le_antisymm le_top
    intro vector _
    have vector_zero :=
      (finrank_zero_iff_forall_zero.mp
        dimension_zero) vector
    simp [vector_zero]
  · intro first first_mem second second_mem distinct
    simp only [Finset.mem_singleton] at first_mem second_mem
    exact (distinct (first_mem.trans second_mem.symm)).elim

theorem exists_pair_eq_one
    {form : LinearMap.BilinForm F2 V}
    (nondegenerate : form.Nondegenerate)
    (dimension_positive : 0 < Module.finrank F2 V) :
    ∃ first second : V, form first second = 1 := by
  letI : Nontrivial V := Module.finrank_pos_iff.mp dimension_positive
  obtain ⟨first, first_nonzero⟩ := exists_ne (0 : V)
  have exists_second : ∃ second, form first second ≠ 0 := by
    by_contra none
    push Not at none
    exact first_nonzero (nondegenerate.1 first none)
  obtain ⟨second, pairing_nonzero⟩ := exists_second
  exact ⟨first, second,
    f2_eq_one_of_ne_zero (form first second) pairing_nonzero⟩

theorem pairSpan_restrict_nondegenerate
    {form : LinearMap.BilinForm F2 V}
    (alternating : form.IsAlt)
    {first second : V} (pair_eq_one : form first second = 1) :
    (form.restrict (Submodule.span F2 {first, second})).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro vector annihilates
  apply Subtype.ext
  obtain ⟨firstCoefficient, secondCoefficient, vector_eq⟩ :=
    Submodule.mem_span_pair.mp vector.property
  have first_mem :
      first ∈ Submodule.span F2 ({first, second} : Set V) :=
    Submodule.subset_span (by simp)
  have second_mem :
      second ∈ Submodule.span F2 ({first, second} : Set V) :=
    Submodule.subset_span (by simp)
  have at_first := annihilates ⟨first, first_mem⟩
  have at_second := annihilates ⟨second, second_mem⟩
  change form vector.1 first = 0 at at_first
  change form vector.1 second = 0 at at_second
  have reverse_pair : form second first = 1 := by
    simpa [f2_neg, pair_eq_one] using
      (alternating.neg_eq first second).symm
  have first_self := alternating.self_eq_zero first
  have second_self := alternating.self_eq_zero second
  rw [← vector_eq] at at_first at_second
  have secondCoefficient_zero : secondCoefficient = 0 := by
    simpa [first_self, reverse_pair] using at_first
  have firstCoefficient_zero : firstCoefficient = 0 := by
    simpa [pair_eq_one, second_self] using at_second
  rw [firstCoefficient_zero, secondCoefficient_zero] at vector_eq
  simpa using vector_eq.symm

omit [FiniteDimensional F2 V] in
theorem pair_linearIndependent
    {form : LinearMap.BilinForm F2 V}
    (alternating : form.IsAlt)
    {first second : V} (pair_eq_one : form first second = 1) :
    LinearIndependent F2 ![first, second] := by
  rw [linearIndependent_fin2]
  change second ≠ 0 ∧ ∀ scalar : F2, scalar • second ≠ first
  constructor
  · intro second_zero
    rw [second_zero, map_zero] at pair_eq_one
    exact zero_ne_one pair_eq_one
  · intro scalar scalar_second_eq_first
    have scalar_eq_zero : scalar = 0 := by
      have evaluated := congrArg (form first) scalar_second_eq_first
      simpa [pair_eq_one, alternating.self_eq_zero first] using evaluated
    rw [scalar_eq_zero, zero_smul] at scalar_second_eq_first
    have first_zero := scalar_second_eq_first.symm
    rw [first_zero, map_zero] at pair_eq_one
    exact zero_ne_one pair_eq_one

omit [FiniteDimensional F2 V] in
theorem finrank_pairSpan
    {form : LinearMap.BilinForm F2 V}
    (alternating : form.IsAlt)
    {first second : V} (pair_eq_one : form first second = 1) :
    Module.finrank F2 (Submodule.span F2 {first, second}) = 2 := by
  let pair : Fin 2 → V := ![first, second]
  have independent : LinearIndependent F2 pair := by
    exact pair_linearIndependent alternating pair_eq_one
  have range_eq : Set.range pair = {first, second} := by
    ext vector
    simp [pair, or_comm]
  rw [← range_eq]
  exact finrank_span_eq_card independent

theorem pairOrthogonal_restrict_nondegenerate
    {form : LinearMap.BilinForm F2 V}
    (nondegenerate : form.Nondegenerate)
    (alternating : form.IsAlt)
    {first second : V} (pair_eq_one : form first second = 1) :
    (form.restrict
      (form.orthogonal
        (Submodule.span F2 {first, second}))).Nondegenerate := by
  let pairSpan := Submodule.span F2 ({first, second} : Set V)
  let complement := form.orthogonal pairSpan
  have pairSpan_nondegenerate :
      (form.restrict pairSpan).Nondegenerate := by
    exact pairSpan_restrict_nondegenerate alternating pair_eq_one
  have complementary :
      IsCompl pairSpan complement :=
    form.isCompl_orthogonal_of_restrict_nondegenerate
      alternating.isRefl pairSpan_nondegenerate
  have double_orthogonal :
      form.orthogonal complement = pairSpan := by
    exact form.orthogonal_orthogonal nondegenerate
      alternating.isRefl pairSpan
  apply form.nondegenerate_restrict_of_disjoint_orthogonal
    alternating.isRefl
  rw [double_orthogonal]
  exact complementary.symm.disjoint

theorem finrank_pairOrthogonal_add_two
    {form : LinearMap.BilinForm F2 V}
    (alternating : form.IsAlt)
    {first second : V} (pair_eq_one : form first second = 1) :
    Module.finrank F2
          (form.orthogonal
            (Submodule.span F2 {first, second})) +
        2 =
      Module.finrank F2 V := by
  let pairSpan := Submodule.span F2 ({first, second} : Set V)
  let complement := form.orthogonal pairSpan
  have pairSpan_nondegenerate :
      (form.restrict pairSpan).Nondegenerate :=
    pairSpan_restrict_nondegenerate alternating pair_eq_one
  have complementary :
      IsCompl pairSpan complement :=
    form.isCompl_orthogonal_of_restrict_nondegenerate
      alternating.isRefl pairSpan_nondegenerate
  have dimensions :=
    Submodule.finrank_add_eq_of_isCompl complementary
  have pair_dimension :
      Module.finrank F2 pairSpan = 2 :=
    finrank_pairSpan alternating pair_eq_one
  rw [pair_dimension] at dimensions
  change Module.finrank F2 complement + 2 = Module.finrank F2 V
  omega

noncomputable def extendSymplecticSimplex
    {form : LinearMap.BilinForm F2 V}
    (alternating : form.IsAlt)
    {first second : V} (pair_eq_one : form first second = 1)
    (simplex :
      SymplecticSimplex
        (form.restrict
          (form.orthogonal
            (Submodule.span F2 {first, second})))) :
    SymplecticSimplex form := by
  classical
  let pairSpan := Submodule.span F2 ({first, second} : Set V)
  let complement := form.orthogonal pairSpan
  let shift : complement → V := fun point => point.1 + first
  let shifted := simplex.points.image shift
  let points := insert second (insert (first + second) shifted)
  have first_mem_pairSpan : first ∈ pairSpan :=
    Submodule.subset_span (by simp)
  have second_mem_pairSpan : second ∈ pairSpan :=
    Submodule.subset_span (by simp)
  have first_self : form first first = 0 :=
    alternating.self_eq_zero first
  have second_self : form second second = 0 :=
    alternating.self_eq_zero second
  have reverse_pair : form second first = 1 := by
    simpa [f2_neg, pair_eq_one] using
      (alternating.neg_eq first second).symm
  have first_nonzero : first ≠ 0 := by
    intro first_zero
    rw [first_zero, map_zero] at pair_eq_one
    exact zero_ne_one pair_eq_one
  have shift_injective : Function.Injective shift := by
    intro left right equal
    apply Subtype.ext
    exact add_right_cancel equal
  have first_pair_complement (point : complement) :
      form first point.1 = 0 :=
    point.2 first first_mem_pairSpan
  have second_pair_complement (point : complement) :
      form second point.1 = 0 :=
    point.2 second second_mem_pairSpan
  have complement_pair_first (point : complement) :
      form point.1 first = 0 := by
    rw [(LinearMap.BilinForm.IsAlt.isSymm_f2 alternating).eq]
    exact first_pair_complement point
  have complement_pair_second (point : complement) :
      form point.1 second = 0 := by
    rw [(LinearMap.BilinForm.IsAlt.isSymm_f2 alternating).eq]
    exact second_pair_complement point
  have second_not_shifted : second ∉ shifted := by
    intro membership
    change second ∈ Finset.image shift simplex.points at membership
    rw [Finset.mem_image] at membership
    obtain ⟨point, point_mem, point_eq⟩ := membership
    have evaluated := congrArg (form first) point_eq
    simp [shift, pair_eq_one, first_pair_complement point,
      first_self] at evaluated
  have sum_not_shifted : first + second ∉ shifted := by
    intro membership
    change first + second ∈ Finset.image shift simplex.points at membership
    rw [Finset.mem_image] at membership
    obtain ⟨point, point_mem, point_eq⟩ := membership
    have evaluated := congrArg (form first) point_eq
    simp [shift, pair_eq_one, first_pair_complement point,
      first_self] at evaluated
  have second_ne_sum : second ≠ first + second := by
    intro equal
    apply first_nonzero
    have := congrArg (fun vector => vector + second) equal
    simpa [add_assoc, add_self_eq_zero_f2] using this.symm
  have second_not_rest :
      second ∉ insert (first + second) shifted := by
    simp [second_ne_sum, second_not_shifted]
  have shifted_sum :
      ∑ point ∈ shifted, point = first := by
    change ∑ point ∈ Finset.image shift simplex.points, point = first
    rw [Finset.sum_image (shift_injective.injOn)]
    simp only [shift, Finset.sum_add_distrib]
    have simplex_sum :
        ∑ point ∈ simplex.points, (point : V) = 0 := by
      calc
        ∑ point ∈ simplex.points, (point : V) =
            complement.subtype
              (∑ point ∈ simplex.points, point) := by
                rw [map_sum]
                rfl
        _ = 0 := by rw [simplex.sum_eq_zero, map_zero]
    rw [simplex_sum, zero_add, Finset.sum_const]
    exact nsmul_eq_self_of_odd_f2 first simplex.card_odd
  have points_sum : ∑ point ∈ points, point = 0 := by
    change ∑ point ∈ insert second
      (insert (first + second) shifted), point = 0
    rw [Finset.sum_insert second_not_rest]
    rw [Finset.sum_insert sum_not_shifted]
    rw [shifted_sum]
    rw [show second + (first + second + first) =
        (second + second) + (first + first) by abel,
      add_self_eq_zero_f2, add_self_eq_zero_f2, zero_add]
  have shifted_pair (left right : complement)
      (left_mem : left ∈ simplex.points)
      (right_mem : right ∈ simplex.points)
      (distinct : left ≠ right) :
      form (shift left) (shift right) = 1 := by
    have old_pair :=
      simplex.pair_eq_one left_mem right_mem distinct
    change form left.1 right.1 = 1 at old_pair
    change form (left.1 + first) (right.1 + first) = 1
    simp [first_pair_complement, complement_pair_first,
      first_self, old_pair]
  have second_pair_shift (point : complement) :
      form second (shift point) = 1 := by
    simp [shift, second_pair_complement, reverse_pair]
  have shift_pair_second (point : complement) :
      form (shift point) second = 1 := by
    rw [(LinearMap.BilinForm.IsAlt.isSymm_f2 alternating).eq]
    exact second_pair_shift point
  have sum_pair_shift (point : complement) :
      form (first + second) (shift point) = 1 := by
    simp [shift, first_pair_complement, second_pair_complement,
      first_self, reverse_pair]
  have shift_pair_sum (point : complement) :
      form (shift point) (first + second) = 1 := by
    rw [(LinearMap.BilinForm.IsAlt.isSymm_f2 alternating).eq]
    exact sum_pair_shift point
  have second_pair_sum :
      form second (first + second) = 1 := by
    simp [second_self, reverse_pair]
  have sum_pair_second :
      form (first + second) second = 1 := by
    rw [(LinearMap.BilinForm.IsAlt.isSymm_f2 alternating).eq]
    exact second_pair_sum
  have pair_points :
      ∀ ⦃left⦄, left ∈ points →
        ∀ ⦃right⦄, right ∈ points →
          left ≠ right → form left right = 1 := by
    intro left left_mem right right_mem distinct
    simp only [points, Finset.mem_insert] at left_mem right_mem
    rcases left_mem with rfl | rfl | left_shifted
    · rcases right_mem with rfl | rfl | right_shifted
      · exact (distinct rfl).elim
      · exact second_pair_sum
      · obtain ⟨point, point_mem, rfl⟩ :=
          Finset.mem_image.mp right_shifted
        exact second_pair_shift point
    · rcases right_mem with rfl | rfl | right_shifted
      · exact sum_pair_second
      · exact (distinct rfl).elim
      · obtain ⟨point, point_mem, rfl⟩ :=
          Finset.mem_image.mp right_shifted
        exact sum_pair_shift point
    · obtain ⟨leftPoint, leftPoint_mem, rfl⟩ :=
        Finset.mem_image.mp left_shifted
      rcases right_mem with rfl | rfl | right_shifted
      · exact shift_pair_second leftPoint
      · exact shift_pair_sum leftPoint
      · obtain ⟨rightPoint, rightPoint_mem, rfl⟩ :=
          Finset.mem_image.mp right_shifted
        apply shifted_pair leftPoint rightPoint
          leftPoint_mem rightPoint_mem
        intro equal
        exact distinct (congrArg shift equal)
  have points_span : Submodule.span F2 (points : Set V) = ⊤ := by
    let spanPoints := Submodule.span F2 (points : Set V)
    have second_mem : second ∈ spanPoints :=
      Submodule.subset_span (by
        simp [points])
    have sum_mem : first + second ∈ spanPoints :=
      Submodule.subset_span (by
        simp [points])
    have first_mem : first ∈ spanPoints := by
      have added := spanPoints.add_mem sum_mem second_mem
      simpa [add_assoc, add_self_eq_zero_f2] using added
    have complement_le : complement ≤ spanPoints := by
      have old_points_le :
          (simplex.points : Set complement) ≤
            Submodule.comap complement.subtype spanPoints := by
        intro point point_mem
        change (point : V) ∈ spanPoints
        have shift_mem_shifted : shift point ∈ shifted := by
          change shift point ∈ Finset.image shift simplex.points
          exact Finset.mem_image.mpr ⟨point, point_mem, rfl⟩
        have shifted_mem : shift point ∈ spanPoints :=
          Submodule.subset_span (by
            simp [points, shift_mem_shifted])
        have added := spanPoints.add_mem shifted_mem first_mem
        simpa [shift, add_assoc, add_self_eq_zero_f2] using added
      have old_span_le :=
        Submodule.span_le.mpr old_points_le
      rw [simplex.spans] at old_span_le
      intro point point_mem
      exact old_span_le
        (x := ⟨point, point_mem⟩) Submodule.mem_top
    have pairSpan_le : pairSpan ≤ spanPoints := by
      change Submodule.span F2 ({first, second} : Set V) ≤ spanPoints
      apply Submodule.span_le.mpr
      rintro point (rfl | rfl)
      · exact first_mem
      · exact second_mem
    have pairSpan_nondegenerate :
        (form.restrict pairSpan).Nondegenerate :=
      pairSpan_restrict_nondegenerate alternating pair_eq_one
    have complementary : IsCompl pairSpan complement :=
      form.isCompl_orthogonal_of_restrict_nondegenerate
        alternating.isRefl pairSpan_nondegenerate
    apply le_antisymm le_top
    rw [← complementary.sup_eq_top]
    exact sup_le pairSpan_le complement_le
  refine
    { points := points
      card_eq := ?_
      card_odd := ?_
      sum_eq_zero := points_sum
      spans := points_span
      pair_eq_one := pair_points }
  · change (insert second (insert (first + second)
      (Finset.image shift simplex.points))).card =
        Module.finrank F2 V + 1
    rw [Finset.card_insert_of_notMem second_not_rest]
    rw [Finset.card_insert_of_notMem sum_not_shifted]
    rw [Finset.card_image_of_injective _ shift_injective,
      simplex.card_eq]
    have dimensions :=
      finrank_pairOrthogonal_add_two alternating pair_eq_one
    omega
  · change Odd (insert second
      (insert (first + second)
        (Finset.image shift simplex.points))).card
    rw [Finset.card_insert_of_notMem second_not_rest]
    rw [Finset.card_insert_of_notMem sum_not_shifted]
    rw [Finset.card_image_of_injective _ shift_injective]
    obtain ⟨half, half_eq⟩ := simplex.card_odd
    refine ⟨half + 1, ?_⟩
    omega

theorem exists_symplecticSimplex
    (form : LinearMap.BilinForm F2 V)
    (nondegenerate : form.Nondegenerate)
    (alternating : form.IsAlt) :
    Nonempty (SymplecticSimplex form) := by
  classical
  generalize dimension_eq : Module.finrank F2 V = dimension
  induction dimension using Nat.strong_induction_on generalizing V with
  | h dimension inductionHypothesis =>
      by_cases dimension_zero : dimension = 0
      · exact ⟨symplecticSimplexOfFinrankZero form
          (dimension_eq.trans dimension_zero)⟩
      · have dimension_positive : 0 < Module.finrank F2 V := by
          rw [dimension_eq]
          omega
        obtain ⟨first, second, pair_eq_one⟩ :=
          exists_pair_eq_one nondegenerate dimension_positive
        let complement :=
          form.orthogonal (Submodule.span F2 {first, second})
        have complement_nondegenerate :
            (form.restrict complement).Nondegenerate :=
          pairOrthogonal_restrict_nondegenerate
            nondegenerate alternating pair_eq_one
        have complement_alternating :
            (form.restrict complement).IsAlt := by
          intro point
          exact alternating point
        have complement_dimension_lt :
            Module.finrank F2 complement < dimension := by
          have dimensions :
              Module.finrank F2 complement + 2 =
                Module.finrank F2 V := by
            simpa [complement] using
              finrank_pairOrthogonal_add_two alternating pair_eq_one
          rw [dimension_eq] at dimensions
          omega
        obtain ⟨simplex⟩ :=
          inductionHypothesis
            (Module.finrank F2 complement)
            complement_dimension_lt
            (V := complement)
            (form.restrict complement)
            complement_nondegenerate
            complement_alternating
            rfl
        exact ⟨extendSymplecticSimplex
          alternating pair_eq_one simplex⟩

end PaulimerFormal
