import PaulimerFormal.Bilinear
import PaulimerFormal.BorderedFactorization
import Mathlib.LinearAlgebra.Dimension.Constructions

open Matrix

namespace PaulimerFormal

def IsBorderedFamily
    {V : Type*} [AddCommGroup V] [Module F2 V]
    {k : ℕ} (form : LinearMap.BilinForm F2 V)
    (vectors : Fin k → V) (relation : Fin k → F2) : Prop :=
  IsUnitLowerTriangular
      (fun row column =>
        form (vectors row) (vectors column) +
          relation row * relation column) ∧
    (∑ index, relation index • vectors index) = 0 ∧
    dotProduct relation relation = 1 ∧
    Submodule.span F2 (Set.range vectors) = ⊤

theorem exists_borderedFamily_of_alternating
    {V : Type*} [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V]
    (form : LinearMap.BilinForm F2 V)
    (nondegenerate : form.Nondegenerate)
    (alternating : form.IsAlt) :
    ∃ vectors : Fin (Module.finrank F2 V + 1) → V,
      ∃ relation : Fin (Module.finrank F2 V + 1) → F2,
        IsBorderedFamily form vectors relation ∧
          relation (Fin.last (Module.finrank F2 V)) = 1 := by
  classical
  obtain ⟨simplex⟩ :=
    exists_symplecticSimplex form nondegenerate alternating
  let pointEquiv :
      Fin (Module.finrank F2 V + 1) ≃
        {point // point ∈ simplex.points} :=
    (simplex.points.equivFinOfCardEq simplex.card_eq).symm
  let vectors : Fin (Module.finrank F2 V + 1) → V :=
    fun index => pointEquiv index
  let relation : Fin (Module.finrank F2 V + 1) → F2 :=
    fun _ => 1
  refine ⟨vectors, relation, ?_, by simp [relation]⟩
  have bordered_matrix_eq :
      (fun row column =>
        form (vectors row) (vectors column) +
          relation row * relation column) =
        (1 : Matrix
          (Fin (Module.finrank F2 V + 1))
          (Fin (Module.finrank F2 V + 1)) F2) := by
    ext row column
    by_cases equal : row = column
    · subst column
      rw [alternating]
      simp [relation]
    · have points_ne :
          (pointEquiv row : V) ≠ pointEquiv column :=
        fun points_eq =>
          equal (pointEquiv.injective (Subtype.ext points_eq))
      rw [simplex.pair_eq_one
        (pointEquiv row).property (pointEquiv column).property points_ne]
      simp [relation, equal]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bordered_matrix_eq]
    constructor
    · intro row column before
      simp [before.ne]
    · intro index
      simp
  · simp only [relation, one_smul]
    change (∑ index, (pointEquiv index : V)) = 0
    rw [Equiv.sum_comp pointEquiv (fun point => (point : V))]
    have sum_eq_zero :
        (∑ point : {point // point ∈ simplex.points}, (point : V)) =
          0 := by
      calc
        (∑ point : {point // point ∈ simplex.points}, (point : V)) =
          ∑ point ∈ simplex.points, point := by
            rw [Finset.univ_eq_attach simplex.points]
            exact Finset.sum_attach simplex.points (fun point => point)
        _ = 0 := simplex.sum_eq_zero
    simpa using sum_eq_zero
  · obtain ⟨half, odd_card⟩ := simplex.card_odd
    have dimension_succ_eq :
        Module.finrank F2 V + 1 = 2 * half + 1 :=
      simplex.card_eq.symm.trans odd_card
    simp [dotProduct, relation, dimension_succ_eq,
      show (2 : F2) = 0 by decide]
  · rw [← simplex.spans]
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨index, rfl⟩
      apply Submodule.subset_span
      exact (pointEquiv index).property
    · refine Submodule.span_le.mpr ?_
      rintro point point_mem
      apply Submodule.subset_span
      refine ⟨pointEquiv.symm ⟨point, point_mem⟩, ?_⟩
      exact congrArg Subtype.val
        (pointEquiv.apply_symm_apply ⟨point, point_mem⟩)

theorem restrict_orthogonal_span_nondegenerate
    {V : Type*} [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V]
    (form : LinearMap.BilinForm F2 V)
    (nondegenerate : form.Nondegenerate)
    {vector : V} (self_ne_zero : form vector vector ≠ 0) :
    (form.restrict
      (form.orthogonal (Submodule.span F2 {vector}))).Nondegenerate := by
  classical
  let line := Submodule.span F2 ({vector} : Set V)
  let complement := form.orthogonal line
  have complementary : IsCompl line complement :=
    form.isCompl_span_singleton_orthogonal self_ne_zero
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingRight
  intro point annihilates
  apply Subtype.ext
  apply nondegenerate.2 point.1
  intro test
  have test_mem : test ∈ line ⊔ complement := by
    rw [complementary.sup_eq_top]
    trivial
  obtain ⟨linePoint, linePoint_mem, complementPoint,
      complementPoint_mem, sum_eq⟩ :=
    Submodule.mem_sup.mp test_mem
  obtain ⟨scalar, linePoint_eq⟩ :=
    Submodule.mem_span_singleton.mp linePoint_mem
  have vector_pair_zero : form vector point.1 = 0 :=
    point.property vector (Submodule.mem_span_singleton_self vector)
  have complement_pair_zero : form complementPoint point.1 = 0 := by
    simpa using annihilates ⟨complementPoint, complementPoint_mem⟩
  rw [← sum_eq, ← linePoint_eq]
  simp [vector_pair_zero, complement_pair_zero]

theorem exists_borderedFamily
    {V : Type*} [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V]
    (form : LinearMap.BilinForm F2 V)
    (nondegenerate : form.Nondegenerate) :
    ∃ k : ℕ, ∃ vectors : Fin k → V, ∃ relation : Fin k → F2,
      k = Module.finrank F2 V + 1 ∧
        IsBorderedFamily form vectors relation := by
  classical
  generalize dimension_eq : Module.finrank F2 V = dimension
  induction dimension using Nat.strong_induction_on generalizing V with
  | h dimension inductionHypothesis =>
      by_cases alternating : form.IsAlt
      · obtain ⟨vectors, relation, bordered, _⟩ :=
          exists_borderedFamily_of_alternating
            form nondegenerate alternating
        exact ⟨Module.finrank F2 V + 1, vectors, relation,
          congrArg (· + 1) dimension_eq, bordered⟩
      · obtain ⟨vector, self_ne_zero⟩ := not_forall.mp alternating
        have self_eq_one : form vector vector = 1 :=
          f2_eq_one_of_ne_zero _ self_ne_zero
        have vector_ne_zero : vector ≠ 0 := by
          intro vector_zero
          subst vector
          simp at self_ne_zero
        let line := Submodule.span F2 ({vector} : Set V)
        let complement := form.orthogonal line
        have complementary : IsCompl line complement :=
          form.isCompl_span_singleton_orthogonal self_ne_zero
        have complement_nondegenerate :
            (form.restrict complement).Nondegenerate := by
          exact restrict_orthogonal_span_nondegenerate
            form nondegenerate self_ne_zero
        have dimensions :
            Module.finrank F2 complement + 1 =
              Module.finrank F2 V := by
          have dimension_sum :=
            Submodule.finrank_add_eq_of_isCompl complementary
          have line_dimension : Module.finrank F2 line = 1 := by
            exact finrank_span_singleton vector_ne_zero
          rw [line_dimension] at dimension_sum
          omega
        have complement_dimension_lt :
            Module.finrank F2 complement < dimension := by
          rw [← dimension_eq]
          omega
        obtain ⟨k, oldVectors, oldRelation, k_eq, oldBordered⟩ :=
          inductionHypothesis
            (Module.finrank F2 complement)
            complement_dimension_lt
            (V := complement)
            (form.restrict complement)
            complement_nondegenerate
            rfl
        let vectors : Fin (k + 1) → V :=
          Fin.cons vector (fun index => oldVectors index)
        let relation : Fin (k + 1) → F2 :=
          Fin.cons 0 oldRelation
        refine ⟨k + 1, vectors, relation, ?_, ?_⟩
        · omega
        · refine ⟨?_, ?_, ?_, ?_⟩
          · constructor
            · intro row
              refine Fin.cases ?_ (fun oldRow => ?_) row
              · intro column
                refine Fin.cases ?_ (fun oldColumn => ?_) column
                · intro before
                  exact (lt_irrefl _ before).elim
                · intro _
                  have orthogonal :
                      form vector (oldVectors oldColumn) = 0 :=
                    (oldVectors oldColumn).property vector
                      (Submodule.mem_span_singleton_self vector)
                  simp [vectors, relation, orthogonal]
              · intro column
                refine Fin.cases ?_ (fun oldColumn => ?_) column
                · intro before
                  simp at before
                · intro before
                  have oldBefore : oldRow < oldColumn := by
                    simpa using before
                  simpa [vectors, relation] using
                    oldBordered.1.1 oldRow oldColumn oldBefore
            · intro index
              refine Fin.cases ?_ (fun oldIndex => ?_) index
              · simp [vectors, relation, self_eq_one]
              · simpa [vectors, relation] using
                  oldBordered.1.2 oldIndex
          · rw [Fin.sum_univ_succ]
            have mapped_sum := congrArg
              (fun point : complement => (point : V))
              oldBordered.2.1
            simpa [vectors, relation] using mapped_sum
          · rw [dotProduct, Fin.sum_univ_succ]
            simpa [dotProduct, relation] using oldBordered.2.2.1
          · have line_le :
                line ≤ Submodule.span F2 (Set.range vectors) := by
              rw [Submodule.span_singleton_le_iff_mem]
              apply Submodule.subset_span
              exact ⟨0, by simp [vectors]⟩
            have complement_le :
                complement ≤
                  Submodule.span F2 (Set.range vectors) := by
              rw [← Submodule.map_subtype_top complement,
                ← oldBordered.2.2.2]
              rw [Submodule.map_span]
              apply Submodule.span_mono
              rintro _ ⟨_, ⟨oldIndex, rfl⟩, rfl⟩
              exact ⟨oldIndex.succ, by simp [vectors]⟩
            apply top_unique
            rw [← complementary.sup_eq_top]
            exact sup_le line_le complement_le

theorem exists_borderedFamily_with_last
    {V : Type*} [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V]
    (form : LinearMap.BilinForm F2 V)
    (nondegenerate : form.Nondegenerate) :
    ∃ vectors : Fin (Module.finrank F2 V + 1) → V,
      ∃ relation : Fin (Module.finrank F2 V + 1) → F2,
        IsBorderedFamily form vectors relation ∧
          relation (Fin.last (Module.finrank F2 V)) = 1 := by
  classical
  generalize dimension_eq : Module.finrank F2 V = dimension
  induction dimension using Nat.strong_induction_on generalizing V with
  | h dimension inductionHypothesis =>
      by_cases alternating : form.IsAlt
      · obtain ⟨vectors, relation, bordered, relation_last⟩ :=
          exists_borderedFamily_of_alternating
            form nondegenerate alternating
        rw [← dimension_eq]
        exact ⟨vectors, relation, bordered, relation_last⟩
      · obtain ⟨vector, self_ne_zero⟩ := not_forall.mp alternating
        have self_eq_one : form vector vector = 1 :=
          f2_eq_one_of_ne_zero _ self_ne_zero
        have vector_ne_zero : vector ≠ 0 := by
          intro vector_zero
          subst vector
          simp at self_ne_zero
        let line := Submodule.span F2 ({vector} : Set V)
        let complement := form.orthogonal line
        have complementary : IsCompl line complement :=
          form.isCompl_span_singleton_orthogonal self_ne_zero
        have complement_nondegenerate :
            (form.restrict complement).Nondegenerate :=
          restrict_orthogonal_span_nondegenerate
            form nondegenerate self_ne_zero
        have dimensions :
            Module.finrank F2 complement + 1 =
              Module.finrank F2 V := by
          have dimension_sum :=
            Submodule.finrank_add_eq_of_isCompl complementary
          have line_dimension : Module.finrank F2 line = 1 :=
            finrank_span_singleton vector_ne_zero
          rw [line_dimension] at dimension_sum
          omega
        have complement_dimension_lt :
            Module.finrank F2 complement < dimension := by
          rw [← dimension_eq]
          omega
        obtain ⟨oldVectors, oldRelation, oldBordered,
            oldRelation_last⟩ :=
          inductionHypothesis
            (Module.finrank F2 complement)
            complement_dimension_lt
            (V := complement)
            (form.restrict complement)
            complement_nondegenerate
            rfl
        rw [← dimensions.trans dimension_eq]
        let vectors :
            Fin ((Module.finrank F2 complement + 1) + 1) → V :=
          Fin.cons vector (fun index => oldVectors index)
        let relation :
            Fin ((Module.finrank F2 complement + 1) + 1) → F2 :=
          Fin.cons 0 oldRelation
        refine ⟨vectors, relation, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_⟩
          · constructor
            · intro row
              refine Fin.cases ?_ (fun oldRow => ?_) row
              · intro column
                refine Fin.cases ?_ (fun oldColumn => ?_) column
                · intro before
                  exact (lt_irrefl _ before).elim
                · intro _
                  have orthogonal :
                      form vector (oldVectors oldColumn) = 0 :=
                    (oldVectors oldColumn).property vector
                      (Submodule.mem_span_singleton_self vector)
                  simp [vectors, relation, orthogonal]
              · intro column
                refine Fin.cases ?_ (fun oldColumn => ?_) column
                · intro before
                  simp at before
                · intro before
                  have oldBefore : oldRow < oldColumn := by
                    simpa using before
                  simpa [vectors, relation] using
                    oldBordered.1.1 oldRow oldColumn oldBefore
            · intro index
              refine Fin.cases ?_ (fun oldIndex => ?_) index
              · simp [vectors, relation, self_eq_one]
              · simpa [vectors, relation] using
                  oldBordered.1.2 oldIndex
          · rw [Fin.sum_univ_succ]
            have mapped_sum := congrArg
              (fun point : complement => (point : V))
              oldBordered.2.1
            simpa [vectors, relation] using mapped_sum
          · rw [dotProduct, Fin.sum_univ_succ]
            simpa [dotProduct, relation] using oldBordered.2.2.1
          · have line_le :
                line ≤ Submodule.span F2 (Set.range vectors) := by
              rw [Submodule.span_singleton_le_iff_mem]
              apply Submodule.subset_span
              exact ⟨0, by simp [vectors]⟩
            have complement_le :
                complement ≤
                  Submodule.span F2 (Set.range vectors) := by
              have mapped_le :
                  Submodule.map complement.subtype
                      (Submodule.span F2 (Set.range oldVectors)) ≤
                    Submodule.span F2 (Set.range vectors) := by
                rw [Submodule.map_span]
                apply Submodule.span_mono
                rintro _ ⟨_, ⟨oldIndex, rfl⟩, rfl⟩
                exact ⟨oldIndex.succ, by simp [vectors]⟩
              calc
                complement =
                    Submodule.map complement.subtype ⊤ :=
                  (Submodule.map_subtype_top complement).symm
                _ = Submodule.map complement.subtype
                    (Submodule.span F2 (Set.range oldVectors)) := by
                  rw [oldBordered.2.2.2]
                _ ≤ Submodule.span F2 (Set.range vectors) := mapped_le
            apply top_unique
            rw [← complementary.sup_eq_top]
            exact sup_le line_le complement_le
        · simpa [relation] using oldRelation_last

theorem initial_linearIndependent_of_bordered_last
    {V : Type*} [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V]
    {n : ℕ} (form : LinearMap.BilinForm F2 V)
    (dimension_eq : Module.finrank F2 V = n)
    (vectors : Fin (n + 1) → V)
    (relation : Fin (n + 1) → F2)
    (bordered : IsBorderedFamily form vectors relation)
    (relation_last : relation (Fin.last n) = 1) :
    LinearIndependent F2 (fun index : Fin n => vectors index.castSucc) := by
  classical
  let initial : Fin n → V := fun index => vectors index.castSucc
  let initialSpan := Submodule.span F2 (Set.range initial)
  have last_eq_sum :
      vectors (Fin.last n) =
        ∑ index : Fin n,
          relation index.castSucc • initial index := by
    have split := bordered.2.1
    rw [Fin.sum_univ_castSucc] at split
    rw [relation_last, one_smul] at split
    have added := congrArg
      (fun vector =>
        vector +
          ∑ index : Fin n,
            relation index.castSucc • initial index)
      split
    simpa [initial, add_assoc, add_comm, add_left_comm,
      ZModModule.add_self] using added
  have last_mem : vectors (Fin.last n) ∈ initialSpan := by
    rw [last_eq_sum]
    exact Submodule.sum_mem initialSpan
      (fun index _ =>
        Submodule.smul_mem initialSpan _ <|
          Submodule.subset_span ⟨index, rfl⟩)
  have initial_span_top : initialSpan = ⊤ := by
    apply top_unique
    rw [← bordered.2.2.2]
    apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    refine Fin.lastCases last_mem (fun initialIndex => ?_) index
    exact Submodule.subset_span ⟨initialIndex, rfl⟩
  change LinearIndependent F2 initial
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank]
  change Fintype.card (Fin n) = Module.finrank F2 initialSpan
  rw [initial_span_top, finrank_top, dimension_eq, Fintype.card_fin]

theorem isBorderedTriangularization_of_family
    {n k : ℕ} (core : Matrix (Fin n) (Fin n) F2)
    (vectors : Fin k → Fin n → F2)
    (relation : Fin k → F2)
    (bordered :
      IsBorderedFamily (Matrix.toBilin' core) vectors relation) :
    IsBorderedTriangularization core vectors relation := by
  classical
  let coefficients : Matrix (Fin k) (Fin n) F2 := vectors
  change IsBorderedTriangularization core coefficients relation
  have congruence_apply (row column : Fin k) :
      (coefficients * core * Matrix.transpose coefficients) row column =
        Matrix.toBilin' core (vectors row) (vectors column) := by
    rw [Matrix.toBilin'_apply', Matrix.dotProduct_mulVec]
    simp [coefficients, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  refine ⟨?_, ?_, bordered.2.2.1, ?_⟩
  · have matrix_eq :
        coefficients * core * Matrix.transpose coefficients +
            Matrix.vecMulVec relation relation =
          fun row column =>
            Matrix.toBilin' core (vectors row) (vectors column) +
              relation row * relation column := by
      ext row column
      simp [congruence_apply, Matrix.vecMulVec_apply]
    rw [matrix_eq]
    exact bordered.1
  · ext column
    have coordinate_eq :=
      congrFun bordered.2.1 column
    simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      smul_eq_mul, mul_comm] using coordinate_eq
  · rw [Matrix.mulVec_injective_iff,
      linearIndependent_iff_card_eq_finrank_span,
      Set.finrank, ← Matrix.rank_eq_finrank_span_cols]
    have span_rows :
        Submodule.span F2 (Set.range coefficients.row) = ⊤ := by
      have row_eq : coefficients.row = vectors := by
        funext row column
        rfl
      rw [row_eq]
      exact bordered.2.2.2
    have matrix_rank : coefficients.rank = n := by
      rw [Matrix.rank_eq_finrank_span_row, span_rows,
        finrank_top, Module.finrank_fin_fun]
    rw [matrix_rank, Fintype.card_fin]

theorem exists_borderedTriangularization
    {n : ℕ} (core : Matrix (Fin n) (Fin n) F2)
    (core_unit : IsUnit core) :
    ∃ k : ℕ,
      ∃ coefficients : Matrix (Fin k) (Fin n) F2,
      ∃ relation : Fin k → F2,
        k = n + 1 ∧
          IsBorderedTriangularization core coefficients relation := by
  have core_nondegenerate :
      (Matrix.toBilin' core).Nondegenerate := by
    apply Matrix.Nondegenerate.toLinearMap₂'
    exact
      { separatingLeft :=
          Matrix.separatingLeft_iff_forall_vecMul_eq_zero.mpr
            (fun vector equal =>
              Matrix.vecMul_injective_of_isUnit core_unit (by
                simpa using equal))
        separatingRight :=
          Matrix.separatingRight_iff_forall_mulVec_eq_zero.mpr
            (fun vector equal =>
              Matrix.mulVec_injective_of_isUnit core_unit (by
                simpa using equal)) }
  obtain ⟨k, vectors, relation, k_eq, bordered⟩ :=
    exists_borderedFamily (Matrix.toBilin' core) core_nondegenerate
  refine ⟨k, vectors, relation, ?_, ?_⟩
  · simpa [Module.finrank_fin_fun] using k_eq
  · exact isBorderedTriangularization_of_family
      core vectors relation bordered

theorem exists_borderedTriangularization_with_last
    {n : ℕ} (core : Matrix (Fin n) (Fin n) F2)
    (core_unit : IsUnit core) :
    ∃ coefficients : Matrix (Fin (n + 1)) (Fin n) F2,
      ∃ relation : Fin (n + 1) → F2,
        IsBorderedTriangularization core coefficients relation ∧
          relation (Fin.last n) = 1 ∧
          LinearIndependent F2
            (fun index : Fin n => coefficients index.castSucc) := by
  have core_nondegenerate :
      (Matrix.toBilin' core).Nondegenerate := by
    apply Matrix.Nondegenerate.toLinearMap₂'
    exact
      { separatingLeft :=
          Matrix.separatingLeft_iff_forall_vecMul_eq_zero.mpr
            (fun vector equal =>
              Matrix.vecMul_injective_of_isUnit core_unit (by
                simpa using equal))
        separatingRight :=
          Matrix.separatingRight_iff_forall_mulVec_eq_zero.mpr
            (fun vector equal =>
              Matrix.mulVec_injective_of_isUnit core_unit (by
                simpa using equal)) }
  have family_exists :
      ∃ vectors : Fin (n + 1) → Fin n → F2,
        ∃ relation : Fin (n + 1) → F2,
          IsBorderedFamily (Matrix.toBilin' core) vectors relation ∧
            relation (Fin.last n) = 1 := by
    have dimension_eq :
        Module.finrank F2 (Fin n → F2) = n :=
      Module.finrank_fin_fun F2
    have witness :=
      exists_borderedFamily_with_last
        (Matrix.toBilin' core) core_nondegenerate
    rw [dimension_eq] at witness
    exact witness
  obtain ⟨vectors, relation, bordered, relation_last⟩ :=
    family_exists
  exact ⟨vectors, relation,
    isBorderedTriangularization_of_family
      core vectors relation bordered,
    relation_last,
    initial_linearIndependent_of_bordered_last
      (Matrix.toBilin' core) (Module.finrank_fin_fun F2)
      vectors relation bordered relation_last⟩

theorem linearIndependent_centerMatrix_of_ofFn
    {m n : ℕ} (centers : Fin n → PhaseVector m)
    (independent : LinearIndependent F2 centers) :
    LinearIndependent F2 (centerMatrix (List.ofFn centers)) := by
  have reindexed := independent.comp
    (ofFnIndexEquiv centers) (ofFnIndexEquiv centers).injective
  have functions_eq :
      centers ∘ ofFnIndexEquiv centers =
        centerMatrix (List.ofFn centers) := by
    funext index column
    simp [ofFnIndexEquiv, centerMatrix]
    apply congrArg (fun centerIndex => centers centerIndex column)
    apply Fin.ext
    rfl
  rwa [functions_eq] at reindexed

theorem CorePresentation.core_unit
    {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n) :
    IsUnit presentation.core := by
  rw [CorePresentation.core, Matrix.isUnit_transpose,
    Matrix.isUnit_nonsing_inv_iff]
  exact presentation.coefficient_unit

theorem CorePresentation.exists_succ_factorization
    {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n) :
    ∃ centers : Fin (n + 1) → PhaseVector m,
      IsFactorization target (List.ofFn centers) := by
  obtain ⟨k, coefficients, relation, k_eq, bordered⟩ :=
    exists_borderedTriangularization
      presentation.core presentation.core_unit
  subst k
  exact ⟨coefficients * presentation.basis,
    factorizationOfBordered
      presentation coefficients relation bordered⟩

theorem CorePresentation.exists_succ_factorization_with_initial_independent
    {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n) :
    ∃ centers : Fin (n + 1) → PhaseVector m,
      IsFactorization target (List.ofFn centers) ∧
        LinearIndependent F2
          (fun index : Fin n => centers index.castSucc) := by
  obtain ⟨coefficients, relation, bordered, _,
      coefficients_independent⟩ :=
    exists_borderedTriangularization_with_last
      presentation.core presentation.core_unit
  let centers : Fin (n + 1) → PhaseVector m :=
    coefficients * presentation.basis
  let initialCoefficients : Matrix (Fin n) (Fin n) F2 :=
    fun index => coefficients index.castSucc
  have initialCoefficients_independent :
      LinearIndependent F2 initialCoefficients := by
    exact coefficients_independent
  have initialCoefficients_injective :
      Function.Injective initialCoefficients.vecMul :=
    Matrix.vecMul_injective_iff.mpr
      initialCoefficients_independent
  have basis_injective :
      Function.Injective presentation.basis.vecMul :=
    Matrix.vecMul_injective_iff.mpr
      presentation.basis_independent
  have product_independent :
      LinearIndependent F2
        (initialCoefficients * presentation.basis).row := by
    rw [← Matrix.vecMul_injective_iff]
    intro first second equal
    apply initialCoefficients_injective
    apply basis_injective
    simpa only [Matrix.vecMul_vecMul] using equal
  have initial_centers_eq :
      (initialCoefficients * presentation.basis).row =
        fun index : Fin n => centers index.castSucc := by
    funext index column
    rfl
  rw [initial_centers_eq] at product_independent
  exact ⟨centers,
    factorizationOfBordered
      presentation coefficients relation bordered,
    product_independent⟩

theorem exists_residueRank_succ_factorization
    {m : ℕ} (target : SymplecticAction m) :
    ∃ centers :
        Fin (residueRank (target : ActionMatrix m) + 1) →
          PhaseVector m,
      IsFactorization target (List.ofFn centers) :=
  (canonicalCorePresentation target).exists_succ_factorization

theorem residueRank_le_length_of_factorization
    {m : ℕ} {target : SymplecticAction m}
    {centers : List (PhaseVector m)}
    (factorization : IsFactorization target centers) :
    residueRank (target : ActionMatrix m) ≤ centers.length := by
  have lower := residueRank_product_le_length centers
  rw [factorization] at lower
  exact lower

theorem CorePresentation.isTriangularizable_of_factorization_length_eq
    {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n)
    (centers : List (PhaseVector m))
    (factorization : IsFactorization target centers)
    (length_eq : centers.length = n) :
    presentation.IsTriangularizable := by
  subst n
  apply presentation.exists_factorization_iff_isTriangularizable.mp
  exact ⟨centers.get, by simpa using factorization⟩

theorem CorePresentation.exists_minimal_factorization
    {m n : ℕ} {target : SymplecticAction m}
    (presentation : CorePresentation target n) :
    ∃ centers : List (PhaseVector m),
      IsFactorization target centers ∧
        (∀ other : List (PhaseVector m),
          IsFactorization target other →
            centers.length ≤ other.length) ∧
        (centers.length = n ∨ centers.length = n + 1) ∧
        (centers.length = n ↔ presentation.IsTriangularizable) := by
  classical
  by_cases triangularizable : presentation.IsTriangularizable
  · obtain ⟨family, factorization⟩ :=
      presentation.exists_factorization_iff_isTriangularizable.mpr
        triangularizable
    refine ⟨List.ofFn family, factorization, ?_, ?_, ?_⟩
    · intro other other_factorization
      simpa [presentation.rank_eq] using
        residueRank_le_length_of_factorization other_factorization
    · left
      simp
    · simp [triangularizable]
  · obtain ⟨family, factorization⟩ :=
      presentation.exists_succ_factorization
    refine ⟨List.ofFn family, factorization, ?_, ?_, ?_⟩
    · intro other other_factorization
      have lower :
          n ≤ other.length := by
        rw [presentation.rank_eq]
        exact residueRank_le_length_of_factorization
          other_factorization
      by_contra not_le
      have below : other.length < n + 1 :=
        Nat.lt_of_not_ge (by simpa using not_le)
      have upper : other.length ≤ n := Nat.le_of_lt_succ below
      have length_eq : other.length = n :=
        Nat.le_antisymm upper lower
      exact triangularizable
        (presentation.isTriangularizable_of_factorization_length_eq
          other other_factorization length_eq)
    · right
      simp
    · constructor
      · intro length_eq
        simp at length_eq
      · exact fun is_triangularizable =>
          (triangularizable is_triangularizable).elim

theorem exists_residue_fix_of_not_triangularizable
    {m : ℕ} (target : SymplecticAction m)
    (not_triangularizable :
      ¬(canonicalCorePresentation target).IsTriangularizable) :
    ∃ fix : PhaseVector m,
      fix ≠ 0 ∧
        fix ∈ residueSpace (target : ActionMatrix m) ∧
        residueRank
          ((target * transvectionAction fix :
            SymplecticAction m) : ActionMatrix m) =
          residueRank (target : ActionMatrix m) ∧
        (canonicalCorePresentation
          (target * transvectionAction fix)).IsTriangularizable := by
  let rank := residueRank (target : ActionMatrix m)
  obtain ⟨centers, factorization, initial_independent⟩ :=
    CorePresentation.exists_succ_factorization_with_initial_independent
      (canonicalCorePresentation target)
  let initial : Fin rank → PhaseVector m :=
    fun index => centers index.castSucc
  let fix := centers (Fin.last rank)
  let updated := target * transvectionAction fix
  have centers_split :
      List.ofFn centers = List.ofFn initial ++ [fix] := by
    simpa [initial, fix] using List.ofFn_succ' centers
  have transvection_squared_action :
      transvectionAction fix * transvectionAction fix = 1 := by
    apply Subtype.ext
    exact transvection_squared fix
  have split_factorization :
      productTransvections (List.ofFn initial) *
          transvectionAction fix =
        target := by
    rw [← factorization, centers_split,
      productTransvections_append]
    simp
  have initial_factorization :
      IsFactorization updated (List.ofFn initial) := by
    calc
      productTransvections (List.ofFn initial) =
          (productTransvections (List.ofFn initial) *
            transvectionAction fix) * transvectionAction fix := by
              rw [mul_assoc, transvection_squared_action, mul_one]
      _ = target * transvectionAction fix := by
            rw [split_factorization]
  have initial_list_independent :
      LinearIndependent F2
        (centerMatrix (List.ofFn initial)) :=
    linearIndependent_centerMatrix_of_ofFn
      initial initial_independent
  have updated_rank :
      residueRank (updated : ActionMatrix m) = rank := by
    have rank_eq :=
      residueRank_product_eq_length_of_linearIndependent
        (List.ofFn initial) initial_list_independent
    rw [initial_factorization] at rank_eq
    simpa [initial] using rank_eq
  have fix_mem_residue :
      fix ∈ residueSpace (target : ActionMatrix m) := by
    have residue_eq_span :=
      residueSpace_eq_centerSpan_of_length_eq_rank_add_one
        target (List.ofFn centers) factorization (by simp)
    rw [residue_eq_span]
    apply mem_centerSpan_of_mem
    rw [List.mem_ofFn']
    exact ⟨Fin.last rank, rfl⟩
  have fix_nonzero : fix ≠ 0 := by
    intro fix_zero
    have transvection_zero_action :
        transvectionAction (0 : PhaseVector m) = 1 := by
      apply Subtype.ext
      exact transvection_zero
    have updated_eq : updated = target := by
      simp [updated, fix_zero, transvection_zero_action]
    apply not_triangularizable
    apply (CorePresentation.exists_factorization_iff_isTriangularizable
      (canonicalCorePresentation target)).mp
    refine ⟨initial, ?_⟩
    rw [updated_eq] at initial_factorization
    exact initial_factorization
  have updated_triangularizable :
      (canonicalCorePresentation updated).IsTriangularizable := by
    apply (CorePresentation.exists_factorization_iff_isTriangularizable
      (canonicalCorePresentation updated)).mp
    rw [updated_rank]
    exact ⟨initial, initial_factorization⟩
  exact ⟨fix, fix_nonzero, fix_mem_residue, updated_rank,
    updated_triangularizable⟩

end PaulimerFormal
