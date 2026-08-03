import BauschkeLean.Chap20.Proposition_20_56
import BauschkeLean.Chap25.Definition_25_10
import BauschkeLean.Chap25.Theorem_25_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Theorem 25.24 records the Brézis--Haraux closure and interior identities under
  the chapter's `3*`-monotonicity hypotheses.
- `core/canonical`: Theorem 25.23 owns the actual closure/interior formulas through
  `FitzpatrickDomainCondition`.
- `bridge/view`: the reusable theorems below convert the stronger Theorem 25.24 hypotheses into
  that canonical Fitzpatrick-domain condition. -/

omit [CompleteSpace H] in
/-- A maximally monotone sum has a common domain point for its two summands. -/
theorem exists_mem_dom_inter_of_maximal_add
    {A B : SetValuedOperator H H} (hAB_max : Maximal IsMonotone (A + B)) :
    ∃ x : H, x ∈ A.dom ∩ B.dom := by
  have hdom_nonempty : (A + B).dom.Nonempty := by
    by_contra hdom_empty
    have hzero_mem : (0 : H) ∈ (A + B) 0 := by
      refine (Maximal.mem_iff hAB_max 0 0).2 ?_
      intro y v hv
      have hy_dom : y ∈ (A + B).dom :=
        (SetValuedOperator.mem_dom_iff (A + B) y).2 ⟨v, hv⟩
      exact False.elim (hdom_empty ⟨y, hy_dom⟩)
    have hzero_dom : (0 : H) ∈ (A + B).dom :=
      (SetValuedOperator.mem_dom_iff (A + B) 0).2 ⟨0, hzero_mem⟩
    exact hdom_empty ⟨0, hzero_dom⟩
  rcases hdom_nonempty with ⟨x, hxAB_dom⟩
  rcases (SetValuedOperator.mem_dom_iff (A + B) x).1 hxAB_dom with ⟨w, hw⟩
  rcases Set.mem_add.mp hw with ⟨u, hu, v, hv, _⟩
  refine ⟨x, ?_⟩
  rw [Set.mem_inter_iff]
  exact ⟨
    (SetValuedOperator.mem_dom_iff A x).2 ⟨u, hu⟩,
    (SetValuedOperator.mem_dom_iff B x).2 ⟨v, hv⟩
  ⟩

omit [CompleteSpace H] in
/-- The symmetric `3*`-monotonicity hypotheses of Theorem 25.24 imply the canonical
Fitzpatrick-domain hypothesis of Theorem 25.23. -/
theorem fitzpatrickDomainCondition_of_isThreeStarMonotone
    {A B : SetValuedOperator H H} (hAB_max : Maximal IsMonotone (A + B))
    (hA_threeStar : A.IsThreeStarMonotone) (hB_threeStar : B.IsThreeStarMonotone) :
    FitzpatrickDomainCondition A B := by
  rcases exists_mem_dom_inter_of_maximal_add hAB_max with ⟨x0, hx0⟩
  intro u hu v hv
  refine ⟨x0, ?_⟩
  exact ⟨
    hA_threeStar.subset_dom_fitzpatrickFunction ⟨hx0.1, hu⟩,
    hB_threeStar.subset_dom_fitzpatrickFunction ⟨hx0.2, hv⟩
  ⟩

omit [CompleteSpace H] in
/-- The asymmetric domain-inclusion hypothesis of Theorem 25.24 also implies the canonical
Fitzpatrick-domain hypothesis of Theorem 25.23. -/
theorem fitzpatrickDomainCondition_of_dom_subset_and_isThreeStarMonotone
    {A B : SetValuedOperator H H} (hA_mono : A.IsMonotone) (hdom : A.dom ⊆ B.dom)
    (hB_threeStar : B.IsThreeStarMonotone) :
    FitzpatrickDomainCondition A B := by
  intro u hu v hv
  rcases (SetValuedOperator.mem_range_iff A u).1 hu with ⟨x, hux⟩
  have hxA_dom : x ∈ A.dom := (SetValuedOperator.mem_dom_iff A x).2 ⟨u, hux⟩
  have hxB_dom : x ∈ B.dom := hdom hxA_dom
  have hxu_graph : (x, u) ∈ gra A := by
    simpa [SetValuedOperator.mem_graph] using hux
  have hAu : (x, u) ∈ ERealFunction.dom (F[A]) := by
    rw [ERealFunction.mem_dom_iff_ne_top]
    rw [fitzpatrickFunction_eq_inner_of_mem_graph A hA_mono hxu_graph]
    exact EReal.coe_ne_top _
  have hBv : (x, v) ∈ ERealFunction.dom (F[B]) :=
    hB_threeStar.subset_dom_fitzpatrickFunction ⟨hxB_dom, hv⟩
  exact ⟨x, hAu, hBv⟩

/-- Theorem 25.24 (1): the Brézis--Haraux closure identity under the symmetric `3*`-monotonicity
hypothesis. Let `A` and `B` be monotone operators on a real Hilbert space such that `A + B` is
maximally monotone. If both `A` and `B` are `3*` monotone, then
`closure (ran (A + B)) = closure (ran A + ran B)`, formalized as
`closure (A + B).range = closure (A.range + B.range)`. -/
theorem closure_range_add_eq_closure_range_sum_of_isThreeStarMonotone
    {A B : SetValuedOperator H H} (hA_mono : A.IsMonotone) (hB_mono : B.IsMonotone)
    (hAB_max : Maximal IsMonotone (A + B))
    (hA_threeStar : A.IsThreeStarMonotone) (hB_threeStar : B.IsThreeStarMonotone) :
    closure (A + B).range = closure (A.range + B.range) := by
  exact closure_range_add_eq_closure_range_sum_of_fitzpatrick_domain_condition
    hA_mono hB_mono hAB_max
    (fitzpatrickDomainCondition_of_isThreeStarMonotone hAB_max hA_threeStar hB_threeStar)

/-- Theorem 25.24 (2): the Brézis--Haraux closure identity under the asymmetric domain-inclusion
hypothesis. Let `A` and `B` be monotone operators on a real Hilbert space such that `A + B` is
maximally monotone. If `A.dom ⊆ B.dom` and `B` is `3*` monotone, then
`closure (ran (A + B)) = closure (ran A + ran B)`, formalized as
`closure (A + B).range = closure (A.range + B.range)`. -/
theorem closure_range_add_eq_closure_range_sum_of_dom_subset_and_isThreeStarMonotone
    {A B : SetValuedOperator H H} (hA_mono : A.IsMonotone) (hB_mono : B.IsMonotone)
    (hAB_max : Maximal IsMonotone (A + B)) (hdom : A.dom ⊆ B.dom)
    (hB_threeStar : B.IsThreeStarMonotone) :
    closure (A + B).range = closure (A.range + B.range) := by
  exact closure_range_add_eq_closure_range_sum_of_fitzpatrick_domain_condition
    hA_mono hB_mono hAB_max
    (fitzpatrickDomainCondition_of_dom_subset_and_isThreeStarMonotone
      hA_mono hdom hB_threeStar)

/-- Theorem 25.24 (3): the Brézis--Haraux interior identity under the symmetric `3*`-monotonicity
hypothesis. Let `A` and `B` be monotone operators on a real Hilbert space such that `A + B` is
maximally monotone. If both `A` and `B` are `3*` monotone, then
`interior (ran (A + B)) = interior (ran A + ran B)`, formalized as
`interior (A + B).range = interior (A.range + B.range)`. -/
theorem interior_range_add_eq_interior_range_sum_of_isThreeStarMonotone
    {A B : SetValuedOperator H H} (hA_mono : A.IsMonotone) (hB_mono : B.IsMonotone)
    (hAB_max : Maximal IsMonotone (A + B))
    (hA_threeStar : A.IsThreeStarMonotone) (hB_threeStar : B.IsThreeStarMonotone) :
    interior (A + B).range = interior (A.range + B.range) := by
  exact interior_range_add_eq_interior_range_sum_of_fitzpatrick_domain_condition
    hA_mono hB_mono hAB_max
    (fitzpatrickDomainCondition_of_isThreeStarMonotone hAB_max hA_threeStar hB_threeStar)

/-- Theorem 25.24 (4): the Brézis--Haraux interior identity under the asymmetric domain-inclusion
hypothesis. Let `A` and `B` be monotone operators on a real Hilbert space such that `A + B` is
maximally monotone. If `A.dom ⊆ B.dom` and `B` is `3*` monotone, then
`interior (ran (A + B)) = interior (ran A + ran B)`, formalized as
`interior (A + B).range = interior (A.range + B.range)`. -/
theorem interior_range_add_eq_interior_range_sum_of_dom_subset_and_isThreeStarMonotone
    {A B : SetValuedOperator H H} (hA_mono : A.IsMonotone) (hB_mono : B.IsMonotone)
    (hAB_max : Maximal IsMonotone (A + B)) (hdom : A.dom ⊆ B.dom)
    (hB_threeStar : B.IsThreeStarMonotone) :
    interior (A + B).range = interior (A.range + B.range) := by
  exact interior_range_add_eq_interior_range_sum_of_fitzpatrick_domain_condition
    hA_mono hB_mono hAB_max
    (fitzpatrickDomainCondition_of_dom_subset_and_isThreeStarMonotone
      hA_mono hdom hB_threeStar)

end SetValuedOperator
