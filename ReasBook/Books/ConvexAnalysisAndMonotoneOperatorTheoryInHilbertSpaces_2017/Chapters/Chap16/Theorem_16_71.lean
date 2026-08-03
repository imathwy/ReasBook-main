import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap15.Theorem_15_3
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap08.Proposition_8_35
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap16.Corollary_16_30
import BauschkeLean.Chap16.Definition_16_67
import BauschkeLean.Chap16.Example_16_13
import BauschkeLean.Chap16.Proposition_16_27
import BauschkeLean.Chap16.Proposition_16_70
import BauschkeLean.Chap16.Proposition_16_61

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise
open WithLp

universe u v

namespace ERealFunction

section SubdifferentialOfComposition

open SetValuedOperator

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: apply Corollary 16.48 to the canonical constrained objective
-- `g + ι[gra F]`, using the `sri` regularity hypothesis to identify its product-space
-- subdifferential with `∂ g + N[gra F]`. The normal-cone term rewrites via the coderivative, and
-- Proposition 16.70 gives the reverse inclusion for the same active graph point `(xbar, ybar)`.
omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Theorem 16 71: the indicator of a nonempty closed convex graph belongs to
`Γ₀(H × K)`. -/
lemma graph_indicator_mem_gammaZero
    (F : SetValuedOperator H K) (xbar : H) (ybar : K)
    (hybar : ybar ∈ F xbar)
    (hgraph_closed : IsClosed (gra F)) (hgraph_convex : Convex ℝ (gra F)) :
    ι[gra F] ∈ Γ₀(H × K) := by
  -- Lower semicontinuity is exactly closedness of the graph when the indicator takes `⊤` off it.
  have hindicator_lsc :
      LowerSemicontinuous (fun z : H × K ↦ ((ι[gra F]) z : EReal)) := by
    simpa using
      (lowerSemicontinuous_indicator_compl_top_iff_isClosed (gra F)).2 hgraph_closed
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨?_, fun _ hz ↦ hz, ?_⟩
  · -- The given graph point witnesses nonemptiness of the effective domain.
    have hxy_graph : (xbar, ybar) ∈ gra F := by
      simpa [SetValuedOperator.mem_graph] using hybar
    have hxy_mem_dom : (xbar, ybar) ∈ effectiveDomain (ι[gra F]) := by
      simpa [effectiveDomain_indicator] using hxy_graph
    exact ⟨(xbar, ybar), hxy_mem_dom⟩
  · -- Convexity of the graph makes the indicator convex on its effective domain.
    intro z hz z' hz' a ha0 ha1
    have hz_graph : z ∈ gra F := by
      simpa [effectiveDomain_indicator] using hz
    have hz'_graph : z' ∈ gra F := by
      simpa [effectiveDomain_indicator] using hz'
    have hab : a + (1 - a) = 1 := by
      ring
    have hcombo_graph : a • z + (1 - a) • z' ∈ gra F :=
      hgraph_convex hz_graph hz'_graph ha0.le (sub_nonneg.mpr ha1.le) hab
    simp [ERealFunction.indicator, hz_graph, hz'_graph, hcombo_graph]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Theorem 16 71: the subdifferential of the graph indicator is the graph normal
cone. -/
lemma subdifferential_graph_indicator_eq_normalCone
    (F : SetValuedOperator H K) (xbar : H) (ybar : K)
    (hybar : ybar ∈ F xbar) :
    (∂ ι[gra F] : SetValuedOperator (H × K) (H × K)) = N[gra F] := by
  -- The graph point witness lets Example 16.13 identify the indicator subdifferential.
  have hxy_graph : (xbar, ybar) ∈ gra F := by
    simpa [SetValuedOperator.mem_graph] using hybar
  have hgraph_nonempty : (gra F).Nonempty := ⟨(xbar, ybar), hxy_graph⟩
  simpa using subdifferential_setIndicator_eq_normalCone (gra F) hgraph_nonempty

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] in
/-- Helper for Theorem 16 71: at an active graph point, the constrained objective and the
infimal projection have the same value. -/
lemma active_graph_point_value_eq_constrained_objective
    (g : H × K → Set.Ioi (⊥ : EReal)) (F : SetValuedOperator H K) (xbar : H) (ybar : K)
    (hybar : ybar ∈ F xbar)
    (hactive : marginalFunction (g + ι[gra F]) xbar = (g (xbar, ybar) : EReal)) :
    marginalFunction (g + ι[gra F]) xbar = ((g + ι[gra F]) (xbar, ybar) : EReal) := by
  -- On the graph, the indicator contributes exactly `0`, so the active value is unchanged.
  simpa [pointwiseAdd_apply, SetValuedOperator.mem_graph, hybar] using hactive

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Theorem 16 71: a product-space subgradient decomposition with zero second
coordinate yields a coderivative witness for the first coordinate. -/
lemma first_component_mem_iUnion_add_coderivative_of_mem_normalCone_add_subdifferential
    (g : H × K → Set.Ioi (⊥ : EReal)) (F : SetValuedOperator H K) (xbar : H) (ybar : K)
    {w : H}
    (hw :
      (w, (0 : K)) ∈ (N[gra F] + (∂ g)) (xbar, ybar)) :
    w ∈ ⋃ p ∈ (∂ g) (xbar, ybar), ({p.1} : Set H) + (((D*F) xbar) ybar p.2) := by
  -- Unpack the pointwise sum into a normal-cone vector `q` and a subgradient `p`.
  rcases Set.mem_add.mp hw with ⟨q, hq, p, hp, hsum⟩
  have hfst : q.1 + p.1 = w := by
    simpa using congrArg Prod.fst hsum
  have hsnd : q.2 + p.2 = (0 : K) := by
    simpa using congrArg Prod.snd hsum
  have hq_second : q.2 = -p.2 := by
    exact (eq_neg_iff_add_eq_zero).2 hsnd
  have hq_eq : q = (q.1, -p.2) := by
    ext <;> simp [hq_second]
  have hcoderivative_pair : (q.1, -p.2) ∈ N[gra F] (xbar, ybar) := by
    simpa using (hq_eq ▸ hq)
  have hcoderivative : q.1 ∈ (((D*F) xbar) ybar p.2) := by
    exact (mem_coderivative_iff F xbar ybar p.2 q.1).2 hcoderivative_pair
  have hfst' : p.1 + q.1 = w := by
    simpa [add_comm] using hfst
  -- Repackage the same witnesses in the union
  -- `⋃ p ∈ ∂ g(xbar, ybar), p.1 + D*F(xbar, ybar)(p.2)`.
  have hp_singleton : p.1 ∈ ({p.1} : Set H) := by
    simp
  refine Set.mem_iUnion.2 ?_
  refine ⟨p, ?_⟩
  refine Set.mem_iUnion.2 ?_
  refine ⟨hp, ?_⟩
  exact Set.mem_add.2 ⟨p.1, hp_singleton, q.1, hcoderivative, hfst'⟩

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Theorem 16 71: membership in
`⋃ p ∈ ∂ g(xbar, ybar), p.1 + D*F(xbar, ybar)(p.2)` gives exactly the witness package
needed for Proposition 16.70 at the active graph point `(xbar, ybar)`. -/
lemma mem_subgradient_coderivative_source_of_mem_iUnion
    (g : H × K → Set.Ioi (⊥ : EReal)) (F : SetValuedOperator H K) (xbar : H) (ybar : K)
    (hybar : ybar ∈ F xbar)
    (hactive : marginalFunction (g + ι[gra F]) xbar = (g (xbar, ybar) : EReal))
    {w : H}
    (hw : w ∈ ⋃ p ∈ (∂ g) (xbar, ybar), ({p.1} : Set H) + (((D*F) xbar) ybar p.2)) :
    w ∈
      {w : H |
        ∃ y ∈ F xbar,
          marginalFunction (pointwiseAdd g (ι[gra F])) xbar = (g (xbar, y) : EReal) ∧
            ∃ p ∈ (∂ g) (xbar, y), w ∈ ({p.1} : Set H) + (((D*F) xbar) y p.2)} := by
  -- Unpack the double union and reuse the same active graph point in
  -- Proposition 16.70's source set.
  rcases Set.mem_iUnion.mp hw with ⟨p, hpw⟩
  rcases Set.mem_iUnion.mp hpw with ⟨hp, hmem⟩
  exact ⟨ybar, hybar, hactive, p, hp, hmem⟩

/-- Helper for Theorem 16 71: under the standard `sri` regularity hypothesis, the constrained
objective `g + ι[gra F]` has subdifferential `N[gra F] + ∂ g`. -/
lemma subdifferential_constrained_objective_eq_normalCone_add_subdifferential
    (g : H × K → Set.Ioi (⊥ : EReal)) (F : SetValuedOperator H K) (xbar : H) (ybar : K)
    (hg : g ∈ Γ₀(H × K))
    (hgraph_closed : IsClosed (gra F))
    (hgraph_convex : Convex ℝ (gra F))
    (hybar : ybar ∈ F xbar)
    (hregular : ((0 : H), (0 : K)) ∈ sri (gra F - effectiveDomain g)) :
    (∂ (g + ι[gra F]) : SetValuedOperator (H × K) (H × K)) = N[gra F] + (∂ g) := by
  have hindicator : ι[gra F] ∈ Γ₀(H × K) :=
    graph_indicator_mem_gammaZero F xbar ybar hybar hgraph_closed hgraph_convex
  have hsri_indicator :
      ((0 : H), (0 : K)) ∈ sri (effectiveDomain (ι[gra F]) - effectiveDomain g) := by
    simpa [effectiveDomain_indicator] using hregular
  have hsum_gamma : ι[gra F] + g ∈ Γ₀(H × K) :=
    pointwiseAdd_mem_gammaZero_of_zero_mem_sri_sub_effectiveDomain
      (ι[gra F]) g hindicator hg hsri_indicator
  have hconj :
      Function.asEReal ((ι[gra F] + g)∗[hsum_gamma]) =
        ((((ι[gra F])∗[hindicator]) □ (g∗[hg])) : (H × K) → EReal) := by
    funext u
    simpa [gammaZeroConjugate_apply] using congrFun
      (conjugate_pointwiseAdd_eq_infimalConvolution_conjugates_of_zero_mem_sri_sub_effectiveDomain
        (ι[gra F]) g hindicator hg hsri_indicator) u
  have hexact :
      infimalConvolution.Exact ((ι[gra F])∗[hindicator]) (g∗[hg]) :=
    infimalConvolution_exact_gammaZeroConjugates_of_zero_mem_sri_sub_effectiveDomain
      (ι[gra F]) g hindicator hg hsri_indicator
  have hsum :
      (∂ (ι[gra F] + g) : SetValuedOperator (H × K) (H × K)) =
        (∂ ι[gra F]) + (∂ g) := by
    ext z u
    constructor
    · intro hu
      have hz_conj : z ∈ (∂ ((ι[gra F] + g)∗[hsum_gamma])) u := by
        rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate
          (f := ι[gra F] + g) hsum_gamma]
        simpa [SetValuedOperator.mem_inverse_iff] using hu
      have hu_eq :
          (((ι[gra F] + g)∗[hsum_gamma] u : Set.Ioi (⊥ : EReal)) : EReal) =
            ((((ι[gra F])∗[hindicator]) □ (g∗[hg])) : (H × K) → EReal) u := by
        simpa using congrFun hconj u
      have hu_dom_sum_conj :
          u ∈ effectiveDomain ((ι[gra F] + g)∗[hsum_gamma]) := by
        exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero
          (f := (ι[gra F] + g)∗[hsum_gamma])
          (gammaZeroConjugate_mem_gammaZero hsum_gamma) <| by
            rw [SetValuedOperator.mem_dom_iff]
            exact ⟨z, hz_conj⟩
      have hu_dom_inf :
          u ∈ dom ((((ι[gra F])∗[hindicator]) □ (g∗[hg])) : (H × K) → EReal) := by
        change ((((ι[gra F])∗[hindicator]) □ (g∗[hg])) : (H × K) → EReal) u < ⊤
        rwa [← hu_eq]
      rcases hexact hu_dom_inf with ⟨y, hy⟩
      have hz_inf :
          z ∈ (∂ ((((ι[gra F])∗[hindicator]) □ (g∗[hg])) : (H × K) → EReal)) u := by
        rw [mem_subdifferential_iff] at hz_conj ⊢
        intro a
        have ha_eq :
            (((ι[gra F] + g)∗[hsum_gamma] a : Set.Ioi (⊥ : EReal)) : EReal) =
              ((((ι[gra F])∗[hindicator]) □ (g∗[hg])) : (H × K) → EReal) a := by
          simpa using congrFun hconj a
        have hz_conj_a := hz_conj a
        calc
          ↑⟪a - u, z⟫_ℝ +
              ((((ι[gra F])∗[hindicator]) □ (g∗[hg])) : (H × K) → EReal) u
              =
            ↑⟪a - u, z⟫_ℝ +
              (((ι[gra F] + g)∗[hsum_gamma] u : Set.Ioi (⊥ : EReal)) : EReal) := by
                rw [← hu_eq]
          _ ≤ (((ι[gra F] + g)∗[hsum_gamma] a : Set.Ioi (⊥ : EReal)) : EReal) := hz_conj_a
          _ =
            ((((ι[gra F])∗[hindicator]) □ (g∗[hg])) : (H × K) → EReal) a := ha_eq
      have hz_inter_eq :
          (∂ ((((ι[gra F])∗[hindicator]) □ (g∗[hg])) : (H × K) → EReal)) u =
            (∂ ((ι[gra F])∗[hindicator])) y ∩ (∂ (g∗[hg])) (u - y) :=
        subdifferential_infimalConvolution_eq_inter_of_value_eq
          ((ι[gra F])∗[hindicator]) (g∗[hg]) u y
          (gammaZeroConjugate_mem_gammaZero hindicator)
          (gammaZeroConjugate_mem_gammaZero hg) hy
      have hz_inter :
          z ∈ (∂ ((ι[gra F])∗[hindicator])) y ∩ (∂ (g∗[hg])) (u - y) := by
        rw [hz_inter_eq] at hz_inf
        exact hz_inf
      have hy_ind : y ∈ (∂ ι[gra F]) z := by
        rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate
          (f := ι[gra F]) hindicator] at hz_inter
        simpa [SetValuedOperator.mem_inverse_iff] using hz_inter.1
      have hy_g : u - y ∈ (∂ g) z := by
        rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate
          (f := g) hg] at hz_inter
        simpa [SetValuedOperator.mem_inverse_iff] using hz_inter.2
      exact Set.mem_add.2 ⟨y, hy_ind, u - y, hy_g, by simp⟩
    · intro hu
      rcases Set.mem_add.mp hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
      rw [mem_subdifferential_iff] at hu₁ hu₂ ⊢
      intro w
      have hu₁w := hu₁ w
      have hu₂w := hu₂ w
      calc
        (⟪w - z, u₁ + u₂⟫_ℝ : EReal) + ((ι[gra F] + g) z : EReal) =
            ((⟪w - z, u₁⟫_ℝ : EReal) + (ι[gra F] z : EReal)) +
              ((⟪w - z, u₂⟫_ℝ : EReal) + (g z : EReal)) := by
                rw [show (⟪w - z, u₁ + u₂⟫_ℝ : EReal) =
                    (⟪w - z, u₁⟫_ℝ : EReal) + (⟪w - z, u₂⟫_ℝ : EReal) by
                      exact_mod_cast (inner_add_right (w - z) u₁ u₂)]
                simp [add_assoc, add_left_comm, add_comm]
        _ ≤ (ι[gra F] w : EReal) + (g w : EReal) := add_le_add hu₁w hu₂w
        _ = ((ι[gra F] + g) w : EReal) := by
            simp
  have hadd : g + ι[gra F] = ι[gra F] + g := by
    ext z
    simp [add_comm]
  calc
    (∂ (g + ι[gra F]) : SetValuedOperator (H × K) (H × K)) = ∂ (ι[gra F] + g) := by
      simp [hadd]
    _ = (∂ ι[gra F]) + (∂ g) := hsum
    _ = N[gra F] + (∂ g) := by
      rw [subdifferential_graph_indicator_eq_normalCone F xbar ybar hybar]

/-- Theorem 16 71: if `g ∈ Γ₀(H × K)`, `F : H → 2^K` has closed convex graph,
and `(xbar, ybar)` is an active graph point for the canonical infimal projection
`marginalFunction (g + ι[gra F])`,
and `((0 : H), (0 : K)) ∈ sri (gra F - dom g)`, then the subdifferential of that infimal
projection at `xbar` is exactly
`⋃ (u, v) ∈ (∂ g) (xbar, ybar), u + D*F(xbar, ybar)(v)`. -/
theorem subdifferential_eq_iUnion_add_coderivative_of_setValuedInfimalProjection
    (g : H × K → Set.Ioi (⊥ : EReal)) (F : SetValuedOperator H K) (xbar : H) (ybar : K)
    (hg : g ∈ Γ₀(H × K))
    (hgraph_closed : IsClosed (gra F))
    (hgraph_convex : Convex ℝ (gra F))
    (hybar : ybar ∈ F xbar)
    (hactive : marginalFunction (g + ι[gra F]) xbar = (g (xbar, ybar) : EReal))
    (hregular : ((0 : H), (0 : K)) ∈ sri (gra F - effectiveDomain g)) :
    (∂ marginalFunction (g + ι[gra F])) xbar =
      ⋃ p ∈ (∂ g) (xbar, ybar), ({p.1} : Set H) + (((D* F) xbar) ybar p.2) := by
  -- First identify the product-space subdifferential of the constrained objective by the sum rule.
  have hsum_rule :
      (∂ (g + ι[gra F]) : SetValuedOperator (H × K) (H × K)) =
        N[gra F] + (∂ g) :=
    subdifferential_constrained_objective_eq_normalCone_add_subdifferential
      g F xbar ybar hg hgraph_closed hgraph_convex hybar hregular
  have hactive_constrained :
      marginalFunction (g + ι[gra F]) xbar = ((g + ι[gra F]) (xbar, ybar) : EReal) :=
    active_graph_point_value_eq_constrained_objective g F xbar ybar hybar hactive
  ext w
  constructor
  · intro hw
    -- Transport the marginal subgradient to the product space, then extract the coderivative part.
    have hw_prod :
        (w, (0 : K)) ∈ (∂ (g + ι[gra F])) (xbar, ybar) := by
      exact
        (mem_subdifferential_marginalFunction_iff_mem_subdifferential_zeroSecond_of_value_eq
          (g + ι[gra F]) xbar ybar hactive_constrained w).1 hw
    have hw_sum :
        (w, (0 : K)) ∈ (N[gra F] + (∂ g)) (xbar, ybar) := by
      simpa [hsum_rule] using hw_prod
    exact
      first_component_mem_iUnion_add_coderivative_of_mem_normalCone_add_subdifferential
        g F xbar ybar hw_sum
  · intro hw
    -- Proposition 16.70 already proves the reverse inclusion for the same active graph point.
    have hsubset :
        {w : H |
            ∃ y ∈ F xbar,
              marginalFunction (pointwiseAdd g (ι[gra F])) xbar = (g (xbar, y) : EReal) ∧
                ∃ p ∈ (∂ g) (xbar, y), w ∈ ({p.1} : Set H) + (((D* F) xbar) y p.2)} ⊆
          (∂ marginalFunction (pointwiseAdd g (ι[gra F]))) xbar :=
      subgradient_coderivative_sum_subset_subdifferential_of_setValuedInfimalProjection
        g F
    have hw_source :
        w ∈
          {w : H |
            ∃ y ∈ F xbar,
              marginalFunction (pointwiseAdd g (ι[gra F])) xbar = (g (xbar, y) : EReal) ∧
                ∃ p ∈ (∂ g) (xbar, y), w ∈ ({p.1} : Set H) + (((D* F) xbar) y p.2)} := by
      -- Reuse the active graph point to package the Proposition 16.70 witness data.
      exact mem_subgradient_coderivative_source_of_mem_iUnion g F xbar ybar hybar hactive hw
    exact hsubset hw_source

end SubdifferentialOfComposition

end ERealFunction
