import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_10 (from Chap03) -/
/- Definition 3.10 lies in the chapter's convex-analysis/minimax-linearization domain.

Sampled owner-style declarations:
- mathlib `unitInterval`
- mathlib `AffineMap.lineMap`
- `IsMinimaxLinearizationParameter`
- `isMinimaxLinearizationParameter_iff`

Best owner abstraction:
- the upstream source-facing owner `IsMinimaxLinearizationParameter`

Primitive data:
- a domain `Q`
- two functions `f₁ f₂ : Q → ℝ`
- a parameter `lam : unitInterval`

Derived API:
- the companion specification theorem `isMinimaxLinearizationParameter_iff`

Source/core/bridge triage:
- source-facing: the textbook notion of a minimax linearization parameter
- core/canonical: the earlier owner predicate `IsMinimaxLinearizationParameter` from
  `Definition_3_1_2_3`
- bridge/view: the displayed `EReal`-infimum equality recalled by
  `isMinimaxLinearizationParameter_iff`

Definition 3.10 adds no new mathematical data beyond that owner predicate, so this file recalls
the owner declarations directly instead of keeping a parallel local wrapper. -/

recall IsMinimaxLinearizationParameter

recall isMinimaxLinearizationParameter_iff

/-! ### Lemma_3_10 (from Chap03) -/
noncomputable section

open scoped Gradient Topology WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 3.10 lies in the chapter's extended-valued convex-analysis / continuous-subgradient
selection domain.

Mandatory domain-style sampling before refinement:
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owner for
  extended-valued subgradients;
- `HasGradientAt` and `gradient` from mathlib's gradient API, the canonical owner for
  differentiability together with a specified gradient vector;
- `subdifferential_eq_singleton_gradient` in `Lemma_3_1_7`, the chapter theorem relating
  differentiability to the singleton subdifferential owner;
- `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior` and
  `subdifferential_convexDirectionalDerivativeReal_at_zero_eq_subdifferential` in `Theorem_3_21`,
  the chapter owner theorems controlling directional derivatives and subdifferentials at interior
  points.

Best owner abstraction:
- source-facing: the continuous subgradient selection theorem below;
- core/canonical: `HasGradientAt (withTopRealPart f) (g x0) x0`;
- bridge/view: the derived differentiability and gradient-identification consequences.

Primitive data:
- a convex extended-real-valued function `f`;
- an interior base point `x0 ∈ interior (dom f)`;
- a local subgradient selection `g`;
- eventual owner membership `g x ∈ ∂ f(x)` near `x0`;
- continuity of `g` at `x0`.

Derived API:
- `hasGradientAt_withTopRealPart_of_continuous_subgradient_selection`;
- `differentiableAt_withTopRealPart_of_continuous_subgradient_selection`;
- `gradient_eq_of_continuous_subgradient_selection`.

Source/core/bridge triage:
- source-facing: Lemma 3.10's differentiability conclusion from a continuous subgradient
  selection;
- core/canonical: `HasGradientAt`, `withTopRealPart`, and `subdifferential`;
- bridge/view: the differentiability and explicit-gradient corollaries derived from the owner
  `HasGradientAt` statement.

The finite-maximum API from `Lemma_3_13` belongs to a later and unrelated source item. This file
therefore returns to the actual Chapter 3.10 domain and states the result directly on the chapter
owners `∂ f(x)`, `withTopRealPart f`, and the canonical gradient owner `HasGradientAt`, instead
of recalling later active-maximum machinery.
-/

section ContinuousSubgradientSelection

variable {f : E → WithTop ℝ} {x0 : E} {g : E → E}

/-- Lemma 3.10: if `f : E → ℝ ∪ {+∞}` is convex, `x₀` lies in the interior of its effective
domain, and a subgradient selection `g` is continuous at `x₀`, then the finite real
representative `withTopRealPart f` has gradient `g x₀` at `x₀`. This is the canonical owner form
of the textbook statement that `f` is differentiable at `x₀` with `∇f(x₀) = g(x₀)`. -/
-- Proof sketch: for each direction `p`, apply the subgradient inequality at nearby points
-- carrying the chosen subgradient `g x`, compare with the interior-point directional-derivative
-- owner from `Theorem_3_21`, and pass to the limit using `hcont`. The resulting directional
-- derivatives are the linear functional `p ↦ ⟪g x₀, p⟫`, which is exactly the
-- `HasGradientAt` owner statement.
theorem hasGradientAt_withTopRealPart_of_continuous_subgradient_selection
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx0 : x0 ∈ interior (dom f))
    (hsub : ∀ᶠ x in 𝓝 x0, g x ∈ ∂ f(x))
    (hcont : ContinuousAt g x0) :
    HasGradientAt (withTopRealPart f) (g x0) x0 := by
  rw [hasGradientAt_iff_tendsto]
  -- Read the goal through the explicit inner-product remainder from the gradient API.
  change Filter.Tendsto
    (fun y : E ↦
      ‖y - x0‖⁻¹ *
        ‖withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0)‖)
    (𝓝 x0) (𝓝 0)
  let _ := hf
  -- Extract the base-point subgradient from the neighborhood selection hypothesis.
  have hx0_sub : g x0 ∈ ∂ f(x0) :=
    hsub.self_of_nhds
  have hx0_sub' : IsSubgradientAt f x0 (g x0) :=
    mem_subdifferential_iff.mp hx0_sub
  have hx0_dom : x0 ∈ dom f := hx0_sub'.mem_dom
  -- Continuity of the selected subgradient makes the variation term tend to `0`.
  have hvariation_tendsto :
      Filter.Tendsto (fun y : E ↦ ‖g y - g x0‖) (𝓝 x0) (𝓝 0) := by
    have hconst : ContinuousAt (fun _ : E ↦ g x0) x0 := continuousAt_const
    have hcontDiff : ContinuousAt (fun y : E ↦ g y - g x0) x0 :=
      hcont.sub hconst
    simpa using hcontDiff.norm.tendsto
  have hnonneg :
      ∀ᶠ y : E in 𝓝 x0,
        0 ≤
          ‖y - x0‖⁻¹ *
            ‖withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0)‖ := by
    exact Filter.Eventually.of_forall fun y ↦ by
      positivity
  have herror_bound :
      ∀ᶠ y : E in 𝓝 x0,
        ‖y - x0‖⁻¹ *
            ‖withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0)‖
          ≤ ‖g y - g x0‖ := by
    filter_upwards [hsub] with y hy
    have hy_sub : IsSubgradientAt f y (g y) :=
      mem_subdifferential_iff.mp hy
    have hy_dom : y ∈ dom f := hy_sub.mem_dom
    -- The two support inequalities trap the linearization error between `0` and the subgradient
    -- variation paired with the displacement.
    have hlower :
        withTopRealPart f x0 + inner ℝ (g x0) (y - x0) ≤ withTopRealPart f y := by
      have hlower_top :
          (((withTopRealPart f x0 : ℝ) : WithTop ℝ) +
              (inner ℝ (g x0) (y - x0) : WithTop ℝ)) ≤
            (((withTopRealPart f y : ℝ) : WithTop ℝ)) := by
        have hineq := hx0_sub'.2 hy_dom
        rw [← coe_withTopRealPart hx0_dom, ← coe_withTopRealPart hy_dom] at hineq
        exact hineq
      exact_mod_cast hlower_top
    have hupper_aux :
        withTopRealPart f y - inner ℝ (g y) (y - x0) ≤ withTopRealPart f x0 := by
      have hupper_add :
          withTopRealPart f y + inner ℝ (g y) (x0 - y) ≤ withTopRealPart f x0 := by
        have hupper_top :
            (((withTopRealPart f y : ℝ) : WithTop ℝ) +
                (inner ℝ (g y) (x0 - y) : WithTop ℝ)) ≤
              (((withTopRealPart f x0 : ℝ) : WithTop ℝ)) := by
          have hineq := hy_sub.2 hx0_dom
          rw [← coe_withTopRealPart hy_dom, ← coe_withTopRealPart hx0_dom] at hineq
          exact hineq
        exact_mod_cast hupper_top
      simpa [sub_eq_add_neg, inner_add_right, inner_neg_right, add_assoc, add_left_comm, add_comm]
        using hupper_add
    have hupper :
        withTopRealPart f y - withTopRealPart f x0 ≤ inner ℝ (g y) (y - x0) := by
      linarith
    have herror_nonneg :
        0 ≤ withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0) := by
      linarith
    have herror_le_pairing :
        withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0) ≤
          inner ℝ (g y - g x0) (y - x0) := by
      rw [inner_sub_left]
      linarith
    have herror_norm_le :
        ‖withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0)‖ ≤
          ‖g y - g x0‖ * ‖y - x0‖ := by
      calc
        ‖withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0)‖ =
            withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0) := by
              rw [Real.norm_eq_abs, abs_of_nonneg herror_nonneg]
        _ ≤ inner ℝ (g y - g x0) (y - x0) := herror_le_pairing
        _ ≤ |inner ℝ (g y - g x0) (y - x0)| := le_abs_self _
        _ ≤ ‖g y - g x0‖ * ‖y - x0‖ := by
              simpa using abs_real_inner_le_norm (g y - g x0) (y - x0)
    by_cases hyx0 : y = x0
    · subst hyx0
      simp
    · have hy_norm_pos : 0 < ‖y - x0‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hyx0)
      exact (inv_mul_le_iff₀ hy_norm_pos).2 <| by
        simpa [mul_comm, mul_left_comm, mul_assoc] using herror_norm_le
  -- Squeeze the normalized remainder by the subgradient variation, which vanishes by continuity.
  exact squeeze_zero' hnonneg herror_bound hvariation_tendsto

/-- Companion consequence: under the hypotheses of Lemma 3.10, `withTopRealPart f` is
differentiable at `x₀`. -/
theorem differentiableAt_withTopRealPart_of_continuous_subgradient_selection
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx0 : x0 ∈ interior (dom f))
    (hsub : ∀ᶠ x in 𝓝 x0, g x ∈ ∂ f(x))
    (hcont : ContinuousAt g x0) :
    DifferentiableAt ℝ (withTopRealPart f) x0 := by
  have hgrad : HasGradientAt (withTopRealPart f) (g x0) x0 :=
    hasGradientAt_withTopRealPart_of_continuous_subgradient_selection hf hx0 hsub hcont
  exact hgrad.differentiableAt

/-- Companion consequence: under the hypotheses of Lemma 3.10, the gradient of
`withTopRealPart f` at `x₀` is the selected subgradient `g x₀`. -/
theorem gradient_eq_of_continuous_subgradient_selection
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx0 : x0 ∈ interior (dom f))
    (hsub : ∀ᶠ x in 𝓝 x0, g x ∈ ∂ f(x))
    (hcont : ContinuousAt g x0) :
    ∇ (withTopRealPart f) x0 = g x0 := by
  have hgrad : HasGradientAt (withTopRealPart f) (g x0) x0 :=
    hasGradientAt_withTopRealPart_of_continuous_subgradient_selection hf hx0 hsub hcont
  exact hgrad.gradient

end ContinuousSubgradientSelection

end

/-! ### Proposition_3_10 (from Chap03) -/
universe u

noncomputable section

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped SupportFunction

/- Proposition 3.10 lies in the chapter's support-function / positive-homogeneity domain.

Sampled owner-style declarations:
- `supportFunction` / `supportFunction_apply` in `Definition_3_9`
- `pointwiseSupremumOn` in `PointwiseSupremumOn`
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`

Best owner abstraction:
- source-facing: positive homogeneity of `ξ[Q]`
- core/canonical: `supportFunction`, built from `pointwiseSupremumOn`
- bridge/view: a real-scalar restatement obtained from the bundled nonnegative-scalar theorem below

Primitive data:
- a set `Q : Set E`
- a nonemptiness witness `hQ : Q.Nonempty`

Derived API:
- the `NNReal`-parameterized scaling theorem `supportFunction_smul`
- the real-scalar companion `supportFunction_nonneg_smul`

Because `supportFunction` is `EReal`-valued, the chapter owner `IsPositivelyHomogeneousOn`
cannot be applied to it directly. The minimal canonical surface is therefore the bundled
nonnegative-scalar theorem with parameter `τ : NNReal`, and the raw `τ : ℝ` plus `0 ≤ τ`
statement is kept only as a bridge.
-/

/-- Proposition 3.10: the support function of a nonempty set in a real inner-product space is
positively homogeneous with respect to every bundled nonnegative scalar. The textbook `ℝⁿ`
statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: rewrite `supportFunction Q (τ • x)` as the supremum of the image of `Q` under
-- `q ↦ ⟪τ • x, q⟫ = τ * ⟪x, q⟫`. If `τ = 0`, the support value at `0` is the supremum of the
-- constant-zero family over the nonempty set `Q`. If `τ > 0`, pull the positive scalar through
-- `sSup` using the standard order-theoretic rule for multiplication by a positive scalar.
theorem supportFunction_smul (Q : Set E) (hQ : Q.Nonempty) (x : E) (τ : NNReal) :
    ξ[Q] (τ • x) = (τ : EReal) * ξ[Q] x := by
  by_cases hτ : τ = 0
  · subst hτ
    rw [supportFunction_apply]
    simp [hQ]
  · have hτpos : 0 < (τ : ℝ) := by
      exact_mod_cast (show 0 < τ from pos_iff_ne_zero.mpr hτ)
    have hτE : (0 : EReal) < (τ : EReal) := by
      exact_mod_cast hτpos
    have hτE_top : (τ : EReal) ≠ ⊤ := EReal.coe_ne_top _
    rw [supportFunction_apply, supportFunction_apply]
    have himage :
        (fun g ↦ ↑(inner ℝ g (τ • x)) : E → EReal) '' Q =
          (fun z ↦ (τ : EReal) * z) '' ((fun g ↦ ↑(inner ℝ g x) : E → EReal) '' Q) := by
      ext y
      constructor
      · rintro ⟨g, hg, rfl⟩
        refine ⟨((inner ℝ g x : ℝ) : EReal), ?_, ?_⟩
        · exact ⟨g, hg, rfl⟩
        · change (τ : EReal) * ((inner ℝ g x : ℝ) : EReal) = ((inner ℝ g (τ • x) : ℝ) : EReal)
          rw [NNReal.smul_def, inner_smul_right]
          rfl
      · rintro ⟨z, ⟨g, hg, rfl⟩, rfl⟩
        refine ⟨g, hg, ?_⟩
        change ((inner ℝ g (τ • x) : ℝ) : EReal) = (τ : EReal) * ((inner ℝ g x : ℝ) : EReal)
        rw [NNReal.smul_def, inner_smul_right]
        rfl
    rw [himage]
    refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact mul_le_mul_of_nonneg_left (le_sSup hz) hτE.le
    · intro w hw
      have hw' : w / (τ : EReal) < sSup ((fun g ↦ ↑(inner ℝ g x) : E → EReal) '' Q) := by
        rw [EReal.div_lt_iff hτE hτE_top, mul_comm]
        exact hw
      rcases lt_sSup_iff.mp hw' with ⟨z, hz, hzw⟩
      refine ⟨(τ : EReal) * z, ⟨z, hz, rfl⟩, ?_⟩
      rw [EReal.div_lt_iff hτE hτE_top] at hzw
      simpa [mul_comm] using hzw

/-- Real-scalar bridge for Proposition 3.10, derived from the bundled `NNReal` theorem
`supportFunction_smul`. -/
theorem supportFunction_nonneg_smul
    (Q : Set E) (hQ : Q.Nonempty) (x : E) (τ : ℝ) (hτ : 0 ≤ τ) :
    ξ[Q] (τ • x) = (τ : EReal) * ξ[Q] x := by
  simpa [NNReal.smul_def, Real.toNNReal_of_nonneg hτ] using
    supportFunction_smul Q hQ x (Real.toNNReal τ)

end

/-! ### Theorem_3_10 (from Chap03) -/
universe u

noncomputable section

/- Theorem 3.10 is a source-facing restatement of the canonical convex-composition owner theorem.

Primary domain:
- convex composition on real modules

Sampled owner-style declarations in this domain:
- mathlib `ConvexOn`
- mathlib `ConvexOn.comp`
- mathlib `ConvexOn.subset`
- mathlib `MonotoneOn`

Source-facing layer:
- convexity of `φ ∘ ψ` on `domψ`

Core/canonical owner:
- mathlib `ConvexOn.comp`

Bridge/view:
- if the textbook first phrases the outer convexity hypothesis on a larger interval `I ⊆ ℝ`, the
  restriction to `ψ '' domψ` is the companion step handled by `ConvexOn.subset`

Primitive data:
- convexity of `ψ` on `domψ`
- convexity of `φ` on `ψ '' domψ`
- monotonicity of `φ` on `ψ '' domψ`

Derived API:
- the composed convexity conclusion from `ConvexOn.comp`

Source/core/bridge triage:
- source-facing: the image-set convex-composition statement on a real module
- core/canonical: `ConvexOn.comp`
- bridge/view: `ConvexOn.subset`, when the outer convexity is first stated on a larger interval

The earlier chapter refinement already identified `ConvexOn.comp` as the owner theorem for this
composition statement. Since the mathlib owner is genuinely more general than the textbook real-
module specialization, this file keeps the source-faithful specialized `#check` surface rather
than promoting the stronger generic statement to the main item.
-/

/- Theorem 3.10: the source-facing composition statement is the real-module specialization of the
owner theorem `ConvexOn.comp`. -/
namespace ConvexOn

section

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]
variable {domψ : Set X} {I : Set ℝ} {ψ : X → ℝ} {φ : ℝ → ℝ}

#check
  (ConvexOn.comp :
    ConvexOn ℝ (ψ '' domψ) φ →
      ConvexOn ℝ domψ ψ →
      MonotoneOn φ (ψ '' domψ) →
      ConvexOn ℝ domψ (φ ∘ ψ))

/-- Helper for Theorem 3.10: once the outer convexity is restricted to `ψ '' domψ`, the canonical
owner theorem `ConvexOn.comp` closes the composition claim. -/
theorem comp_of_monotoneOn_image_of_convex_image
    (hφ_image : ConvexOn ℝ (ψ '' domψ) φ) (hψ : ConvexOn ℝ domψ ψ)
    (hφ_mono : MonotoneOn φ (ψ '' domψ)) :
    ConvexOn ℝ domψ (φ ∘ ψ) := by
  -- This is exactly the owner-level composition theorem on the image set.
  simpa using ConvexOn.comp hφ_image hψ hφ_mono

/-- Helper for Theorem 3.10: restricting `ψ` to the scalar segment between two domain points keeps
the resulting one-variable map convex on `[0,1]`. -/
lemma segment_restriction_convexOn_Icc
    (hψ : ConvexOn ℝ domψ ψ) {x y : X} (hx : x ∈ domψ) (hy : y ∈ domψ) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ ↦ ψ ((1 - t) • x + t • y)) := by
  refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
  intro a ha b hb μ ν hμ hν hμν
  have ha_dom : (1 - a) • x + a • y ∈ domψ := by
    -- The first sampled point lies on the segment joining `x` and `y`.
    exact hψ.1 hx hy (sub_nonneg.mpr ha.2) ha.1 (sub_add_cancel _ _)
  have hb_dom : (1 - b) • x + b • y ∈ domψ := by
    -- The second sampled point lies on the same segment.
    exact hψ.1 hx hy (sub_nonneg.mpr hb.2) hb.1 (sub_add_cancel _ _)
  have hcombo :
      (1 - (μ * a + ν * b)) • x + (μ * a + ν * b) • y =
        μ • ((1 - a) • x + a • y) + ν • ((1 - b) • x + b • y) := by
    -- This rewrites the segment point at `μa + νb` as the convex combination of the segment points
    -- at `a` and `b`.
    have hxcoeff : 1 - (μ * a + ν * b) = μ * (1 - a) + ν * (1 - b) := by
      nlinarith [hμν]
    rw [hxcoeff, add_smul, add_smul, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
      smul_smul]
    abel_nf
  -- After the algebraic rewrite, convexity of `ψ` applies directly.
  simpa [smul_eq_mul, hcombo] using hψ.2 ha_dom hb_dom hμ hν hμν

/-- Helper for Theorem 3.10: any value of the scalar segment restriction comes from a point of
`domψ`, so it belongs to `ψ '' domψ`. -/
lemma segment_value_mem_image
    (hψ : ConvexOn ℝ domψ ψ) {x y : X} (hx : x ∈ domψ) (hy : y ∈ domψ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ψ ((1 - t) • x + t • y) ∈ ψ '' domψ := by
  -- The segment point itself lies in `domψ`, so its image lies in `ψ '' domψ`.
  refine ⟨(1 - t) • x + t • y, ?_, rfl⟩
  exact hψ.1 hx hy (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel _ _)

/-- Helper for Theorem 3.10: the segment restriction is continuous on the open interval `(0,1)`. -/
lemma segment_restriction_continuousOn_Ioo
    (hψ : ConvexOn ℝ domψ ψ) {x y : X} (hx : x ∈ domψ) (hy : y ∈ domψ) :
    ContinuousOn (fun t : ℝ ↦ ψ ((1 - t) • x + t • y)) (Set.Ioo (0 : ℝ) 1) := by
  -- Restrict the convex segment map from `[0,1]` to its open interior, where convex functions are
  -- automatically continuous.
  exact ((segment_restriction_convexOn_Icc hψ hx hy).subset Set.Ioo_subset_Icc_self
    (convex_Ioo (0 : ℝ) 1)).continuousOn isOpen_Ioo

/-- Helper for Theorem 3.10: the image of a continuous real-valued map on `(0,1)` is an interval. -/
lemma image_Ioo_ordConnected {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo (0 : ℝ) 1)) :
    Set.OrdConnected (g '' Set.Ioo (0 : ℝ) 1) := by
  -- Continuous images of preconnected sets remain preconnected, hence interval-shaped in `ℝ`.
  exact (isPreconnected_Ioo.image g hg).ordConnected

/-- Helper for Theorem 3.10: once a convex real function is weakly increasing at one interior pair,
it stays monotone to the right. -/
lemma convexOn_monotoneOn_Ici_of_le {J : Set ℝ} {g : ℝ → ℝ}
    (hg : ConvexOn ℝ J g) {u v : ℝ} (hu : u ∈ J) (hv : v ∈ J) (huv : u < v)
    (hguv : g u ≤ g v) :
    MonotoneOn g (J ∩ Set.Ici v) := by
  intro s hs t ht hst
  have hvs : v ≤ s := hs.2
  rcases eq_or_lt_of_le hvs with rfl | hvs_strict
  · -- The base comparison already shows the function does not decrease past `v`.
    simpa using hg.le_right_of_left_le'' hu ht.1 huv ht.2 hguv
  have hgv : g v ≤ g s := by
    -- First push the base comparison from `v` to the intermediate point `s`.
    exact hg.le_right_of_left_le'' hu hs.1 huv hs.2 hguv
  -- Then reuse the same propagation step from `s` to `t`.
  exact hg.le_right_of_left_le'' hv ht.1 hvs_strict hst hgv

/-- Helper for Theorem 3.10: the interior image of the segment restriction is either a singleton
or contains a strict ordered pair. -/
lemma interior_image_subsingleton_or_exists_lt {g : ℝ → ℝ} :
    Set.Subsingleton (g '' Set.Ioo (0 : ℝ) 1) ∨
      ∃ u v, u ∈ g '' Set.Ioo (0 : ℝ) 1 ∧ v ∈ g '' Set.Ioo (0 : ℝ) 1 ∧ u < v := by
  classical
  by_cases hlt : ∃ u v, u ∈ g '' Set.Ioo (0 : ℝ) 1 ∧ v ∈ g '' Set.Ioo (0 : ℝ) 1 ∧ u < v
  · exact Or.inr hlt
  · left
    intro u hu v hv
    rcases lt_trichotomy u v with huv | rfl | hvu
    · exact False.elim (hlt ⟨u, v, hu, hv, huv⟩)
    · rfl
    · exact False.elim (hlt ⟨v, u, hv, hu, hvu⟩)

/-- Helper for Theorem 3.10: if the interior image of the segment restriction is a singleton, then
the composition is convex because the interior values are constant and sit below the endpoint
values. -/
lemma convex_on_Icc_comp_of_monotoneOn_image_of_subsingleton_Ioo_image {g : ℝ → ℝ}
    (hg : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) g) (_hφ : ConvexOn ℝ I φ)
    (hφ_mono : MonotoneOn φ (g '' Set.Icc (0 : ℝ) 1))
    (_himage : g '' Set.Icc (0 : ℝ) 1 ⊆ I)
    (hsub : Set.Subsingleton (g '' Set.Ioo (0 : ℝ) 1)) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (φ ∘ g) := by
  let c : ℝ := g (1 / 2)
  have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hquarter_mem : (1 / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hthree_quarter_mem : (3 / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hconst :
      ∀ {s : ℝ}, s ∈ Set.Ioo (0 : ℝ) 1 → g s = c := by
    intro s hs
    apply hsub
    · exact ⟨s, hs, rfl⟩
    · exact ⟨1 / 2, hhalf_mem, rfl⟩
  have hc_le_left : c ≤ g 0 := by
    have hquarter_eq : g (1 / 4 : ℝ) = c := hconst hquarter_mem
    have hhalf_eq : g (1 / 2 : ℝ) = c := hconst hhalf_mem
    have hconv :=
      hg.2 (x := (0 : ℝ)) (y := (1 / 2 : ℝ)) (by constructor <;> norm_num)
        (by constructor <;> norm_num)
        (by norm_num) (by norm_num) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hconv' := hconv
    norm_num [smul_eq_mul] at hconv'
    have hquarter_eq' : g ((4 : ℝ)⁻¹) = c := by
      simpa using hquarter_eq
    have hhalf_eq' : g ((2 : ℝ)⁻¹) = c := by
      simpa using hhalf_eq
    -- Convexity at the midpoint between `0` and `1/2` shows the constant interior value is below
    -- the left endpoint.
    have : c ≤ (1 / 2 : ℝ) * g 0 + (1 / 2 : ℝ) * c := by
      simpa [hquarter_eq', hhalf_eq'] using hconv'
    linarith
  have hc_le_right : c ≤ g 1 := by
    have hhalf_eq : g (1 / 2 : ℝ) = c := hconst hhalf_mem
    have hthree_quarter_eq : g (3 / 4 : ℝ) = c := hconst hthree_quarter_mem
    have hconv :=
      hg.2 (x := (1 / 2 : ℝ)) (y := (1 : ℝ)) (by constructor <;> norm_num)
        (by constructor <;> norm_num)
        (by norm_num) (by norm_num) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have hconv' := hconv
    norm_num [smul_eq_mul] at hconv'
    have hhalf_eq' : g ((2 : ℝ)⁻¹) = c := by
      simpa using hhalf_eq
    -- The same midpoint argument on `[1/2, 1]` bounds the constant interior value by `g 1`.
    have : c ≤ (1 / 2 : ℝ) * c + (1 / 2 : ℝ) * g 1 := by
      have hconv'' := hconv'
      rw [hthree_quarter_eq, hhalf_eq] at hconv''
      exact hconv''
    linarith
  have hφc_le :
      ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → φ c ≤ φ (g t) := by
    intro t ht
    by_cases htIoo : t ∈ Set.Ioo (0 : ℝ) 1
    · -- Every interior point has the same image value `c`.
      simp [hconst htIoo]
    · have ht_eq : t = 0 ∨ t = 1 := by
        rcases eq_or_lt_of_le ht.1 with rfl | ht0
        · exact Or.inl rfl
        rcases eq_or_lt_of_le ht.2 with rfl | ht1
        · exact Or.inr rfl
        exact False.elim (htIoo ⟨ht0, ht1⟩)
      rcases ht_eq with rfl | rfl
      · have hc_mem : c ∈ g '' Set.Icc (0 : ℝ) 1 := by
          exact ⟨1 / 2, Set.Ioo_subset_Icc_self hhalf_mem, rfl⟩
        have hzero_mem : g 0 ∈ g '' Set.Icc (0 : ℝ) 1 := by
          exact ⟨0, by constructor <;> norm_num, rfl⟩
        exact hφ_mono hc_mem hzero_mem hc_le_left
      · have hc_mem : c ∈ g '' Set.Icc (0 : ℝ) 1 := by
          exact ⟨1 / 2, Set.Ioo_subset_Icc_self hhalf_mem, rfl⟩
        have hone_mem : g 1 ∈ g '' Set.Icc (0 : ℝ) 1 := by
          exact ⟨1, by constructor <;> norm_num, rfl⟩
        exact hφ_mono hc_mem hone_mem hc_le_right
  refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
  intro x hx y hy a b ha hb hab
  let m : ℝ := a * x + b * y
  have hm_mem : m ∈ Set.Icc (0 : ℝ) 1 := by
    exact (convex_Icc (0 : ℝ) 1) hx hy ha hb hab
  by_cases hmIoo : m ∈ Set.Ioo (0 : ℝ) 1
  · have hm_eq : g m = c := hconst hmIoo
    -- Once the midpoint lands in the interior, both endpoint and interior values dominate `φ c`.
    calc
      φ (g m) = φ c := by rw [hm_eq]
      _ = a * φ c + b * φ c := by
        rw [← add_mul, hab, one_mul]
      _ ≤ a * φ (g x) + b * φ (g y) := by
        gcongr
        · exact hφc_le hx
        · exact hφc_le hy
  · have hm_eq : m = 0 ∨ m = 1 := by
      rcases eq_or_lt_of_le hm_mem.1 with hm0 | hm0
      · exact Or.inl hm0.symm
      rcases eq_or_lt_of_le hm_mem.2 with hm1 | hm1
      · exact Or.inr hm1
      exact False.elim (hmIoo ⟨hm0, hm1⟩)
    rcases hm_eq with hm0 | hm1
    · -- If the convex combination equals `0`, all positive-weight inputs are already at `0`.
      have hm0' : a * x + b * y = 0 := by
        simpa [m] using hm0
      rcases lt_or_eq_of_le ha with ha_pos | ha_zero
      · rcases lt_or_eq_of_le hb with hb_pos | hb_zero
        · have hx0 : x = 0 := by
            nlinarith [hx.1, hy.1, ha_pos, hb_pos, hm0']
          have hy0 : y = 0 := by
            nlinarith [hx.1, hy.1, ha_pos, hb_pos, hm0']
          subst hx0
          subst hy0
          have hsum : a * φ (g 0) + b * φ (g 0) = φ (g 0) := by
            rw [← add_mul, hab, one_mul]
          simp [Function.comp, hsum]
        · have hb_zero' : b = 0 := hb_zero.symm
          have hb_one : b = 0 := hb_zero'
          have ha_one : a = 1 := by linarith
          have hx0 : x = 0 := by
            simpa [m, ha_one, hb_one] using hm0
          subst hx0
          simp [Function.comp, ha_one, hb_one]
      · have ha_zero' : a = 0 := ha_zero.symm
        have hb_one : b = 1 := by linarith
        have hy0 : y = 0 := by
          simpa [m, ha_zero', hb_one] using hm0
        subst hy0
        simp [Function.comp, ha_zero', hb_one]
    · -- The same endpoint arithmetic handles the right endpoint `1`.
      have hm1' : a * x + b * y = 1 := by
        simpa [m] using hm1
      rcases lt_or_eq_of_le ha with ha_pos | ha_zero
      · rcases lt_or_eq_of_le hb with hb_pos | hb_zero
        · have hx1 : x = 1 := by
            nlinarith [hx.2, hy.2, ha_pos, hb_pos, hm1']
          have hy1 : y = 1 := by
            nlinarith [hx.2, hy.2, ha_pos, hb_pos, hm1']
          subst hx1
          subst hy1
          have hsum : a * φ (g 1) + b * φ (g 1) = φ (g 1) := by
            rw [← add_mul, hab, one_mul]
          simp [Function.comp, hab, hsum]
        · have hb_zero' : b = 0 := hb_zero.symm
          have ha_one : a = 1 := by linarith
          have hx1 : x = 1 := by
            simpa [m, ha_one, hb_zero'] using hm1
          subst hx1
          simp [Function.comp, ha_one, hb_zero']
      · have ha_zero' : a = 0 := ha_zero.symm
        have hb_one : b = 1 := by linarith
        have hy1 : y = 1 := by
          simpa [m, ha_zero', hb_one] using hm1
        subst hy1
        simp [Function.comp, ha_zero', hb_one]

/-- Helper for Theorem 3.10: if an ordered comparison value lies above one interior-image point but
is not itself in the interior image, then it must lie to the right of any fixed interior witness. -/
lemma right_witness_le_of_not_mem_interior_image {S : Set ℝ} (hS : Set.OrdConnected S)
    {s v w : ℝ} (hs : s ∈ S) (hv : v ∈ S) (hsw : s ≤ w) (hw : w ∉ S) :
    v ≤ w := by
  -- If `w < v`, then interval-connectedness forces `w` back into `S`, contradiction.
  by_contra hvw
  have hwv : w < v := lt_of_not_ge hvw
  have hw_mem : w ∈ Set.Icc s v := ⟨hsw, hwv.le⟩
  exact hw ((hS.out hs hv) hw_mem)

/-- Helper for Theorem 3.10: once the comparison value `w` sits to the right of the fixed witness
`v`, monotonicity on the image and on the right tail of `I` bounds `φ s` by `φ w`. -/
lemma phi_le_comparison_value_of_not_mem_interior_image {g : ℝ → ℝ}
    (hS : Set.OrdConnected (g '' Set.Ioo (0 : ℝ) 1))
    (himage : g '' Set.Icc (0 : ℝ) 1 ⊆ I) {s v w : ℝ}
    (hs : s ∈ g '' Set.Ioo (0 : ℝ) 1) (hv : v ∈ g '' Set.Ioo (0 : ℝ) 1) (hsw : s ≤ w)
    (hwI : w ∈ I) (hw : w ∉ g '' Set.Ioo (0 : ℝ) 1)
    (hφ_mono : MonotoneOn φ (g '' Set.Icc (0 : ℝ) 1))
    (hφ_right : MonotoneOn φ (I ∩ Set.Ici v)) :
    φ s ≤ φ w := by
  have hsIcc : s ∈ g '' Set.Icc (0 : ℝ) 1 := by
    rcases hs with ⟨t, ht, rfl⟩
    exact ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩
  have hvIcc : v ∈ g '' Set.Icc (0 : ℝ) 1 := by
    rcases hv with ⟨t, ht, rfl⟩
    exact ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩
  have hsI : s ∈ I := himage hsIcc
  have hvI : v ∈ I := himage hvIcc
  have hvw : v ≤ w := right_witness_le_of_not_mem_interior_image hS hs hv hsw hw
  by_cases hvs : v ≤ s
  · -- When `s` is already to the right of `v`, the tail monotonicity compares `s` directly to `w`.
    exact hφ_right ⟨hsI, hvs⟩ ⟨hwI, hvw⟩ hsw
  · -- Otherwise first move from `s` up to `v` along the image, then from `v` to `w` on the tail.
    have hsv : s ≤ v := le_of_not_ge hvs
    have hφsv : φ s ≤ φ v := hφ_mono hsIcc hvIcc hsv
    have hv_mem_Ici : v ∈ Set.Ici v := by
      show v ≤ v
      exact le_rfl
    have hφvw : φ v ≤ φ w := hφ_right ⟨hvI, hv_mem_Ici⟩ ⟨hwI, hvw⟩ hvw
    exact le_trans hφsv hφvw

/-- Helper for Theorem 3.10: in the nondegenerate interior-image branch, the remaining work is to
bootstrap monotonicity of `φ` from an actual interior ordered pair and compare the Jensen value to
the right edge of the interior image. -/
lemma convex_on_Icc_comp_of_monotoneOn_image_of_strict_pair {g : ℝ → ℝ}
    (hg : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) g) (_hφ : ConvexOn ℝ I φ)
    (hφ_mono : MonotoneOn φ (g '' Set.Icc (0 : ℝ) 1))
    (_himage : g '' Set.Icc (0 : ℝ) 1 ⊆ I)
    {u v : ℝ} (hu : u ∈ g '' Set.Ioo (0 : ℝ) 1) (hv : v ∈ g '' Set.Ioo (0 : ℝ) 1)
    (huv : u < v) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (φ ∘ g) := by
  have hcont : ContinuousOn g (Set.Ioo (0 : ℝ) 1) := by
    -- The interior restriction of a convex real function is continuous.
    exact ((hg.subset Set.Ioo_subset_Icc_self (convex_Ioo (0 : ℝ) 1)).continuousOn isOpen_Ioo)
  have hS : Set.OrdConnected (g '' Set.Ioo (0 : ℝ) 1) := image_Ioo_ordConnected hcont
  have huIcc : u ∈ g '' Set.Icc (0 : ℝ) 1 := by
    rcases hu with ⟨t, ht, rfl⟩
    exact ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩
  have hvIcc : v ∈ g '' Set.Icc (0 : ℝ) 1 := by
    rcases hv with ⟨t, ht, rfl⟩
    exact ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩
  have huI : u ∈ I := _himage huIcc
  have hvI : v ∈ I := _himage hvIcc
  have hφuv : φ u ≤ φ v := hφ_mono huIcc hvIcc huv.le
  have hφ_right : MonotoneOn φ (I ∩ Set.Ici v) :=
    convexOn_monotoneOn_Ici_of_le _hφ huI hvI huv hφuv
  refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
  intro x hx y hy a b ha hb hab
  let m : ℝ := a * x + b * y
  let w : ℝ := a * g x + b * g y
  have hx_image : g x ∈ g '' Set.Icc (0 : ℝ) 1 := ⟨x, hx, rfl⟩
  have hy_image : g y ∈ g '' Set.Icc (0 : ℝ) 1 := ⟨y, hy, rfl⟩
  have hxI : g x ∈ I := _himage hx_image
  have hyI : g y ∈ I := _himage hy_image
  have hm_mem : m ∈ Set.Icc (0 : ℝ) 1 := by
    exact (convex_Icc (0 : ℝ) 1) hx hy ha hb hab
  by_cases hmIoo : m ∈ Set.Ioo (0 : ℝ) 1
  · have hs : g m ∈ g '' Set.Ioo (0 : ℝ) 1 := ⟨m, hmIoo, rfl⟩
    have hsIcc : g m ∈ g '' Set.Icc (0 : ℝ) 1 := ⟨m, Set.Ioo_subset_Icc_self hmIoo, rfl⟩
    have hgmw : g m ≤ w := by
      -- Convexity of `g` gives the inner Jensen comparison value.
      simpa [m, w, smul_eq_mul] using hg.2 hx hy ha hb hab
    have hwI : w ∈ I := by
      -- The outer convexity domain contains the scalar Jensen combination of `g x` and `g y`.
      simpa [w, smul_eq_mul] using _hφ.1 hxI hyI ha hb hab
    have hφgmw : φ (g m) ≤ φ w := by
      by_cases hwS : w ∈ g '' Set.Ioo (0 : ℝ) 1
      · -- If the comparison value stays in the interior image, monotonicity on the image suffices.
        have hwIcc : w ∈ g '' Set.Icc (0 : ℝ) 1 := by
          rcases hwS with ⟨t, ht, htw⟩
          exact ⟨t, Set.Ioo_subset_Icc_self ht, htw⟩
        exact hφ_mono hsIcc hwIcc hgmw
      · -- Otherwise the comparison value sits to the right of the fixed interior witness `v`.
        exact phi_le_comparison_value_of_not_mem_interior_image hS _himage hs hv hgmw hwI hwS
          hφ_mono hφ_right
    have hφw : φ w ≤ a * φ (g x) + b * φ (g y) := by
      -- Convexity of `φ` on `I` closes the outer Jensen step.
      simpa [w, smul_eq_mul] using _hφ.2 hxI hyI ha hb hab
    exact le_trans hφgmw hφw
  · have hm_eq : m = 0 ∨ m = 1 := by
      rcases eq_or_lt_of_le hm_mem.1 with hm0 | hm0
      · exact Or.inl hm0.symm
      rcases eq_or_lt_of_le hm_mem.2 with hm1 | hm1
      · exact Or.inr hm1
      exact False.elim (hmIoo ⟨hm0, hm1⟩)
    rcases hm_eq with hm0 | hm1
    · -- If the convex combination equals `0`, all positive-weight inputs are already at `0`.
      have hm0' : a * x + b * y = 0 := by
        simpa [m] using hm0
      rcases lt_or_eq_of_le ha with ha_pos | ha_zero
      · rcases lt_or_eq_of_le hb with hb_pos | hb_zero
        · have hx0 : x = 0 := by
            nlinarith [hx.1, hy.1, ha_pos, hb_pos, hm0']
          have hy0 : y = 0 := by
            nlinarith [hx.1, hy.1, ha_pos, hb_pos, hm0']
          subst hx0
          subst hy0
          have hsum : a * φ (g 0) + b * φ (g 0) = φ (g 0) := by
            rw [← add_mul, hab, one_mul]
          simp [Function.comp, hsum]
        · have hb_zero' : b = 0 := hb_zero.symm
          have hb_one : b = 0 := hb_zero'
          have ha_one : a = 1 := by
            linarith
          have hx0 : x = 0 := by
            simpa [m, ha_one, hb_one] using hm0
          subst hx0
          simp [Function.comp, ha_one, hb_one]
      · have ha_zero' : a = 0 := ha_zero.symm
        have hb_one : b = 1 := by
          linarith
        have hy0 : y = 0 := by
          simpa [m, ha_zero', hb_one] using hm0
        subst hy0
        simp [Function.comp, ha_zero', hb_one]
    · -- The same endpoint arithmetic handles the right endpoint `1`.
      have hm1' : a * x + b * y = 1 := by
        simpa [m] using hm1
      rcases lt_or_eq_of_le ha with ha_pos | ha_zero
      · rcases lt_or_eq_of_le hb with hb_pos | hb_zero
        · have hx1 : x = 1 := by
            nlinarith [hx.2, hy.2, ha_pos, hb_pos, hm1']
          have hy1 : y = 1 := by
            nlinarith [hx.2, hy.2, ha_pos, hb_pos, hm1']
          subst hx1
          subst hy1
          have hsum : a * φ (g 1) + b * φ (g 1) = φ (g 1) := by
            rw [← add_mul, hab, one_mul]
          simp [Function.comp, hab, hsum]
        · have hb_zero' : b = 0 := hb_zero.symm
          have ha_one : a = 1 := by
            linarith
          have hx1 : x = 1 := by
            simpa [m, ha_one, hb_zero'] using hm1
          subst hx1
          simp [Function.comp, ha_one, hb_zero']
      · have ha_zero' : a = 0 := ha_zero.symm
        have hb_one : b = 1 := by
          linarith
        have hy1 : y = 1 := by
          simpa [m, ha_zero', hb_one] using hm1
        subst hy1
        simp [Function.comp, ha_zero', hb_one]

/-- Helper for Theorem 3.10: the univariate composition step on `[0,1]` reduces the textbook proof
to a single interval-analysis argument on the segment restriction. -/
lemma convex_on_Icc_comp_of_monotoneOn_image {g : ℝ → ℝ}
    (hg : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) g) (hφ : ConvexOn ℝ I φ)
    (hφ_mono : MonotoneOn φ (g '' Set.Icc (0 : ℝ) 1))
    (himage : g '' Set.Icc (0 : ℝ) 1 ⊆ I) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (φ ∘ g) := by
  -- Route correction: the old global-image-convexity bridge is false for Lean's `ConvexOn` on
  -- closed intervals because endpoint jumps are allowed. The correct route is segmentwise: analyze
  -- the continuous interior image of `g`, propagate monotonicity of `φ` from that interval, and
  -- handle the endpoint jumps separately.
  rcases interior_image_subsingleton_or_exists_lt (g := g) with hsub | ⟨u, v, hu, hv, huv⟩
  · -- The degenerate interior-image branch is now closed directly.
    exact convex_on_Icc_comp_of_monotoneOn_image_of_subsingleton_Ioo_image hg hφ hφ_mono himage
      hsub
  · -- Route correction: the remaining nondegenerate branch should use the ordered interior pair,
    -- not a global image-convexity shortcut.
    exact convex_on_Icc_comp_of_monotoneOn_image_of_strict_pair hg hφ hφ_mono himage hu hv huv

/-- Theorem 3.10: if `ψ` is convex on `domψ`, `φ` is convex on a set `I` containing `ψ '' domψ`,
and `φ` is nondecreasing on `ψ '' domψ`, then `φ ∘ ψ` is convex on `domψ`. -/
theorem comp_of_monotoneOn_image
    (hφ : ConvexOn ℝ I φ) (hψ : ConvexOn ℝ domψ ψ)
    (hφ_mono : MonotoneOn φ (ψ '' domψ)) (himage : ψ '' domψ ⊆ I) :
    ConvexOn ℝ domψ (φ ∘ ψ) := by
  refine ⟨hψ.1, ?_⟩
  intro x hx y hy a b ha hb hab
  let g : ℝ → ℝ := fun t ↦ ψ ((1 - t) • x + t • y)
  have hg : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) g :=
    segment_restriction_convexOn_Icc hψ hx hy
  have hsegment_image : g '' Set.Icc (0 : ℝ) 1 ⊆ ψ '' domψ := by
    intro r hr
    rcases hr with ⟨t, ht, rfl⟩
    exact segment_value_mem_image hψ hx hy ht
  have hg_image : g '' Set.Icc (0 : ℝ) 1 ⊆ I := by
    intro r hr
    exact himage (hsegment_image hr)
  have hmono_g : MonotoneOn φ (g '' Set.Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    exact hφ_mono (hsegment_image hu) (hsegment_image hv) huv
  have hcomp : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (φ ∘ g) :=
    convex_on_Icc_comp_of_monotoneOn_image hg hφ hmono_g hg_image
  have hab' : a * 0 + b * 1 = b := by ring
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_rfl
    · norm_num
  have hone_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · norm_num
    · exact le_rfl
  have hseg := hcomp.2 hzero_mem hone_mem ha hb hab
  have hba : -b + 1 = a := by
    linarith
  -- The segmentwise univariate convexity statement now reads back as the desired Jensen bound.
  simpa [g, Function.comp, hab', hab, hba, smul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] using hseg

end

end ConvexOn

end
