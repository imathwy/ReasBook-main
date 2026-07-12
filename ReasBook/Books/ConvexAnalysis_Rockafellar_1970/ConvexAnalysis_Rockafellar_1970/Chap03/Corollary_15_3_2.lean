import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_21
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_24
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped GaugePolar RealInnerProductSpace Rockafellar

universe u

local instance powerGaugeTransformInstSMulRealEReal : SMul ℝ EReal := WithBotTop.instSMul

section

variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 15.3.2 applies Corollary 15.3.1 to the concrete power profile and
  concludes that the explicit transform `(p f)^(1/p)` is a closed gauge whose polar is
  `(q f*)^(1/q)`, together with the resulting Hölder-type inequality and the polarity of the
  sublevel sets `{x | f x ≤ 1 / p}` and `{x* | f* x* ≤ 1 / q}`.
- `core/canonical`: the owner abstractions already present in the chapter are
  `powerProfile` from Corollary 15.3.1, together with `Function.PositivelyHomogeneousOfDegree`,
  `Function.IsClosedProperConvex`, `IsClosedGauge`, `gauge_polar`, `convexConjugate`, and
  `Set.polar`.
- `bridge/view`: the explicit inverse-view transform `powerGaugeTransform p f` is reused directly
  from Text 15.0.24 as the chapter owner for expressions of the form `(p f)^(1/p)`.

Domain-style sampling used here:
- `powerGaugeTransform` and `powerGaugeTransform_apply_of_nonneg_lt_top` from `Text_15_0_24`;
- `Function.PositivelyHomogeneousOfDegree` from `Text_15_0_21`;
- `gauge_polar_isClosedGauge` and `gauge_polar_egauge_eq_egauge_polar` from
  `Theorem_15_1`;
- `inner_le_mul_gauge_polar` from `Text_15_0_9`.

Primitive data vs derived API:
- primitive inputs: exponents `p q`, the function `f`, and the source assumptions on `f`;
- owner bridge datum: the scalar profile `powerProfile` from Corollary 15.3.1;
- reused bridge owner: the explicit transform `powerGaugeTransform p f`;
- derived outputs: the closed-gauge structure of that transform, its polar formula, the pairing
  inequality, and the polar-sublevel-set identity.

Layer target:
- clause (1) is `source-facing` on the weak real topological-module layer already used by
  `powerGaugeTransform`, `Function.IsClosedProperConvex`,
  `Function.PositivelyHomogeneousOfDegree`, and `IsClosedGauge`;
- clauses (2)-(4) remain `source-facing` on the finite-dimensional real inner-product layer
  required by the chapter owners `gauge_polar`, `convexConjugate`, and the pairing inequality.
- in both layers the corollary is stated directly for the explicit transform `(p f)^(1/p)`
  rather than through any wrapper/package abstraction, so the textbook `R^n` statement remains a
  specialization rather than the public owner surface.
-/

-- Proof sketch: apply Corollary 15.3.1 to write `f` as `x ↦ (1 / p) * k(x)^p` for a closed gauge
-- `k`. Then `powerGaugeTransform p f = k` pointwise, and the conjugate formula from the same
-- corollary rewrites `powerGaugeTransform q (convexConjugate f)` as the polar gauge
-- `kᵒ`.
/-- Corollary 15.3.2: if `f` is a closed proper convex function positively homogeneous of degree
`p` with `1 < p`, then `(p f)^(1/p)`, formalized as
`powerGaugeTransform p f`, is a closed gauge. -/
theorem powerGaugeTransform_isClosedGauge
    {p : ℝ} (hp : 1 < p) {f : E → EReal}
    (hf_closed : f.IsClosedProperConvex)
    (hf_hom : f.PositivelyHomogeneousOfDegree p) :
    IsClosedGauge (powerGaugeTransform p f) := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: apply Corollary 15.3.1 to write `f` as `x ↦ (1 / p) * k(x)^p` for a closed gauge
-- `k`. Then `powerGaugeTransform p f = k` pointwise, and the conjugate formula from the same
-- corollary rewrites `powerGaugeTransform q f⋆` as the polar gauge `kᵒ`.
/-- Corollary 15.3.2: under the same hypotheses, the polar of `powerGaugeTransform p f` is
`powerGaugeTransform q f⋆`. -/
theorem gauge_polar_powerGaugeTransform_eq_conjugatePowerGaugeTransform
    {p q : ℝ} (hpq : p.HolderConjugate q) {f : E → EReal}
    (hf_closed : f.IsClosedProperConvex)
    (hf_hom : f.PositivelyHomogeneousOfDegree p) :
    (powerGaugeTransform p f)ᵒ = powerGaugeTransform q f⋆ := sorry

-- Proof sketch: apply the generalized Cauchy inequality from Text 15.0.9 to the closed gauge
-- `powerGaugeTransform p f` and its polar. Then use the previous polar identity to rewrite the
-- right-hand side by `powerGaugeTransform q f⋆`.
/-- The corollary's Hölder-type inequality for `f` and its conjugate, stated on the finite-value
domains of `f` and `f*`. -/
theorem inner_le_mul_powerGaugeTransform_convexConjugate_of_mem_dom
    {p q : ℝ} (hpq : p.HolderConjugate q) {f : E → EReal} {x xStar : E}
    (hf_closed : f.IsClosedProperConvex)
    (hf_hom : f.PositivelyHomogeneousOfDegree p)
    (hx : x ∈ dom(f)) (hxStar : xStar ∈ dom(f⋆)) :
    (⟪x, xStar⟫ : EReal) ≤
      powerGaugeTransform p f x * powerGaugeTransform q f⋆ xStar := sorry

-- Proof sketch: let `C = {x | f x ≤ 1 / p}`. Under Corollary 15.3.1, `powerGaugeTransform p f` is
-- exactly the gauge of `C`, and its polar is the gauge of `Set.polar C` by Theorem 15.1. The
-- previous polar identity identifies that polar gauge with the gauge of
-- `{xStar | f⋆ xStar ≤ 1 / q}`, so the two sublevel sets are polar.
/-- The sublevel sets `{x | f x ≤ 1 / p}` and `{x* | f*(x*) ≤ 1 / q}` are polar to each other. -/
theorem polar_powerSublevel_eq_conjugatePowerSublevel
    {p q : ℝ} (hpq : p.HolderConjugate q) {f : E → EReal}
    (hf_closed : f.IsClosedProperConvex)
    (hf_hom : f.PositivelyHomogeneousOfDegree p) :
    {x : E | f x ≤ (1 / p : ℝ)}ᵒ =
      {xStar : E | f⋆ xStar ≤ (1 / q : ℝ)} := sorry

end
