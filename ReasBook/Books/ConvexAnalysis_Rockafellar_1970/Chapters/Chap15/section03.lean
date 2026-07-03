import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_15_3_1 (from Chap03) -/
noncomputable section

open scoped GaugePolar ProfileConjugate RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance powerProfileInstSMulRealEReal : SMul ℝ EReal := WithBotTop.instSMul
/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 15.3.1 specializes Theorem 15.3 to the scalar profile
  `ζ ↦ (1 / p) * ζ^p`, characterizing degree-`p` positively homogeneous closed proper convex
  functions as powers of closed gauges and then computing the conjugate by the dual exponent.
- `core/canonical`: the owner abstractions already present in the project are
  `isGaugeLike_and_isClosedProperConvex_iff_exists_closedGauge_profile`,
  `convexConjugate_eq_rayProfileConjugate_comp_gauge_polar_of_eq_comp_closedGauge_profile`,
  `rayProfileConjugate`,
  `rayProfileExtension`,
  `Function.PositivelyHomogeneousOfDegree`, `Function.IsClosedProperConvex`, `IsClosedGauge`,
  `convexConjugate`, and `gauge_polar`.
- `bridge/view`: the only new ingredient needed here is the concrete scalar profile
  `powerProfile p`, which packages the source formula `(1 / p) * ζ^p` on the canonical
  nonnegative ray. The only `EReal`-valued surface used here is the bridge
  `rayProfileExtension`, while the dual profile remains the owner-level ray conjugate `g⁺`.

Domain-style sampling used here:
- `Function.PositivelyHomogeneousOfDegree`;
- `Function.IsClosedProperConvex`;
- `gauge_polar`;
- the owner ray conjugate `rayProfileConjugate`, written in this file as `g⁺`.

Primitive data vs derived API:
- primitive inputs: the exponent `p`, its Hölder-conjugate `q`, and the function `f`;
- primitive ray-side profile: `powerProfile p`;
- bridge data: the `EReal`-valued view `rayProfileExtension (powerProfile p)`;
- derived API: the gauge representation of `f`, the explicit formula for `f*`, and the
  degree-`q` positive homogeneity of `f*`.

Layer target: `source-facing` for the main corollary, with `powerProfile` as the source-facing
ray profile and `rayProfileExtension` as the minimal bridge needed to state the textbook gauge
compositions. The ambient owner layer is the same finite-dimensional real inner-product-space
level as Theorem 15.3; the textbook `R^n` formulation is a specialization rather than the public
core.
-/

/-- The scalar profile `ζ ↦ (1 / p) * ζ^p` on the canonical nonnegative ray. -/
def powerProfile (p : ℝ) : NNReal → EReal :=
  fun t ↦ (((1 / p) * Real.rpow t.1 p : ℝ) : EReal)

variable {p q : ℝ} {f k : E → EReal}

-- Proof sketch: verify directly that the concrete power profile satisfies the scalar-profile
-- hypotheses from Theorem 15.3. On the nonnegative ray it is the closed convex monotone real
-- function `t ↦ (1 / p) * t^p`; the finiteness and nonconstancy clauses are immediate from the
-- explicit formula and the assumption `1 < p`.
private theorem powerProfile_isMonotoneClosedConvexOnNonnegativeRay (hp : 1 < p) :
    (powerProfile p).IsMonotoneClosedConvexOnNonnegativeRay := sorry

private theorem powerProfile_finite_pos (hp : 1 < p) :
    ∃ ζ : NNReal, 0 < ζ.1 ∧ powerProfile p ζ < ⊤ := sorry

private theorem powerProfile_nonconstant (hp : 1 < p) :
    ∃ s t : NNReal, powerProfile p s ≠ powerProfile p t := sorry

-- Proof sketch: compute the one-dimensional profile conjugate `(powerProfile p)⁺` using the
-- orthant/ray conjugate owner from Chapter 12 and the Hölder-conjugacy relation. The result is
-- the dual power profile `ζStar ↦ (1 / q) * ζStar^q`, i.e. `powerProfile q`.
/-- The ray-profile conjugate of the degree-`p` power profile is the dual degree-`q`
power profile when `p` and `q` are Hölder-conjugate exponents. -/
theorem powerProfile_conjugate_eq (hpq : p.HolderConjugate q) :
    (powerProfile p)⁺ = powerProfile q := sorry

-- Proof sketch: specialize
-- `isGaugeLike_and_isClosedProperConvex_iff_exists_closedGauge_profile` to the
-- concrete profile `powerProfile p`, using the ray-side Chapter 12 owner together with the
-- finiteness/nonconstancy clauses recorded above. This turns the owner
-- closed-gauge/profile decomposition into the source-facing power-profile representation, while
-- the converse direction recovers degree-`p` homogeneity from the degree-`1` homogeneity of the
-- closed gauge.
/-- Corollary 15.3.1 (1): for `1 < p`, a closed proper convex function is positively homogeneous
of degree `p` if and only if it is of the form
`f = rayProfileExtension (powerProfile p) ∘ k` for some closed gauge `k`; equivalently,
`f(x) = (1 / p) * k(x)^p` on the nonnegative gauge values. -/
theorem positivelyHomogeneousOfDegree_iff_eq_powerProfile_comp_closedGauge
    (hp : 1 < p) (hf_closed : f.IsClosedProperConvex) :
    f.PositivelyHomogeneousOfDegree p ↔
      ∃ k : E → EReal, IsClosedGauge k ∧
        f = rayProfileExtension (powerProfile p) ∘ k := sorry

-- Proof sketch: this is the degree-`q` homogeneous consequence of the explicit conjugate formula
-- below. Once Theorem 15.3 gives
-- `f⋆ = rayProfileExtension ((powerProfile p)⁺) ∘ kᵒ`, rewrite the profile conjugate by
-- `powerProfile_conjugate_eq hpq`; the degree-`1` homogeneity of `kᵒ` then
-- upgrades through the dual power profile to degree `q`.
/-- Corollary 15.3.1 (2): under the representation
`f = rayProfileExtension (powerProfile p) ∘ k`, the Fenchel
conjugate `f⋆` is positively homogeneous of degree `q`, where `q` is the Hölder-conjugate
exponent to `p`. -/
theorem positivelyHomogeneousOfDegree_convexConjugate_of_eq_powerProfile_comp_closedGauge
    (hpq : p.HolderConjugate q) (hk : IsClosedGauge k)
    (hf : f = rayProfileExtension (powerProfile p) ∘ k) :
    (f⋆ : E → EReal).PositivelyHomogeneousOfDegree q := sorry

-- Proof sketch: apply
-- `convexConjugate_eq_rayProfileConjugate_comp_gauge_polar_of_eq_comp_closedGauge_profile` to the
-- profile `powerProfile p`, then rewrite `(powerProfile p)⁺` by `powerProfile_conjugate_eq hpq`.
/-- Corollary 15.3.1 (3): for the power-profile representation
`f = rayProfileExtension (powerProfile p) ∘ k`, the Fenchel conjugate is the dual power profile
composed with the polar gauge:
`f⋆ = rayProfileExtension (powerProfile q) ∘ kᵒ`. -/
theorem convexConjugate_eq_powerProfile_comp_gauge_polar_of_eq_powerProfile_comp_closedGauge
    (hpq : p.HolderConjugate q) (hk : IsClosedGauge k)
    (hf : f = rayProfileExtension (powerProfile p) ∘ k) :
    f⋆ = rayProfileExtension (powerProfile q) ∘ kᵒ := sorry

end

/-! ### Corollary_15_3_2 (from Chap03) -/
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

/-! ### Theorem_15_3 (from Chap03) -/
noncomputable section

open scoped GaugePolar Rockafellar

/-- The one-dimensional conjugate of a profile on the canonical nonnegative ray, using the
intrinsic nonnegative-ray type `NNReal`. -/
def rayProfileConjugate (g : NNReal → EReal) : NNReal → EReal :=
  g⋆

/-- View a canonical nonnegative-ray profile as an `EReal`-valued function by reading finite
nonnegative inputs on the ray and sending `⊤` or negative inputs to `⊤`. This is only the bridge
needed to compose a ray profile with a gauge-like `EReal`-valued owner. -/
def rayProfileExtension (g : NNReal → EReal) : EReal → EReal :=
  fun s ↦
    if hs_top : s = ⊤ then
      ⊤
    else if hs_nonneg : 0 ≤ s then
      g ⟨s.toReal, by simpa using EReal.toReal_nonneg hs_nonneg⟩
    else
      ⊤

@[simp] theorem rayProfileExtension_apply_top (g : NNReal → EReal) :
    rayProfileExtension g ⊤ = ⊤ := by
  simp [rayProfileExtension]

@[simp] theorem rayProfileExtension_apply_coe_of_nonneg
    (g : NNReal → EReal) {t : ℝ} (ht : 0 ≤ t) :
    rayProfileExtension g (t : EReal) = g ⟨t, ht⟩ := by
  simp [rayProfileExtension, ht]

namespace ProfileConjugate

/- In `open scoped ProfileConjugate`, write the textbook ray-profile conjugate as `g⁺`. -/
scoped macro:max g:term:max noWs "⁺" : term => `(rayProfileConjugate $g)

end ProfileConjugate

open scoped ProfileConjugate

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 15.3 characterizes gauge-like closed proper convex functions on a
  finite-dimensional real inner-product space as composites `f = g ∘ k` of a closed gauge `k`
  with a one-variable nondecreasing closed convex profile `g`, and then identifies the Fenchel
  conjugate `f⋆` by the textbook `g⁺` profile composed with the polar gauge `kᵒ`.
- `core/canonical`: the existing chapter owners already present in the project are
  `Function.IsGaugeLike`, `Function.IsClosedProperConvex`,
  `Function.IsMonotoneClosedConvexOnNonnegativeRay`, `convexConjugate`, `IsGauge`, `IsClosedGauge`,
  `gauge_polar`, and `f⋆`.
- `bridge/view`: the intrinsic scalar profile is the existing ray-side owner
  `g.IsMonotoneClosedConvexOnNonnegativeRay`. The only `EReal`-valued surface retained here is
  the thin bridge `rayProfileExtension g`, used to compose the ray profile with a closed gauge `k`
  and to evaluate the ray-side conjugate `g⁺` on the nonnegative polar gauge `kᵒ`; the extension
  is not promoted to the main owner.

Domain-style sampling used here:
- `Function.IsGaugeLike` from `Text_15_0_20`;
- `Function.IsMonotoneClosedConvexOnNonnegativeRay` from `Text_12_3_5`;
- `convexConjugate` on the intrinsic ray owner `NNReal` from `Defn_12_2`;
- `Function.IsClosedProperConvex` from `Text_12_3_6`;
- `IsGauge` and `gauge_polar` from `Text_15_0_1` and `Text_15_0_5`;
- `IsClosedGauge` from `Text_15_0_24`;
- `convexConjugate` from `Theorem_20_0_1`, reused here through `Text_12_3_6`.

Primitive data vs derived API:
- primitive owner data: the function `f : E → EReal`;
- primitive ray-side owner data: a scalar profile `g : NNReal → EReal`;
- bridge data: a closed gauge `k : E → EReal` and the thin extension `rayProfileExtension g`;
- derived outputs: the representation criterion, the gauge-like property of `f⋆`, and the explicit
  formula for `f⋆`.

Layer target:
- the main theorem is `source-facing`, stated directly as a characterization of `f`;
- the profile-side assumptions are expressed directly through the canonical nonnegative-ray owner,
  and the theorem surface uses the textbook notation `g⁺` for the ray-side conjugate while keeping
  the `EReal`-valued extension as a secondary bridge only;
- the ambient owner level is the intrinsic finite-dimensional real inner-product-space layer
  already used by the chapter's gauge, polar, and Fenchel-conjugate owners, not the concrete
  `EuclideanSpace ℝ (Fin n)` display model.
 -/

-- Proof sketch: for `→`, unpack the gauge-like and closed-proper-convex hypotheses on `f`. Use
-- the proportionality of positive finite sublevel sets to identify a canonical closed gauge `k`
-- from the unit sublevel set and define the scalar profile by the minimal dilation parameter.
-- For `←`, compose a closed gauge `k` with a scalar profile `g`; the monotonicity and convexity of
-- `g` transfer the gauge structure of `k` to `f`, while the closedness and finiteness hypotheses
-- on `g` yield properness and lower semicontinuity.
/-- Theorem 15.3: a function on a finite-dimensional real inner-product space is gauge-like and
closed proper convex exactly when it admits a decomposition `f(x) = g(k(x))` with `k` a closed
gauge and `g` a nonconstant nondecreasing lower semicontinuous convex scalar profile on the
nonnegative ray, viewed on gauge values through the thin bridge `rayProfileExtension`. -/
theorem isGaugeLike_and_isClosedProperConvex_iff_exists_closedGauge_profile
    (f : E → EReal) :
    IsGaugeLike[ℝ] f ∧ f.IsClosedProperConvex ↔
      ∃ k : E → EReal,
        IsClosedGauge k ∧
          ∃ g : NNReal → EReal,
            g.IsMonotoneClosedConvexOnNonnegativeRay ∧
            (∃ ζ : NNReal, 0 < ζ.1 ∧ g ζ < ⊤) ∧
            (∃ s t : NNReal, g s ≠ g t) ∧
            f = rayProfileExtension g ∘ k := sorry

-- Proof sketch: write `f` as `rayProfileExtension g ∘ k` with `k` a closed gauge and `g` a
-- gauge-like scalar profile on the canonical nonnegative ray.
-- Theorem 15.1 identifies `gauge_polar k` as a closed gauge, and the one-dimensional Chapter 12
-- conjugacy theorem identifies `g⁺` as the matching dual scalar profile.
-- Applying the main characterization to the explicit formula for `f⋆` yields the
-- gauge-like property of `f⋆`.
/-- If `f(x) = g(k(x))` with `k` a closed gauge and `g` an admissible scalar profile, then the
Fenchel conjugate `f⋆` is gauge-like. -/
theorem isGaugeLike_convexConjugate_of_eq_comp_closedGauge_profile
    {f k : E → EReal} {g : NNReal → EReal}
    (hk : IsClosedGauge k)
    (hg_ray : g.IsMonotoneClosedConvexOnNonnegativeRay)
    (hg_finite_pos : ∃ ζ : NNReal, 0 < ζ.1 ∧ g ζ < ⊤)
    (hg_nonconstant : ∃ s t : NNReal, g s ≠ g t)
    (hf : f = rayProfileExtension g ∘ k) :
    IsGaugeLike[ℝ] (f⋆ : E → EReal) := sorry

-- Proof sketch: start from the Fenchel supremum defining `f⋆`. Substitute the
-- representation `f = rayProfileExtension g ∘ k`, separate the radial gauge part from the scalar
-- profile, and rewrite the admissible majorants using the polar-gauge formula from Theorem 15.1.
-- The remaining one-dimensional supremum is exactly the canonical profile conjugate `g⁺`.
-- Unlike the representation theorem above, this bridge identity keeps only the owner predicates
-- used by the ray-conjugacy and polar-gauge APIs themselves.
/-- If `f(x) = g(k(x))` with `k` a closed gauge and `g` a monotone closed convex scalar profile on
the nonnegative ray, then `f⋆(x⋆) = g⁺(kᵒ(x⋆))`, where `g⁺` is the one-dimensional monotone
conjugate coming from the canonical ray/orthant owner stack, viewed on `EReal` gauge values
through `rayProfileExtension`. -/
theorem convexConjugate_eq_rayProfileConjugate_comp_gauge_polar_of_eq_comp_closedGauge_profile
    {f k : E → EReal} {g : NNReal → EReal}
    (hk : IsClosedGauge k)
    (hg_ray : g.IsMonotoneClosedConvexOnNonnegativeRay)
    (hf : f = rayProfileExtension g ∘ k) :
    f⋆ = rayProfileExtension (g⁺) ∘ kᵒ := sorry

end
