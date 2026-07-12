import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_15_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_21

-- Declarations for this item will be appended below by the statement pipeline.

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
