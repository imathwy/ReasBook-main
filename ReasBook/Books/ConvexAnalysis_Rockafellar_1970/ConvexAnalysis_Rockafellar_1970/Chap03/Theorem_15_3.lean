import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.ERealSMul
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_20
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_24

-- Declarations for this item will be appended below by the statement pipeline.

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
