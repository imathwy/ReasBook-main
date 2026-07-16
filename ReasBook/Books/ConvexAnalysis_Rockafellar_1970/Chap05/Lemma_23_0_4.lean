import Mathlib.Analysis.Calculus.Gradient.Basic
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open Filter

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 23.0.4 says that differentiability at `x` forces the directional
  derivative in every direction to be finite and bilateral. In real inner-product spaces this
  value is the gradient pairing.
- `core/canonical`: the ambient owner abstractions already exist upstream: mathlib's
  `HasFDerivAt`, together with the Chapter 23 owners
  `Function.directionalDifferenceQuotientAt`, `Function.HasDirectionalDerivativeAt`,
  `Function.HasBilateralDirectionalDerivativeAt`, and `Function.directionalDerivativeAt`.
- `bridge/view`: this file is only the bridge from the scalar-valued differentiability owner to
  the chapter directional-derivative owner on `WithTopBot 𝕜` via the codomain lift
  `Function.toWithTopBot`; it should not introduce a second directional-derivative package.
  The gradient-facing statements are downstream real inner-product specializations of this
  Fréchet-derivative bridge.

Domain-style sampling used here:
- mathlib's derivative owners `HasFDerivAt`, `HasLineDerivAt`, and
  `HasLineDerivAt.tendsto_slope_zero_right`;
- the gradient specialization bridge `HasGradientAt.hasFDerivAt` and
  `InnerProductSpace.toDual_apply`;
- the project Chapter 23 owners `Function.directionalDifferenceQuotientAt`,
  `Function.HasDirectionalDerivativeAt`, `Function.HasBilateralDirectionalDerivativeAt`, and
  `Function.directionalDerivativeAt` from
  `ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1`.

Primitive data vs derived API:
- primitive owner-side input: `HasFDerivAt f f' x`;
- primitive owner-side output:
  `HasDirectionalDerivativeAt f.toWithTopBot x y ((f' y : 𝕜) : WithTopBot 𝕜)`;
- derived owner-side companions: the bilateral owner view
  `HasBilateralDirectionalDerivativeAt f.toWithTopBot x y ((f' y : 𝕜) : WithTopBot 𝕜)` and the
  value formula for `directionalDerivativeAt`;
- derived source-facing input: `HasGradientAt f g x` and then `DifferentiableAt ℝ f x`, which
  canonically recover the source gradient pairing `⟪g, y⟫ = (f' y)`.

Layer target: `bridge/view`. The source statement adds no new owner object; it identifies the
existing directional-derivative owner with the canonical gradient pairing under a stronger smooth
hypothesis. The owner theorem here should therefore land first on
`HasDirectionalDerivativeAt` at the primitive Fréchet-derivative layer, with gradient and
bilateral source forms exposed only as companion views.

Ambient-assumption minimization:
- the Chapter 23 directional-difference owner only uses the additive/module structure already
  provided in `Lemma_23_0_1`;
- the Fréchet-derivative bridge needs only `[SeminormedAddCommGroup E] [NormedSpace 𝕜 E]`;
- the inner-pairing bridge (`⟪g, y⟫`) needs only `[InnerProductSpace ℝ E]`;
- the `HasGradientAt` source view needs only the inner-product structure, while the
  `DifferentiableAt`/`∇` source view remains in the complete real inner-product specialization.
-/

namespace Function

/-- Owner-side primitive bridge for Lemma 23.0.4: if `f` has Fréchet derivative `f'` at `x`, then
the Chapter 23 right directional-derivative owner for `f.toWithTopBot` in direction `y` exists and
is the finite value `f' y`. -/
theorem hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt
    {f : E → 𝕜} {x y : E} {f' : E →L[𝕜] 𝕜} (hf : HasFDerivAt f f' x) :
    HasDirectionalDerivativeAt f.toWithTopBot x y (f' y : WithTopBot 𝕜) := by
  sorry

section

variable [OrderTopology 𝕜] [OrderTopology (WithTopBot 𝕜)]

/-- Bilateral owner companion at the primitive derivative layer: Fréchet differentiability gives
the punctured-neighborhood directional-derivative owner with value `f' y`. -/
theorem hasBilateralDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt
    {f : E → 𝕜} {x y : E} {f' : E →L[𝕜] 𝕜} (hf : HasFDerivAt f f' x) :
    HasBilateralDirectionalDerivativeAt f.toWithTopBot x y (f' y : WithTopBot 𝕜) := by
  refine hasBilateralDirectionalDerivativeAt_iff_hasDirectionalDerivativeAt_and_neg.2 ?_
  refine ⟨?_, ?_⟩
  · exact hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt hf
  · have hneg :
        HasDirectionalDerivativeAt f.toWithTopBot x (-y) (f' (-y) : WithTopBot 𝕜) :=
      hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt hf
    simpa [map_neg] using hneg

end

section

variable [T2Space (WithTopBot 𝕜)]

/-- Owner-side value form at the primitive derivative layer: Fréchet derivative evaluation gives
the Chapter 23 directional-derivative owner value on `f.toWithTopBot`. -/
theorem directionalDerivativeAt_toWithTopBot_eq_fderiv_apply_of_hasFDerivAt
    {f : E → 𝕜} {x y : E} {f' : E →L[𝕜] 𝕜} (hf : HasFDerivAt f f' x) :
    directionalDerivativeAt f.toWithTopBot x y = (f' y : WithTopBot 𝕜) := by
  simpa [HasDirectionalDerivativeAt, directionalDerivativeAt] using
    (hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt hf).limUnder_eq

end

end Function

end

section

open Filter
open scoped RealInnerProductSpace

variable {E : Type u} [InnerProductSpace ℝ E]

namespace Function

/-- Pairing-level bridge at the primitive derivative layer: if the Fréchet derivative at `x`
evaluates as `⟪g, ·⟫`, then the Chapter 23 right directional derivative of `f.toWithTopBot` in
direction `y` exists with value `⟪g, y⟫`. -/
theorem hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt_inner
    {f : E → ℝ} {x y g : E} {f' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x)
    (hinner : ∀ z : E, f' z = ⟪g, z⟫) :
    HasDirectionalDerivativeAt f.toWithTopBot x y (⟪g, y⟫ : WithTopBot ℝ) := by
  have hFDeriv :
      HasDirectionalDerivativeAt f.toWithTopBot x y (f' y : WithTopBot ℝ) :=
    hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt hf
  simpa [hinner y] using hFDeriv

/-- Pairing-level bilateral companion at the primitive derivative layer: if the Fréchet
derivative at `x` evaluates as `⟪g, ·⟫`, then the punctured-neighborhood directional-derivative
owner exists with value `⟪g, y⟫`. -/
theorem hasBilateralDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt_inner
    {f : E → ℝ} {x y g : E} {f' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x)
    (hinner : ∀ z : E, f' z = ⟪g, z⟫) :
    HasBilateralDirectionalDerivativeAt f.toWithTopBot x y (⟪g, y⟫ : WithTopBot ℝ) := by
  have hFDeriv :
      HasBilateralDirectionalDerivativeAt f.toWithTopBot x y (f' y : WithTopBot ℝ) :=
    hasBilateralDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt hf
  simpa [hinner y] using hFDeriv

/-- Pairing-level bilateral-limit view: if the Fréchet derivative at `x` evaluates as `⟪g, ·⟫`,
then the directional difference quotient of `f.toWithTopBot` converges on the punctured
neighborhood of `0` to `⟪g, y⟫`. -/
theorem tendsto_directionalDifferenceQuotientAt_toWithTopBot_bilateral_of_hasFDerivAt_inner
    {f : E → ℝ} {x y g : E} {f' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x)
    (hinner : ∀ z : E, f' z = ⟪g, z⟫) :
    Tendsto (directionalDifferenceQuotientAt f.toWithTopBot x y)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (⟪g, y⟫ : WithTopBot ℝ)) := by
  simpa [HasBilateralDirectionalDerivativeAt] using
    hasBilateralDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt_inner hf hinner

/-- Pairing-level value form at the primitive derivative layer: if the Fréchet derivative at `x`
evaluates as `⟪g, ·⟫`, then `directionalDerivativeAt f.toWithTopBot x y = ⟪g, y⟫`. -/
theorem directionalDerivativeAt_toWithTopBot_eq_inner_of_hasFDerivAt_inner
    {f : E → ℝ} {x y g : E} {f' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x)
    (hinner : ∀ z : E, f' z = ⟪g, z⟫) :
    directionalDerivativeAt f.toWithTopBot x y = (⟪g, y⟫ : WithTopBot ℝ) := by
  have hFDeriv :
      directionalDerivativeAt f.toWithTopBot x y = (f' y : WithTopBot ℝ) :=
    directionalDerivativeAt_toWithTopBot_eq_fderiv_apply_of_hasFDerivAt hf
  simpa [hinner y] using hFDeriv

end Function

end

section

open Filter
open scoped Gradient RealInnerProductSpace

variable {E : Type u} [InnerProductSpace ℝ E]

namespace Function

/-- Owner-side gradient specialization for Lemma 23.0.4: if `f` has gradient `g` at `x`, then the
Chapter 23 right directional derivative of `f.toWithTopBot` in direction `y` is `⟪g, y⟫`. -/
theorem hasDirectionalDerivativeAt_toWithTopBot_of_hasGradientAt
    {f : E → ℝ} {x y g : E} (hf : HasGradientAt f g x) :
    HasDirectionalDerivativeAt f.toWithTopBot x y (⟪g, y⟫ : WithTopBot ℝ) := by
  exact
    hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt_inner hf.hasFDerivAt
      (fun z ↦ by
        simpa using (InnerProductSpace.toDual_apply_apply (x := g) (y := z)))

/-- Bilateral owner specialization for a prescribed gradient: the punctured-neighborhood owner
form follows from the primitive derivative-layer bridge. -/
theorem hasBilateralDirectionalDerivativeAt_toWithTopBot_of_hasGradientAt
    {f : E → ℝ} {x y g : E} (hf : HasGradientAt f g x) :
    HasBilateralDirectionalDerivativeAt f.toWithTopBot x y (⟪g, y⟫ : WithTopBot ℝ) := by
  exact
    hasBilateralDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt_inner hf.hasFDerivAt
      (fun z ↦ by
        simpa using (InnerProductSpace.toDual_apply_apply (x := g) (y := z)))

/-- Lemma 23.0.4, bilateral companion for a prescribed gradient: the source's bilateral-limit
wording is the punctured-neighborhood view of the Chapter 23 directional-derivative owner, so it
is derived from the owner theorem together with the left/right symmetry from Lemma 23.0.3. -/
theorem tendsto_directionalDifferenceQuotientAt_toWithTopBot_bilateral_of_hasGradientAt
    {f : E → ℝ} {x y g : E} (hf : HasGradientAt f g x) :
    Tendsto (directionalDifferenceQuotientAt f.toWithTopBot x y)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (⟪g, y⟫ : WithTopBot ℝ)) := by
  exact
    tendsto_directionalDifferenceQuotientAt_toWithTopBot_bilateral_of_hasFDerivAt_inner
      hf.hasFDerivAt
      (fun z ↦ by
        simpa using (InnerProductSpace.toDual_apply_apply (x := g) (y := z)))

/-- Owner-side value form for Lemma 23.0.4: a prescribed gradient `g` at `x` evaluates the
Chapter 23 directional-derivative owner on `f.toWithTopBot`. -/
theorem directionalDerivativeAt_toWithTopBot_eq_inner_of_hasGradientAt
    {f : E → ℝ} {x y g : E} (hf : HasGradientAt f g x) :
    directionalDerivativeAt f.toWithTopBot x y = (⟪g, y⟫ : WithTopBot ℝ) := by
  exact
    directionalDerivativeAt_toWithTopBot_eq_inner_of_hasFDerivAt_inner hf.hasFDerivAt
      (fun z ↦ by
        simpa using (InnerProductSpace.toDual_apply_apply (x := g) (y := z)))

section

variable [CompleteSpace E]

/-- Lemma 23.0.4, bilateral-limit form: if `f` is differentiable at `x`, then the directional
difference quotient of `f.toWithTopBot` has a finite bilateral limit, namely the gradient pairing
with the direction `y`. -/
theorem tendsto_directionalDifferenceQuotientAt_toWithTopBot_bilateral_of_differentiableAt
    {f : E → ℝ} {x y : E} (hf : DifferentiableAt ℝ f x) :
    Tendsto (directionalDifferenceQuotientAt f.toWithTopBot x y)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (⟪∇ f x, y⟫ : WithTopBot ℝ)) := by
  simpa using
    tendsto_directionalDifferenceQuotientAt_toWithTopBot_bilateral_of_hasGradientAt hf.hasGradientAt

/-- Lemma 23.0.4, owner form: if `f` is differentiable at `x`, then the Chapter 23 directional
derivative of `f.toWithTopBot` in the direction `y` is the finite value `⟪∇ f x, y⟫`. -/
theorem directionalDerivativeAt_toWithTopBot_eq_inner_gradient
    {f : E → ℝ} {x y : E} (hf : DifferentiableAt ℝ f x) :
    directionalDerivativeAt f.toWithTopBot x y = (⟪∇ f x, y⟫ : WithTopBot ℝ) := by
  simpa using
    directionalDerivativeAt_toWithTopBot_eq_inner_of_hasGradientAt hf.hasGradientAt

end

end Function

end
