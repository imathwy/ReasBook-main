import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_35_9 (from Chap07) -/
noncomputable section

open Function Set
open scoped Gradient Rockafellar

universe u v w

namespace Bifunction

section

variable {𝕜 : Type w}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [FiniteDimensional 𝕜 (U × V)]
variable {K : U → V → 𝕜} {C : Set U} {D : Set V}

local notation "K∞" => uncurry K₁[K | C, D]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 35.9 concerns differentiability of a finite bifunction on a product
  domain. In this file, the public surface is normalized to the Chapter 25 canonical owner of the
  restricted uncurried function.
- `core/canonical`: the owner is `K₁[K | C, D]` with
  `K∞ := uncurry K₁[K | C, D]`, and the Chapter 25
  declarations
  `Function.dense_differentiabilitySetWithinInteriorDom` and
  `Function.volume_diff_differentiabilitySetWithinInteriorDom_eq_zero`.
- `bridge/view`: this file is the bridge that reuses those owners directly on the restricted
  uncurried bifunction; saddle-shape hypotheses belong to upstream/downstream files that prove
  convex/proper bridges for this owner.

Layer target: `core/canonical` for the density and measure-null clauses.
-/

-- Proof sketch: this is exactly the Chapter 25 density theorem applied to
-- `K∞ = uncurry K₁[K | C, D]`.
/-- Theorem 35.9 (density clause), canonical owner form: if the restricted uncurried bifunction
+∞-extension `K∞` is proper and convex, then its Chapter 25 differentiability locus is dense in
`interior (dom(K∞))`. -/
theorem dense_differentiabilitySetOn
    (hK_proper : K∞.IsProper)
    (hK_convex : K∞.IsConvex 𝕜) :
    Dense (differentiabilitySetWithinInteriorDom K∞) := by
  simpa using
    (Function.dense_differentiabilitySetWithinInteriorDom
      (f := K∞) hK_proper hK_convex)

-- Proof sketch: this is exactly the Chapter 25 measure-null theorem applied to
-- `K∞ = uncurry K₁[K | C, D]`.
/-- Theorem 35.9 (measure clause), canonical owner form: for any additive Haar measure on `U × V`,
if `K∞` is proper and convex, then the complement of the Chapter 25 differentiability locus in
`interior (dom(K∞))` has measure zero. -/
theorem volume_diff_differentiabilitySetOn_eq_zero
    [MeasurableSpace (U × V)] [BorelSpace (U × V)]
    (μ : MeasureTheory.Measure (U × V)) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (hK_proper : K∞.IsProper)
    (hK_convex : K∞.IsConvex 𝕜) :
    μ
        ((interior (dom(K∞))) \ differentiabilitySetWithinInteriorDomAmbient K∞) =
      0 := by
  simpa using
    (Function.volume_diff_differentiabilitySetWithinInteriorDom_eq_zero
      (μ := μ) (f := K∞) hK_proper hK_convex)

end

section

variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ (U × V)]
variable {K : U → V → ℝ} {C : Set U} {D : Set V}

local notation "K∞" => uncurry K₁[K | C, D]

/-- The product-valued gradient of a real-valued bifunction, obtained by taking the Euclidean
gradient of its uncurried form on the canonical `L²` product carrier and then returning to raw
product coordinates. -/
abbrev gradient (K : U → V → ℝ) : U × V → U × V :=
  fun p ↦
    (∇ (fun q : WithLp 2 (U × V) ↦ uncurry K q.ofLp) (WithLp.toLp 2 p)).ofLp

-- Proof sketch: on `interior (dom(K∞))`, the finite real branch
-- of the restricted owner agrees locally with `uncurry K`; transport the Chapter 25 real-branch
-- gradient continuity statement through the canonical `WithLp` product-coordinate identification.
/-- Theorem 35.9 (gradient clause): if the restricted uncurried bifunction
`K∞ = uncurry K₁[K | C, D]` is proper and convex, then the product-coordinate
gradient view `gradient K`
is continuous on its Chapter 25 differentiability locus. -/
theorem continuous_gradientOn_differentiabilitySetOn
    (hK_proper : K∞.IsProper)
    (hK_convex : K∞.IsConvex ℝ) :
    Continuous
      (fun p : differentiabilitySetWithinInteriorDom K∞ ↦ gradient K p) := by
  sorry

end

end Bifunction
