import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2

noncomputable section

universe u v w z

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Lemma33.0.22 studies the partial conjugate in the second variable attached to
  a convex bifunction `F`.
- `core/canonical`: the chapter already owns that object as `Bifunction.lowerPairing XStar F`,
  together with the saddle-shape owner `SaddleFunction.IsConcaveConvex`, the Chapter 34
  closed-convex owner `Bifunction.IsClosedConvex`, and the first-variable closedness owner
  `Bifunction.IsConcaveClosed`.
- `bridge/view`: this item should therefore be stated through the canonical owner
  `lowerPairing XStar F`, split into the source's two atomic clauses.

Domain-style sampling used here:
- `lowerPairing` from `Defn_34_2`;
- `convexConjugate` / `(·)⋆` and `Function.isConvex_convexConjugate` from Chapter 12;
- `SaddleFunction.IsConcaveConvex` from Definition33.0.1;
- `Bifunction.IsClosedConvex` from `Defn_34_2`;
- `Bifunction.IsConcaveClosed` from Definition33.0.4;
- `Function.partialInfimum` / `Function.linearImage` from Chapter 1;
- `Function.linearImageEpigraph_eq_epi_linearImage_of_sections_closed` from
  `Chap02/Proposition_9_0_0_3`;
- the graph-function owner `(Function.uncurry F).IsConvex 𝕜`.

Layer target: `bridge/view`.
-/

section Shape

variable {𝕜 : Type z} {U : Type u} {X : Type v} {XStar : Type w}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid XStar] [Module 𝕜 XStar]
variable [HasLinearPairing X XStar 𝕜]

-- Proof sketch: for each fixed `xStar`, the map `u ↦ (F u)⋆ xStar` is a supremum of the affine
-- perturbations `u ↦ ⟪x, xStar⟫ - F u x`, hence is concave because `Function.uncurry F` is
-- convex in `(u, x)`. For each fixed `u`, the slice `xStar ↦ (F u)⋆ xStar` is convex by the
-- canonical convexity theorem for Fenchel conjugates.
/-- Lemma33.0.22 (1): the lower representative `(u, x⋆) ↦ (F u)⋆ x⋆` of a jointly convex
graph function is concave in `u` and convex in `x⋆`. -/
theorem lowerPairing_isConcaveConvex_of_uncurry_isConvex
    (F : U → X → WithTopBot 𝕜)
    (hF : (Function.uncurry F).IsConvex 𝕜) :
    SaddleFunction.IsConcaveConvex 𝕜 (lowerPairing XStar F) := sorry

end Shape

section Closedness

variable {𝕜 : Type z} {U : Type u} {X : Type v} {XStar : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable [Semiring 𝕜] [Sub (WithTopBot 𝕜)]
variable [TopologicalSpace U] [AddCommMonoid U] [SMul 𝕜 U]
variable [TopologicalSpace X] [AddCommMonoid X] [SMul 𝕜 X]
variable [HasPairing X XStar 𝕜]

-- Proof sketch: fix `xStar` and consider the perturbation
-- `g_xStar (u, x) = F u x - ⟪x, xStar⟫`. The owner hypothesis `IsClosedConvex F` gives closed
-- convexity of the graph function, while lower semicontinuity of the pairing slices
-- `x ↦ ((⟪x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)` supplies the section-closedness input needed by the
-- Chapter 2 linear-image/epigraph machinery. This yields upper semicontinuity of
-- `u ↦ (F u)⋆ xStar`, exactly `Bifunction.IsConcaveClosed` for the lower representative.
/-- Lemma33.0.22 (2): if the graph function of `F` is closed convex and the pairing slices
`x ↦ ((⟪x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)` are lower semicontinuous, then every `u`-slice of the
lower representative is closed concave, i.e. the lower representative is concave-closed in its
first variable. -/
theorem lowerPairing_isConcaveClosed_of_isClosedConvex
    (F : U → X → WithTopBot 𝕜) (hF : IsClosedConvex F)
    (hpair : ∀ xStar : XStar,
      LowerSemicontinuous (fun x : X ↦ ((⟪x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜))) :
    IsConcaveClosed (lowerPairing XStar F) := sorry

end Closedness

end Bifunction
