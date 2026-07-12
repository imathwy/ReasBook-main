import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_4_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_3_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_0_4
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_1

noncomputable section

universe u v u' v' w

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 38.4 introduces the image `Ff` of a convex function `f` under a convex
  bifunction `F`, given by the infimum formula `x ↦ inf_u (f u + F u x)`.
- `core/canonical`: the existing chapter owners are `Bifunction.image` from
  `Definition_38_0_4`, `Bifunction.dom` from `Definition_6_29_8` / `Theorem_38_1`, and the
  Chapter 1 linear-image
  owner `Function.linearImage`.
- `bridge/view`: proof-level bridges pass through the Chapter 1 linear-image owner and through the
  adjoint-side owners `adjoint` and the image-side operational view `Function.swap (F⋆)`,
  but the public theorem surface should stay on `Bifunction.image` and `Bifunction.dom`.

Primary mathematical domain:
- convex bifunctions, infimal images, Fenchel conjugates, and relative-interior qualification.

Domain-style sampling used here:
- `Bifunction.image` and `Bifunction.image_apply` from `Chap08.Definition_38_0_4`;
- `Bifunction.dom` from `Chap06.Definition_6_29_8`, reused in `Chap08.Theorem_38_1`;
- `Bifunction.image_eq_linearImage_fst` from `Chap08.Definition_38_3_1`;
- `Function.isConvex_linearImage` from `Chap01.Theorem_5_7`;
- `adjoint` from `Chap06.Definition_6_30_14`;
- `inverse` from `Chap07.Definition_36_4_1`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop 𝕜` and a function
  `f : U → WithBotTop 𝕜`;
- primitive source-facing owners already present upstream: `image F f`, `dom F`, the adjoint
  notation `F⋆ : XStar → UStar → WithBotTop ℝ`, and its canonical image-side operational view
  `Function.swap (F⋆)`;
- derived API here: convexity of `image F f`, the conjugacy identity for
  `convexConjugate (image F f)`, and the attainment statement for the adjoint-side infimum over
  `Function.swap (F⋆)`.

Layer target: `source-facing`, stated directly through the established chapter owners rather than
through a parallel wrapper for “image data” or “dual attainment data”.
-/

section Convexity

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

-- Proof sketch: pass from the source-facing owner `image F f` to the Chapter 1 owner
-- `Function.partialInfimum` via `image_eq_linearImage_fst`, then apply the intrinsic
-- partial-infimum convexity theorem to the convex graph kernel `(x, u) ↦ f u + F u x`.
/-- Theorem 38.4 (1): if `F` is a convex bifunction and `f` is convex, then the image `image F f`
is convex. -/
theorem isConvex_image
    (F : U → X → WithBotTop 𝕜) (f : U → WithBotTop 𝕜)
    (hF_convex : Function.IsConvex 𝕜 (Function.uncurry F))
    (hf_convex : Function.IsConvex 𝕜 f) :
    (image F f).IsConvex 𝕜 := sorry

end Convexity

section Conjugacy

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [Neg UStar]
variable [HasPairing U UStar ℝ] [HasPairing X XStar ℝ]
variable (F : U → X → WithBotTop ℝ) (f : U → WithBotTop ℝ)

local notation "ri(" C ")" => intrinsicInterior ℝ C
local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithBotTop ℝ)
local notation "f⋆" => (convexConjugate f : UStar → WithBotTop ℝ)

-- Proof sketch: rewrite `(image F f)⋆` using the same perturbation-function representation of
-- `image F f` that underlies Theorem 5.7, then apply the Chapter 31 Fenchel-duality argument to
-- the concave slice `u ↦ ⟪F u, x⋆⟫`. The qualification hypothesis is exactly the common
-- relative-interior condition `ri(dom f) ∩ ri(dom F) ≠ ∅`.
/-- Conjugacy clause of Theorem 38.4: if `ri (dom f)` and `ri (dom F)` have a point in common,
then for each `x⋆`, the Fenchel conjugate of `image F f` at `x⋆` equals the value at `x⋆` of the
image of `f⋆` under the canonical image-side view `Function.swap (F⋆)` of the adjoint
bifunction. -/
theorem convexConjugate_image_eq_image_adjoint_conjugate_of_common_riDom
    (hF_convex : Function.IsConvex ℝ (Function.uncurry F))
    (hf_convex : Function.IsConvex ℝ f)
    (hf_proper : f.IsProper)
    (hri : (riDom(f) ∩ ri(dom F)).Nonempty)
    (xStar : XStar) :
    (image F f)⋆ xStar = image (Function.swap F⋆) (f⋆) xStar := sorry

-- Proof sketch: the same duality argument that gives the equality in clause (2) also yields, for
-- each `x⋆`, a minimizing dual point `u⋆` in the infimum formula defining the adjoint-side image.
/-- Attainment clause of Theorem 38.4: under the same relative-interior hypothesis, the infimum in
the definition of `(image (Function.swap (F⋆)) (f⋆)) x⋆` is attained for every `x⋆`. -/
theorem exists_eq_image_adjoint_conjugate_of_common_riDom
    (hF_convex : Function.IsConvex ℝ (Function.uncurry F))
    (hf_convex : Function.IsConvex ℝ f)
    (hf_proper : f.IsProper)
    (hri : (riDom(f) ∩ ri(dom F)).Nonempty)
    (xStar : XStar) :
    ∃ uStar : UStar,
      image (Function.swap F⋆) (f⋆) xStar =
        f⋆ uStar + F⋆ xStar uStar := sorry

end Conjugacy

end Bifunction
