import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_8
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_3_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_5_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_1

noncomputable section

open scoped Rockafellar

universe u v

namespace Bifunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type u} {XStar : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [AddCommGroup X] [Module 𝕜 X]
variable [Neg UStar] [HasPairing U UStar 𝕜]
variable [HasPairing X XStar 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: despite the legacy file name, this item is Rockafellar's Corollary 38.7.1. For
  a fixed `x⋆`, it specializes the Chapter 38 image/adjoint duality to the statement that the
  pairing `(f, F⋆ x⋆)` exists and that `(Ff, x⋆) = (f, F⋆ x⋆)`.
- `core/canonical`: the owner abstractions already present upstream are `Function.innerProduct`
  and `Function.HasInnerProduct` from `Definition_38_5_2`, together with the Chapter 38 image
  owner `Bifunction.image`, the adjoint owner `Bifunction.adjoint`, the slice-domain owner
  `Bifunction.dom`, and Fenchel conjugation `f⋆`.
  evaluation `(image F f)⋆ xStar`. Likewise `F⋆ x⋆` is the existing adjoint slice
  `adjoint XStar UStar F xStar`.

Primary mathematical domain:
- Fenchel pairings between a convex image `image F f` and fixed adjoint slices of a convex
  bifunction.

Domain-style sampling used here:
- `Function.innerProduct` and `Function.HasInnerProduct` from `Definition_38_5_2`;
- `Bifunction.image_apply_eq_iInf_sub_inverse` from `Definition_38_3_1`;
- `Bifunction.adjoint` from `Lemma_31_0_8`;
- `Bifunction.dom` / `Bifunction.IsProper` from `Theorem_38_1`.

Primitive data vs derived API:
- primitive inputs: a bifunction `F : U → X → WithBotTop 𝕜`, a function
  `f : U → WithBotTop 𝕜`, and a dual point `xStar : XStar`;
- primitive owner layer already upstream: `image F f`, `adjoint XStar UStar F xStar`,
  `image_apply_eq_iInf_sub_inverse`, `Function.innerProduct`, and
  `Function.HasInnerProduct`;
- primitive hypothesis layer used here: convexity of the graph function `Function.uncurry F`,
  properness of `F`, convexity/properness of `f`, and the common-relative-interior condition
  `(riDom[𝕜](f) ∩ ri[𝕜](dom F)).Nonempty`;
- derived API in this file: existence of the pairing with the adjoint slice, and the equality
  between that pairing and the conjugate evaluation of `image F f`.

Layer target: `bridge/view`. The source corollary is recorded directly in the existing owner
language, without introducing a new wrapper for pairings with a dual vector.

-/

/- The inverse-slice evaluation formula for `image` is already owned by
`Bifunction.image_apply_eq_iInf_sub_inverse`; this file only records the Chapter 38.7.1 pairing
reformulation on top of that owner layer. -/
recall Bifunction.image_apply_eq_iInf_sub_inverse

variable (F : U → X → WithBotTop 𝕜) (f : U → WithBotTop 𝕜)

/-- Corollary 38.7.1, existence clause at the `WithBotTop 𝕜` pairing layer: if `F` is convex and
proper, `f` is convex and proper, and `riDom[𝕜](f)` meets `ri[𝕜](dom F)`, then the pairing of `f`
with the adjoint slice `adjoint XStar UStar F xStar` exists for every `xStar`. -/
theorem hasInnerProduct_adjointFunction_of_common_riDom
    (hF_convex : (Function.uncurry F).IsConvex 𝕜) (hF_proper : IsProper F)
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hri : (riDom[𝕜](f) ∩ ri[𝕜](dom F)).Nonempty)
    (xStar : XStar) :
    Function.HasInnerProduct f (adjoint XStar UStar F xStar : UStar → WithBotTop 𝕜) := by
  sorry

/-- Corollary 38.7.1, equality clause in owner form: the source notation `(Ff, x⋆)` is the
conjugate value `(image F f)⋆ xStar`, so for every `xStar` one has
`(image F f)⋆ xStar = Function.innerProduct f (adjoint XStar UStar F xStar)` under the same
convexity/properness and common-relative-interior hypotheses. -/
theorem convexConjugate_image_eq_innerProduct_adjointFunction_of_common_riDom
    (hF_convex : (Function.uncurry F).IsConvex 𝕜) (hF_proper : IsProper F)
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hri : (riDom[𝕜](f) ∩ ri[𝕜](dom F)).Nonempty)
    (xStar : XStar) :
    (image F f)⋆ xStar =
      Function.innerProduct f (adjoint XStar UStar F xStar : UStar → WithBotTop 𝕜) := by
  sorry

end

end Bifunction
