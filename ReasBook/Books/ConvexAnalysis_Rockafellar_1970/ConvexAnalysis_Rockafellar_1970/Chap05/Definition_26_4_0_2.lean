import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap05.Text_26_4_0_2

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 26.4.0.2 identifies the textbook Legendre-transform values of a
  differentiable pair `(C, f)` along the derivative image `fderivWithin 𝕜 f C '' C`.
- `core/canonical`: the owner data already present upstream are the canonical extension
  `Function.toWithTopBotOn f C`, its Fenchel conjugate `(Function.toWithTopBotOn f C)⋆`, and the
  pointwise value theorem
  `Function.convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub`.
- `bridge/view`: this file stays a recall/bridge node for the canonical owner layer and does not
  introduce a second public owner.

Domain-style sampling used here:
- `convexConjugate`;
- `Function.convexConjugate_toWithTopBotOn_imageFactorization_intrinsicInterior_eq_apply_sub`;
- `Function.mem_dom_convexConjugate_toWithTopBotOn_fderiv`;
- `Function.mapsTo_fderiv_dom_convexConjugate_toWithTopBotOn_intrinsicInterior`;
- `Function.image_fderiv_subset_dom_convexConjugate_toWithTopBotOn_intrinsicInterior`;
- `Function.convexConjugate_toWithTopBotOn_imageFactorization_eq_apply_sub`;
- `Function.mem_dom_convexConjugate_toWithTopBotOn_fderivWithin`;
- `Function.mapsTo_fderivWithin_dom_convexConjugate_toWithTopBotOn`;
- `Function.image_fderivWithin_subset_dom_convexConjugate_toWithTopBotOn`;
- `Function.convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub`.

Primitive data vs derived API:
- primitive owner surface: the Fenchel conjugate `(Function.toWithTopBotOn f C)⋆`;
- derived API: the owner-level derivative-image affine-defect evaluation theorem, together with
  pointwise, `Set.MapsTo`, and image-level finiteness corollaries on the same canonical owner.

Layer target:
- `core/canonical`: `convexConjugate`;
- `bridge/view`: recall existing derivative-image/value and finiteness bridges on that canonical
  owner layer.
-/

namespace Function

/- Definition 26.4.0.2 uses the chapter's canonical Fenchel-conjugate owner. -/
#check convexConjugate

/- The derivative-image and finiteness formulas already live upstream on the canonical owner. -/
recall convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub
recall convexConjugate_toWithTopBotOn_imageFactorization_intrinsicInterior_eq_apply_sub
recall mem_dom_convexConjugate_toWithTopBotOn_fderiv
recall mapsTo_fderiv_dom_convexConjugate_toWithTopBotOn_intrinsicInterior
recall image_fderiv_subset_dom_convexConjugate_toWithTopBotOn_intrinsicInterior
recall convexConjugate_toWithTopBotOn_imageFactorization_eq_apply_sub
recall mem_dom_convexConjugate_toWithTopBotOn_fderivWithin
recall mapsTo_fderivWithin_dom_convexConjugate_toWithTopBotOn
recall image_fderivWithin_subset_dom_convexConjugate_toWithTopBotOn

end Function
