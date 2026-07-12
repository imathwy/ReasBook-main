import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

/- Domain-style sampling:
- primary domain: localization of pretriangulated and triangulated categories by a multiplicative
  system compatible with distinguished triangles;
- relevant upstream owner declarations in this domain:
  `MorphismProperty.commShift_Q`,
  `Triangulated.Localization.pretriangulated`,
  `Triangulated.Localization.isTriangulated_functor`,
  `Functor.distTriang_iff`;
- source/core/bridge triage:
  `source-facing`: the Verdier-localized category carries distinguished triangles coming from the
    essential image of distinguished triangles upstairs;
  `core/canonical`: the owner API in `CategoryTheory.Localization.Triangulated`;
  `bridge/view`: `Functor.distTriang_iff`, specialized downstream to the localization functor
    `W.Q`.

Primitive data is the localization functor `W.Q` together with the compatible-triangulation
hypothesis on `W`. The pretriangulated structure on `W.Localization`, exactness of `W.Q`, the
distinguished-triangle characterization, and the triangulated structure under `[IsTriangulated D]`
are all derived owner API, so this file should stay at direct canonical recall/use.
-/

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

variable (W : MorphismProperty D) [W.HasLeftCalculusOfFractions] [W.IsCompatibleWithTriangulation]

/- Companion recall: the localization functor `W.Q` commutes with the shift by `ℤ` via the
canonical instance `MorphismProperty.commShift_Q`. -/
recall MorphismProperty.commShift_Q

/- Proposition 13.5.6: if `D` is pretriangulated and `W` is a multiplicative system compatible
with the triangulated structure, then the localized category `W.Localization` carries the
canonical pretriangulated structure `Triangulated.Localization.pretriangulated`. The companion
recalls below record that `W.Q` commutes with shift, is exact, and that `W.Localization` is
triangulated whenever `D` is triangulated. -/
recall Triangulated.Localization.pretriangulated

/- Companion recall: with the canonical pretriangulated structure on `W.Localization`, the
localization functor `W.Q` is triangulated, i.e. exact. -/
recall Triangulated.Localization.isTriangulated_functor

/- Companion recall: with the canonical pretriangulated structure on `W.Localization`, a triangle
is distinguished exactly when it lies in the essential image of distinguished triangles of `D`
under `W.Q`. -/
recall Functor.distTriang_iff

variable [IsTriangulated D]

/- Companion recall: if the source category `D` is triangulated, then the localized category
`W.Localization` is triangulated. -/
recall Triangulated.Localization.isTriangulated

end CategoryTheory
