import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_5

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:
- `source-facing`: Text 18.0.10 says that every exposed ray of a convex cone is an extreme ray.
- `core/canonical`: the primitive direction-owner theorem is
  `ConvexCone.IsExposedRay.isExtremeRay`.
- `bridge/view`: the source-facing subset theorem `IsExposedRay.isExtremeRay` is kept upstream as a
  bridge through `originRay`; this text item recalls the primitive owner surface directly.

Abstraction checks:
- codomain/ambient layer: no ordered-extended codomain appears in this item.
- scalar/ambient minimization: the primitive theorem already lives on the chapter's cone/ray owner
  layer, with no `ℝ`-specialized binder surface.
- owner correctness: `ConvexCone.IsExposedRay` and `ConvexCone.IsExtremeRay` are the intrinsic
  direction owners; the subset surface remains a bridge.
- topology phrasing: this item is not an ambient-vs-relative topology theorem.
- notation surface: the canonical owner theorem surface is already primary;
  no additional notation is required.
-/

/- Text 18.0.10: every exposed direction ray of a convex cone is an extreme direction ray. This is
the canonical primitive-owner theorem `ConvexCone.IsExposedRay.isExtremeRay`. -/
recall ConvexCone.IsExposedRay.isExtremeRay
