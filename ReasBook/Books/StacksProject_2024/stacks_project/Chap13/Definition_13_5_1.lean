import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.MorphismProperty

/- Domain-style sampling:
- primary domain: compatibility of multiplicative systems with the triangulated structure on a
  pretriangulated category, as used in localization of triangulated categories;
- relevant upstream owner declarations in this domain:
  `MorphismProperty.IsCompatibleWithTriangulation`,
  `MorphismProperty.IsCompatibleWithShift`,
  `MorphismProperty.compatible_with_triangulation`,
  `Triangulated.Localization.pretriangulated`,
  `Triangulated.Localization.isTriangulated_functor`;
- source/core/bridge triage:
  `source-facing`: Stacks Definition 13.5.1, namely compatibility with the triangulated
    structure, consisting of the shift condition `f ∈ S ↔ f[1] ∈ S` together with the
    distinguished-triangle completion square;
  `core/canonical`: the owner class `MorphismProperty.IsCompatibleWithTriangulation`, whose
    primitive data is exactly the shift-compatibility owner `MorphismProperty.IsCompatibleWithShift`
    plus the triangle-completion field `compatible_with_triangulation`;
  `bridge/view`: the projection `compatible_with_triangulation`, used downstream to complete a
    morphism of distinguished triangles.

Primitive data is exactly the canonical owner class; the named projection and the localization
consequences are derived API. Since Definition 13.5.1 only recalls this existing owner, the
refined file should stay a pure canonical recall rather than introducing any parallel wrapper.
-/

/- Definition 13.5.1: the textbook notion that a multiplicative system is compatible with the
triangulated structure, meaning both shift invariance and the distinguished-triangle completion
condition, is the canonical mathlib class `MorphismProperty.IsCompatibleWithTriangulation`. -/
recall IsCompatibleWithTriangulation

/- Companion recall: the triangle-completion clause of Definition 13.5.1 is exposed by the
projection `compatible_with_triangulation`; the shift clause is inherited from
`MorphismProperty.IsCompatibleWithShift`. -/
recall compatible_with_triangulation

end CategoryTheory.MorphismProperty
