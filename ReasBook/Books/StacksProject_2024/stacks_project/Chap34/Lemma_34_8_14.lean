import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import StacksProject_2024.stacks_project.Chap34.Definition_34_8_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

noncomputable section

namespace AlgebraicGeometry
namespace Scheme

/- Source/core/bridge triage:
- `source-facing`: Lemma 34.8.14 identifies the affine `ph` inclusion as the Stacks-project
  "special cocontinuous" functor and records the induced equivalence on sheaves.
- `core/canonical`: `Functor.IsDenseSubsite` and the induced `sheafPushforwardContinuous`
  equivalence are the canonical owners.
- `bridge/view`: no extra bridge owner is needed here because `AffineOver.forget S` is already
  the repository's canonical inclusion `(Aff/S) ⥤ (Sch/S)`.
-/

-- Semantic recall: local Chapter 34 precedent treats the Stacks notion of a special
-- cocontinuous affine inclusion through the canonical dense-subsite owner. Here the source-facing
-- affine `ph` topology from Definition 34.8.11 remains the bridge to the induced topology on the
-- affine full subcategory, and Lemma 34.8.14 records the resulting dense-subsite comparison and
-- the induced equivalence on set-valued sheaves.

variable (S : Scheme.{u})

/-- Lemma 34.8.14 (1): the inclusion `(Aff/S)_{ph} ⥤ (Sch/S)_{ph}` is special cocontinuous;
canonically, it is a dense-subsite functor for the affine `ph` topology and the big `ph`
topology over `S`. -/
@[stacks 0DBP]
theorem bigAffinePhInclusion_isDenseSubsite :
    (AffineOver.forget S).IsDenseSubsite (bigAffinePhTopology S) (bigPhSite S) := by
  sorry

/-- The affine `ph` inclusion carries the canonical dense-subsite instance from
`bigAffinePhInclusion_isDenseSubsite`. -/
instance bigAffinePhInclusionIsDenseSubsite :
    (AffineOver.forget S).IsDenseSubsite (bigAffinePhTopology S) (bigPhSite S) :=
  bigAffinePhInclusion_isDenseSubsite S

/-- Lemma 34.8.14 (2): the special-cocontinuous affine inclusion induces an equivalence of topoi;
equivalently, the restriction/inverse-image functor on set-valued sheaves is an equivalence. -/
@[stacks 0DBP]
theorem bigAffinePhSheafPushforwardContinuous_isEquivalence :
    ((AffineOver.forget S).sheafPushforwardContinuous (Type v)
      (bigAffinePhTopology S) (bigPhSite S)).IsEquivalence := by
  sorry

end Scheme
end AlgebraicGeometry
