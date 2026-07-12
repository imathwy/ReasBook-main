import Mathlib
import StacksProject_2024.Chap07.Definition_7_29_2
import StacksProject_2024.Chap34.Definition_34_4_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace Scheme

/- Source/core/bridge triage:
- `source-facing`: Lemma 34.4.11 identifies the affine étale inclusion as the Stacks-project
  "special cocontinuous" functor and records the induced equivalence on sheaves.
- `core/canonical`: `Functor.IsDenseSubsite` and the induced `sheafPushforwardContinuous`
  equivalence are the canonical owners.
- `bridge/view`: no extra bridge owner is needed here because `Scheme.AffineOver.forget S` is
  already the repository's canonical inclusion `(Aff/S) ⥤ (Sch/S)`.
-/

-- Semantic recall: `lean_leansearch` returned the dense-subsite/sheaf-equivalence owners
-- `Functor.IsDenseSubsite.sheafEquiv` and the Chapter 7 source-facing bridge in
-- `Definition_7_29_2`. Local Chapter 34 precedent in `Definition_34_4_8` fixes the affine étale
-- restricted topology `bigAffineEtaleTopology` on `S.AffineOver`, so this file uses the direct
-- canonical inclusion `AffineOver.forget S` rather than introducing a duplicate local
-- wrapper.

variable (S : Scheme.{u})

/-- Lemma 34.4.11 (1): the inclusion `(Aff/S)_{\acute{e}tale} ⥤ (Sch/S)_{\acute{e}tale}` is
special cocontinuous; canonically, it is a dense-subsite functor for the affine étale topology and
the big étale topology over `S`. -/
@[stacks 021E]
theorem bigAffineEtaleSiteInclusion_isDenseSubsite :
    (Scheme.AffineOver.forget S).IsDenseSubsite
      (bigAffineEtaleTopology S) (S.overGrothendieckTopology @Etale) := sorry

/-- The affine étale inclusion carries the canonical dense-subsite instance from
`bigAffineEtaleSiteInclusion_isDenseSubsite`. -/
instance bigAffineEtaleSiteInclusionIsDenseSubsite :
    (Scheme.AffineOver.forget S).IsDenseSubsite
      (bigAffineEtaleTopology S) (S.overGrothendieckTopology @Etale) :=
  bigAffineEtaleSiteInclusion_isDenseSubsite S

/-- Lemma 34.4.11 (2): the special-cocontinuous affine inclusion induces an equivalence of topoi;
equivalently, the restriction/inverse-image functor on set-valued sheaves is an equivalence. -/
@[stacks 021E]
theorem bigAffineEtaleSheafPushforwardContinuous_isEquivalence :
    ((Scheme.AffineOver.forget S).sheafPushforwardContinuous (Type v)
      (bigAffineEtaleTopology S) (S.overGrothendieckTopology @Etale)).IsEquivalence := sorry

end Scheme
end AlgebraicGeometry
