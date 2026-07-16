import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_29_2
import StacksProject_2024.stacks_project.Chap34.Definition_34_4_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace Scheme

-- Semantic recall: `lean_leansearch` returned the dense-subsite/sheaf-equivalence owners
-- `Functor.IsDenseSubsite.sheafEquiv` and `Functor.sheafPushforwardContinuous`. For this Stacks
-- item, the source's chosen big étale site containing `S` is bookkeeping for the canonical small
-- étale site `S_{\acute{e}tale}`; local Chapter 34 precedent in `Definition_34_4_8` fixes the
-- affine small étale subsite owner `smallAffineEtaleSite`, its inclusion
-- `smallAffineEtaleSiteInclusion`, and the topology `smallAffineEtaleTopology`.

variable (S : Scheme.{u})

/-- Lemma 34.4.12 (1): the functor `S_{affine, \acute{e}tale} ⥤ S_{\acute{e}tale}` is special
cocontinuous; canonically, the inclusion of the affine small étale site into the small étale site
is a dense-subsite functor. -/
@[stacks 04HR]
theorem smallAffineEtaleSiteInclusion_isDenseSubsite :
    (smallAffineEtaleSiteInclusion S).IsDenseSubsite
      (smallAffineEtaleTopology S) S.smallEtaleTopology := sorry

/-- The small-affine étale inclusion carries the canonical dense-subsite instance from
`smallAffineEtaleSiteInclusion_isDenseSubsite`. -/
instance smallAffineEtaleSiteInclusionIsDenseSubsite :
    (smallAffineEtaleSiteInclusion S).IsDenseSubsite
      (smallAffineEtaleTopology S) S.smallEtaleTopology :=
  smallAffineEtaleSiteInclusion_isDenseSubsite S

/-- Lemma 34.4.12 (2): the special-cocontinuous functor
`S_{affine, \acute{e}tale} ⥤ S_{\acute{e}tale}` induces an equivalence of topoi; canonically,
the inverse-image functor on set-valued sheaves is an equivalence. -/
@[stacks 04HR]
theorem smallAffineEtaleSheafPushforwardContinuous_isEquivalence :
    ((smallAffineEtaleSiteInclusion S).sheafPushforwardContinuous (Type v)
      (smallAffineEtaleTopology S) S.smallEtaleTopology).IsEquivalence := sorry

end Scheme
end AlgebraicGeometry
