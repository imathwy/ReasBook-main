import Mathlib
import StacksProject_2024.Chap07.Definition_7_29_2
import StacksProject_2024.Chap34.Lemma_34_3_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open Functor.IsDenseSubsite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace Scheme

-- Semantic recall: `lean_leansearch` returned `Functor.IsDenseSubsite.sheafEquiv` and the
-- canonical small-site comparison `Scheme.AffineZariskiSite.sheafEquiv`; for this Stacks item the
-- source-faithful owner remains the affine-open full-subcategory inclusion from
-- Definition 34.3.7 / Lemma 34.3.8 into the chapter-local small Zariski site `S_{Zar}`.

variable (S : Scheme.{u})

/-- Lemma 34.3.11 (1): the functor `S_{affine, Zar} ⥤ S_{Zar}` is special cocontinuous; in the
canonical dense-subsite owner, it is a dense subsite functor. -/
@[stacks 0F1B]
theorem smallAffineZariskiInclusion_isDenseSubsite :
    (smallAffineZariskiInclusion S).IsDenseSubsite
      S.smallAffineZariskiTopology S.smallZariskiTopology := sorry

/-- The small-affine inclusion carries the canonical dense-subsite instance from
`smallAffineZariskiInclusion_isDenseSubsite`. -/
instance smallAffineZariskiInclusionIsDenseSubsite :
    (smallAffineZariskiInclusion S).IsDenseSubsite
      S.smallAffineZariskiTopology S.smallZariskiTopology :=
  smallAffineZariskiInclusion_isDenseSubsite S

/-- Lemma 34.3.11 (2): the special-cocontinuous small-affine inclusion induces an equivalence of
topoi; canonically, the direct-image functor on set-valued sheaves is an equivalence. -/
@[stacks 0F1B]
theorem smallAffineZariskiSheafPushforwardContinuous_isEquivalence :
    ((smallAffineZariskiInclusion S).sheafPushforwardContinuous (Type v)
      S.smallAffineZariskiTopology S.smallZariskiTopology).IsEquivalence := sorry

end Scheme
end AlgebraicGeometry
