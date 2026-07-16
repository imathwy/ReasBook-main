import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_29_2
import StacksProject_2024.stacks_project.Chap34.Lemma_34_3_8

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
-- local owner remains the full-subcategory inclusion from Definition 34.3.7 / Lemma 34.3.8
-- because `(Aff/S)_{Zar}` here uses arbitrary affine `S`-schemes with standard-open coverings.

variable (S : Scheme.{u})

/-- Lemma 34.3.10 (1): the inclusion functor `(Aff/S)_{Zar} ⥤ (Sch/S)_{Zar}` is special
cocontinuous; in the canonical dense-subsite owner, it is a dense subsite functor. -/
@[stacks 020W]
theorem bigAffineZariskiInclusion_isDenseSubsite :
    (bigAffineZariskiInclusion S).IsDenseSubsite
      S.bigAffineZariskiTopology S.bigZariskiTopology := sorry

/-- The affine-over inclusion carries the canonical dense-subsite instance from
`bigAffineZariskiInclusion_isDenseSubsite`. -/
instance bigAffineZariskiInclusionIsDenseSubsite :
    (bigAffineZariskiInclusion S).IsDenseSubsite
      S.bigAffineZariskiTopology S.bigZariskiTopology :=
  bigAffineZariskiInclusion_isDenseSubsite S

/-- Lemma 34.3.10 (2): the special-cocontinuous affine inclusion induces an equivalence of topoi;
canonically, the direct-image functor on set-valued sheaves is an equivalence. -/
@[stacks 020W]
theorem bigAffineZariskiSheafPushforwardContinuous_isEquivalence :
    ((bigAffineZariskiInclusion S).sheafPushforwardContinuous (Type v)
      S.bigAffineZariskiTopology S.bigZariskiTopology).IsEquivalence := sorry

end Scheme
end AlgebraicGeometry
