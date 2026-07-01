import Mathlib
import stacks_project.Chap07.Lemma_7_30_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite CategoryOfElements
open CategoryTheory.Sheaf

noncomputable section

universe u v

namespace CategoryTheory
namespace Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The inverse-image functor on abelian sheaves for the localization morphism at `K`. -/
abbrev localizationInverseImage (K : Sheaf J (Type v)) :
    Sheaf J AddCommGrpCat.{v} ⥤ Sheaf (localizationTopology K) AddCommGrpCat.{v} :=
  Functor.sheafPushforwardContinuous (localizationProjection K)
    AddCommGrpCat.{v} (localizationTopology K) J

/-- The cohomology of an abelian sheaf over a sheaf of sets, computed on the localized site. -/
abbrev cohomologyOverSheaf (K : Sheaf J (Type v))
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{v}]
    [HasExt (Sheaf (localizationTopology K) AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) : AddCommGrpCat.{v} :=
  AddCommGrpCat.of (((localizationInverseImage K).obj F).H p)

-- Proof sketch: the localization morphism at `K` is presented by the projection from the
-- category of elements of `K`; apply the standard exact-left-adjoint criterion for a geometric
-- inverse-image functor.
/-- Lemma 21.13.3 (1): the inverse-image functor of the localization morphism
`j : \operatorname{Sh}(\mathcal C/K) \to \operatorname{Sh}(\mathcal C)` preserves injective
abelian sheaves. -/
theorem localizationInverseImage_preserves_injective
    (K : Sheaf J (Type v)) (F : Sheaf J AddCommGrpCat.{v}) (hF : Injective F) :
    Injective ((localizationInverseImage K).obj F) := sorry

variable (K : Sheaf J (Type v))
variable [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{v}]
variable [HasSheafify (localizationTopology K) AddCommGrpCat.{v}]
variable [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{v}]
variable [HasExt (Sheaf (localizationTopology K) AddCommGrpCat.{v})]

-- Proof sketch: unfold `cohomologyOverSheaf`; by definition it is the global cohomology of the
-- inverse-image abelian sheaf on the localized site presenting `Sh(C/K)`.
/-- Lemma 21.13.3 (2): the cohomology `H^p(K, \mathcal F)` is computed by the global cohomology of
the inverse-image abelian sheaf on the localized site `\mathcal C/K`. -/
theorem cohomologyOverSheaf_eq_localizedSite_cohomology
    (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) :
    cohomologyOverSheaf K F p =
      AddCommGrpCat.of (((localizationInverseImage K).obj F).H p) := sorry

end

end Sheaf
end CategoryTheory
