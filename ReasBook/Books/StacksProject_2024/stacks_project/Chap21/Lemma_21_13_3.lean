import StacksProject_2024.Chap07.LocalizationProjection
import StacksProject_2024.Chap21.Definition_21_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Abelian
open CategoryTheory.Sheaf
open scoped CategoryTheory.Sheaf

noncomputable section

universe u v

namespace CategoryTheory
namespace Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 21.13.3:
- primary domain: cohomology of abelian sheaves over a sheaf of sets, realized via the
  localization site on the category of elements;
- sampled owner declarations:
  `localizationProjection`,
  `Functor.PreservesInjectiveObjects`,
  `Functor.sheafPushforwardContinuous`,
  `cohomologyOverSheaf`,
  `Sheaf.H`;
- best owner abstraction: the localization inverse-image statement is canonically owned by
  `Functor.PreservesInjectiveObjects` for
  `(localizationProjection K).sheafPushforwardContinuous AddCommGrpCat (localizationTopology K) J`,
  and the source-facing cohomology `H^p(K, F)` is canonically owned by `cohomologyOverSheaf K F p`;
- primitive data: the sheaf of sets `K`, the abelian sheaf `F`, and the degree `p`;
- derived API: the localized inverse-image injectivity instance and theorem companion, together
  with the comparison to localized-site cohomology.

Source/core/bridge triage:
- `source-facing`: the two textbook assertions below;
- `core/canonical`: `Functor.PreservesInjectiveObjects`,
  `(localizationProjection K).sheafPushforwardContinuous AddCommGrpCat (localizationTopology K) J`,
  `cohomologyOverSheaf`, and `Sheaf.H`;
- `bridge/view`: the localized inverse-image `Injective` instance,
  `localizationInverseImage_injective`, and
  `cohomologyOverSheaf_isomorphic_localizedSite_cohomology`.
-/

variable (K : Sheaf J (Type v))

private abbrev localizationInverseImageAbelianFunctor :
    Sheaf J AddCommGrpCat.{v} ⥤ Sheaf (localizationTopology K) AddCommGrpCat.{v} :=
  (localizationProjection K).sheafPushforwardContinuous AddCommGrpCat.{v}
    (localizationTopology K) J

/-- Lemma 21.13.3 (1), owner form: the inverse-image functor of the localization morphism
`j : Sh(𝒞/K) ⟶ Sh(𝒞)` preserves injective abelian sheaves. -/
@[stacks 07A0]
instance localizationInverseImage_preservesInjectiveObjects :
    ((localizationProjection K).sheafPushforwardContinuous AddCommGrpCat.{v}
      (localizationTopology K) J).PreservesInjectiveObjects := by
  sorry

/-- Typeclass companion to Lemma 21.13.3 (1): the inverse image of an injective abelian sheaf on
`(𝒞, J)` is injective on the localized site `𝒞/K`. -/
instance instLocalizationInverseImageInjective
    (F : Sheaf J AddCommGrpCat.{v}) [Injective F] :
    Injective
      (((localizationProjection K).sheafPushforwardContinuous AddCommGrpCat.{v}
        (localizationTopology K) J).obj F) :=
  (localizationInverseImageAbelianFunctor K).injective_obj_of_injective inferInstance

/-- Lemma 21.13.3 (1), objectwise form: if `F` is an injective abelian sheaf on
`(𝒞, J)`, then its inverse image on the localized site `𝒞/K` is injective. -/
@[stacks 07A0]
theorem localizationInverseImage_injective
    (F : Sheaf J AddCommGrpCat.{v}) (hF : Injective F) :
    Injective
      (((localizationProjection K).sheafPushforwardContinuous AddCommGrpCat.{v}
        (localizationTopology K) J).obj F) := by
  let _ : Injective F := hF
  infer_instance

variable [HasWeakSheafify J AddCommGrpCat.{v}]
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt (Sheaf J AddCommGrpCat.{v})]
variable [HasSheafify (localizationTopology K) AddCommGrpCat.{v}]
variable [HasExt (Sheaf (localizationTopology K) AddCommGrpCat.{v})]

-- Proof sketch: identify the free abelian sheaf on `K` with the lower shriek of the constant
-- integer sheaf along the localization at `K`, then apply the lower-shriek/inverse-image
-- adjunction to compare `H^p(K, F)` with the global cohomology of `j^{-1} F`.
/-- Lemma 21.13.3 (2): the cohomology `H^p(K, F)`, formalized by the canonical `Ext`
owner from the free abelian sheaf on `K`, is canonically isomorphic to the global cohomology of
the inverse-image abelian sheaf on the localized site `𝒞/K`. -/
@[stacks 07A0]
theorem cohomologyOverSheaf_isomorphic_localizedSite_cohomology
    (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) :
    IsIsomorphic
      (H^p(K, F))
      (AddCommGrpCat.of
        ((((localizationProjection K).sheafPushforwardContinuous AddCommGrpCat.{v}
            (localizationTopology K) J).obj F).H p)) := by
  sorry

end

end Sheaf
end CategoryTheory
