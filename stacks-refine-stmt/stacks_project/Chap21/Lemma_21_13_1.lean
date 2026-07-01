import Mathlib
import stacks_project.Chap07.Lemma_7_30_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Sheaf
open Opposite CategoryOfElements

noncomputable section

universe u v

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J (Type (max u v))]
variable (𝒪 : Sheaf J RingCat.{max u v})

/-- The pullback of the structure sheaf `\mathcal O` to the localized site `\mathcal C/K`. -/
abbrev localizationRingSheaf
    (K : Sheaf J (Type (max u v))) :
    Sheaf (localizationTopology K) RingCat.{max u v} :=
  (CategoryTheory.Functor.sheafPushforwardContinuous (localizationProjection K)
    RingCat.{max u v} (localizationTopology K) J).obj 𝒪

/-- The inverse-image functor on abelian sheaves for localization at a sheaf of sets `K`. -/
abbrev localizationInverseImage
    (K : Sheaf J (Type (max u v))) :
    Sheaf J AddCommGrpCat.{max u v} ⥤
      Sheaf (localizationTopology K) AddCommGrpCat.{max u v} :=
  (CategoryTheory.Functor.sheafPushforwardContinuous (localizationProjection K)
    AddCommGrpCat.{max u v} (localizationTopology K) J)

/-- The cohomology of an abelian sheaf over a sheaf of sets `K`, computed on the localized site
`\mathcal C/K`. -/
abbrev cohomologyOverSheaf
    (K : Sheaf J (Type (max u v)))
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasExt (Sheaf (localizationTopology K) AddCommGrpCat.{max u v})]
    (F : Sheaf J AddCommGrpCat.{max u v}) (p : ℕ) :
    AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of (((localizationInverseImage K).obj F).H p)

/-- Restriction of `\mathcal O`-modules from the base ringed site to the localized ringed site
over a sheaf of sets `K`. -/
abbrev localizationModuleRestriction
    (K : Sheaf J (Type (max u v))) :
    SheafOfModules 𝒪 ⥤ SheafOfModules (localizationRingSheaf 𝒪 K) :=
  SheafOfModules.pushforward (𝟙 (localizationRingSheaf 𝒪 K))

/-- Module cohomology over a sheaf of sets `K`, computed on the localized ringed site
`(\mathcal C/K, \mathcal O|_K)`. -/
abbrev moduleCohomologyOverSheaf
    (K : Sheaf J (Type (max u v)))
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasExt (Sheaf (localizationTopology K) AddCommGrpCat.{max u v})]
    [HasExt (SheafOfModules (localizationRingSheaf 𝒪 K))]
    (ℱ : SheafOfModules 𝒪) (p : ℕ) : AddCommGrpCat.{max u v} :=
  (Abelian.extFunctorObj (SheafOfModules.unit (localizationRingSheaf 𝒪 K)) p).obj
    ((localizationModuleRestriction 𝒪 K).obj ℱ)

-- Proof sketch: apply Lemma `21.12.4 (1)` on the localized ringed site
-- `(\mathcal C/K, \mathcal O|_K)` to the restricted module `j_K^* \mathcal F`. The resulting
-- comparison identifies module cohomology on the localized ringed site with the cohomology of the
-- underlying abelian sheaf pulled back to `\mathcal C/K`, which is exactly
-- `cohomologyOverSheaf K \mathcal F_{ab}` by Definition `21.13.3`.
/-- The module cohomology of an `\mathcal O`-module over a sheaf of sets `K` agrees with the
cohomology of its underlying abelian sheaf over `K`. -/
theorem moduleCohomologyOverSheaf_eq_underlyingAbelianSheafCohomology
    (K : Sheaf J (Type (max u v)))
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasExt (Sheaf (localizationTopology K) AddCommGrpCat.{max u v})]
    [HasExt (SheafOfModules (localizationRingSheaf 𝒪 K))]
    (ℱ : SheafOfModules 𝒪) (p : ℕ) :
    moduleCohomologyOverSheaf 𝒪 K ℱ p =
      cohomologyOverSheaf K ((SheafOfModules.toSheaf 𝒪).obj ℱ) p := sorry

-- Proof sketch: replace the presheaf of sets `K` by its sheafification `aK`. By definition,
-- `H^p(K, \mathcal F)` is computed on the localized ringed site over `aK`, and the preceding
-- localized-site comparison identifies this with the cohomology of the underlying abelian sheaf
-- over `aK`.
/-- Lemma 21.13.1: for a ringed site `(\mathcal C, \mathcal O)`, a presheaf of sets `K`, and an
`\mathcal O`-module `\mathcal F`, the cohomology `H^p(K, \mathcal F)` computed after sheafifying
`K` agrees with the cohomology `H^p(K, \mathcal F_{ab})` of the underlying sheaf of abelian
groups. -/
theorem moduleCohomologyOverPresheaf_eq_underlyingAbelianSheafCohomology
    (K : Cᵒᵖ ⥤ Type (max u v))
    [HasWeakSheafify (localizationTopology ((presheafToSheaf J (Type (max u v))).obj K))
      AddCommGrpCat.{max u v}]
    [HasSheafify (localizationTopology ((presheafToSheaf J (Type (max u v))).obj K))
      AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor
      (localizationTopology ((presheafToSheaf J (Type (max u v))).obj K))
      AddCommGrpCat.{max u v}]
    [HasExt
      (Sheaf (localizationTopology ((presheafToSheaf J (Type (max u v))).obj K))
        AddCommGrpCat.{max u v})]
    [HasExt
      (SheafOfModules
        (localizationRingSheaf 𝒪 ((presheafToSheaf J (Type (max u v))).obj K)))]
    (ℱ : SheafOfModules 𝒪) (p : ℕ) :
    moduleCohomologyOverSheaf 𝒪 ((presheafToSheaf J (Type (max u v))).obj K) ℱ p =
      cohomologyOverSheaf ((presheafToSheaf J (Type (max u v))).obj K)
        ((SheafOfModules.toSheaf 𝒪).obj ℱ) p := sorry

end Sheaf
end CategoryTheory
