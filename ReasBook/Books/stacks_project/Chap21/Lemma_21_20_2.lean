import Mathlib
import stacks_project.Chap18.Lemma_18_27_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "ModU" => ringedSiteModuleCategory (J.over U) (𝒪.over U)

private abbrev localizedStructureMap :=
  (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U)

variable [CategoryWithHomology Mod]
variable [HasGlobalSectionsFunctor (J.over U) AddCommGrpCat]

/-- Restriction from `(\mathcal C, \mathcal O)` to the localized ringed site
`(\mathcal C/U, \mathcal O_U)`. -/
abbrev localizedRestriction : Mod ⥤ ModU :=
  SheafOfModules.pushforward (𝟙 (localizedStructureMap J 𝒪 U))

/-- The sections functor `\Gamma(U,-)` on `\mathcal O`-modules over the fixed object `U`. -/
private abbrev sectionsOverObjectFunctor : Mod ⥤ AddCommGrpCat :=
  SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) ⋙
    sheafToPresheaf J AddCommGrpCat ⋙
      (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj (op U)

/-- The global-sections functor on `\mathcal O_U`-modules over the localized ringed site
`(\mathcal C/U, \mathcal O_U)`. -/
private abbrev localizedGlobalSectionsFunctor : ModU ⥤ AddCommGrpCat :=
  SheafOfModules.toSheaf
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (𝒪.over U)) ⋙
    Sheaf.Γ (J.over U) AddCommGrpCat

variable [(sectionsOverObjectFunctor J 𝒪 U).Additive]
variable [(localizedGlobalSectionsFunctor J 𝒪 U).Additive]
variable [(localizedRestriction J 𝒪 U).Additive]

/-- The degree-`p` homology of the sections complex `Γ(U, I^•)`. -/
private abbrev sectionsOverObjectHomology
    (I : CochainComplex Mod ℤ) (p : ℤ) : AddCommGrpCat :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) p).obj
    (((sectionsOverObjectFunctor J 𝒪 U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

/-- The degree-`p` homology of the global sections complex of `I^•|_{\mathcal C/U}` on the
localized ringed site. -/
private abbrev localizedSectionsHomology
    (I : CochainComplex Mod ℤ) (p : ℤ) : AddCommGrpCat :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) p).obj
    (((localizedGlobalSectionsFunctor J 𝒪 U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((localizedRestriction J 𝒪 U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))

/-- The comparison proposition asserting that the two homology objects are isomorphic. -/
private abbrev sectionsHomologyComparisonProp
    (I : CochainComplex Mod ℤ) (p : ℤ) : Prop :=
  IsIsomorphic
    (sectionsOverObjectHomology J 𝒪 U I p)
    (localizedSectionsHomology J 𝒪 U I p)

/-- Lemma 21.20.2: for a ringed site `(\mathcal C, \mathcal O)`, an object `U : \mathcal C`, and
a cochain complex `I^•` of `\mathcal O`-modules, the degree-`p` homology of the sections complex
`Γ(U, I^•)` agrees with the degree-`p` homology of the global sections complex of the restricted
complex on the localized ringed site `(\mathcal C/U, \mathcal O_U)`. For a K-injective
representative of `K`, this computes the textbook equality
`H^p(U, K) = H^p(\mathcal C/U, K|_{\mathcal C/U})`. -/
abbrev ringedSiteSectionsHomologyOverObject_isomorphic_onLocalizedSite
    (I : CochainComplex Mod ℤ) (p : ℤ) : Prop :=
  sectionsHomologyComparisonProp J 𝒪 U I p
end

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)
variable [HasGlobalSectionsFunctor (J.over U) AddCommGrpCat]
variable [(localizedRestriction J 𝒪 U).Additive]

-- Proof sketch: compare `Γ(U, -)` with global sections on the localized site via the canonical
-- restriction identification from the previous item, then apply homology in degree `p`.
/-- The proposition `ringedSiteSectionsHomologyOverObject_isomorphic_onLocalizedSite` is the
expected comparison statement for homology over an object and over the localized ringed site. -/
theorem ringedSiteSectionsHomologyOverObject_isomorphic_onLocalizedSite_holds
    (I : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ) (p : ℤ) :
    ringedSiteSectionsHomologyOverObject_isomorphic_onLocalizedSite J 𝒪 U I p := sorry

end
