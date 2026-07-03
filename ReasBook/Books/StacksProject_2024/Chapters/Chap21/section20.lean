import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_20_1 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev ringedSiteModules :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- Restriction of `\mathcal O`-modules from `(\mathcal C, \mathcal O)` to the localized
ringed site `(\mathcal C/U, \mathcal O_U)`. -/
private abbrev localizedRestriction :
    ringedSiteModules J 𝒪 ⥤
      SheafOfModules (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U) :=
  SheafOfModules.pushforward (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))

variable [(localizedRestriction J 𝒪 U).PreservesZeroMorphisms]

-- Proof sketch: the localization restriction functor `j_U^*` on `\mathcal O`-modules is right
-- adjoint to extension by zero `j_{U!}` by the canonical localized adjunction, and
-- `j_{U!}` is exact by Lemma `18.19.3`. Apply Lemma `13.31.9` to conclude that the induced
-- functor on cochain complexes preserves K-injective complexes.
/-- Lemma 21.20.1: for a ringed site `(\mathcal C, \mathcal O)`, an object `U : \mathcal C`, and
a K-injective complex of `\mathcal O`-modules, the restricted complex on the localized ringed site
`(\mathcal C/U, \mathcal O_U)` is K-injective. -/
theorem ringedSiteLocalizedRestriction_isKInjective
    (I : CochainComplex (ringedSiteModules J 𝒪) ℤ) [I.IsKInjective] :
    let K := (((localizedRestriction J 𝒪 U).mapHomologicalComplex (up ℤ)).obj I)
    CochainComplex.IsKInjective K :=
  sorry

end

/-! ### Lemma_21_20_2 (from Chap21) -/
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

/-! ### Lemma_21_20_3 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u w

attribute [local instance] HasDerivedCategory.standard

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})

local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [hGroth : IsGrothendieckAbelian.{w} Mod]

/-- The additive functor from `\operatorname{Mod}(\mathcal O)` to abelian presheaves on
`(\mathcal C, J)` obtained by forgetting the module structure to the underlying abelian sheaf and
then forgetting the sheaf condition. -/
abbrev ringedSiteUnderlyingAbelianPresheafFunctor :
    Mod ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) ⋙
    sheafToPresheaf J AddCommGrpCat.{u}

/-- The total right derived functor of the forgetful functor from `\operatorname{Mod}(\mathcal O)`
to abelian presheaves on `(\mathcal C, J)`. -/
abbrev ringedSiteUnderlyingAbelianPresheafDerived :
    DerivedCategory Mod ⥤ DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  @CategoryTheory.additiveFunctorTotalRightDerived
    Mod (Cᵒᵖ ⥤ AddCommGrpCat.{u}) _ _ _ _
    (ringedSiteUnderlyingAbelianPresheafFunctor J 𝒪)
    inferInstance hGroth

/-- The presheaf `U ↦ H^q(U, K)` for a derived `\mathcal O`-module `K`, realized as the
degree-`q` homology presheaf of the total right derived underlying-presheaf functor. -/
abbrev ringedSiteObjectwiseCohomologyPresheaf
    (K : DerivedCategory Mod) (q : ℤ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{u}) q).obj
    ((ringedSiteUnderlyingAbelianPresheafDerived J 𝒪).obj K)

/-- The underlying abelian sheaf of the degree-`q` cohomology sheaf `H^q(K)` of a derived
`\mathcal O`-module `K`. -/
abbrev ringedSiteCohomologySheaf
    (K : DerivedCategory Mod) (q : ℤ) :
    Sheaf J AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)).obj
    ((DerivedCategory.homologyFunctor Mod q).obj K)

/-- Lemma 21.20.3: for a ringed site `(\mathcal C, \mathcal O)` and an object `K` of
`D(\mathcal O)`, the sheaf associated to the presheaf `U ↦ H^q(U, K)` is the underlying abelian
sheaf of the degree-`q` cohomology sheaf `H^q(K)`. -/
abbrev ringedSiteObjectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf
    (K : DerivedCategory Mod) (q : ℤ) : Prop :=
  IsIsomorphic
    (ringedSiteCohomologySheaf J 𝒪 K q)
    ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (ringedSiteObjectwiseCohomologyPresheaf J 𝒪 K q))

end

attribute [-instance] HasDerivedCategory.standard

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [hGroth : IsGrothendieckAbelian.{w} (ringedSiteModuleCategory J 𝒪)]

local notation "StdDerivedMod" =>
  @DerivedCategory (ringedSiteModuleCategory J 𝒪) _ _
    (HasDerivedCategory.standard (ringedSiteModuleCategory J 𝒪))

-- Proof sketch: this is exactly the comparison proposition introduced above; the substantive proof
-- will identify the derived underlying-presheaf homology with the underlying sheaf homology after
-- sheafification.
/-- Canonical theorem wrapper for the ringed-site comparison between sheafified objectwise
cohomology and the cohomology sheaf. -/
theorem ringedSiteObjectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf_holds
    (K : StdDerivedMod) (q : ℤ) :
    ringedSiteObjectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf J 𝒪 K q :=
  sorry

end

/-! ### Lemma_21_20_4 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace RingedSite.Hom

/-- Restriction of `\mathcal O_X`-modules from a ringed site `X` to the localized ringed site
`(X/U, \mathcal O_U)`. -/
abbrev localizedRestriction (X : RingedSite.{u, v}) (U : X) :
    ModuleCat X ⥤ SheafOfModules (X.structureSheaf.over U) :=
  SheafOfModules.pushforward (𝟙 (X.structureSheaf.over U))

/-- The exact functor on derived categories induced by restriction to the localized ringed site
`(X/U, \mathcal O_U)`. -/
abbrev localizedRestrictionDerived
    (X : RingedSite.{u, v}) (U : X)
    [(localizedRestriction X U).Additive]
    [PreservesFiniteLimits (localizedRestriction X U)]
    [PreservesFiniteColimits (localizedRestriction X U)] :
    ModuleDerived X ⥤ DerivedCategory (SheafOfModules (X.structureSheaf.over U)) :=
  CategoryTheory.Functor.mapDerivedCategory (localizedRestriction X U)

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) (V : Y)

variable [f.modulePushforward.Additive]
variable [(RingedSite.Hom.localization f V).modulePushforward.Additive]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived (RingedSite.Hom.localization f V))
  (ModuleQis (X.localization (f.base.obj V)))]

variable [(localizedRestriction X (f.base.obj V)).Additive]
variable [PreservesFiniteLimits (localizedRestriction X (f.base.obj V))]
variable [PreservesFiniteColimits (localizedRestriction X (f.base.obj V))]

variable [(localizedRestriction Y V).Additive]
variable [PreservesFiniteLimits (localizedRestriction Y V)]
variable [PreservesFiniteColimits (localizedRestriction Y V)]

-- Proof sketch: use the underived identity
-- `(f_* \mathcal F)|_{\mathcal D/V} \cong g_*(\mathcal F|_{\mathcal C/U})`
-- coming from the localization square of Lemma `18.20.1` and Sites, Lemma `7.28.1`. Then pass to
-- unbounded derived functors by representing `E` with a K-injective complex, applying
-- Lemma `21.20.1` to keep the restricted complex K-injective, and comparing the two resulting
-- pushforwards termwise.
/-- Lemma 21.20.4: if `f : X ⟶ Y` is a morphism of ringed sites, `V : Y`, `U = f.base.obj V`,
and `g : X/U ⟶ Y/V` is the localized morphism of ringed sites, then restriction to `Y/V`
commutes with the unbounded derived direct image:
`(Rf_* E)|_{Y/V} \cong Rg_*(E|_{X/U})` for every `E : D(\mathcal O_X)`. -/
theorem modulePushforwardDerived_localizedRestriction_iso
    (E : ModuleDerived X) :
    let U := f.base.obj V
    let g := RingedSite.Hom.localization f V
    ∃ η :
      ((localizedRestrictionDerived Y V).obj ((modulePushforwardDerived f).obj E)) ⟶
        ((modulePushforwardDerived g).obj ((localizedRestrictionDerived X U).obj E)),
      IsIso η := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_20_5 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace RingedSite.Hom

/-- The abelian category of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on `X`. -/
abbrev ModuleDerived (X : RingedSite.{u, v}) :=
  DerivedCategory (ModuleCat X)

/-- The homotopy-to-derived functor induced by pushforward on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive] :
    HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived Y :=
  mapHomotopyCategoryToDerived f.modulePushforward

/-- The unbounded derived direct-image functor `Rf_*` on module sheaves. -/
noncomputable abbrev modulePushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The complex-level global-sections functor on `\mathcal O_X`-modules, viewed on underlying
abelian groups. -/
abbrev moduleGlobalSectionsToDerived (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [(moduleGlobalSectionsFunctor X).Additive] :
    HomotopyCategory (ModuleCat X) (up ℤ) ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
  mapHomotopyCategoryToDerived (moduleGlobalSectionsFunctor X)

/-- The chosen unbounded derived global-sections functor on a ringed site, formalized on
underlying additive groups. -/
noncomputable abbrev moduleGlobalSectionsDerived (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [(moduleGlobalSectionsFunctor X).Additive]
    [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)] :
    ModuleDerived X ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
  Functor.totalRightDerived (moduleGlobalSectionsToDerived X)
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The ring of sections `\Gamma(U, \mathcal O_X)` on an object `U` of the ringed site `X`. -/
abbrev sectionsRingOnObject (X : RingedSite.{u, v}) (U : X) : RingCat.{max u v} :=
  X.structureSheaf.1.obj (op U)

/-- The sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules over the fixed object `U`. -/
abbrev moduleSectionsFunctorAtObject (X : RingedSite.{u, v}) (U : X) :
    ModuleCat X ⥤ _root_.ModuleCat (sectionsRingOnObject X U) :=
  SheafOfModules.evaluation X.structureSheaf (op U)

/-- The map on section rings induced by a morphism of ringed sites at an object `V` of the target.
-/
abbrev sectionsMapOnObject {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) (V : Y) :
    sectionsRingOnObject Y V ⟶ sectionsRingOnObject X (f.base.obj V) :=
  f.structureSheafMap.1.app (op V)

/-- Restriction of scalars along the map
`\Gamma(V, \mathcal O_Y) \to \Gamma(f(V), \mathcal O_X)`. -/
abbrev moduleSectionsRestrictionFunctor {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    (V : Y) :
    _root_.ModuleCat (sectionsRingOnObject X (f.base.obj V)) ⥤
      _root_.ModuleCat (sectionsRingOnObject Y V) :=
  _root_.ModuleCat.restrictScalars (sectionsMapOnObject f V).hom

/-- The complex-level sections functor over a fixed object of a ringed site. -/
abbrev moduleSectionsToDerived (X : RingedSite.{u, v}) (U : X)
    [(moduleSectionsFunctorAtObject X U).Additive] :
    HomotopyCategory (ModuleCat X) (up ℤ) ⥤
      DerivedCategory (_root_.ModuleCat (sectionsRingOnObject X U)) :=
  mapHomotopyCategoryToDerived (moduleSectionsFunctorAtObject X U)

/-- The chosen unbounded derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`. -/
noncomputable abbrev moduleSectionsDerived (X : RingedSite.{u, v}) (U : X)
    [(moduleSectionsFunctorAtObject X U).Additive]
    [Functor.HasRightDerivedFunctor (moduleSectionsToDerived X U) (ModuleQis X)] :
    ModuleDerived X ⥤ DerivedCategory (_root_.ModuleCat (sectionsRingOnObject X U)) :=
  Functor.totalRightDerived (moduleSectionsToDerived X U)
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The derived restriction-of-scalars functor on section rings attached to `f` and `V`. -/
abbrev moduleSectionsRestrictionDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    (V : Y)
    [(moduleSectionsRestrictionFunctor f V).Additive]
    [PreservesFiniteLimits (moduleSectionsRestrictionFunctor f V)]
    [PreservesFiniteColimits (moduleSectionsRestrictionFunctor f V)] :
    DerivedCategory (_root_.ModuleCat (sectionsRingOnObject X (f.base.obj V))) ⥤
      DerivedCategory (_root_.ModuleCat (sectionsRingOnObject Y V)) :=
  Functor.mapDerivedCategory (moduleSectionsRestrictionFunctor f V)

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{max u v}]

variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

variable [(moduleGlobalSectionsFunctor X).Additive]
variable [(moduleGlobalSectionsFunctor Y).Additive]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived Y) (ModuleQis Y)]

-- Proof sketch: let `g : Y ⟶ pt` be the canonical morphism to the punctual ringed topos whose
-- structure sheaf is `Γ(Y, \mathcal O_Y)`. Then `RΓ(Y,-)` is the derived pushforward `Rg_*`.
-- Apply Lemma `21.19.2` to the composite `X ⟶ Y ⟶ pt`, and use the identification of the
-- composite pushforward with global sections. This formalization records the resulting objectwise
-- isomorphism after forgetting to underlying additive groups.
/-- Lemma 21.20.5 (1): after forgetting the natural module structure to underlying abelian groups,
derived global sections on `Y` applied to `Rf_* K` are isomorphic to derived global sections on
`X` applied to `K`. This is the objectwise form of
`R\Gamma(\mathcal D,-) \circ Rf_* = R\Gamma(\mathcal C,-)`. -/
theorem modulePushforwardDerived_globalSections_isIsomorphic
    (K : ModuleDerived X) :
    IsIsomorphic
      ((moduleGlobalSectionsDerived Y).obj ((modulePushforwardDerived f).obj K))
      ((moduleGlobalSectionsDerived X).obj K) := sorry

variable (V : Y)

variable [(moduleSectionsFunctorAtObject X (f.base.obj V)).Additive]
variable [(moduleSectionsFunctorAtObject Y V).Additive]
variable [Functor.HasRightDerivedFunctor
  (moduleSectionsToDerived X (f.base.obj V)) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (moduleSectionsToDerived Y V) (ModuleQis Y)]
variable [(moduleSectionsRestrictionFunctor f V).Additive]
variable [PreservesFiniteLimits (moduleSectionsRestrictionFunctor f V)]
variable [PreservesFiniteColimits (moduleSectionsRestrictionFunctor f V)]

-- Proof sketch: identify `RΓ(U,-)` with derived global sections on the localized ringed site
-- `X/U` via Lemma `21.20.2`, identify `RΓ(V,-)` with derived global sections on `Y/V`, and then
-- use Lemma `21.20.4` to commute localized restriction with `Rf_*`. The resulting comparison is
-- expressed in the target ring `Γ(V, \mathcal O_Y)` by explicit restriction of scalars along
-- `Γ(V, \mathcal O_Y) → Γ(U, \mathcal O_X)`.
/-- Lemma 21.20.5 (2): for `V : Y` and `U = f(V)`, derived sections over `U` on `X`, viewed in
`D(\Gamma(V,\mathcal O_Y))` by restriction of scalars along
`\Gamma(V,\mathcal O_Y) \to \Gamma(U,\mathcal O_X)`, are isomorphic to derived sections over `V`
of `Rf_* K`. This is the objectwise form of
`R\Gamma(U,-) = R\Gamma(V,-) \circ Rf_*`. -/
theorem modulePushforwardDerived_sectionsOverObject_isIsomorphic
    (K : ModuleDerived X) :
    IsIsomorphic
      ((moduleSectionsRestrictionDerived f V).obj
        ((moduleSectionsDerived X (f.base.obj V)).obj K))
      ((moduleSectionsDerived Y V).obj ((modulePushforwardDerived f).obj K)) := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_20_6 (from Chap21) -/
open CategoryTheory
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

open RingedSite.Hom

namespace RingedSite

/-- The additive functor from `\mathcal O_X`-modules to abelian presheaves on the underlying site
of `X`, obtained by forgetting module structure to the underlying abelian sheaf and then
forgetting the sheaf condition. -/
private abbrev underlyingAbelianPresheafFunctor (X : RingedSite.{u, v}) :
    ModuleCat X ⥤ Xᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v}

/-- The total right derived functor of the underlying-abelian-presheaf functor on a ringed site.
-/
private abbrev underlyingAbelianPresheafDerived (X : RingedSite.{u, v})
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)] :
    DerivedCategory (ModuleCat X) ⥤
      DerivedCategory (Xᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (underlyingAbelianPresheafFunctor X)

/-- The presheaf `U ↦ H^i(U, K)` on a ringed site `X`, realized as the degree-`i` homology
presheaf of the derived underlying-presheaf functor. -/
abbrev objectwiseCohomologyPresheaf (X : RingedSite.{u, v})
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
    (K : DerivedCategory (ModuleCat X)) (i : ℤ) :
    Xᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor (Xᵒᵖ ⥤ AddCommGrpCat.{max u v}) i).obj
    ((underlyingAbelianPresheafDerived X).obj K)

/-- The underlying abelian sheaf of the degree-`i` cohomology sheaf `H^i(K)` on a ringed site
`X`. -/
abbrev cohomologySheaf (X : RingedSite.{u, v})
    (K : DerivedCategory (ModuleCat X)) (i : ℤ) :
    Sheaf X.siteTopology AddCommGrpCat.{max u v} :=
  (SheafOfModules.toSheaf X.structureSheaf).obj
    ((DerivedCategory.homologyFunctor (ModuleCat X) i).obj K)

end RingedSite

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat Y)]

variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

/-- The presheaf on the target site sending `V` to the objectwise cohomology `H^i(u(V), K)` on
the source site, expressed by precomposition with the continuous functor underlying `f`. -/
abbrev sourceObjectwiseCohomologyPresheaf (f : RingedSite.Hom X Y)
    (K : ModuleDerived X) (i : ℤ) :
    Yᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  f.base.op ⋙ X.objectwiseCohomologyPresheaf K i

-- Proof sketch: for each object `V : Y`, Lemma `21.20.5 (2)` identifies `RΓ(u(V), K)` with
-- `RΓ(V, Rf_* K)` after restriction of scalars. Taking degree-`i` homology and forgetting the
-- module structure gives the required objectwise isomorphism of abelian presheaves.
/-- The source-side and pushforward-side objectwise cohomology presheaves are canonically
isomorphic. -/
theorem sourceObjectwiseCohomologyPresheaf_isomorphic_pushforwardObjectwiseCohomologyPresheaf
    (K : ModuleDerived X) (i : ℤ) :
    IsIsomorphic
      (sourceObjectwiseCohomologyPresheaf f K i)
      (Y.objectwiseCohomologyPresheaf ((modulePushforwardDerived f).obj K) i) := sorry

-- Proof sketch: first replace the presheaf `V ↦ H^i(u(V), K)` by the canonically isomorphic
-- presheaf `V ↦ H^i(V, Rf_* K)` using the previous theorem. Then identify the sheafification of
-- that presheaf with the cohomology sheaf `H^i(Rf_* K)` on the target ringed site via the
-- derived underlying-presheaf comparison.
/-- Lemma 21.20.6: for a morphism of ringed sites `f : X ⟶ Y` and `K : D(\mathcal O_X)`, the
sheaf associated to the presheaf `V ↦ H^i(u(V), K)` is the degree-`i` cohomology sheaf of
`Rf_* K`. Equivalently, it is the sheaf associated to `V ↦ H^i(V, Rf_* K)`. -/
theorem sourceObjectwiseCohomologyPresheaf_sheafification_isomorphic_cohomologySheaf
    (K : ModuleDerived X) (i : ℤ) :
    IsIsomorphic
      ((presheafToSheaf Y.siteTopology AddCommGrpCat.{max u v}).obj
        (sourceObjectwiseCohomologyPresheaf f K i))
      (Y.cohomologySheaf ((modulePushforwardDerived f).obj K) i) := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_20_7 (from Chap21) -/
open CategoryTheory
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace RingedSite.Hom

/-- The abelian category of sheaves of abelian groups on the site underlying a ringed site. -/
abbrev AbelianSheafCat (X : RingedSite.{u, v}) :=
  Sheaf X.siteTopology AddCommGrpCat.{max u v}

/-- The forgetful functor from `\mathcal O_X`-modules to their underlying abelian sheaves. -/
abbrev underlyingAbelianSheafFunctor (X : RingedSite.{u, v}) :
    ModuleCat X ⥤ AbelianSheafCat X :=
  SheafOfModules.toSheaf X.structureSheaf

/-- The derived forgetful functor sending a complex of `\mathcal O_X`-modules to its underlying
complex of abelian sheaves. -/
abbrev underlyingAbelianSheafDerived (X : RingedSite.{u, v})
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)] :
    ModuleDerived X ⥤ DerivedCategory (AbelianSheafCat X) :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (underlyingAbelianSheafFunctor X)

/-- The global-sections functor on abelian sheaves over the site underlying `X`. -/
abbrev abelianGlobalSectionsFunctor (X : RingedSite.{u, v})
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}] :
    AbelianSheafCat X ⥤ AddCommGrpCat.{max u v} :=
  CategoryTheory.Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v}

/-- The total right derived functor of global sections on abelian sheaves over the site underlying
`X`. -/
abbrev abelianGlobalSectionsDerived (X : RingedSite.{u, v})
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
    [(abelianGlobalSectionsFunctor X).Additive]
    [IsGrothendieckAbelian.{max u v} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (abelianGlobalSectionsFunctor X)

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian
groups. -/
abbrev moduleSectionsAsAbelianFunctor (X : RingedSite.{u, v}) (U : X)
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}] :
    ModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
      (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

/-- The derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleSectionsAsAbelianDerived (X : RingedSite.{u, v}) (U : X)
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    [IsGrothendieckAbelian.{max u v} (ModuleCat X)] :
    ModuleDerived X ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (moduleSectionsAsAbelianFunctor X U)

/-- The underived sections functor `\Gamma(U,-)` on abelian sheaves over the site underlying
`X`. -/
abbrev abelianSectionsFunctor (X : RingedSite.{u, v}) (U : X)
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}] :
    AbelianSheafCat X ⥤ AddCommGrpCat.{max u v} :=
  sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v} ⋙
    (evaluation X.carrierᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

/-- The total right derived functor of sections over `U` on abelian sheaves over the site
underlying `X`. -/
abbrev abelianSectionsDerived (X : RingedSite.{u, v}) (U : X)
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [(abelianSectionsFunctor X U).Additive]
    [IsGrothendieckAbelian.{max u v} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤ DerivedCategory AddCommGrpCat.{max u v} :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (abelianSectionsFunctor X U)

/-- The direct-image functor on abelian sheaves induced by a morphism of ringed sites. -/
abbrev abelianPushforwardFunctor {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    AbelianSheafCat X ⥤ AbelianSheafCat Y :=
  f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v}
    Y.siteTopology X.siteTopology

/-- The total right derived direct-image functor on underlying abelian sheaves. -/
abbrev abelianPushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [(abelianPushforwardFunctor f).Additive]
    [IsGrothendieckAbelian.{max u v} (AbelianSheafCat X)] :
    DerivedCategory (AbelianSheafCat X) ⥤ DerivedCategory (AbelianSheafCat Y) :=
  CategoryTheory.additiveFunctorTotalRightDerived
    (abelianPushforwardFunctor f)

section

variable (X : RingedSite.{u, v})

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [(moduleGlobalSectionsFunctor X).Additive]
variable [Functor.HasRightDerivedFunctor (moduleGlobalSectionsToDerived X) (ModuleQis X)]
variable [(abelianGlobalSectionsFunctor X).Additive]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (AbelianSheafCat X)]

-- Proof sketch: the underived global-sections functor on `\mathcal O_X`-modules is the composite
-- of the forgetful functor to abelian sheaves with global sections on abelian sheaves. Compare the
-- two total right derived functors of this composite; the induced canonical map is the one from
-- the statement, and it is an isomorphism because the same K-injective representative computes
-- both sides after forgetting module structure.
/-- Lemma 21.20.7 (1): for a ringed site `X` and `K : D(\mathcal O_X)`, the canonical comparison
map `R\Gamma(\mathcal C, K) \to R\Gamma(\mathcal C, K_{ab})` is an isomorphism in
`D(\operatorname{Ab})`. -/
theorem moduleGlobalSectionsDerived_underlyingAbelian_isomorphic
    (K : ModuleDerived X) :
    IsIsomorphic
      ((moduleGlobalSectionsDerived X).obj K)
      ((abelianGlobalSectionsDerived X).obj
        ((underlyingAbelianSheafDerived X).obj K)) := sorry

end

section

variable (X : RingedSite.{u, v})

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (AbelianSheafCat X)]

variable (U : X)
variable [(moduleSectionsAsAbelianFunctor X U).Additive]
variable [(abelianSectionsFunctor X U).Additive]

-- Proof sketch: both underived sections functors over `U` are computed by evaluation of the
-- underlying abelian presheaf at `U`; the left-hand functor first starts from module sheaves and
-- the right-hand functor first forgets to abelian sheaves. Compare their total right derived
-- functors to obtain the canonical map `R\Gamma(U, K) \to R\Gamma(U, K_{ab})`, and use the same
-- K-injective resolution argument as in the textbook to see that it is an isomorphism.
/-- Lemma 21.20.7 (2): for an object `U` of a ringed site `X` and `K : D(\mathcal O_X)`, the
canonical comparison map `R\Gamma(U, K) \to R\Gamma(U, K_{ab})` is an isomorphism in
`D(\operatorname{Ab})`. -/
theorem moduleSectionsAsAbelianDerived_underlyingAbelian_isomorphic
    (K : ModuleDerived X) :
    IsIsomorphic
      ((moduleSectionsAsAbelianDerived X U).obj K)
      ((abelianSectionsDerived X U).obj
        ((underlyingAbelianSheafDerived X).obj K)) := sorry

end

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [f.modulePushforward.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [(abelianPushforwardFunctor f).Additive]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat Y)]
variable [IsGrothendieckAbelian.{max u v} (AbelianSheafCat X)]

-- Proof sketch: underived pushforward of `\mathcal O_X`-modules followed by forgetting module
-- structure agrees with pushforward of the underlying abelian sheaf along the underlying morphism
-- of sites. Comparing the two total right derived functors yields the canonical morphism
-- `Rf_* K \to Rf_*(K_{ab})` in the derived category of abelian sheaves on `Y`, and the textbook
-- K-injective construction shows that this morphism is an isomorphism.
/-- Lemma 21.20.7 (3): for a morphism of ringed sites `f : X ⟶ Y` and `K : D(\mathcal O_X)`, the
canonical comparison map `Rf_* K \to Rf_*(K_{ab})`, viewed in the derived category of abelian
sheaves on `Y`, is an isomorphism. -/
theorem modulePushforwardDerived_underlyingAbelian_isomorphic
    (K : ModuleDerived X) :
    IsIsomorphic
      ((underlyingAbelianSheafDerived Y).obj ((modulePushforwardDerived f).obj K))
      ((abelianPushforwardDerived f).obj
        ((underlyingAbelianSheafDerived X).obj K)) := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_20_8 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "ModU" => ringedSiteModuleCategory (J.over U) (𝒪.over U)
local notation "DMod" => DerivedCategory Mod
local notation "DModU" => DerivedCategory ModU
local notation "Q" => (DerivedCategory.Q : CochainComplex Mod ℤ ⥤ DMod)
local notation "QU" => (DerivedCategory.Q : CochainComplex ModU ℤ ⥤ DModU)
local notation "Qis" => HomologicalComplex.quasiIso Mod (up ℤ)
local notation "QisU" => HomologicalComplex.quasiIso ModU (up ℤ)

private abbrev ringedSiteRingSheaf : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

variable [Abelian Mod]
variable [Abelian ModU]

/-- Extension by zero from the localized ringed site preserves finite limits. -/
private instance ringedSiteLocalizedExtensionByZero_preservesFiniteLimits :
    PreservesFiniteLimits
      (SheafOfModules.pullback (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))) := sorry

/-- Extension by zero from the localized ringed site preserves finite colimits. -/
private instance ringedSiteLocalizedExtensionByZero_preservesFiniteColimits :
    PreservesFiniteColimits
      (SheafOfModules.pullback (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))) := sorry

/-- Restriction to the localized ringed site preserves finite limits. -/
private instance ringedSiteLocalizedRestriction_preservesFiniteLimits :
    PreservesFiniteLimits
      (SheafOfModules.pushforward (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))) := sorry

/-- Restriction to the localized ringed site preserves finite colimits. -/
private instance ringedSiteLocalizedRestriction_preservesFiniteColimits :
    PreservesFiniteColimits
      (SheafOfModules.pushforward (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))) := sorry

/-- Extension by zero from the localized ringed site is additive. -/
private instance ringedSiteLocalizedExtensionByZero_additive :
    (SheafOfModules.pullback (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))).Additive := sorry

/-- Restriction to the localized ringed site is additive. -/
private instance ringedSiteLocalizedRestriction_additive :
    (SheafOfModules.pushforward (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))).Additive := sorry

/-- The functor on derived categories induced by extension by zero from the localized ringed site.
-/
noncomputable abbrev ringedSiteLocalizedExtensionByZeroDerived :
    DModU ⥤ DMod :=
  (SheafOfModules.pullback (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))).mapDerivedCategory

/-- The functor on derived categories induced by restriction to the localized ringed site. -/
noncomputable abbrev ringedSiteLocalizedRestrictionDerived :
    DMod ⥤ DModU :=
  (SheafOfModules.pushforward (𝟙 ((ringedSiteRingSheaf J 𝒪).over U))).mapDerivedCategory

-- Proof sketch: apply the module-sheaf adjunction of Lemma `18.19.2` on complexes and combine it
-- with the K-injective comparison from Lemma `21.20.1`, exactly as in the textbook proof, to
-- obtain the derived Hom-adjunction.
/-- Lemma 21.20.8: for a ringed site `(\mathcal C, \mathcal O)` and `U : \mathcal C`, the
restriction functor `D(\mathcal O) ⥤ D(\mathcal O_U)` is a right adjoint; its intended left
adjoint is the derived extension-by-zero functor from `(\mathcal C/U, \mathcal O_U)` to
`(\mathcal C, \mathcal O)`. -/
instance ringedSiteLocalizedRestrictionDerived_isRightAdjoint :
    (ringedSiteLocalizedRestrictionDerived J 𝒪 U).IsRightAdjoint := sorry

-- Proof sketch: use the same derived adjunction construction as in
-- `ringedSiteLocalizedRestrictionDerived_isRightAdjoint`, but record the adjunction on the left
-- adjoint side.
/-- The derived extension-by-zero functor from the localized ringed site is a left adjoint. -/
instance ringedSiteLocalizedExtensionByZeroDerived_isLeftAdjoint :
    (ringedSiteLocalizedExtensionByZeroDerived J 𝒪 U).IsLeftAdjoint := sorry

end

/-! ### Lemma_21_20_9 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

private abbrev localizedStructureMap :=
  (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U)

/-- The ambient category of `\mathcal O`-modules on the fixed ringed site. -/
private abbrev ambientModuleCategory :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The category of `\mathcal O_U`-modules on the localized ringed site over `U`. -/
private abbrev localizedModuleCategory :=
  SheafOfModules ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (𝒪.over U))

/-- The ambient derived category `D(\mathcal O)`. -/
private abbrev ambientDerivedCategory :=
  DerivedCategory (ambientModuleCategory J 𝒪)

/-- The localized derived category `D(\mathcal O_U)`. -/
private abbrev localizedDerivedCategory :=
  DerivedCategory (localizedModuleCategory J 𝒪 U)

/-- Restriction from the ambient ringed site to the localization at `U`. -/
private abbrev localizedRestriction :
    ambientModuleCategory J 𝒪 ⥤ localizedModuleCategory J 𝒪 U :=
  SheafOfModules.pushforward (𝟙 (localizedStructureMap J 𝒪 U))

/-- Extension by zero from the localization at `U` back to the ambient ringed site. -/
private abbrev localizedExtensionByZero :
    localizedModuleCategory J 𝒪 U ⥤ ambientModuleCategory J 𝒪 :=
  SheafOfModules.pullback (𝟙 (localizedStructureMap J 𝒪 U))

variable [CategoryWithHomology (ambientModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ambientModuleCategory J 𝒪)]
variable [MonoidalCategory (ambientModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ambientModuleCategory J 𝒪)]
variable [HasColimits (ambientModuleCategory J 𝒪)]
variable [(curriedTensor (ambientModuleCategory J 𝒪)).Additive]
variable [∀ X : ambientModuleCategory J 𝒪,
  ((curriedTensor (ambientModuleCategory J 𝒪)).obj X).Additive]
variable [∀ (X Y : CochainComplex (ambientModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor X Y (curriedTensor (ambientModuleCategory J 𝒪))]

variable [CategoryWithHomology (localizedModuleCategory J 𝒪 U)]
variable [HasCountableCoproducts (localizedModuleCategory J 𝒪 U)]
variable [MonoidalCategory (localizedModuleCategory J 𝒪 U)]
variable [MonoidalPreadditive (localizedModuleCategory J 𝒪 U)]
variable [HasColimits (localizedModuleCategory J 𝒪 U)]
variable [(curriedTensor (localizedModuleCategory J 𝒪 U)).Additive]
variable [∀ X : localizedModuleCategory J 𝒪 U,
  ((curriedTensor (localizedModuleCategory J 𝒪 U)).obj X).Additive]
variable [∀ (X Y : CochainComplex (localizedModuleCategory J 𝒪 U) ℤ),
  CochainComplex.HasMapBifunctor X Y (curriedTensor (localizedModuleCategory J 𝒪 U))]

/-- The localized category has the chosen homological structure. -/
local instance instCategoryWithHomologyLocalizedModuleCategory :
    CategoryWithHomology (localizedModuleCategory J 𝒪 U) :=
  inferInstanceAs (CategoryWithHomology (localizedModuleCategory J 𝒪 U))

/-- The localized category has countable coproducts. -/
local instance instHasCountableCoproductsLocalizedModuleCategory :
    HasCountableCoproducts (localizedModuleCategory J 𝒪 U) :=
  inferInstanceAs (HasCountableCoproducts (localizedModuleCategory J 𝒪 U))

/-- The localized category carries the chosen monoidal structure. -/
local instance instMonoidalCategoryLocalizedModuleCategory :
    MonoidalCategory (localizedModuleCategory J 𝒪 U) :=
  inferInstanceAs (MonoidalCategory (localizedModuleCategory J 𝒪 U))

/-- The localized category is monoidal preadditive. -/
local instance instMonoidalPreadditiveLocalizedModuleCategory :
    MonoidalPreadditive (localizedModuleCategory J 𝒪 U) :=
  inferInstanceAs (MonoidalPreadditive (localizedModuleCategory J 𝒪 U))

/-- The localized category has all colimits. -/
local instance instHasColimitsLocalizedModuleCategory :
    HasColimits (localizedModuleCategory J 𝒪 U) :=
  inferInstanceAs (HasColimits (localizedModuleCategory J 𝒪 U))

/-- The curried tensor functor on the localized category is additive. -/
local instance instCurriedTensorAdditiveLocalizedModuleCategory :
    (curriedTensor (localizedModuleCategory J 𝒪 U)).Additive :=
  inferInstanceAs ((curriedTensor (localizedModuleCategory J 𝒪 U)).Additive)

/-- Tensoring on the localized category is additive in the variable object. -/
local instance instTensorObjAdditiveLocalizedModuleCategory :
    ∀ X : localizedModuleCategory J 𝒪 U,
      ((curriedTensor (localizedModuleCategory J 𝒪 U)).obj X).Additive :=
  inferInstanceAs
    (∀ X : localizedModuleCategory J 𝒪 U,
      ((curriedTensor (localizedModuleCategory J 𝒪 U)).obj X).Additive)

/-- The localized tensor product admits the standard map bifunctor on cochain complexes. -/
local instance instHasMapBifunctorLocalizedModuleCategory :
    ∀ (X Y : CochainComplex (localizedModuleCategory J 𝒪 U) ℤ),
      CochainComplex.HasMapBifunctor X Y (curriedTensor (localizedModuleCategory J 𝒪 U)) :=
  inferInstanceAs
    (∀ (X Y : CochainComplex (localizedModuleCategory J 𝒪 U) ℤ),
      CochainComplex.HasMapBifunctor X Y (curriedTensor (localizedModuleCategory J 𝒪 U)))

/-- Extension by zero preserves finite limits on module sheaves. -/
local instance instPreservesFiniteLimitsJShriek :
    PreservesFiniteLimits (localizedExtensionByZero J 𝒪 U) := sorry

/-- Extension by zero preserves finite colimits on module sheaves. -/
local instance instPreservesFiniteColimitsJShriek :
    PreservesFiniteColimits (localizedExtensionByZero J 𝒪 U) := sorry

/-- Extension by zero is additive on module sheaves. -/
local instance instAdditiveJShriek :
    (localizedExtensionByZero J 𝒪 U).Additive := sorry

/-- Restriction to the localized ringed site preserves finite limits on module sheaves. -/
local instance instPreservesFiniteLimitsJStar :
    PreservesFiniteLimits (localizedRestriction J 𝒪 U) := sorry

/-- Restriction to the localized ringed site preserves finite colimits on module sheaves. -/
local instance instPreservesFiniteColimitsJStar :
    PreservesFiniteColimits (localizedRestriction J 𝒪 U) := sorry

/-- Restriction to the localized ringed site is additive on module sheaves. -/
local instance instAdditiveJStar :
    (localizedRestriction J 𝒪 U).Additive := sorry

/-- The derived tensor product endofunctor on `D(\mathcal O)` specialized to the current ringed
site. -/
private abbrev ambientDerivedTensorProduct :
    ambientDerivedCategory J 𝒪 →
      ambientDerivedCategory J 𝒪 ⥤ ambientDerivedCategory J 𝒪 :=
  show ambientDerivedCategory J 𝒪 →
      ambientDerivedCategory J 𝒪 ⥤ ambientDerivedCategory J 𝒪 from
    derivedTensorProduct

/-- The derived tensor product endofunctor on `D(\mathcal O_U)` specialized to the localized
ringed site over `U`. -/
private abbrev localizedDerivedTensorProduct :
    localizedDerivedCategory J 𝒪 U →
      localizedDerivedCategory J 𝒪 U ⥤ localizedDerivedCategory J 𝒪 U :=
  show localizedDerivedCategory J 𝒪 U →
      localizedDerivedCategory J 𝒪 U ⥤ localizedDerivedCategory J 𝒪 U from
    derivedTensorProduct

/-- The functor on derived categories induced by extension by zero. -/
private abbrev derivedLocalizedExtensionByZero :
    localizedDerivedCategory J 𝒪 U ⥤ ambientDerivedCategory J 𝒪 :=
  show localizedDerivedCategory J 𝒪 U ⥤ ambientDerivedCategory J 𝒪 from
    Functor.mapDerivedCategory (localizedExtensionByZero J 𝒪 U)

/-- The functor on derived categories induced by localization restriction. -/
private abbrev derivedLocalizedRestriction :
    ambientDerivedCategory J 𝒪 ⥤ localizedDerivedCategory J 𝒪 U :=
  show ambientDerivedCategory J 𝒪 ⥤ localizedDerivedCategory J 𝒪 U from
    Functor.mapDerivedCategory (localizedRestriction J 𝒪 U)

-- Proof sketch: represent `L` by a complex of `\mathcal O_U`-modules and `K` by a K-flat
-- complex of `\mathcal O`-modules. Apply the underived comparison isomorphism of
-- Lemma `18.27.9` degreewise to identify tensoring after `j_{U!}` with `j_{U!}` after
-- restriction and tensoring, then pass to the derived category through the chosen K-flat model
-- of `K`.
/-- Lemma 21.20.9: for a ringed site `(\mathcal C, \mathcal O)`, an object `U : \mathcal C`,
an object `L` of `D(\mathcal O_U)`, and an object `K` of `D(\mathcal O)`, derived tensoring with
`K` commutes with extension by zero from the localized ringed site:
`j_{U!}L \otimes_{\mathcal O}^{\mathbf L} K \cong
j_{U!}(L \otimes_{\mathcal O_U}^{\mathbf L} K|_U)`. -/
theorem ringedSiteLocalizedExtensionByZero_derivedTensorProduct_isIsomorphic
    (L : localizedDerivedCategory J 𝒪 U) (K : ambientDerivedCategory J 𝒪) :
    IsIsomorphic
      (((ambientDerivedTensorProduct J 𝒪 K).obj ((derivedLocalizedExtensionByZero J 𝒪 U).obj L)))
      (((derivedLocalizedExtensionByZero J 𝒪 U).obj
        ((localizedDerivedTensorProduct J 𝒪 U ((derivedLocalizedRestriction J 𝒪 U).obj K)).obj
          L))) := sorry

end

/-! ### Lemma_21_20_10 (from Chap21) -/
open CategoryTheory

/- Domain-style sampling for Lemma 21.20.10:
- primary domain: K-injective cochain complexes under exact additive adjunctions between abelian
  categories;
- inspected owner declarations:
  `CochainComplex.IsKInjective`,
  `Functor.mapHomologicalComplex`,
  `CategoryTheory.exactFunctor`,
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- best owner abstraction:
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`.

Source/core/bridge triage:
- `source-facing`: for a flat morphism of ringed sites, the direct-image functor on module sheaves
  sends K-injective cochain complexes to K-injective cochain complexes;
- `core/canonical`: a right adjoint to an exact additive left adjoint preserves K-injective
  cochain complexes;
- `bridge/view`: this item, because after abstracting away the ringed-site realization, the only
  primitive data are the adjunction `f^* ⊣ f_*` and exactness of `f^*`.

Primitive data are therefore just the exact additive left adjoint and its right adjoint; the
K-injectivity conclusion is derived API from the canonical Chapter 13 owner theorem. The former
local declaration was only a renamed shell with the same interface, so the refined file is a
direct recall of the owner declaration.
-/

/- Lemma 21.20.10: the flat ringed-site statement is exactly the Chapter 13 theorem that a right
adjoint to an exact additive left adjoint preserves K-injective cochain complexes. -/
recall right_adjoint_preserves_isKInjective_of_exact_left_adjoint

/-! ### Lemma_21_20_11 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 𝒪' : Sheaf J CommRingCat.{u}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the fixed site. -/
private abbrev ringedSiteModules (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules (ringSheaf J 𝒪)

/-- A same-site morphism of structure sheaves, written in the form expected by
`SheafOfModules.pushforward`. -/
private abbrev sameSiteStructureMap (𝒪 𝒪' : Sheaf J CommRingCat.{u}) :=
  ringSheaf J 𝒪 ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{u} J J).obj (ringSheaf J 𝒪')

-- Proof sketch: the textbook functor `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal O', -)` is
-- characterized as the right adjoint of restriction of scalars along
-- `\mathcal O \to \mathcal O'`. This declaration records that canonical adjoint on module sheaves.
/-- Restriction of scalars along a same-site morphism of sheaves of rings has its canonical right
adjoint. -/
private instance instPushforwardIsLeftAdjoint
    (p : sameSiteStructureMap 𝒪 𝒪') :
    (SheafOfModules.pushforward p).IsLeftAdjoint := sorry

/-- The coextension-of-scalars functor on module sheaves representing
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal O', -)`. -/
private abbrev changeOfRingsCoextend
    (p : sameSiteStructureMap 𝒪 𝒪') :
    ringedSiteModules 𝒪 ⥤ ringedSiteModules 𝒪' :=
  (SheafOfModules.pushforward p).rightAdjoint

-- Proof sketch: restriction of scalars on module sheaves is exact because it does not change the
-- underlying sheaf of abelian groups and only modifies the scalar action along the map of sheaves
-- of rings.
/-- Restriction of scalars along a same-site morphism of sheaves of rings is exact on module
sheaves. -/
private theorem changeOfRingsPushforward_exact
    (p : sameSiteStructureMap 𝒪 𝒪') :
    exactFunctor (ringedSiteModules 𝒪') (ringedSiteModules 𝒪)
      (SheafOfModules.pushforward p) := sorry

-- Proof sketch: apply Lemma `13.31.9` to the adjunction between restriction of scalars
-- `SheafOfModules.pushforward p` and its right adjoint `changeOfRingsCoextend p`. The exactness
-- input is `changeOfRingsPushforward_exact p`, and Lemma `18.27.8` identifies the resulting right
-- adjoint on complexes with the textbook complex
-- `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal O', \mathcal I^\bullet)`.
/-- Lemma 21.20.11: for a site, a map of sheaves of rings `\mathcal O \to \mathcal O'`, and a
K-injective complex `\mathcal I^\bullet` of `\mathcal O`-modules, the coextension-of-scalars
complex representing `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal O', \mathcal I^\bullet)` is
K-injective as a complex of `\mathcal O'`-modules. -/
theorem changeOfRingsCoextendComplex_isKInjective
    (p : sameSiteStructureMap 𝒪 𝒪')
    (I : CochainComplex (ringedSiteModules 𝒪) ℤ) [I.IsKInjective] :
    let F := changeOfRingsCoextend p
    let K :=
      ((F.mapHomologicalComplex (up ℤ)).obj I)
    CochainComplex.IsKInjective K := sorry

end
