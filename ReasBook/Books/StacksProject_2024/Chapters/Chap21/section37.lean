import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_37_1 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [HasExt (Sheaf JC AddCommGrpCat.{u})]
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable {𝒪D : Sheaf JD RingCat.{u}}

-- Proof sketch: for each covering family of `U`, continuity sends it to a covering family of
-- `u(U)`, and cocontinuity identifies the iterated fibre products so that the Čech complexes for
-- `g⁻¹ ℐ` on `C` and for `ℐ` on `D` agree. Lemma `21.12.3` gives vanishing of the positive Čech
-- cohomology of `ℐ`, and Lemma `21.10.9` upgrades this to vanishing of the higher cohomology
-- groups over `U`.
/-- Lemma 21.37.1: if `u : \mathcal C \to \mathcal D` is continuous and cocontinuous, `\mathcal
O_\mathcal D` is a sheaf of rings on `\mathcal D`, and `\mathcal I` is an injective
`\mathcal O_\mathcal D`-module, then the inverse image `g^{-1}\mathcal I`, formalized on sites by
`SheafOfModules.pushforward (𝟙 ((u.sheafPushforwardContinuous RingCat JC JD).obj \mathcal
O_\mathcal D))`, has vanishing higher cohomology over every object `U : \mathcal C`. -/
theorem higherCohomology_isZero_moduleInverseImage_of_injective
    (ℐ : SheafOfModules 𝒪D) (hℐ : Injective ℐ)
    (U : C) (p : ℕ) (hp : 0 < p) :
    Limits.IsZero
      (((SheafOfModules.toSheaf
          ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj 𝒪D)).obj
        ((SheafOfModules.pushforward
            (𝟙 ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj 𝒪D))).obj ℐ)).H' p U) := sorry

end

/-! ### Lemma_21_37_2 (from Chap21) -/
open CategoryTheory
open ComplexShape
open SheafOfModules.RingedSite

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe v

section

variable {C : Type v} [Category.{v} C]
variable {D : Type v} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- The inverse-image sheaf of commutative rings `g^{-1}\mathcal O_\mathcal D` on `\mathcal C`.
-/
private abbrev inverseImageCommRingSheaf
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD CommRingCat.{v}) :
    Sheaf JC CommRingCat.{v} :=
  (u.sheafPushforwardContinuous CommRingCat.{v} JC JD).obj 𝒪D

/-- The same inverse-image structure sheaf, viewed as a `RingCat`-valued sheaf. -/
private abbrev inverseImageRingSheaf
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD CommRingCat.{v}) :
    Sheaf JC RingCat.{v} :=
  (u.sheafPushforwardContinuous RingCat.{v} JC JD).obj (ringSheaf JD 𝒪D)

/-- The source module category `\mathrm{Mod}(g^{-1}\mathcal O_\mathcal D)`. -/
private abbrev sourceModuleCat
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD CommRingCat.{v}) :=
  SheafOfModules (inverseImageRingSheaf JC JD u 𝒪D)

/-- The target module category `\mathrm{Mod}(\mathcal O_\mathcal D)`. -/
private abbrev targetModuleCat
    (JD : GrothendieckTopology D)
    (𝒪D : Sheaf JD CommRingCat.{v}) :=
  SheafOfModules (ringSheaf JD 𝒪D)

variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable (𝒪D : Sheaf JD CommRingCat.{v})

local notation "SourceModules" =>
  sourceModuleCat JC JD u 𝒪D
local notation "TargetModules" =>
  targetModuleCat JD 𝒪D
local notation "SourceDerived" =>
  DerivedCategory SourceModules
local notation "TargetDerived" =>
  DerivedCategory TargetModules
local notation "QisSource" =>
  HomotopyCategory.quasiIso SourceModules (up ℤ)
local notation "QisTarget" =>
  HomotopyCategory.quasiIso TargetModules (up ℤ)

variable
  [Abelian (sourceModuleCat JC JD u 𝒪D)]
  [CategoryWithHomology (sourceModuleCat JC JD u 𝒪D)]
  [Abelian (targetModuleCat JD 𝒪D)]
  [CategoryWithHomology (targetModuleCat JD 𝒪D)]

local instance instPreadditiveSource : Preadditive SourceModules :=
  (inferInstance : Abelian SourceModules).toPreadditive

local instance instPreadditiveTarget : Preadditive TargetModules :=
  (inferInstance : Abelian TargetModules).toPreadditive

-- Proof sketch: use Proposition `13.29.2` with the generating family of modules
-- `j_{U!}\mathcal O_U`. Lemma `18.41.1` gives the left adjoint `g_!`, Lemma `18.28.8` gives
-- enough such generators, and Lemma `21.37.1` supplies the acyclicity needed to verify the
-- adapted-generator criterion for existence of the total left derived functor.
/-- Lemma 21.37.2 (1): for the canonical lower-shriek functor
`g_! : \mathrm{Mod}(g^{-1}\mathcal O_\mathcal D) \to \mathrm{Mod}(\mathcal O_\mathcal D)`
attached to a continuous and cocontinuous functor of sites, the induced functor
`K(\mathrm{Mod}(g^{-1}\mathcal O_\mathcal D)) \to D(\mathcal O_\mathcal D)` has a total left
derived functor. -/
theorem moduleLowerShriek_hasLeftDerivedFunctor
    (gShriek : SourceModules ⥤ TargetModules)
    [Functor.Additive gShriek] :
    Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived gShriek)
      QisSource := sorry

-- Proof sketch: start from the adjunction `g_! ⊣ g^{-1}` on module sheaves from
-- Lemma `18.41.1`, then apply the general derived-adjunction theorem to any chosen left-derived
-- functor of `g_!` and any chosen right-derived functor of `g^{-1}`.
/-- Lemma 21.37.2 (2): any chosen left derived functor `Lg_!` of the canonical lower-shriek
`g_!` is left adjoint to any chosen right derived functor of the inverse-image functor
`g^* = g^{-1}`, provided the usual absolute-derived-functor hypotheses needed by
`Adjunction.derived` hold. -/
theorem derivedLowerShriek_isLeftAdjoint_of_inverseImageRightDerived
    (gShriek : SourceModules ⥤ TargetModules)
    [Functor.Additive gShriek]
    (gStar : TargetModules ⥤ SourceModules)
    [Functor.Additive gStar]
    (adj : gShriek ⊣ gStar)
    (gStarDerived : TargetDerived ⥤ SourceDerived)
    (LgShriek : SourceDerived ⥤ TargetDerived)
    (α :
      DerivedCategory.Qh ⋙ LgShriek ⟶
        mapHomotopyCategoryToDerived gShriek)
    (β :
      mapHomotopyCategoryToDerived gStar ⟶
        DerivedCategory.Qh ⋙ gStarDerived)
    [LgShriek.IsLeftDerivedFunctor α QisSource]
    [gStarDerived.IsRightDerivedFunctor β QisTarget]
    [((LgShriek ⋙ gStarDerived).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α gStarDerived) QisSource)]
    [((gStarDerived ⋙ LgShriek).IsRightDerivedFunctor
      (Functor.whiskerRight β LgShriek ≫ (Functor.associator _ _ _).hom) QisTarget)] :
    Nonempty (LgShriek ⊣ gStarDerived) := sorry

variable [HasWeakSheafify JC AddCommGrpCat.{v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [JC.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{v})]
variable [HasWeakSheafify JD AddCommGrpCat.{v}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [JD.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{v})]

-- Proof sketch: this is the generator computation from the proof of Lemma `18.41.1`. Restrict
-- `g^{-1}` to the slice site over `U`, identify the represented sections functor on
-- `j_{U!}\mathcal O_U`, and transport the adjunction to obtain the corresponding target generator
-- `j_{u(U)!}\mathcal O_{u(U)}`.
/-- Lemma 21.37.2 (3): on the standard generators `j_{U!}\mathcal O_U` of
`\mathrm{Mod}(g^{-1}\mathcal O_\mathcal D)`, the underived lower-shriek functor is canonically
isomorphic to the corresponding generator `j_{u(U)!}\mathcal O_{u(U)}` on the target site. This
is the degree-zero calculation underlying the formula `Lg_!(j_{U!}\mathcal O_U) = j_{u(U)!}
\mathcal O_{u(U)}`. -/
theorem moduleLowerShriek_obj_localizedStructureModuleExtensionByZero_iso
    (gShriek : SourceModules ⥤ TargetModules)
    (U : C) :
    Nonempty
      ((gShriek.obj
          (localizedStructureModuleExtensionByZero
            (inverseImageCommRingSheaf JC JD u 𝒪D) U)) ≅
        localizedStructureModuleExtensionByZero 𝒪D (u.obj U)) := sorry

end

/-! ### Remark_21_37_3 (from Chap21) -/
open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section

variable {DCMod : Type u₁} [Category.{v₁} DCMod]
variable {DDMod : Type u₂} [Category.{v₂} DDMod]
variable {DCAb : Type u₃} [Category.{v₃} DCAb]
variable {DDAb : Type u₄} [Category.{v₄} DDAb]

variable (forgetC : DCMod ⥤ DCAb) (forgetD : DDMod ⥤ DDAb)
variable (derivedLowerShriek : DCMod ⥤ DDMod) (derivedLowerShriekAb : DCAb ⥤ DDAb)

/-- Remark 21.37.3: in the setup of Lemma 21.37.2, even though the forget square for
`Lg_!` and `Lg_!^{Ab}` need not commute by an isomorphism, there is a natural transformation
from `Lg_!^{Ab} ∘ forget` to `forget ∘ Lg_!`. -/
def derivedLowerShriek_forget_comparison_exists : Prop :=
  Nonempty ((forgetC ⋙ derivedLowerShriekAb) ⟶ (derivedLowerShriek ⋙ forgetD))

/-- The comparison proposition is the existence of a natural transformation between the two
forgetful composites. -/
-- Proof sketch: unfold `derivedLowerShriek_forget_comparison_exists`.
theorem derivedLowerShriek_forget_comparison_exists_iff :
    derivedLowerShriek_forget_comparison_exists forgetC forgetD derivedLowerShriek
        derivedLowerShriekAb ↔
      Nonempty ((forgetC ⋙ derivedLowerShriekAb) ⟶ (derivedLowerShriek ⋙ forgetD)) := sorry

end

/-! ### Lemma_21_37_4 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace CategoryTheory

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasExt (Sheaf JC AddCommGrpCat.{u})]
variable [PreservesLimitsOfShape WalkingCospan (u.sheafPullback (Type u) JC JD)]
variable {𝒪D : Sheaf JD RingCat.{u}}

-- Proof sketch: use Lemma `21.13.5` on the underlying abelian sheaf of the inverse-image module.
-- Lemma `21.37.1` supplies the vanishing of higher cohomology over objects of `C`. For the Čech
-- exactness criterion, apply the adjunction between `u.sheafPullback (Type u) JC JD` and
-- `u.sheafPushforwardContinuous (Type u) JC JD`, use that left adjoints preserve surjections, and
-- use the pullback-preservation hypothesis to identify the iterated fibre products after applying
-- `g_!^{Sh}`. Lemma `21.14.1` gives total acyclicity of the injective module `ℐ` on `D`, so the
-- converse direction of Lemma `21.13.5` yields the desired exactness on the source site.
/-- Lemma 21.37.4: let `u : \mathcal C \to \mathcal D` be continuous and cocontinuous, let
`g : \mathit{Sh}(\mathcal C) \to \mathit{Sh}(\mathcal D)` be the associated morphism of topoi,
let `\mathcal O_\mathcal D` be a sheaf of rings on `\mathcal D`, and let `\mathcal I` be an
injective `\mathcal O_\mathcal D`-module. If the lower shriek on sheaves of sets
`g_!^{Sh}`, formalized by `u.sheafPullback (Type u) JC JD`, commutes with fibre products, then
the inverse image `g^{-1}\mathcal I`, formalized by the module-theoretic inverse-image functor
`SheafOfModules.pushforward (𝟙 ((u.sheafPushforwardContinuous RingCat JC JD).obj 𝒪D))`, is
totally acyclic. -/
theorem moduleInverseImage_isTotallyAcyclicOne_of_injective_of_sheafPullback_preserves_pullbacks
    (ℐ : SheafOfModules 𝒪D) (hℐ : Injective ℐ) :
    IsTotallyAcyclicOne
      ((SheafOfModules.toSheaf ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj 𝒪D)).obj
        ((SheafOfModules.pushforward
            (𝟙 ((u.sheafPushforwardContinuous RingCat.{u} JC JD).obj 𝒪D))).obj ℐ)) := sorry

end

end CategoryTheory

/-! ### Lemma_21_37_5 (from Chap21) -/
open CategoryTheory
open Opposite

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- The abelian category of sheaves of abelian groups on a site. -/
abbrev SiteAbelianSheafCat (J : GrothendieckTopology C) :=
  Sheaf J AddCommGrpCat.{max u v}

/-- The sections functor `\Gamma(U,-)` on abelian sheaves over a site. -/
abbrev siteAbelianSectionsFunctor (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{max u v}] :
    SiteAbelianSheafCat J ⥤ AddCommGrpCat.{max u v} :=
  sheafToPresheaf J AddCommGrpCat.{max u v} ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

/-- The chosen unbounded derived sections functor `R\Gamma(U,-)` on abelian sheaves over a site.
-/
abbrev siteAbelianSectionsDerived (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [(siteAbelianSectionsFunctor J U).Additive]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat J)] :
    DerivedCategory (SiteAbelianSheafCat J) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  additiveFunctorTotalRightDerived (siteAbelianSectionsFunctor J U)

/-- The chosen unbounded derived inverse-image functor on abelian sheaves attached to a
continuous and cocontinuous functor of sites. -/
abbrev siteAbelianInverseImageDerived
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
    [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD)]
    [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat JD)] :
    DerivedCategory (SiteAbelianSheafCat JD) ⥤
      DerivedCategory (SiteAbelianSheafCat JC) :=
  additiveFunctorTotalRightDerived
    (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD)

/-- The inverse-image ring sheaf `g^{-1}\mathcal O_\mathcal D` on `\mathcal C`. -/
abbrev inverseImageRingSheaf
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{max u v}) :
    Sheaf JC RingCat.{max u v} :=
  (u.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj 𝒪D

/-- The source module category `\mathrm{Mod}(g^{-1}\mathcal O_\mathcal D)`. -/
abbrev SourceModuleCat
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{max u v}) :=
  SheafOfModules (inverseImageRingSheaf JC JD u 𝒪D)

/-- The target module category `\mathrm{Mod}(\mathcal O_\mathcal D)`. -/
abbrev TargetModuleCat (𝒪D : Sheaf JD RingCat.{max u v}) :=
  SheafOfModules 𝒪D

/-- The inverse-image functor `g^* = g^{-1}` on module sheaves, realized by the identity map on
the inverse-image structure sheaf. -/
abbrev moduleInverseImageFunctor
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{max u v}) :
    TargetModuleCat 𝒪D ⥤ SourceModuleCat JC JD u 𝒪D :=
  SheafOfModules.pushforward
    (𝟙 (inverseImageRingSheaf JC JD u 𝒪D))

/-- The chosen derived inverse-image functor on module sheaves attached to `u`. -/
abbrev moduleInverseImageDerived
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{max u v})
    [Functor.Additive (moduleInverseImageFunctor JC JD u 𝒪D)]
    [IsGrothendieckAbelian.{max u v} (TargetModuleCat 𝒪D)] :
    DerivedCategory (TargetModuleCat 𝒪D) ⥤
      DerivedCategory (SourceModuleCat JC JD u 𝒪D) :=
  additiveFunctorTotalRightDerived
    (moduleInverseImageFunctor JC JD u 𝒪D)

/-- Sections over `U` on `g^{-1}\mathcal O_\mathcal D`-modules, viewed in abelian groups. -/
abbrev sourceModuleSectionsAsAbelianFunctor
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{max u v}) (U : C)
    [HasWeakSheafify JC AddCommGrpCat.{max u v}] :
    SourceModuleCat JC JD u 𝒪D ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf (inverseImageRingSheaf JC JD u 𝒪D) ⋙
    sheafToPresheaf JC AddCommGrpCat.{max u v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

/-- Derived sections over `U` on `g^{-1}\mathcal O_\mathcal D`-modules, viewed in
`D(\operatorname{Ab})`. -/
abbrev sourceModuleSectionsAsAbelianDerived
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (u : C ⥤ D) [Functor.IsContinuous u JC JD]
    (𝒪D : Sheaf JD RingCat.{max u v}) (U : C)
    [HasWeakSheafify JC AddCommGrpCat.{max u v}]
    [(sourceModuleSectionsAsAbelianFunctor JC JD u 𝒪D U).Additive]
    [IsGrothendieckAbelian.{max u v} (SourceModuleCat JC JD u 𝒪D)] :
    DerivedCategory (SourceModuleCat JC JD u 𝒪D) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  additiveFunctorTotalRightDerived
    (sourceModuleSectionsAsAbelianFunctor JC JD u 𝒪D U)

/-- Sections over `V` on `\mathcal O_\mathcal D`-modules, viewed in abelian groups. -/
abbrev targetModuleSectionsAsAbelianFunctor
    (𝒪D : Sheaf JD RingCat.{max u v}) (V : D)
    [HasWeakSheafify JD AddCommGrpCat.{max u v}] :
    TargetModuleCat 𝒪D ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf 𝒪D ⋙
    sheafToPresheaf JD AddCommGrpCat.{max u v} ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{max u v}).obj (op V)

/-- Derived sections over `V` on `\mathcal O_\mathcal D`-modules, viewed in
`D(\operatorname{Ab})`. -/
abbrev targetModuleSectionsAsAbelianDerived
    (𝒪D : Sheaf JD RingCat.{max u v}) (V : D)
    [HasWeakSheafify JD AddCommGrpCat.{max u v}]
    [(targetModuleSectionsAsAbelianFunctor 𝒪D V).Additive]
    [IsGrothendieckAbelian.{max u v} (TargetModuleCat 𝒪D)] :
    DerivedCategory (TargetModuleCat 𝒪D) ⥤
      DerivedCategory AddCommGrpCat.{max u v} :=
  additiveFunctorTotalRightDerived
    (targetModuleSectionsAsAbelianFunctor 𝒪D V)

section

variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable [Functor.Additive (u.sheafPushforwardContinuous AddCommGrpCat.{max u v} JC JD)]
variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat JC)]
variable [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat JD)]

-- Proof sketch: compute the chosen derived inverse image by a K-injective representative of `M`.
-- Lemma `21.37.1` gives acyclicity of inverse images of injective objects for sections over `U`,
-- so `RΓ(U,-)` of the inverse image is computed by ordinary sections. Evaluating the inverse-image
-- sheaf at `U` is the same as evaluating the original sheaf at `u(U)`, giving the comparison.
/-- Objectwise derived sections commute with inverse image on abelian sheaves for a continuous and
cocontinuous functor of sites. -/
theorem inverseImageAbelianDerived_sectionsOverObject_isomorphic
    (U : C)
    [(siteAbelianSectionsFunctor JC U).Additive]
    [(siteAbelianSectionsFunctor JD (u.obj U)).Additive]
    (M : DerivedCategory (SiteAbelianSheafCat JD)) :
    IsIsomorphic
      ((siteAbelianSectionsDerived JC U).obj
        ((siteAbelianInverseImageDerived u).obj M))
      ((siteAbelianSectionsDerived JD (u.obj U)).obj M) := sorry

end

section

variable (u : C ⥤ D) [Functor.IsContinuous u JC JD] [Functor.IsCocontinuous u JC JD]
variable (𝒪D : Sheaf JD RingCat.{max u v})
variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [Functor.Additive (moduleInverseImageFunctor JC JD u 𝒪D)]
variable [IsGrothendieckAbelian.{max u v} (SourceModuleCat JC JD u 𝒪D)]
variable [IsGrothendieckAbelian.{max u v} (TargetModuleCat 𝒪D)]

-- Proof sketch: represent `M` by a K-injective complex of `\mathcal O_\mathcal D`-modules.
-- Lemma `21.37.1` shows that inverse images of injective modules are acyclic for sections over
-- `U`, so the left-hand derived sections are computed by ordinary sections of the inverse-image
-- complex. Evaluating the inverse-image module at `U` agrees with evaluating the original complex
-- at `u(U)`, which gives the stated comparison in `D(\operatorname{Ab})`.
/-- Lemma 21.37.5: let `u : \mathcal C \to \mathcal D` be a continuous and cocontinuous functor
of sites, let `g : \mathit{Sh}(\mathcal C) \to \mathit{Sh}(\mathcal D)` be the associated
morphism of topoi, and let `\mathcal O_\mathcal C = g^{-1}\mathcal O_\mathcal D`. Then for
`U : \mathcal C` and `M : D(\mathcal O_\mathcal D)`, the derived sections of the inverse-image
complex `g^* M = g^{-1} M` over `U`, viewed in `D(\operatorname{Ab})`, are canonically
isomorphic to the derived sections of `M` over `u(U)`. This is the statement-stage form of the
textbook formula `R\Gamma(U, g^* M) = R\Gamma(u(U), M)`. -/
theorem moduleInverseImageDerived_sectionsOverObject_isomorphic
    (U : C)
    [(sourceModuleSectionsAsAbelianFunctor JC JD u 𝒪D U).Additive]
    [(targetModuleSectionsAsAbelianFunctor 𝒪D (u.obj U)).Additive]
    (M : DerivedCategory (TargetModuleCat 𝒪D)) :
    IsIsomorphic
      ((sourceModuleSectionsAsAbelianDerived JC JD u 𝒪D U).obj
        ((moduleInverseImageDerived JC JD u 𝒪D).obj M))
      ((targetModuleSectionsAsAbelianDerived 𝒪D (u.obj U)).obj M) := sorry

end

end

end CategoryTheory

/-! ### Lemma_21_37_6 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X' X Y' Y : RingedSite.{u, v}}
variable (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)

variable [f.modulePushforward.Additive]
variable [f'.modulePushforward.Additive]
variable [g.modulePullback.Additive]
variable [g'.modulePullback.Additive]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]

/-- The pullback functor on derived categories induced by an exact pullback on module sheaves. -/
private noncomputable abbrev modulePullbackDerivedOfExact
    {A B : RingedSite.{u, v}} (h : RingedSite.Hom A B)
    [h.modulePullback.Additive]
    (hexact : CategoryTheory.exactFunctor (ModuleCat B) (ModuleCat A) h.modulePullback) :
    ModuleDerived B ⥤ ModuleDerived A :=
  let _ : PreservesFiniteLimits h.modulePullback :=
    ((CategoryTheory.exactFunctor_iff h.modulePullback).mp hexact).1
  let _ : PreservesFiniteColimits h.modulePullback :=
    ((CategoryTheory.exactFunctor_iff h.modulePullback).mp hexact).2
  Functor.mapDerivedCategory h.modulePullback

-- Proof sketch: choose K-injective representatives for objects of `D(\mathcal O_\mathcal C)`.
-- Exactness of `(g')^*` lets the left composite be computed by first applying `(g')^*` on the
-- chosen representative, and the source hypothesis identifies the resulting underived composite
-- with `g^* \circ f_*`. Exactness of `g^*` then upgrades this objectwise comparison to a natural
-- isomorphism of the two derived composites.
/-- Lemma 21.37.6: for a commutative square of ringed topoi
`\xymatrix{
(\operatorname{Sh}(\mathcal C'), \mathcal O_{\mathcal C'}) \ar[r]^{g'} \ar[d]_{f'} &
(\operatorname{Sh}(\mathcal C), \mathcal O_{\mathcal C}) \ar[d]^{f} \\
(\operatorname{Sh}(\mathcal D'), \mathcal O_{\mathcal D'}) \ar[r]_{g} &
(\operatorname{Sh}(\mathcal D), \mathcal O_{\mathcal D})
}`
in the situation where the underived module square satisfies
`f'_* \circ (g')^* = g^* \circ f_*` and the pullback functors along `g` and `g'` are exact on
module sheaves, the induced derived functors satisfy the canonical functor isomorphism
`Rf'_* \circ (g')^* \cong g^* \circ Rf_*`. This is the library-facing form of the textbook
equality of functors on `D(\mathcal O_{\mathcal C})`. -/
theorem derived_pushforward_pullback_iso_of_exact_pullback_square
    (hunderived :
      g'.modulePullback ⋙ f'.modulePushforward =
        f.modulePushforward ⋙ g.modulePullback)
    (hexact_g :
      CategoryTheory.exactFunctor (ModuleCat Y) (ModuleCat Y') g.modulePullback)
    (hexact_g' :
      CategoryTheory.exactFunctor (ModuleCat X) (ModuleCat X') g'.modulePullback) :
    ∃ comparison :
      modulePullbackDerivedOfExact g' hexact_g' ⋙ modulePushforwardDerived f' ⟶
        modulePushforwardDerived f ⋙ modulePullbackDerivedOfExact g hexact_g,
      IsIso comparison := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_37_7 (from Chap21) -/
open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe w u v

namespace RingedSite.Hom

/-- Exactness of the abelian lower shriek attached to a morphism of ringed sites, expressed on the
underlying abelian-sheaf categories by the site-level functor realizing `g_!`. -/
abbrev abelianLowerShriekExact {X Y : RingedSite.{u, v}} (g : RingedSite.Hom X Y) : Prop :=
  CategoryTheory.exactFunctor
    (Sheaf X.siteTopology AddCommGrpCat.{max u v})
    (Sheaf Y.siteTopology AddCommGrpCat.{max u v})
    (g.base.sheafPushforwardContinuous AddCommGrpCat.{max u v}
      Y.siteTopology X.siteTopology)

section

variable {X' X Y' Y : RingedSite.{u, v}}
variable (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
variable (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)

variable [Functor.IsCocontinuous f.base Y.siteTopology X.siteTopology]
variable [Functor.IsCocontinuous f'.base Y'.siteTopology X'.siteTopology]
variable [Functor.IsCocontinuous g.base Y.siteTopology Y'.siteTopology]
variable [Functor.IsCocontinuous g'.base X.siteTopology X'.siteTopology]

variable [f.modulePushforward.Additive]
variable [f'.modulePushforward.Additive]
variable [g.modulePullback.Additive]
variable [g'.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]

-- Proof sketch: use Lemma `18.41.3 (1)` to identify the underived composites
-- `(g')^* ⋙ (f')_*` and `f_* ⋙ g^*` on module sheaves. Then apply the bounded-below
-- right-derived-functor formalism to a bounded-below object. Under the source hypotheses, the
-- derived pullbacks along `g` and `g'` compute the ordinary inverse-image functors on such
-- objects.
/-- Lemma 21.37.7 (1): for a commutative square of ringed topoi presented by ringed-site morphisms
`g'`, `f'`, `f`, and `g` as in `18.41.3`, the bounded-below derived functors satisfy the base
change isomorphism
`Rf'_* \circ (g')^* K \cong g^* \circ Rf_* K`
for every bounded-below object `K` of `D(\mathcal O_\mathcal C)`. This is the objectwise form of
the textbook equality of functors on `D^+(\mathcal O_\mathcal C)`. -/
theorem boundedBelow_derived_pushforward_pullback_object_isomorphic
    (hcomm : g.base ⋙ f'.base = f.base ⋙ g'.base)
    (hcofinal : ∀ V : X,
      Functor.Final
        (CostructuredArrow.map₂ (eqToHom hcomm) (𝟙 (g'.base.obj V))))
    (hO_g :
      Y.structureSheaf =
        (g.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology Y'.siteTopology).obj Y'.structureSheaf)
    (hO_g' :
      X.structureSheaf =
        (g'.base.sheafPushforwardContinuous RingCat.{max u v}
          X.siteTopology X'.siteTopology).obj X'.structureSheaf)
    (hg : g.structureSheafMap = eqToHom hO_g)
    (hg' : g'.structureSheafMap = eqToHom hO_g')
    (K : ModuleDerived X)
    (hbounded : ∃ n : ℤ, K.IsGE n) :
    IsIsomorphic
      ((modulePushforwardDerived f').obj ((modulePullbackDerived g').obj K))
      ((modulePullbackDerived g).obj ((modulePushforwardDerived f).obj K)) := sorry

-- Proof sketch: compute `Rf_*` and `R(f')_*` on K-injective representatives. The additional
-- exactness hypothesis on `g'_!` is the source condition used to ensure that the pullback along
-- `g'` preserves K-injective representatives on the underlying abelian-sheaf categories, so the
-- underived base-change equality from Lemma `18.41.3 (1)` upgrades to the unbounded derived
-- categories.
/-- Lemma 21.37.7 (2): with the same square and hypotheses as in clause (1), if the abelian lower
shriek `g'_! : \mathrm{Ab}(\mathcal C') \to \mathrm{Ab}(\mathcal C)` is exact, then the same base
change comparison holds on the unbounded derived categories. In the library-facing formulation,
this is the unbounded isomorphism
`Rf'_* \circ L(g')^* \cong Lg^* \circ Rf_*`,
which agrees with the textbook statement because the horizontal pullbacks are exact in this
site-presented situation. -/
theorem unbounded_derived_pushforward_pullback_square_iso_of_exact_abelian_lowerShriek
    (hcomm : g.base ⋙ f'.base = f.base ⋙ g'.base)
    (hcofinal : ∀ V : X,
      Functor.Final
        (CostructuredArrow.map₂ (eqToHom hcomm) (𝟙 (g'.base.obj V))))
    (hO_g :
      Y.structureSheaf =
        (g.base.sheafPushforwardContinuous RingCat.{max u v}
          Y.siteTopology Y'.siteTopology).obj Y'.structureSheaf)
    (hO_g' :
      X.structureSheaf =
        (g'.base.sheafPushforwardContinuous RingCat.{max u v}
          X.siteTopology X'.siteTopology).obj X'.structureSheaf)
    (hg : g.structureSheafMap = eqToHom hO_g)
    (hg' : g'.structureSheafMap = eqToHom hO_g')
    (hexact_g'_shriek : abelianLowerShriekExact g') :
    IsIsomorphic
      (modulePullbackDerived g' ⋙ modulePushforwardDerived f')
      (modulePushforwardDerived f ⋙ modulePullbackDerived g) := sorry

end

end RingedSite.Hom
