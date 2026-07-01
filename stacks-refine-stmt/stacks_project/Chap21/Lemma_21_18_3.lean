import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C]
variable {D : Type u} [Category.{u} D]
variable {E : Type u} [Category.{u} E]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D} {JE : GrothendieckTopology E}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JE.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JE AddCommGrpCat.{u}]
variable [JE.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on a site with structure sheaf
`\mathcal O`. -/
abbrev RingedSiteModules {X : Type u} [Category.{u} X]
    (J : GrothendieckTopology X) (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of module sheaves on a ringed site. -/
abbrev RingedSiteDerived {X : Type u} [Category.{u} X]
    (J : GrothendieckTopology X) (𝒪 : Sheaf J CommRingCat.{u}) :=
  DerivedCategory (RingedSiteModules J 𝒪)

/-- The quasi-isomorphisms in the homotopy category of cochain complexes of `\mathcal O`-modules.
-/
abbrev RingedSiteQis {X : Type u} [Category.{u} X]
    (J : GrothendieckTopology X) (𝒪 : Sheaf J CommRingCat.{u}) :=
  HomotopyCategory.quasiIso (RingedSiteModules J 𝒪) (up ℤ)

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable (G : D ⥤ E) [Functor.IsContinuous G JD JE]
variable {𝒪C : Sheaf JC CommRingCat.{u}}
variable {𝒪D : Sheaf JD CommRingCat.{u}}
variable {𝒪E : Sheaf JE CommRingCat.{u}}
variable (φ : 𝒪C ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)
variable (ψ : 𝒪D ⟶ (G.sheafPushforwardContinuous CommRingCat.{u} JD JE).obj 𝒪E)

/-- The underlying `RingCat`-valued structure map attached to the site-presented morphism of
ringed topoi determined by `φ`. -/
abbrev ringedSiteUnderlyingStructureMap
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪C ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D) :
    (sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪C ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JC JD).obj
        ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪D) :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap G ψ)).IsRightAdjoint]

/-- The inverse-image functor on module sheaves attached to the site-presented morphism of ringed
topoi determined by `φ`. -/
abbrev pullbackFunctor
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (φ : 𝒪C ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D) :
    RingedSiteModules JC 𝒪C ⥤ RingedSiteModules JD 𝒪D :=
  SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)

variable [Abelian (RingedSiteModules JC 𝒪C)]
variable [CategoryWithHomology (RingedSiteModules JC 𝒪C)]
variable [Abelian (RingedSiteModules JD 𝒪D)]
variable [CategoryWithHomology (RingedSiteModules JD 𝒪D)]
variable [Abelian (RingedSiteModules JE 𝒪E)]
variable [CategoryWithHomology (RingedSiteModules JE 𝒪E)]

local instance instPreadditiveModulesJC : Preadditive (RingedSiteModules JC 𝒪C) :=
  (inferInstance : Abelian (RingedSiteModules JC 𝒪C)).toPreadditive

local instance instPreadditiveModulesJD : Preadditive (RingedSiteModules JD 𝒪D) :=
  (inferInstance : Abelian (RingedSiteModules JD 𝒪D)).toPreadditive

local instance instPreadditiveModulesJE : Preadditive (RingedSiteModules JE 𝒪E) :=
  (inferInstance : Abelian (RingedSiteModules JE 𝒪E)).toPreadditive

/-- The homotopy-to-derived functor obtained by first pulling back along `F` on homotopy
categories and then applying the underived pullback-to-derived functor for `G`. -/
private abbrev compositeUnderivedPullbackToDerived
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    (G : D ⥤ E) [Functor.IsContinuous G JD JE]
    (φ : 𝒪C ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)
    (ψ : 𝒪D ⟶ (G.sheafPushforwardContinuous CommRingCat.{u} JD JE).obj 𝒪E)
    [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
    [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap G ψ)).IsRightAdjoint]
    [(pullbackFunctor F φ).Additive]
    [(pullbackFunctor G ψ).Additive] :
    HomotopyCategory (RingedSiteModules JC 𝒪C) (up ℤ) ⥤
      DerivedCategory (RingedSiteModules JE 𝒪E) :=
  let FH :
      HomotopyCategory (RingedSiteModules JC 𝒪C) (up ℤ) ⥤
        HomotopyCategory (RingedSiteModules JD 𝒪D) (up ℤ) :=
    (pullbackFunctor F φ).mapHomotopyCategory (up ℤ)
  let GH :
      HomotopyCategory (RingedSiteModules JD 𝒪D) (up ℤ) ⥤
        HomotopyCategory (RingedSiteModules JE 𝒪E) (up ℤ) :=
    (pullbackFunctor G ψ).mapHomotopyCategory (up ℤ)
  FH ⋙ GH ⋙ DerivedCategory.Qh

variable [(pullbackFunctor F φ).Additive]
variable [(pullbackFunctor G ψ).Additive]

-- Proof sketch: apply the general composition comparison for total left derived functors from
-- Lemma `21.17.11` to resolve by K-flat complexes with flat terms, then pull those resolutions
-- back successively using Lemma `21.18.1`. This shows that the composite underived pullback
-- already computes the iterated derived pullback, so it admits a total left derived functor.
/-- Lemma 21.18.3: the composite underived pullback-to-derived functor attached to two composable
site-presented morphisms of ringed topoi admits a total left derived functor. This is the
statement-stage core underlying the identity `Lf^* \circ Lg^* = L(g \circ f)^*`. -/
theorem compositeUnderivedPullbackToDerived_hasLeftDerivedFunctor :
    CategoryTheory.Functor.HasRightKanExtension
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSiteModules JC 𝒪C) (up ℤ) ⥤
          DerivedCategory (RingedSiteModules JC 𝒪C))
      (compositeUnderivedPullbackToDerived F G φ ψ)
      := sorry

end
end RingedSite
end SheafOfModules
