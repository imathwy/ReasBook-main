import StacksProject_2024.stacks_project.Chap21.Lemma_21_18_2

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
variable [JE.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JE AddCommGrpCat.{u}]
variable [JE.WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Lemma 21.18.3:
- primary domain: iterated inverse-image functors on homotopy and derived categories of module
  sheaves on site-presented composite morphisms of ringed topoi;
- inspected owner declarations:
  `ringedSiteUnderlyingStructureMap`,
  `pullbackFunctor`,
  `pullbackToDerived`,
  `pullbackToDerived_hasLeftDerivedFunctor`,
  `AlgebraicGeometry.RingedSpace.modulePullbackDerivedCompIso`;
- best owner abstraction: the only `bridge/view` datum local to this file is the composite
  structure map determined by `φ` and `ψ`; the derived existence statement itself is already owned
  upstream by `pullbackToDerived_hasLeftDerivedFunctor`, specialized to `F ⋙ G` and that
  composite structure map;
- primitive data: the two site-presented structure morphisms attached to `φ` and `ψ`;
- derived API: direct reuse of the canonical Chapter 21 owners `pullbackToDerived` and
  `pullbackToDerived_hasLeftDerivedFunctor`, with no parallel composite-specific alias.

Source/core/bridge triage:
- `source-facing`: the composite site morphism `F ⋙ G` equipped with the induced structure map;
- `core/canonical`: `pullbackFunctor`, `pullbackToDerived`, and
  `pullbackToDerived_hasLeftDerivedFunctor`;
- `bridge/view`: the composite structure map below. -/

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable (G : D ⥤ E) [Functor.IsContinuous G JD JE]
variable {𝒪C : Sheaf JC CommRingCat.{u}}
variable {𝒪D : Sheaf JD CommRingCat.{u}}
variable {𝒪E : Sheaf JE CommRingCat.{u}}
variable (φ : 𝒪C ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪D)
variable (ψ : 𝒪D ⟶ (G.sheafPushforwardContinuous CommRingCat.{u} JD JE).obj 𝒪E)
variable [Functor.IsContinuous (F ⋙ G) JC JE]

private abbrev compositeStructureMap :
    𝒪C ⟶ ((F ⋙ G).sheafPushforwardContinuous CommRingCat.{u} JC JE).obj 𝒪E :=
  φ ≫
    (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).map ψ ≫
      (Functor.sheafPushforwardContinuousComp'
        (Iso.refl (F ⋙ G))
        CommRingCat.{u}
        JC
        JD
        JE).hom.app 𝒪E

variable [(SheafOfModules.pushforward
  (ringedSiteUnderlyingStructureMap (F ⋙ G) (compositeStructureMap F G φ ψ))).IsRightAdjoint]
variable [Abelian (ringedSiteModuleCategory JC 𝒪C)]
variable [CategoryWithHomology (ringedSiteModuleCategory JC 𝒪C)]
variable [Abelian (ringedSiteModuleCategory JE 𝒪E)]
variable [CategoryWithHomology (ringedSiteModuleCategory JE 𝒪E)]
variable [MonoidalCategory (ringedSiteModuleCategory JC 𝒪C)]
variable [MonoidalPreadditive (ringedSiteModuleCategory JC 𝒪C)]
variable [MonoidalCategory (ringedSiteModuleCategory JE 𝒪E)]
variable [MonoidalPreadditive (ringedSiteModuleCategory JE 𝒪E)]
variable [(pullbackFunctor (F ⋙ G) (compositeStructureMap F G φ ψ)).Additive]

local notation "ModC" => ringedSiteModuleCategory JC 𝒪C
local notation "QisC" => HomotopyCategory.quasiIso ModC (up ℤ)

/- Lemma 21.18.3: for the composite site-presented morphism `F ⋙ G` with induced composite
structure map `compositeStructureMap F G φ ψ`, the homotopy-category pullback-to-derived functor
admits a total left derived functor. This is exactly the Chapter 21 `HasLeftDerivedFunctor`
instance from Lemma `21.18.2`, specialized to `F ⋙ G` and
`compositeStructureMap F G φ ψ`, so no separate composite-specific alias is introduced here. -/
#check
  (inferInstance :
    Functor.HasLeftDerivedFunctor
      (pullbackToDerived (F ⋙ G) (compositeStructureMap F G φ ψ))
      QisC)

end

end SheafOfModules.RingedSite
