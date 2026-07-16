import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.stacks_project.Chap21.Definition_21_17_13_Core
import StacksProject_2024.stacks_project.Chap21.Lemma_21_18_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open scoped RingedSite.Hom RingedSiteDerived RingedSiteDerivedTensor

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-
Domain-style sampling for Lemma 21.18.4:
- primary domain: compatibility between derived pullback and derived tensor product for sheaves of
  modules on a site-presented morphism of ringed topoi;
- sampled owner declarations:
  `RingedSite.Hom.pullbackTensorComparison`,
  `pullbackFunctor`,
  `pullbackToDerived`,
  `Functor.totalLeftDerived`,
  `derivedTensorProduct`,
  `Functor.leftDerivedNatTrans`,
  `CategoryTheory.CommSq`;
- best owner abstraction: the pullback side is already owned upstream in Lemma `21.18.2` by
  `ringedSiteUnderlyingStructureMap`, `pullbackFunctor`, `pullbackToDerived`, and
  the canonical Chapter 13 total-left-derived owner `Functor.totalLeftDerived PtoD QhC QisC`,
  while the tensor side is owned by `derivedTensorProduct` from Definition `21.17.13`; the public
  statement here should therefore be the source-facing isomorphism statement
  `Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L`, together with an underived comparison square for the
  fixed-right-factor route;
- primitive vs derived: the primitive data are the site-presented inverse-image functor on module
  sheaves, the Chapter 18 underived pullback-tensor comparison for that inverse image, and the
  fixed-right-factor homotopy tensor functor built from a chosen representative of a derived right
  factor; the derived API here is theorem-level, so no non-Prop comparison data is fabricated
  before the proof stage.

Source/core/bridge triage:
- `source-facing`: the pullback-tensor comparison for derived pullback on a ringed site;
- `core/canonical`: `Functor.totalLeftDerived PtoD QhC QisC`, `derivedTensorProduct`, and
  the derived-functor comparison machinery around `Functor.leftDerivedNatTrans`;
- `bridge/view`: the underived comparison square relating the source and target counits.
-/

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪)
variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
variable [(pullbackFunctor F φ).Additive]

local notation "ModC" => ringedSiteModuleCategory JC 𝒪'
local notation "ModD" => ringedSiteModuleCategory JD 𝒪
variable [CategoryWithHomology (ringedSiteModuleCategory JC 𝒪')]
variable [HasCountableCoproducts (ringedSiteModuleCategory JC 𝒪')]
variable [MonoidalCategory (ringedSiteModuleCategory JC 𝒪')]
variable [MonoidalPreadditive (ringedSiteModuleCategory JC 𝒪')]
variable [HasColimits (ringedSiteModuleCategory JC 𝒪')]
variable [CategoryWithHomology (ringedSiteModuleCategory JD 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory JD 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory JD 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory JD 𝒪)]
variable [HasColimits (ringedSiteModuleCategory JD 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory JC 𝒪')).Additive]
variable [∀ K : ringedSiteModuleCategory JC 𝒪',
  ((curriedTensor (ringedSiteModuleCategory JC 𝒪')).obj K).Additive]
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory JC 𝒪') ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory JC 𝒪'))]
variable [(curriedTensor (ringedSiteModuleCategory JD 𝒪)).Additive]
variable [∀ K : ringedSiteModuleCategory JD 𝒪,
  ((curriedTensor (ringedSiteModuleCategory JD 𝒪)).obj K).Additive]
variable [∀ (K L : CochainComplex (ringedSiteModuleCategory JD 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ringedSiteModuleCategory JD 𝒪))]

local instance : Preadditive ModC :=
  (inferInstance : Abelian ModC).toPreadditive

local instance : Preadditive ModD :=
  (inferInstance : Abelian ModD).toPreadditive

local notation "KModC" => HomotopyCategory ModC (up ℤ)
local notation "DModC" => DerivedCategory ModC
local notation "DModD" => DerivedCategory ModD
local notation "QisC" => HomotopyCategory.quasiIso ModC (up ℤ)
local notation "QhC" => (DerivedCategory.Qh : KModC ⥤ DModC)

local notation "PtoD" => (pullbackToDerived F φ : KModC ⥤ DModD)
local notation "LfStar" => (Functor.totalLeftDerived PtoD QhC QisC : DModC ⥤ DModD)

/-- One may choose the functor-level comparison of Lemma 21.18.4 so that the defining square
built from the canonical counits of `derivedTensorProduct L` and
`Functor.totalLeftDerived PtoD QhC QisC` commutes. This is the bridge/view form of the
statement; the source-facing owner remains the pointwise comparison
`leftDerivedPullback_tensorComparison`. -/
theorem leftDerivedPullback_tensor_existsComparison_commSq
    (L : DModC) :
    ∃ τ :
      derivedTensorProduct L ⋙ LfStar ⟶
        LfStar ⋙ derivedTensorProduct ((LfStar).obj L),
      ∃ σ :
        derivedTensorSourceFunctor L ⋙ LfStar ⟶
          PtoD ⋙ derivedTensorProduct ((LfStar).obj L),
        IsIso τ ∧
          CommSq
            (Functor.whiskerLeft QhC τ)
            ((Functor.associator QhC (derivedTensorProduct L) LfStar).hom ≫
              Functor.whiskerRight (derivedTensorProductCounit L) LfStar)
            ((Functor.associator QhC LfStar
                (derivedTensorProduct ((LfStar).obj L))).hom ≫
              Functor.whiskerRight
                (Functor.totalLeftDerivedCounit PtoD QhC QisC)
                (derivedTensorProduct ((LfStar).obj L)))
            σ := by
  sorry

/-- Lemma 21.18.4, source-facing pointwise form: evaluating the functor-level comparison package
at a chosen homotopy-category representative of `K` yields a comparison morphism
`Lf^*(K ⊗^L L) ⟶ Lf^* K ⊗^L Lf^* L`, and that morphism is an isomorphism. -/
@[stacks 07A4]
theorem leftDerivedPullback_tensorComparison
    (K L : DModC) :
    ∃ τ :
      (LfStar).obj (K ⊗^L L) ⟶
        (LfStar ⋙ derivedTensorProduct ((LfStar).obj L)).obj K,
      IsIso τ := by
  sorry

end

end SheafOfModules.RingedSite
