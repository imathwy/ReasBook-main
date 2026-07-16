import StacksProject_2024.stacks_project.Chap17.Lemma_17_6_3
import StacksProject_2024.stacks_project.Chap18.Lemma_18_14_2
import StacksProject_2024.stacks_project.Chap20.«20_11_0_1»
import StacksProject_2024.stacks_project.Chap20.Lemma_20_34_4

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open ClosedSubsetSectionsWithSupport
open scoped RingedSpaceClosedSubsetDerived
open scoped RingedSpaceClosedSubsetSectionsWithSupport
open scoped RingedSpaceClosedSubsetGlobalSectionsWithSupport

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology (TopCat.of Z)).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u} (X.Sheaf AddCommGrpCat.{u})]
variable [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} (TopCat.closedSubsetInclusion X Z)).Additive]

local instance : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  HasSheafify.isRightAdjoint

local instance : HasWeakSheafify (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u} :=
  HasSheafify.isRightAdjoint

private instance sheafToPresheaf_additive :
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive := by
  constructor
  intro F G f g
  ext U x
  rfl

private instance abelianPresheafLimit_additive :
    (lim : ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).Additive := by
  constructor
  intro F G f g
  apply limit.hom_ext
  intro j
  change limMap (f + g) ≫ limit.π G j = (limMap f + limMap g) ≫ limit.π G j
  rw [limMap_π, Preadditive.add_comp, limMap_π, limMap_π]
  simp

private instance sheafGlobalSections_additive :
    (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive := by
  exact Functor.additive_of_iso
    (Sheaf.ΓNatIsoLim (Opens.grothendieckTopology X) AddCommGrpCat.{u}).symm

/- Internal helper: the derived sections-with-support functor on abelian sheaves over a
topological space. -/
end

end TopCat.Sheaf

namespace AlgebraicGeometry.RingedSpace


open TopCat.Sheaf

section

variable {X : RingedSpace.{u}} {Z : Set X} (hZ : IsClosed Z)
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology (TopCat.of Z)).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u} (RingedSpace.Modules X)]
variable [IsGrothendieckAbelian.{u} (X.carrier.Sheaf AddCommGrpCat.{u})]
variable [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} (X.closedSubsetInclusion Z)).Additive]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "ModX" => RingedSpace.Modules X
local notation "ModZ" => RingedSpace.closedSubsetModuleCategory X Z
local notation "DModZ" => closedSubsetModuleDerived X Z
local notation "QModX" => (DerivedCategory.Q : CochainComplex ModX ℤ ⥤ DModX)
local notation "QModZ" => (DerivedCategory.Q : CochainComplex ModZ ℤ ⥤ DModZ)
local notation "QisModX" => HomologicalComplex.quasiIso ModX (ComplexShape.up ℤ)

private abbrev QAb :
    CochainComplex AddCommGrpCat.{u} ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  DerivedCategory.Q

attribute [local instance]
  moduleUnderlyingSheaf_preservesFiniteLimits
  moduleUnderlyingSheaf_preservesFiniteColimits
  closedSubsetModuleUnderlyingSheaf_preservesFiniteLimits
  closedSubsetModuleUnderlyingSheaf_preservesFiniteColimits

local instance : Functor.IsRightAdjoint ((𝓗[hZ] : ModX ⥤ ModZ)) :=
  (RingedSpace.ClosedSubsetSectionsWithSupport.pushforwardSectionsWithSupportAdjunction hZ).isRightAdjoint

local instance : ((𝓗[hZ] : ModX ⥤ ModZ)).Additive := inferInstance
local instance : ((𝓗[hZ] : ModX ⥤ ModZ)).PreservesZeroMorphisms := inferInstance
local instance : (Γ_[hZ] : ModX ⥤ ModuleCat (globalSectionsRing X)).Additive := inferInstance
local instance :
    (Γ_[hZ] : ModX ⥤ ModuleCat (globalSectionsRing X)).PreservesZeroMorphisms := inferInstance
local instance :
    (closedSubsetSectionsWithSupportFunctor hZ :
      X.carrier.Sheaf AddCommGrpCat.{u} ⥤ (TopCat.of Z).Sheaf AddCommGrpCat.{u}).Additive := by
  let adj := closedSubset_pushforwardSectionsWithSupportAdjunction hZ
  exact adj.right_adjoint_additive

local instance :
    (closedSubsetSectionsWithSupportFunctor hZ :
      X.carrier.Sheaf AddCommGrpCat.{u} ⥤ (TopCat.of Z).Sheaf AddCommGrpCat.{u}).PreservesZeroMorphisms :=
  inferInstance

/- Domain-style sampling for Lemma 20.34.8:
- primary domain: derived local cohomology for `\mathcal O_X`-modules and its comparison with the
  corresponding derived functors on underlying abelian sheaves;
- sampled owner declarations:
  `moduleUnderlyingSheaf`,
  `closedSubsetModuleUnderlyingSheaf`,
  `closedSubsetModuleSectionsWithSupportDerived`,
  `closedSubsetModuleGlobalSectionsWithSupportDerived X Z hZ`,
  the exact forgetful functor owners `moduleUnderlyingSheaf`, `closedSubsetModuleUnderlyingSheaf`,
  and the canonical abelian-sheaf total right derived composites built from
  `closedSubsetSectionsWithSupportFunctor hZ`, `TopCat.Sheaf.pushforward`, and `Sheaf.Γ`;
- best owner abstraction:
  `core/canonical`: the module-side Chapter 20 owners
    `closedSubsetModuleSectionsWithSupportDerived`,
    `closedSubsetModuleGlobalSectionsWithSupportDerived X Z hZ`, together with the exact
    forgetful functor owners `moduleUnderlyingSheaf` and `closedSubsetModuleUnderlyingSheaf`;
  `bridge/view`: this file compares those owners after forgetting module structure to abelian
    sheaves, with the abelian-sheaf derived composites kept internal because they are used only to
    formulate the comparison morphisms.

Primitive data are just the closed subset `Z`, the module-side derived owners, the corresponding
abelian-sheaf derived composites, and the exact forgetful bridges. The public output should
therefore be only the comparison isomorphism statements below, not a second owner for the
abelian derived functors.

Source/core/bridge triage:
- `source-facing`: the textbook claim that local cohomology with support is unchanged after
  forgetting module structure to abelian sheaves;
- `core/canonical`: the existing owners listed above;
- `bridge/view`: the functor-level comparisons below, which compare the module-side and
  abelian-side derived functors via those owners. -/

private abbrev closedSubsetModuleSectionsWithSupportToDerived
    (hZ : IsClosed Z) :
    CochainComplex ModX ℤ ⥤ DModZ :=
  let F : ModX ⥤ ModZ := 𝓗[hZ]
  F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QModZ

private instance closedSubsetModuleSectionsWithSupportToDerived_hasRightDerivedFunctor :
    (closedSubsetModuleSectionsWithSupportToDerived hZ).HasRightDerivedFunctor QisModX :=
  CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
    ((𝓗[hZ] : ModX ⥤ ModZ))

private instance closedSubsetSectionsWithSupportToDerived_hasRightDerivedFunctor :
    (((closedSubsetSectionsWithSupportFunctor hZ).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
      (DerivedCategory.Q :
        CochainComplex ((TopCat.of Z).Sheaf AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory ((TopCat.of Z).Sheaf AddCommGrpCat.{u}))).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso
        (X.carrier.Sheaf AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) :=
  CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
    (closedSubsetSectionsWithSupportFunctor hZ)

private abbrev closedSubsetSheafGlobalSectionsWithSupportFunctor
    (hZ : IsClosed Z) :
    X.carrier.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  closedSubsetSectionsWithSupportFunctor hZ ⋙
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (X.closedSubsetInclusion Z) ⋙
    Sheaf.Γ (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}

local instance closedSubsetSheafGlobalSectionsWithSupportFunctor_additive :
    (closedSubsetSheafGlobalSectionsWithSupportFunctor hZ).Additive := by
  let H :
      X.carrier.Sheaf AddCommGrpCat.{u} ⥤ (TopCat.of Z).Sheaf AddCommGrpCat.{u} :=
    closedSubsetSectionsWithSupportFunctor hZ
  let P : (TopCat.of Z).Sheaf AddCommGrpCat.{u} ⥤ X.carrier.Sheaf AddCommGrpCat.{u} :=
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} (X.closedSubsetInclusion Z)
  let G : X.carrier.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    Sheaf.Γ (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}
  letI : H.Additive := inferInstance
  letI : P.Additive := inferInstance
  letI : G.Additive := sheafGlobalSections_additive
  change (H ⋙ P ⋙ G).Additive
  infer_instance

local instance closedSubsetSheafGlobalSectionsWithSupportFunctor_preservesZeroMorphisms :
    (closedSubsetSheafGlobalSectionsWithSupportFunctor hZ).PreservesZeroMorphisms := by
  let _ : (closedSubsetSheafGlobalSectionsWithSupportFunctor hZ).Additive := inferInstance
  dsimp [closedSubsetSheafGlobalSectionsWithSupportFunctor]
  infer_instance

private abbrev closedSubsetModuleGlobalSectionsWithSupportToDerived
    (hZ : IsClosed Z) :
    CochainComplex ModX ℤ ⥤
      DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  let F : ModX ⥤ ModuleCat (globalSectionsRing X) := Γ_[hZ]
  F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

private instance closedSubsetModuleGlobalSectionsWithSupportToDerived_hasRightDerivedFunctor :
    (closedSubsetModuleGlobalSectionsWithSupportToDerived hZ).HasRightDerivedFunctor QisModX :=
  CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
    Γ_[hZ]

private instance closedSubsetSheafGlobalSectionsWithSupportToDerived_hasRightDerivedFunctor :
    (((closedSubsetSheafGlobalSectionsWithSupportFunctor hZ).mapHomologicalComplex
        (ComplexShape.up ℤ)) ⋙
      QAb).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso
        (X.carrier.Sheaf AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) :=
  CategoryTheory.mapHomologicalComplexQ_hasRightDerivedFunctor
    (closedSubsetSheafGlobalSectionsWithSupportFunctor hZ)

-- Proof sketch: for `RΓ_Z(X,-)`, compare the distinguished triangles of Lemmas `20.34.5` for
-- module sheaves and for underlying abelian sheaves, and use Lemma `20.32.7` on the ordinary
-- derived global-sections terms together with the two-out-of-three principle from Derived
-- Categories, Lemma `13.4.3`. For `R\mathcal H_Z`, repeat the same comparison on the closed
-- subset itself.
/-- Functor-level companion to Lemma 20.34.8, sections-with-support part: after forgetting
`𝒪_X`-module structure, the module-side derived sections-with-support functor is canonically
isomorphic to the abelian-sheaf derived sections-with-support functor. -/
theorem closedSubsetModuleSectionsWithSupportDerived_underlyingAbelian_functor_isomorphic :
    IsIsomorphic
      ((R𝓗[hZ]) ⋙ (closedSubsetModuleUnderlyingSheaf X Z).mapDerivedCategory)
      ((moduleUnderlyingSheaf X).mapDerivedCategory ⋙
        additiveFunctorTotalRightDerived (closedSubsetSectionsWithSupportFunctor hZ)) := by
  sorry

/-- Lemma 20.34.8, sections-with-support part: after forgetting `𝒪_X`-module structure, the
derived sections with support of `K` are canonically isomorphic to the derived sections with
support of the underlying abelian sheaf of `K`. -/
@[stacks 0G74]
theorem closedSubsetModuleSectionsWithSupportDerived_underlyingAbelian_isomorphic
    (K : DModX) :
    IsIsomorphic
      (((R𝓗[hZ]) ⋙ (closedSubsetModuleUnderlyingSheaf X Z).mapDerivedCategory).obj K)
      (((moduleUnderlyingSheaf X).mapDerivedCategory ⋙
        additiveFunctorTotalRightDerived (closedSubsetSectionsWithSupportFunctor hZ)).obj K) := by
  rcases closedSubsetModuleSectionsWithSupportDerived_underlyingAbelian_functor_isomorphic hZ
      with ⟨e⟩
  exact ⟨e.app K⟩

/-- Functor-level companion to Lemma 20.34.8, supported-global-sections part: after forgetting
`𝒪_X`-module structure, the module-side derived supported-global-sections functor is canonically
isomorphic to the corresponding abelian-sheaf derived functor. -/
theorem closedSubsetModuleGlobalSectionsWithSupportDerived_underlyingAbelian_functor_isomorphic :
    IsIsomorphic
      (RΓ_[hZ] ⋙ (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory)
      ((moduleUnderlyingSheaf X).mapDerivedCategory ⋙
        additiveFunctorTotalRightDerived
          (closedSubsetSectionsWithSupportFunctor hZ ⋙
            TopCat.Sheaf.pushforward AddCommGrpCat.{u} (X.closedSubsetInclusion Z) ⋙
            Sheaf.Γ (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})) := by
  sorry

/-- Lemma 20.34.8, supported-global-sections part: after forgetting `𝒪_X`-module structure, the
derived supported global sections of `K` are canonically isomorphic to the derived supported
global sections of the underlying abelian sheaf of `K`. -/
@[stacks 0G74]
theorem closedSubsetModuleGlobalSectionsWithSupportDerived_underlyingAbelian_isomorphic
    (K : DModX) :
    IsIsomorphic
      ((RΓ_[hZ] ⋙
        (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory).obj K)
      (((moduleUnderlyingSheaf X).mapDerivedCategory ⋙
        additiveFunctorTotalRightDerived
          (closedSubsetSectionsWithSupportFunctor hZ ⋙
            TopCat.Sheaf.pushforward AddCommGrpCat.{u} (X.closedSubsetInclusion Z) ⋙
            Sheaf.Γ (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})).obj K) := by
  rcases closedSubsetModuleGlobalSectionsWithSupportDerived_underlyingAbelian_functor_isomorphic hZ
      with ⟨e⟩
  exact ⟨e.app K⟩

end

end AlgebraicGeometry.RingedSpace
