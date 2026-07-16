import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.stacks_project.Chap13.Situation_13_15_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_28_1
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory
import StacksProject_2024.stacks_project.Chap21.«21_18_0_1»
import StacksProject_2024.stacks_project.Chap21.Lemma_21_19_1_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open scoped RingedSite.Hom

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

/- Domain-style sampling for Lemma 21.18.2:
- primary domain: total left derived functors on homotopy categories of complexes of sheaves of
  modules on ringed sites;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `ringSheaf`,
  `mapHomotopyCategoryToDerived`,
  `Functor.HasLeftDerivedFunctor`,
  `RingedSite.Hom.modulePullbackToDerived`;
- best owner abstraction: the ambient module category is the Chapter 18 owner
  `ringedSiteModuleCategory J 𝒪`, while the theorem itself should be stated directly in the
  Chapter 13 total-left-derived owner API for `mapHomotopyCategoryToDerived`;
- primitive vs derived: the primitive data are the site-presented `RingCat`-valued structure map
  and the induced pullback functor on module sheaves, now owned by the upstream Chapter 21 bridge
  file `21_18_0_1`. The derived-existence statement belongs to `Functor.HasLeftDerivedFunctor`;
  bundled derived pullback data should be reused from stronger canonical owners such as
  `RingedSite.Hom.modulePullbackDerived`, not re-exported here from a sorry-backed existence proof.

Source/core/bridge triage:
- `source-facing`: the derived inverse-image functor attached to a site-presented morphism of
  ringed topoi;
- `core/canonical`: `ringedSiteModuleCategory`, `pullbackFunctor`,
  `mapHomotopyCategoryToDerived`, `Functor.HasLeftDerivedFunctor`, and, in same-site
  specializations, `RingedSite.Hom.modulePullbackToDerived`;
- `bridge/view`: `ringedSiteUnderlyingStructureMap`, now defined upstream in `21_18_0_1`, and
  the induced module-sheaf pullback owner `pullbackFunctor`. -/

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪)
variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]

local notation "ModC" => ringedSiteModuleCategory JC 𝒪'
local notation "ModD" => ringedSiteModuleCategory JD 𝒪
local notation "KModC" => HomotopyCategory ModC (up ℤ)
local notation "DModD" => DerivedCategory ModD
local notation "QisC" => HomotopyCategory.quasiIso ModC (up ℤ)

local instance instPreadditiveModC : Preadditive ModC :=
  (inferInstance : Abelian ModC).toPreadditive

local instance instPreadditiveModD : Preadditive ModD :=
  (inferInstance : Abelian ModD).toPreadditive

/-- The functor on homotopy categories induced by pullback of module sheaves for the
site-presented morphism of ringed topoi determined by `φ`, followed by passage to the derived
category. -/
abbrev pullbackToDerived
    [(pullbackFunctor F φ).Additive] :
    KModC ⥤ DModD :=
  mapHomotopyCategoryToDerived (pullbackFunctor F φ)
/-- Lemma 21.18.2: the pullback functor on homotopy categories of module sheaves associated to a
site-presented morphism of ringed topoi admits a total left derived functor, giving the
unbounded derived pullback `Lf^* : D(𝒪') ⥤ D(𝒪)`. -/
-- Proof sketch: apply Lemma `13.14.15` to the class of quasi-isomorphisms in the homotopy
-- category. Lemma `21.17.11` provides enough K-flat complexes with flat terms, while
-- Lemmas `21.18.1` and `21.17.12` show that pullback sends quasi-isomorphisms between those
-- chosen resolutions to quasi-isomorphisms.
@[stacks 06YY]
theorem pullbackToDerived_hasLeftDerivedFunctor
    [(pullbackFunctor F φ).Additive] :
    Functor.HasLeftDerivedFunctor
      (pullbackToDerived F φ)
      QisC := sorry

instance instPullbackToDerivedHasLeftDerivedFunctor
    [(pullbackFunctor F φ).Additive] :
    Functor.HasLeftDerivedFunctor
      (pullbackToDerived F φ)
      QisC :=
  pullbackToDerived_hasLeftDerivedFunctor F φ

end

section SameSite

open RingedSite.Hom

variable {C : Type u} [Category.{u} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 𝒪' : Sheaf J CommRingCat.{u}} (α : 𝒪 ⟶ 𝒪')

local notation "X" => RingedSite.ofCommRingSheaf J 𝒪

/-- The same-site specialization of Lemma `21.18.2` on the canonical Chapter 21 owner
`RingedSite.Hom.modulePullbackToDerived (sameSiteHom α)`. -/
theorem sameSiteModulePullbackToDerived_hasLeftDerivedFunctor :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived (sameSiteHom α)) (ModuleQis X) := by
  simpa [modulePullbackToDerived, sameSiteHom, pullbackToDerived, pullbackFunctor,
    ringedSiteStructureMap, mapHomotopyCategoryToDerived] using
    (pullbackToDerived_hasLeftDerivedFunctor (𝟭 C) α :
      Functor.HasLeftDerivedFunctor (pullbackToDerived (𝟭 C) α)
        (HomotopyCategory.quasiIso (ringedSiteModuleCategory J 𝒪) (up ℤ)))

instance instSameSiteModulePullbackToDerivedHasLeftDerivedFunctor :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived (sameSiteHom α)) (ModuleQis X) :=
  sameSiteModulePullbackToDerived_hasLeftDerivedFunctor α

end SameSite

end SheafOfModules.RingedSite
