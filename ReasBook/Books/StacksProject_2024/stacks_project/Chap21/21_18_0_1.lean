import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

section

/- Domain-style sampling for 21.18.0.1:
- primary domain: site-presented inverse image on sheaves of modules over ringed sites;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `ringSheaf`,
  `SheafOfModules.pullback`,
  `sheafCompose`;
- best owner abstraction: this file is a `bridge/view` layer. The primitive data are a continuous
  functor of sites together with the structure-sheaf morphism `φ`, and the derived API is the
  canonical module pullback functor induced by that data;
- primitive vs derived: the `RingCat`-valued structure map is primitive bridge data, while the
  module pullback functor is the immediate canonical view derived from it.

Source/core/bridge triage:
- `source-facing`: none; this file is only the shared bridge layer for Chapter 21 site-presented
  inverse-image arguments;
- `core/canonical`: `ringedSiteModuleCategory` and `SheafOfModules.pullback`;
- `bridge/view`: `ringedSiteUnderlyingStructureMap` and `pullbackFunctor`. -/

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪' : Sheaf JC CommRingCat.{max u v}} {𝒪 : Sheaf JD CommRingCat.{max u v}}
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} JC JD).obj 𝒪)

/-- The underlying `RingCat`-valued structure map attached to the site-presented morphism of
ringed topoi determined by `φ`. -/
def ringedSiteUnderlyingStructureMap :
    ringSheaf JC 𝒪' ⟶
      (F.sheafPushforwardContinuous RingCat.{max u v} JC JD).obj (ringSheaf JD 𝒪) :=
  (sheafCompose JC (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map φ

variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]

/-- The inverse-image functor on module sheaves attached to the site-presented morphism of ringed
topoi determined by `φ`. -/
def pullbackFunctor :
    ringedSiteModuleCategory JC 𝒪' ⥤ ringedSiteModuleCategory JD 𝒪 :=
  SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)

instance instPullbackFunctorPreservesZeroMorphisms :
    (pullbackFunctor F φ).PreservesZeroMorphisms := by
  simpa [pullbackFunctor] using
    (inferInstance :
      (SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)).PreservesZeroMorphisms)

section Additive

variable [HasWeakSheafify JD AddCommGrpCat.{max u v}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The site-presented inverse-image functor on module sheaves is the canonical left adjoint to
the corresponding pushforward functor. -/
instance instPullbackFunctorIsLeftAdjoint :
    (pullbackFunctor F φ).IsLeftAdjoint := by
  simpa [pullbackFunctor] using
    (SheafOfModules.pullbackPushforwardAdjunction
      (ringedSiteUnderlyingStructureMap F φ)).isLeftAdjoint

/-- The Chapter 21 site-presented pullback functor on module sheaves is additive. This shared
owner supplies the additive hypothesis needed by the derived pullback API without target-local
instance plumbing. -/
instance instPullbackFunctorAdditive :
    Functor.Additive (pullbackFunctor F φ) := by
  letI : (pullbackFunctor F φ).IsLeftAdjoint :=
    instPullbackFunctorIsLeftAdjoint (F := F) (φ := φ)
  letI : Abelian (ringedSiteModuleCategory JC 𝒪') := inferInstance
  letI : Abelian (ringedSiteModuleCategory JD 𝒪) := inferInstance
  letI : HasBinaryBiproducts (ringedSiteModuleCategory JC 𝒪') := Abelian.hasBinaryBiproducts
  letI : HasBinaryBiproducts (ringedSiteModuleCategory JD 𝒪) := Abelian.hasBinaryBiproducts
  exact Functor.additive_of_preservesBinaryBiproducts
    (pullbackFunctor F φ :
      ringedSiteModuleCategory JC 𝒪' ⥤ ringedSiteModuleCategory JD 𝒪)

end Additive

end

section SameSite

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪')
variable [(SheafOfModules.pushforward (ringedSiteStructureMap α)).IsRightAdjoint]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The Chapter 21 same-site `ringedSiteStructureMap α` and the underlying site-presented owner
`ringedSiteUnderlyingStructureMap (𝟭 C) α` induce the same canonical right adjoint on module
sheaves. -/
instance instSameSiteUnderlyingStructureMapPushforwardIsRightAdjoint :
    (SheafOfModules.pushforward
      (ringedSiteUnderlyingStructureMap (𝟭 C) α)).IsRightAdjoint := by
  simpa [ringedSiteUnderlyingStructureMap, ringedSiteStructureMap] using
    (inferInstance :
      (SheafOfModules.pushforward (ringedSiteStructureMap α)).IsRightAdjoint)

/-- The same-site `pullbackFunctor` and the ringed-site pullback on `ringedSiteStructureMap α`
share the same additive structure. This is the shared Chapter 21 bridge from the source-facing
same-site owner `pullbackFunctor (𝟭 C) α` to the ringed-site pullback functor consumed by derived
owners. -/
instance instSameSiteStructureMapPullbackAdditive :
    Functor.Additive (SheafOfModules.pullback (ringedSiteStructureMap α)) := by
  simpa [pullbackFunctor, ringedSiteUnderlyingStructureMap, ringedSiteStructureMap]
    using (inferInstance : Functor.Additive (pullbackFunctor (𝟭 C) α))

end SameSite

end SheafOfModules.RingedSite
