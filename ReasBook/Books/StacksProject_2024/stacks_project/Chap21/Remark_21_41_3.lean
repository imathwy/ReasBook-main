import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_3
import StacksProject_2024.stacks_project.Chap21.Lemma_21_37_2
import StacksProject_2024.stacks_project.Chap21.Lemma_21_41_2
import StacksProject_2024.stacks_project.Chap21.Remark_21_37_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory

open RingedSite.Hom
open SheafOfModules.RingedSite
open scoped CategoryTheory
open scoped SimplicialDerivedTensorChangeOfRings

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify (simplicialSite J) CommRingCat]
variable [(simplicialSite J).WEqualsLocallyBijective CommRingCat]
variable [(simplicialSite J).HasSheafCompose (forget₂ CommRingCat RingCat)]

local notation "DMod[" A "]" => DerivedCategory (Mod(A•))

/- Domain-style sampling for Remark 21.41.3:
- primary domain: simplicial modules, augmentation to a structure sheaf `𝒪`, and the
  projection lower shriek from the simplicial site `Δ × 𝒞` to `𝒞`;
- sampled owner declarations:
  `CategoryTheory.simplicialProjectionDerivedLowerShriek` with theorem-surface notation
    `Lπ![A]`,
  `CategoryTheory.simplicialProjectionDerivedLowerShriek_after_tensor_structureSheafChange_functor_isomorphic`,
  `RingedSite.Hom.modulePullbackDerived`,
  `RingedSite.Hom.modulePushforwardDerived`,
  `RingedSite.Hom.underlyingAbelianSheafFunctor`;
-- best owner abstraction: this remark is `source-facing`. Its mathematical content is the
  canonical composite obtained by tensoring along the augmentation and then applying the
  `D(𝒪)`-valued projection lower shriek. The relevant owners are the abelian simplicial
  lower shriek `simplicialProjectionDerivedLowerShriek`, the same-site change-of-rings owner
  `modulePullbackDerived (sameSiteHom (simplicialAssociatedRingSheafMap ε))`, the
  module-valued projection lower shriek
  `Functor.leftAdjoint (modulePushforwardDerived (moduleInverseImageHom ...))`, and the exact
  forgetful functor `underlyingAbelianSheafFunctor`, whose derived-category surface here is
  `.mapDerivedCategory`.

Primitive-vs-derived split:
- primitive data: the augmentation `ε : A_• ⟶ (SimplicialObject.const (Sheaf J CommRingCat)).obj 𝒪`, the canonical
  change-of-rings owner
  `modulePullbackDerived (sameSiteHom (simplicialAssociatedRingSheafMap ε))`,
  and the theorem-level canonical isomorphism comparing the abelian simplicial lower
  shriek to its base-changed form;
- derived API: the augmentation-specific composite with the `D(𝒪)`-valued projection
  lower shriek, the proposition-level forgetful comparison after forgetting
  `𝒪`-module structure, and the induced objectwise `𝒪`-module structure on
  `Lπ_!(K)`.

Source/core/bridge triage:
- `source-facing`: the augmentation functor `augmentationDerivedLowerShriek 𝒪 ε` and its
  forgetful comparison with `Lπ![A]`;
- `core/canonical`: `simplicialProjectionDerivedLowerShriek` with surface notation `Lπ![A]`,
  `modulePullbackDerived (sameSiteHom (simplicialAssociatedRingSheafMap ε))`,
  `modulePushforwardDerived`, `Functor.leftAdjoint`, and `underlyingAbelianSheafFunctor`;
- `bridge/view`: the transport from the constant simplicial structure sheaf to the inverse-image
  owner used by Remark `21.37.3`.
-/

variable (𝒪 : Sheaf J CommRingCat)

/-- The constant simplicial structure sheaf `𝒪_•` attached to a sheaf of rings `𝒪`. -/
abbrev constantStructureSheaf (𝒪 : Sheaf J CommRingCat) :
    SimplicialObject (Sheaf J CommRingCat) :=
  (SimplicialObject.const (Sheaf J CommRingCat)).obj 𝒪

section Comparison

variable [HasSheafify J AddCommGrpCat]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [HasSheafify (simplicialSite J) AddCommGrpCat]
variable [(simplicialSite J).WEqualsLocallyBijective AddCommGrpCat]
variable [Functor.IsContinuous simplicialProjection (simplicialSite J) J]
variable [Functor.IsCocontinuous simplicialProjection (simplicialSite J) J]
variable [Functor.Additive
  (simplicialProjection.sheafPushforwardContinuous AddCommGrpCat (simplicialSite J) J)]
variable [IsGrothendieckAbelian (Sheaf J AddCommGrpCat)]
variable [Functor.HasRightDerivedFunctor
  (mapHomotopyCategoryToDerived
    (simplicialProjection.sheafPushforwardContinuous AddCommGrpCat (simplicialSite J) J))
  (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat) (ComplexShape.up ℤ))]
variable [Functor.IsRightAdjoint
  (siteAbelianInverseImageDerived (simplicialSite J) J simplicialProjection)]
variable [((𝟭 (SimplexCategory × C)).sheafPushforwardContinuous
  CommRingCat (simplicialSite J) (simplicialSite J)).IsRightAdjoint]

/- Remark 21.41.3 is source-facing: from an augmentation `ε : A_• ⟶ 𝒪_•`, first tensor along
`ε`, then apply the canonical `D(𝒪)`-valued projection lower shriek in the constant case. The
constant case itself is obtained by transporting the constant simplicial structure sheaf to the
inverse-image owner of Remark `21.37.3`. -/
variable {A : SimplicialObject (Sheaf J CommRingCat)}
variable [IsGrothendieckAbelian (Mod(A•))]
variable [CategoryWithHomology (Mod(A•))]
variable [MonoidalCategory (Mod(A•))]
variable [MonoidalPreadditive (Mod(A•))]
variable [CategoryWithHomology (SimplicialSheafOfModules (constantStructureSheaf 𝒪))]
variable [MonoidalCategory (SimplicialSheafOfModules (constantStructureSheaf 𝒪))]
variable [MonoidalPreadditive (SimplicialSheafOfModules (constantStructureSheaf 𝒪))]
variable [Functor.Additive
  ((moduleInverseImageHom (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪)).modulePushforward)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived
    (moduleInverseImageHom (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪)))
  (ModuleQis (RingedSite.ofRingSheaf J (ringSheaf J 𝒪)))]
variable [Functor.IsRightAdjoint
  (modulePushforwardDerived
    (moduleInverseImageHom (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪)))]
variable [((moduleInverseImageHom (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪))^*).Additive]
variable [Functor.Additive
  (SheafOfModules.pullback
    (moduleInverseImageHom (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪)).structureSheafMap)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived
    (moduleInverseImageHom (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪)))
  (ModuleQis
    (RingedSite.ofRingSheaf (simplicialSite J)
      (inverseImageRingSheaf (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪))))]

local notation "X𝒪" => RingedSite.ofRingSheaf J (ringSheaf J 𝒪)
local notation "Xπ" =>
  RingedSite.ofRingSheaf (simplicialSite J)
    (inverseImageRingSheaf (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪))
local notation "gπ" => moduleInverseImageHom (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪)

private local instance : Abelian (ModuleCat X𝒪) := SheafOfModules.instAbelian (ringSheaf J 𝒪)
private local instance : Abelian (ModuleCat Xπ) :=
  SheafOfModules.instAbelian
    (inverseImageRingSheaf (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪))
private local instance :
    Functor.Additive
      (modulePushforward
        (moduleInverseImageHom (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪))) :=
  inferInstance
private local instance :
    Functor.Additive
      (SheafOfModules.pullback
        (moduleInverseImageHom (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪)).structureSheafMap) :=
  inferInstance
private local instance :
    ((moduleInverseImageHom (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪))^*).Additive :=
  inferInstance

section

private def constantStructureSheafProjectionIso :
    simplicialAssociatedRingSheaf (constantStructureSheaf 𝒪) ≅
      (simplicialProjection.sheafPushforwardContinuous
        CommRingCat (simplicialSite J) J).obj 𝒪 := by
  simpa [constantStructureSheaf] using
    (CategoryTheory.sheafificationIso
      ((simplicialProjection.sheafPushforwardContinuous
        CommRingCat (simplicialSite J) J).obj 𝒪)).symm

/-- The constant-case `D(𝒪)`-valued lower shriek of Remark `21.41.3`, obtained by transporting
the constant simplicial structure sheaf to the inverse-image owner of Remark `21.37.3` and then
applying the canonical module-valued projection lower shriek `modulePullbackDerived gπ`. -/
noncomputable abbrev constantStructureSheafDerivedLowerShriek :
    DMod[(constantStructureSheaf 𝒪)] ⥤ ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪) := by
  let g :
      RingedSite.ofRingSheaf J (ringSheaf J 𝒪) ⟶
        RingedSite.ofRingSheaf (simplicialSite J)
          (inverseImageRingSheaf (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪)) :=
    moduleInverseImageHom (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪)
  let h : ModuleDerived Xπ ⥤ ModuleDerived X𝒪 := by
    letI : (PresheafOfModules.pushforward g.structureSheafMap.hom).IsRightAdjoint := inferInstance
    letI : Functor.Additive (SheafOfModules.pullback g.structureSheafMap) := by
      simpa [g] using
        (inferInstance :
          ((moduleInverseImageHom (simplicialSite J) J simplicialProjection (ringSheaf J 𝒪))^*).Additive)
    letI : Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Xπ) := inferInstance
    exact modulePullbackDerived g
  exact
    modulePullbackDerived (sameSiteHom (constantStructureSheafProjectionIso 𝒪).hom) ⋙ h
local notation "forgetMod𝒪" =>
  (Functor.mapDerivedCategory
    (underlyingAbelianSheafFunctor (RingedSite.ofCommRingSheaf J 𝒪)))

/-- Remark `21.41.3`, constant case: after forgetting `𝒪`-module structure, the canonical
`D(𝒪)`-valued lower shriek on the constant simplicial structure sheaf recovers the abelian
projection lower shriek `Lπ![𝒪_•]`. -/
theorem constantStructureSheafDerivedLowerShriek_forget_functor_isomorphic :
    IsIsomorphic
      (Lπ![(constantStructureSheaf 𝒪)])
      (constantStructureSheafDerivedLowerShriek 𝒪 ⋙ forgetMod𝒪) := by
  sorry

variable (ε : A ⟶ constantStructureSheaf 𝒪)

private local instance augmentationChangeOfRingsPushforwardIsRightAdjoint :
    (SheafOfModules.pushforward.{u}
      (ringedSiteStructureMap (simplicialAssociatedRingSheafMap ε))).IsRightAdjoint := by
  simpa [ringedSiteUnderlyingStructureMap, ringedSiteStructureMap]
    using
      (inferInstance :
        (SheafOfModules.pushforward.{u}
          (ringedSiteUnderlyingStructureMap
            (𝟭 (SimplexCategory × C))
            (simplicialAssociatedRingSheafMapOverId ε))).IsRightAdjoint)

local notation "Lε" =>
  modulePullbackDerived (sameSiteHom (simplicialAssociatedRingSheafMap ε))

/-- Remark `21.41.3`: the canonical `D(𝒪)`-valued lower shriek attached to an augmentation
`ε : A_• ⟶ 𝒪_•`, obtained by first tensoring along `ε` and then applying the constant-case lower
shriek `constantStructureSheafDerivedLowerShriek 𝒪`. -/
noncomputable abbrev augmentationDerivedLowerShriek :
    DMod[A] ⥤ ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪) :=
  Lε ⋙ constantStructureSheafDerivedLowerShriek 𝒪

/-- Remark `21.41.3`: if the augmentation unit comparison of Lemma `21.41.2` is an isomorphism,
then after forgetting `𝒪`-module structure the functor `augmentationDerivedLowerShriek 𝒪 ε`
recovers the abelian projection lower shriek `Lπ![A]`. -/
@[stacks 09D3]
theorem augmentationDerivedLowerShriek_forget_functor_isomorphic
    (hε : IsIso (simplicialProjectionDerivedLowerShriekUnitComparison ε)) :
    IsIsomorphic
      (Lπ![A])
      (augmentationDerivedLowerShriek 𝒪 ε ⋙ forgetMod𝒪) := by
  sorry

/-- For every `K : D(A_•)`, the underlying abelian sheaf of
`(augmentationDerivedLowerShriek 𝒪 ε).obj K` is canonically isomorphic to `(Lπ![A]).obj K`. -/
theorem augmentationDerivedLowerShriek_forget_isomorphic
    (hε : IsIso (simplicialProjectionDerivedLowerShriekUnitComparison ε))
    (K : DMod[A]) :
    IsIsomorphic
      ((Lπ![A]).obj K)
      ((augmentationDerivedLowerShriek 𝒪 ε ⋙ forgetMod𝒪).obj K) := by
  sorry

end

end Comparison

end

end CategoryTheory
