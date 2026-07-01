import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import stacks_project.Chap13.Lemma_13_16_1
import stacks_project.Chap18.Lemma_18_28_7
import stacks_project.Chap18.Lemma_18_41_1

-- Declarations for this item will be appended below by the statement pipeline.

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
