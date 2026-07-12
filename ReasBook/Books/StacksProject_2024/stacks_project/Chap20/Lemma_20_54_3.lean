import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import StacksProject_2024.Chap20.Lemma_20_28_1
import StacksProject_2024.Chap20.Perfect_on_opens_ringed_site
import StacksProject_2024.Chap20.Lemma_20_50_6
import StacksProject_2024.Chap20.«20_54_2_1»
import StacksProject_2024.Chap21.Lemma_21_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open ComplexShape
open RingedSite.Hom
open TopologicalSpace
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.54.3:
- primary domain: projection-formula morphisms for derived pullback and derived pushforward of
  module sheaves, with the intrinsic owner living on ringed sites and the ringed-space statement
  as its opens-site specialization;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.DerivedCategory.IsPerfect`,
  `_root_.RingedSite.Hom.projectionFormulaMorphism_isIso_of_isPerfect`,
  `_root_.RingedSite.Hom.projectionFormulaMorphism`,
  `CategoryTheory.projectionFormulaMorphism`,
  `RingedSite.Hom.modulePullbackDerived_pushforward_adjunction`,
  `modulePullbackDerivedTensor_existsComparison`;
- best owner abstraction:
  `source-facing`: the ringed-space specialization for a morphism `f : X ⟶ Y`, stated with the
    Chapter 20 perfectness owner `DerivedCategory.IsPerfect`;
  `core/canonical`: `_root_.RingedSite.Hom.projectionFormulaMorphism_isIso_of_isPerfect` together with
    the ringed-site perfectness owner;
  `bridge/view`: the Chapter 20 comparison between ringed-space and opens-site perfectness,
    together with a chosen pullback-tensor comparison family for `L(f)^*`.
- primitive data: the ringed-space morphism `f` and the source-facing perfectness hypothesis on
  `K`, plus the chosen pullback-tensor comparison family used by the Chapter 20 owner
  `projectionFormulaMorphism`;
- derived API: the `IsIso` conclusion for the canonical ringed-space projection-formula morphism,
  obtained by specializing the ringed-site owner theorem through the canonical derived adjunction
  `RingedSite.Hom.modulePullbackDerived_pushforward_adjunction (opensRingedSiteHom f)`. -/

section

variable {X Y : RingedSpace.{u}}

local notation "DModX" =>
  RingedSpaceDerived X
local notation "DModY" =>
  RingedSpaceDerived Y
local notation "SiteDModX" => RingedSite.Hom.ModuleDerived (opensRingedSite X)
local notation "SiteDModY" => RingedSite.Hom.ModuleDerived (opensRingedSite Y)

variable (f : X ⟶ Y)

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules Y)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules Y)]
variable [SymmetricCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules Y)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules Y)]
variable [HasColimits (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules Y)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [(curriedTensor (RingedSpace.Modules Y)).Additive]
variable [∀ ℱ : RingedSpace.Modules X, ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ ℱ : RingedSpace.Modules Y, ((curriedTensor (RingedSpace.Modules Y)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules Y) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules Y))]
variable [monoidalDModX : MonoidalCategory DModX]
variable [monoidalDModY : MonoidalCategory DModY]
variable [∀ G₁ G₂ : GradedObject ℤ (RingedSpace.Modules X), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ : GradedObject ℤ (RingedSpace.Modules Y), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules X),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules Y),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules X),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules Y),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (RingedSpace.Modules X),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (RingedSpace.Modules Y),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ ℱ : RingedSpace.Modules X,
  PreservesColimit (Functor.empty.{0} (RingedSpace.Modules X))
    ((curriedTensor (RingedSpace.Modules X)).obj ℱ)]
variable [∀ ℱ : RingedSpace.Modules Y,
  PreservesColimit (Functor.empty.{0} (RingedSpace.Modules Y))
    ((curriedTensor (RingedSpace.Modules Y)).obj ℱ)]
variable [∀ ℱ : RingedSpace.Modules X,
  PreservesColimit (Functor.empty.{0} (RingedSpace.Modules X))
    ((curriedTensor (RingedSpace.Modules X)).flip.obj ℱ)]
variable [∀ ℱ : RingedSpace.Modules Y,
  PreservesColimit (Functor.empty.{0} (RingedSpace.Modules Y))
    ((curriedTensor (RingedSpace.Modules Y)).flip.obj ℱ)]
variable [(f^*).Additive]
variable [Functor.Monoidal (RingedSpace.Hom.pullback f)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived f)
    (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
variable [∀ U : Opens Y.carrier, CategoryWithHomology (openSubspaceModuleCategory Y U)]
variable [HasBinaryProducts (opensRingedSite X).carrier]
variable [HasBinaryProducts (opensRingedSite Y).carrier]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : (opensRingedSite X).carrier,
  (RingedSite.Hom.localizedRestriction (opensRingedSite X) U).Additive]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteLimits (RingedSite.Hom.localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteColimits (RingedSite.Hom.localizedRestriction (opensRingedSite X) U)]
variable [CategoryWithHomology (RingedSite.Hom.ModuleCat (opensRingedSite X))]
variable [∀ U : (opensRingedSite X).carrier,
  CategoryWithHomology (RingedSite.Hom.ModuleCat ((opensRingedSite X).localization U))]
variable [∀ U : (opensRingedSite Y).carrier,
  (RingedSite.Hom.localizedRestriction (opensRingedSite Y) U).Additive]
variable [∀ U : (opensRingedSite Y).carrier,
  PreservesFiniteLimits (RingedSite.Hom.localizedRestriction (opensRingedSite Y) U)]
variable [∀ U : (opensRingedSite Y).carrier,
  PreservesFiniteColimits (RingedSite.Hom.localizedRestriction (opensRingedSite Y) U)]
variable [CategoryWithHomology (RingedSite.Hom.ModuleCat (opensRingedSite Y))]
variable [∀ U : (opensRingedSite Y).carrier,
  CategoryWithHomology (RingedSite.Hom.ModuleCat ((opensRingedSite Y).localization U))]

local instance opensRingedSiteX_monoidalCategory : MonoidalCategory SiteDModX := monoidalDModX

local instance opensRingedSiteY_monoidalCategory : MonoidalCategory SiteDModY := monoidalDModY

-- Proof sketch: this is exactly the projection-formula argument from the Stacks Project. Work
-- locally on `Y` and represent the perfect object `K` by a strictly perfect complex.
-- The claim is stable under finite direct sums, shifts, and direct summands, so stupid
-- truncations reduce to the case `K = 𝒪_Y[n]`, where the projection-formula morphism is
-- immediate.
/-- Lemma 20.54.3: for a morphism of ringed spaces `f : X ⟶ Y`, an object `E ∈ D(𝒪_X)`, a
perfect object `K ∈ D(𝒪_Y)`, and a chosen pullback-tensor comparison for `L(f)^*`, the resulting
projection-formula morphism
`K ⊗^L R(f)_* E ⟶ R(f)_*((L(f)^*).obj K ⊗^L E)` is an isomorphism in `D(𝒪_Y)`. -/
@[stacks 0B54]
instance projectionFormulaMorphism_isIso_of_isPerfect
    (pullbackTensorIso :
      ∀ L : DModY,
        (tensoringRight DModY).obj L ⋙ L(f)^* ≅
          L(f)^* ⋙ (tensoringRight DModX).obj ((L(f)^*).obj L))
    (E : DModX) (K : DModY) (hK : DerivedCategory.IsPerfect K) :
    IsIso
      (projectionFormulaMorphism
        (L(f)^*)
        (R(f)_*)
        (RingedSite.Hom.modulePullbackDerived_pushforward_adjunction (opensRingedSiteHom f))
        (fun A B ↦ (pullbackTensorIso B).app A)
        E
        K) := by
  let localizedRestrictionAdditiveY :
      ∀ U : (opensRingedSite Y).carrier,
        (RingedSite.Hom.localizedRestriction (opensRingedSite Y) U).Additive :=
    inferInstanceAs
      (∀ U : (opensRingedSite Y).carrier,
        (RingedSite.Hom.localizedRestriction (opensRingedSite Y) U).Additive)
  let pullbackTensorIsoSite :
      ∀ L : SiteDModY,
        (tensoringRight SiteDModY).obj L ⋙
            RingedSite.Hom.modulePullbackDerived (opensRingedSiteHom f) ≅
          RingedSite.Hom.modulePullbackDerived (opensRingedSiteHom f) ⋙
            (tensoringRight SiteDModX).obj
              ((RingedSite.Hom.modulePullbackDerived (opensRingedSiteHom f)).obj L) :=
    fun L ↦ by
      change (tensoringRight DModY).obj L ⋙ L(f)^* ≅
        L(f)^* ⋙ (tensoringRight DModX).obj ((L(f)^*).obj L)
      simpa using pullbackTensorIso L
  let hKSite :
      (ModuleDerived.IsPerfect : RingedSite.Hom.ModuleDerived (opensRingedSite Y) → Prop) K :=
    (DerivedCategory.isPerfect_iff_opensRingedSiteIsPerfect K).1 hK
  have hSiteIso :
      IsIso
        (CategoryTheory.projectionFormulaMorphism
          (RingedSite.Hom.modulePullbackDerived (opensRingedSiteHom f))
          (RingedSite.Hom.modulePushforwardDerived (opensRingedSiteHom f))
          (RingedSite.Hom.modulePullbackDerived_pushforward_adjunction (opensRingedSiteHom f))
          (fun A B ↦ (pullbackTensorIsoSite B).app A)
          E
          K) :=
    @RingedSite.Hom.projectionFormulaMorphism_isIso_of_isPerfect
      (opensRingedSite X)
      (opensRingedSite Y)
      (opensRingedSiteHom f)
      monoidalDModX
      monoidalDModY
      inferInstance
      inferInstance
      inferInstance
      localizedRestrictionAdditiveY
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      (RingedSite.Hom.modulePullbackDerived_pushforward_adjunction (opensRingedSiteHom f))
      pullbackTensorIsoSite
      E
      K
      hKSite
  simpa using hSiteIso

end

end AlgebraicGeometry.RingedSpace
