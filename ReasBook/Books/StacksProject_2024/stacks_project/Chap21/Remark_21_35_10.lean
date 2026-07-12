import StacksProject_2024.Chap18.Lemma_18_27_6
import StacksProject_2024.Chap21.Lemma_21_19_1
import StacksProject_2024.Chap21.Lemma_21_33_1_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/-
Domain-style sampling for Remark 21.35.10:
- primary domain: pushforward/internal-Hom comparison morphisms in braided closed monoidal
  derived categories of module sheaves on ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.modulePullbackDerived`,
  `RingedSite.Hom.modulePullbackDerived_pushforward_adjunction`,
  `CategoryTheory.relativeDerivedCupProduct`,
  `braidedHomEquiv`,
  `CategoryTheory.ihom.ev`,
  `(β_ (L ⟹ K) L).hom ≫ (ihom.ev L).app K`;
- best owner abstraction:
  `source-facing`: the comparison morphism
    `Rf_* Rℋom(L, K) ⟶
      Rℋom(Rf_* L, Rf_* K)` for the canonical derived adjunction
      `modulePullbackDerived_pushforward_adjunction f : L(f)^* ⊣ R(f)_*` on module sheaves;
  `core/canonical`: `RingedSite.Hom.modulePullbackDerived`,
    `RingedSite.Hom.modulePushforwardDerived`,
    `RingedSite.Hom.modulePullbackDerived_pushforward_adjunction`,
    `CategoryTheory.relativeDerivedCupProduct`,
    `braidedHomEquiv`, and the closed-monoidal evaluation morphism
    `(β_ (L ⟹ K) L).hom ≫ (ihom.ev L).app K`;
  `bridge/view`: the pointwise pullback-tensor comparison
    `L(f)^*(A ⊗ B) ≅ L(f)^* A ⊗ L(f)^* B`, which is genuinely extra here.
- primitive data: the morphism `f`, the canonical owners `L(f)^*`, `R(f)_*`, their canonical
  adjunction, the pointwise pullback-tensor comparison, and the objects `L`, `K`;
- derived API: the comparison morphism and its tensor-side specification. The relative cup product
  is already owned by `CategoryTheory.relativeDerivedCupProduct`, so this file should reuse that
  owner rather than keep a parallel local copy.
-/

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable [MonoidalCategory (ModuleDerived X)]
variable [BraidedCategory (ModuleDerived X)]
variable [MonoidalClosed (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived Y)]
variable [BraidedCategory (ModuleDerived Y)]
variable [MonoidalClosed (ModuleDerived Y)]

variable [f.modulePushforward.Additive]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [Functor.Additive (SheafOfModules.pullback.{max u v} f.structureSheafMap)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

/-- The canonical evaluation morphism
`Rℋom(L, K) ⊗ᴸ L ⟶ K`
in the source derived category. -/
private abbrev derivedInternalHomEvaluation (L K : ModuleDerived X) :
    (L ⟹ K) ⊗ L ⟶ K :=
  (β_ (L ⟹ K) L).hom ≫ (ihom.ev L).app K

/-- Internal bridge from the pointwise pullback-tensor comparison surface to the `curriedTensor`
shape expected by `CategoryTheory.relativeDerivedCupProduct`. -/
private noncomputable def relativeDerivedCupProductTensorComparison
    (pullbackTensorIso :
      ∀ A B : ModuleDerived Y,
        (L(f)^*).obj (A ⊗ B) ≅
          ((L(f)^*).obj A ⊗ (L(f)^*).obj B)) :
    ∀ A B : ModuleDerived Y,
      (L(f)^*).obj (((curriedTensor (ModuleDerived Y)).obj B).obj A) ≅
        (((curriedTensor (ModuleDerived X)).obj ((L(f)^*).obj B)).obj
          ((L(f)^*).obj A)) :=
  fun A B ↦ by
    simpa using pullbackTensorIso B A

/-- The tensor-side composite of Remark `21.35.10`,
`Rf_* Rℋom(L, K) ⊗ᴸ Rf_* L ⟶ Rf_* K`,
obtained by applying the relative cup product and then pushing forward the source-side evaluation
morphism. Its adjoint transpose is
`derivedPushforwardInternalHomComparison`. -/
private noncomputable def derivedPushforwardInternalHomComparisonAdjointMap
    (pullbackTensorIso :
      ∀ A B : ModuleDerived Y,
        (L(f)^*).obj (A ⊗ B) ≅
          ((L(f)^*).obj A ⊗ (L(f)^*).obj B))
    (L K : ModuleDerived X) :
    (R(f)_*).obj (L ⟹ K) ⊗ (R(f)_*).obj L ⟶
      (R(f)_*).obj K :=
  relativeDerivedCupProduct
      (L(f)^*)
      (R(f)_*)
      (modulePullbackDerived_pushforward_adjunction f)
      (curriedTensor (ModuleDerived X))
      (curriedTensor (ModuleDerived Y))
      (relativeDerivedCupProductTensorComparison f pullbackTensorIso)
      L
      (L ⟹ K) ≫
    (R(f)_*).map (derivedInternalHomEvaluation L K)

/-- Remark 21.35.10: for a morphism of ringed topoi formalized by the ringed-site morphism `f`,
the canonical Chapter 21 adjunction
`modulePullbackDerived_pushforward_adjunction f : L(f)^* ⊣ R(f)_*`,
a pullback-tensor comparison for `L(f)^*`, and objects `L`, `K` of `D(𝒪_𝒞)` determine a canonical
morphism
`Rf_* Rℋom(L, K) ⟶
  Rℋom(Rf_* L, Rf_* K)`. It is the adjoint transpose of the composite
obtained by first applying the relative cup product to
`Rf_* Rℋom(L, K) ⊗[𝒪_𝒟]ᴸ Rf_* L` and
then applying `Rf_*` to the source-side evaluation map
`Rℋom(L, K) ⊗[𝒪_𝒞]ᴸ L ⟶ K`. -/
@[stacks 0B6D]
noncomputable def derivedPushforwardInternalHomComparison
    (pullbackTensorIso :
      ∀ A B : ModuleDerived Y,
        (L(f)^*).obj (A ⊗ B) ≅
          ((L(f)^*).obj A ⊗ (L(f)^*).obj B))
    (L K : ModuleDerived X) :
    (R(f)_*).obj (L ⟹ K) ⟶
      ((R(f)_*).obj L ⟹ (R(f)_*).obj K) :=
    braidedHomEquiv
      ((R(f)_*).obj (L ⟹ K))
      ((R(f)_*).obj L)
      ((R(f)_*).obj K) <|
    derivedPushforwardInternalHomComparisonAdjointMap
      f
      pullbackTensorIso
      L
      K

-- Proof sketch: apply the target-side internal-Hom adjunction. By definition,
-- `derivedPushforwardInternalHomComparison` is the inverse adjoint transpose of the composite
-- consisting of the already-owned relative cup product followed by `Rf_*` applied to the
-- source-side evaluation morphism.
/-- The canonical map
`Rf_* Rℋom(L, K) ⟶ Rℋom(Rf_* L, Rf_* K)` is adjoint to
the composite
`Rf_* Rℋom(L, K) ⊗ᴸ Rf_* L ⟶
  Rf_*(Rℋom(L, K) ⊗ᴸ L) ⟶ Rf_* K`
described in Remark `21.35.10`. -/
theorem derivedPushforwardInternalHomComparison_spec
    (pullbackTensorIso :
      ∀ A B : ModuleDerived Y,
        (L(f)^*).obj (A ⊗ B) ≅
          ((L(f)^*).obj A ⊗ (L(f)^*).obj B))
    (L K : ModuleDerived X) :
    (braidedHomEquiv
        ((R(f)_*).obj (L ⟹ K))
        ((R(f)_*).obj L)
        ((R(f)_*).obj K)).symm
      (derivedPushforwardInternalHomComparison f pullbackTensorIso L K) =
      relativeDerivedCupProduct
          (L(f)^*)
          (R(f)_*)
          (modulePullbackDerived_pushforward_adjunction f)
          (curriedTensor (ModuleDerived X))
          (curriedTensor (ModuleDerived Y))
          (relativeDerivedCupProductTensorComparison f pullbackTensorIso)
          L
          (L ⟹ K) ≫
        (R(f)_*).map (derivedInternalHomEvaluation L K) :=
  by
  simpa [derivedPushforwardInternalHomComparison,
    derivedPushforwardInternalHomComparisonAdjointMap, derivedInternalHomEvaluation] using
    (braidedHomEquiv
        ((R(f)_*).obj (L ⟹ K))
        ((R(f)_*).obj L)
        ((R(f)_*).obj K)).symm_apply_apply
      (derivedPushforwardInternalHomComparisonAdjointMap
        f
        pullbackTensorIso
        L
        K)

end

end RingedSite.Hom
