import StacksProject_2024.stacks_project.Chap20.Definition_20_26_14_Core
import StacksProject_2024.stacks_project.Chap20.Lemma_20_26_8
import StacksProject_2024.stacks_project.Chap20.Lemma_20_26_12
import StacksProject_2024.stacks_project.Chap20.Lemma_20_27_1

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace}

/-
Domain-style sampling for Lemma 20.27.3:
- primary domain: compatibility between derived pullback and the fixed-right-factor derived tensor
  product on `D(𝒪_X)`;
- sampled owner declarations:
  `modulePullbackDerived`,
  `derivedTensorProduct`,
  `Functor.leftDerivedNatTrans`;
- best owner abstraction: the source-facing public API is the existence theorem
  `modulePullbackDerivedTensor_existsComparison`, together with the counit-square companion
  `modulePullbackDerivedTensor_existsComparison_commSq`; the representative-level comparison and
  the underived bottom edge in the counit square remain private bridge data;
- primitive data: a morphism of ringed spaces `f : X ⟶ Y` and a fixed right factor
  `𝒢 : D(𝒪_Y)`;
- derived API: proposition-level existence of a pullback-tensor comparison morphism
  `(- ⊗^L 𝒢) ⋙ L(f)^* ⟶ L(f)^* ⋙ (- ⊗^L L(f)^*𝒢)` that is an isomorphism, together with a
  companion existence theorem for the defining counit square.

Source/core/bridge triage:
- `source-facing`: `modulePullbackDerivedTensor_existsComparison`;
- `core/canonical`: `modulePullbackDerived`, `derivedTensorProduct`, and
  `Functor.leftDerivedNatTrans`;
- `bridge/view`: the K-flat replacement and underived pullback-tensor comparison used in the
  proof.
-/

local notation "DModX" =>
  @DerivedCategory (RingedSpace.Modules X) _ (RingedSpace.modules_abelian X) _
local notation "DModY" =>
  @DerivedCategory (RingedSpace.Modules Y) _ (RingedSpace.modules_abelian Y) _
local notation "QhY" =>
  (DerivedCategory.Qh :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DModY)

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [MonoidalCategory (CochainComplex (RingedSpace.Modules X) ℤ)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : RingedSpace.Modules X, ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [HasCountableCoproducts (RingedSpace.Modules Y)]
variable [MonoidalCategory (RingedSpace.Modules Y)]
variable [MonoidalPreadditive (RingedSpace.Modules Y)]
variable [HasColimits (RingedSpace.Modules Y)]
variable [MonoidalCategory (CochainComplex (RingedSpace.Modules Y) ℤ)]
variable [(curriedTensor (RingedSpace.Modules Y)).Additive]
variable [∀ ℱ : RingedSpace.Modules Y, ((curriedTensor (RingedSpace.Modules Y)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules Y) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules Y))]

/-- The source-side counit for the pullback-tensor comparison: first derive tensoring with the
fixed right factor `𝒢`, then postcompose with `Lf^*`. -/
abbrev modulePullbackDerivedTensorSourceCounit
    (f : X ⟶ Y) [(f^*).Additive] (𝒢 : DModY) :
    QhY ⋙
      (derivedTensorProduct 𝒢 ⋙ modulePullbackDerived f) ⟶
        derivedTensorSourceFunctor 𝒢 ⋙ modulePullbackDerived f :=
  (Functor.associator
      QhY
      (derivedTensorProduct 𝒢)
      (modulePullbackDerived f)).hom ≫
    Functor.whiskerRight
      (derivedTensorProductCounit 𝒢)
      (modulePullbackDerived f)

/-- The counit exhibiting `L(f)^* ⋙ (- ⊗^L (L(f)^*).obj 𝒢)` as a left derived functor of the
underived pullback-to-derived functor followed by derived tensoring on `X`. -/
abbrev modulePullbackDerivedTensorTargetCounit
    (f : X ⟶ Y) [(f^*).Additive] (𝒢 : DModY) :
    QhY ⋙
      (modulePullbackDerived f ⋙ derivedTensorProduct ((modulePullbackDerived f).obj 𝒢)) ⟶
        modulePullbackToDerived f ⋙
          derivedTensorProduct ((modulePullbackDerived f).obj 𝒢) :=
  (Functor.associator
      QhY
      (modulePullbackDerived f)
      (derivedTensorProduct ((modulePullbackDerived f).obj 𝒢))).hom ≫
    Functor.whiskerRight
      ((modulePullbackToDerived f).totalLeftDerivedCounit
        QhY
        (ModuleQis Y))
      (derivedTensorProduct ((modulePullbackDerived f).obj 𝒢))

/-- Lemma 20.27.3: there exists a pullback-tensor comparison morphism
`(- ⊗^L 𝒢) ⋙ L(f)^* ⟶ L(f)^* ⋙ (- ⊗^L (L(f)^*).obj 𝒢)` and this morphism is an isomorphism. -/
@[stacks 079U]
theorem modulePullbackDerivedTensor_existsComparison
    (f : X ⟶ Y) [(f^*).Additive] [Functor.Monoidal (RingedSpace.Hom.pullback f)] (𝒢 : DModY) :
    ∃ τ :
      derivedTensorProduct 𝒢 ⋙ L(f)^* ⟶
        L(f)^* ⋙ derivedTensorProduct ((L(f)^*).obj 𝒢),
      IsIso τ := by
  sorry

/-- One may choose a pullback-tensor comparison for Lemma 20.27.3 so that the defining square
built from the two canonical counits commutes at any homotopy-category object `Kq`. -/
theorem modulePullbackDerivedTensor_existsComparison_commSq
    (f : X ⟶ Y) [(f^*).Additive] [Functor.Monoidal (RingedSpace.Hom.pullback f)]
    (Kq : HomotopyCategory (RingedSpace.Modules Y) (up ℤ)) (𝒢 : DModY) :
    ∃ τ :
      derivedTensorProduct 𝒢 ⋙ L(f)^* ⟶
        L(f)^* ⋙ derivedTensorProduct ((L(f)^*).obj 𝒢),
      ∃ σ :
        derivedTensorSourceFunctor 𝒢 ⋙ modulePullbackDerived f ⟶
          modulePullbackToDerived f ⋙
            derivedTensorProduct ((modulePullbackDerived f).obj 𝒢),
        IsIso τ ∧
          CommSq
            ((Functor.whiskerLeft QhY τ).app Kq)
            ((modulePullbackDerivedTensorSourceCounit f 𝒢).app Kq)
            ((modulePullbackDerivedTensorTargetCounit f 𝒢).app Kq)
            (σ.app Kq) := by
  sorry

end AlgebraicGeometry.RingedSpace
