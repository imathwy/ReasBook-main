import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Monoidal.Category
import StacksProject_2024.stacks_project.Chap20.«20_14_1_1»
import StacksProject_2024.stacks_project.Chap20.Lemma_20_27_3
import StacksProject_2024.stacks_project.Chap20.Lemma_20_28_1
import StacksProject_2024.stacks_project.Chap20.Lemma_20_50_6
import StacksProject_2024.stacks_project.Chap20.«20_54_2_1»

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open ComplexShape
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModY" => DerivedCategory (RingedSpace.Modules Y)

local instance : Abelian (RingedSpace.Modules X) := RingedSpace.modules_abelian X
local instance : Abelian (RingedSpace.Modules Y) := RingedSpace.modules_abelian Y

variable (f : X ⟶ Y)

/- Domain-style sampling for Lemma 20.54.4:
- primary domain: the canonical projection-formula morphism for derived pullback/pushforward of
  module sheaves on ringed spaces, under the source-facing closed-subset hypothesis on the
  underlying map;
- sampled owner declarations:
  `CategoryTheory.projectionFormulaMorphism`,
  `RingedSpace.modulePullbackDerived`,
  `RingedSpace.moduleDerivedPushforward`,
  `RingedSite.Hom.modulePullbackDerived_pushforward_adjunction`,
  a chosen pullback-tensor comparison for `L(f)^*`,
  `RingedSpace.Hom.pushforward_exact_of_isClosedEmbedding`;
- best owner abstraction:
  `source-facing`: the ringed-space closed-embedding criterion for the canonical projection-formula
    morphism;
  `core/canonical`: `CategoryTheory.projectionFormulaMorphism`;
  `bridge/view`: the ringed-space specialization `L(f)^*` of `modulePullbackDerived f` and
    `moduleDerivedPushforward f`, together with the exactness package attached to a closed
    embedding of the underlying topological spaces;
- primitive data: the morphism `f` and the closed-embedding hypothesis on `f.hom.base`;
- derived API: the `IsIso` conclusion for the canonical projection-formula morphism specialized to
  ringed spaces, built from the canonical opens-ringed-site adjunction
  `RingedSite.Hom.modulePullbackDerived_pushforward_adjunction (opensRingedSiteHom f)` and a
  chosen pullback-tensor comparison for `L(f)^*`. -/

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
variable [MonoidalCategory DModX]
variable [MonoidalCategory DModY]
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

-- Proof sketch: because `f` identifies `X` with a closed subset of `Y`, pushforward on module
-- sheaves is exact, so `Rf_*` is computed by ordinary pushforward on complexes. Pullback of a
-- K-flat representative computes `Lf^*`, and the stalkwise tensor identity for a closed subset
-- inclusion identifies the two complexes representing the source and target of the projection
-- formula map.
/-- Lemma 20.54.4: if `f : X ⟶ Y` identifies `X` homeomorphically with a closed subset of `Y`,
then the projection-formula morphism
`K ⊗^L R(f)_* E ⟶ R(f)_* (((L(f)^*).obj K) ⊗^L E)` is an isomorphism for all
`E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)`, for any chosen pullback-tensor comparison on `L(f)^*`. -/
@[stacks 0B55]
instance projectionFormulaMorphism_isIso_of_isClosedEmbedding
    (pullbackTensorIso :
      ∀ L : DModY,
        (tensoringRight DModY).obj L ⋙ L(f)^* ≅
          L(f)^* ⋙ (tensoringRight DModX).obj ((L(f)^*).obj L))
    (hf : Topology.IsClosedEmbedding f.hom.base)
    (E : DModX) (K : DModY) :
    IsIso
      (projectionFormulaMorphism
        (L(f)^*)
        (R(f)_*)
        (RingedSite.Hom.modulePullbackDerived_pushforward_adjunction (opensRingedSiteHom f))
        (fun A B ↦ (pullbackTensorIso B).app A)
        E
        K) := sorry

end

end AlgebraicGeometry.RingedSpace
