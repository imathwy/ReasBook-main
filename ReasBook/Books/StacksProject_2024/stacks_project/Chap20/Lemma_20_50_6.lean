import StacksProject_2024.stacks_project.Chap15.Lemma_15_58_3
import StacksProject_2024.stacks_project.Chap20.Definition_20_26_14_Core
import StacksProject_2024.stacks_project.Chap20.RingedSpaceModuleHasDerivedCategory

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

/- 
Domain-style sampling for Lemma 20.50.6:
- primary domain: localization of symmetric monoidal homotopy categories to derived categories of
  `𝒪_X`-modules on a ringed space;
- sampled owner declarations:
  `HomologicalComplex.homotopyEquivalences`,
  `HomotopyCategory.quotient`,
  `CategoryTheory.LocalizedMonoidal`,
  `CategoryTheory.Localization.Monoidal.toMonoidalCategory`,
  `CategoryTheory.Localization.Monoidal.instSymmetricCategoryLocalizedMonoidal`,
  `CategoryTheory.SymmetricCategory`;
- best owner abstraction: the public owner is the `SymmetricCategory` structure on
  `DerivedCategory (RingedSpace.Modules X)`, obtained canonically by first localizing the tensor
  product on complexes to `K(X)` and then localizing quasi-isomorphisms to `D(X)`;
- primitive data: the ringed space `X`, the symmetric monoidal tensor on `RingedSpace.Modules X`,
  the induced tensor on cochain complexes, and the monoidal stability of homotopy equivalences and
  quasi-isomorphisms under those canonical tensor functors;
- derived API: the localized monoidal and symmetric structures on `D(X)`, together with the
  monoidal transport on `DerivedCategory.Qh` used to express the localization step.

Layer triage:
- `source-facing`: the symmetric monoidal structure on `D(𝒪_X)` together with the source-facing
  tensor notation `K ⊗^L L`;
- `core/canonical`: the localized `MonoidalCategory`/`SymmetricCategory` owner on
  `DerivedCategory (RingedSpace.Modules X)`;
- `bridge/view`: the monoidal functor structure on `Qh` induced by the localized tensor product.
-/

variable {X : RingedSpace.{u}}
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryTheory.Limits.HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : RingedSpace.Modules X, ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]
variable [∀ G₁ G₂ : GradedObject ℤ (RingedSpace.Modules X), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules X),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules X),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (RingedSpace.Modules X),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ ℱ : RingedSpace.Modules X,
  PreservesColimit (Functor.empty.{0} (RingedSpace.Modules X))
    ((curriedTensor (RingedSpace.Modules X)).obj ℱ)]
variable [∀ ℱ : RingedSpace.Modules X,
  PreservesColimit (Functor.empty.{0} (RingedSpace.Modules X))
    ((curriedTensor (RingedSpace.Modules X)).flip.obj ℱ)]

local notation "KMod" => HomotopyCategory (RingedSpace.Modules X) (ComplexShape.up ℤ)
local notation "DMod" => DerivedCategory (RingedSpace.Modules X)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (RingedSpace.Modules X) (ComplexShape.up ℤ)

local instance : MonoidalCategory KMod := CategoryTheory.homotopyCategory_monoidalCategory

local instance : SymmetricCategory KMod := CategoryTheory.homotopyCategory_symmetricCategory

/-- Lemma 20.50.6: the derived category `D(𝒪_X)` is a symmetric monoidal category. -/
@[stacks 0FPB, implicit_reducible] noncomputable instance ringedSpaceDerived_symmetricCategory :
    SymmetricCategory DMod := by
  -- Route correction: the previous proof tried to localize the homotopy-category tensor along all
  -- quasi-isomorphisms in `K(𝒪_X)`, but that asks for a false global monoidality statement.
  -- The source-facing owner should instead reuse the canonical symmetric structure on
  -- `D(𝒪_X)` coming from derived tensor product.
  -- TODO: either import the dependency-closed owner providing `SymmetricCategory DMod`, or build
  -- this instance from the Chapter 20 K-flat derived-tensor infrastructure in
  -- `Definition_20_26_14_Core`.
  sorry

end

end AlgebraicGeometry.RingedSpace
