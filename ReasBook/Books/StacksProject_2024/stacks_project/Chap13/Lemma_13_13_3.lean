import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_16_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_13_2

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

/- Domain-style sampling for Lemma `13.13.3`.
- primary domain: homological functors out of the homotopy category of finite filtered objects;
- sampled core/canonical declarations in this domain:
  `finiteFilteredObjectAssociatedGradedFunctor`,
  `filteredAssociatedGradedHomotopyFunctor`,
  `finiteFilteredObjectForgetFunctor`,
  `HomotopyCategory.homologyFunctor`;
- best owner abstraction: the owner is the canonical `Functor.IsHomological` instance on composites
  into degree-zero homology, together with the owner instances
  `Functor.CommShift` and `Functor.IsTriangulated` for `mapHomotopyCategory`;
- primitive data: the canonical associated-graded and forgetful functors from Definitions
  `13.13.1` and `13.13.2`;
- derived API: the three homologicality facts for `H^0 ∘ gr`, `H^0 ∘ gr^p`, and
  `H^0 ∘ forget`.

Source/core/bridge triage:
- `source-facing`: the three homologicality statements in Lemma `13.13.3`;
- `core/canonical`: `Functor.CommShift`, `Functor.IsTriangulated`, and
  `Functor.IsHomological`;
- `bridge/view`: `filteredAssociatedGradedHomotopyFunctor 𝒜`,
  `(GradedObject.eval p).mapHomotopyCategory (up ℤ)`, and
  `(finiteFilteredObjectForgetFunctor 𝒜).mapHomotopyCategory (up ℤ)`.

This item is therefore a pure canonical-recall file: after supplying the ordinary finite/binary
biproduct support on `Fil^f(𝒜)`, mathlib already infers the needed `CommShift`,
`IsTriangulated`, and `IsHomological` structures, so no parallel public wrapper declarations
belong here. -/

section Homologicality

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => Fil^f(𝒜)
local notation "Hzero" => HomotopyCategory.homologyFunctor 𝒜 (up ℤ) 0

local instance : HasFiniteBiproducts FilF :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance : HasBinaryBiproducts FilF :=
  hasBinaryBiproducts_of_finite_biproducts FilF

/-- Lemma 13.13.3: the functor `K(Fil^f(𝒜)) ⥤ Gr(𝒜)` sending `K^•` to `H^0(gr(K^•))` is
homological. -/
instance filteredAssociatedGraded_homologyZero_isHomological :
    (filteredAssociatedGradedHomotopyFunctor 𝒜 ⋙
      HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (up ℤ) 0).IsHomological := by
  -- The source proof factors through exactness of `gr` and homologicality of `H^0`.
  infer_instance

/-- Helper for Lemma 13.13.3: for each `p : ℤ`, the functor sending `K^•` to `H^0(gr^p(K^•))`
is homological. -/
instance filteredGradedPiece_homologyZero_isHomological (p : ℤ) :
    (filteredAssociatedGradedHomotopyFunctor 𝒜 ⋙
      (GradedObject.eval p).mapHomotopyCategory (up ℤ) ⋙ Hzero).IsHomological := by
  -- This specializes the graded homologicality statement along evaluation at degree `p`.
  infer_instance

/-- Helper for Lemma 13.13.3: the functor sending `K^•` to `H^0((forget F)K^•)` is homological. -/
instance filteredForget_homologyZero_isHomological :
    ((finiteFilteredObjectForgetFunctor 𝒜 : FilF ⥤ 𝒜).mapHomotopyCategory (up ℤ) ⋙
      Hzero).IsHomological := by
  -- This is the forgetful exact functor composed with the standard degree-zero homology functor.
  infer_instance

end Homologicality

end CategoryTheory
