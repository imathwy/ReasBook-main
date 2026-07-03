import Mathlib
import StacksProject_2024.Chap12.Lemma_12_16_2
import StacksProject_2024.Chap13.Definition_13_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open HomotopyCategory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KFilt" => HomotopyCategory (Fil^f(𝒜)) (up ℤ)

/- Domain-style sampling for Definition `13.13.2`.
- primary domain: filtered complexes in the homotopy category and their associated graded images;
- sampled owner declarations in this domain:
  `finiteFilteredObjectCat 𝒜`,
  `FilteredObject.associatedGradedFunctor`,
  `Functor.mapHomotopyCategory`,
  `HomotopyCategory.quasiIso`,
  `HomotopyCategory.subcategoryAcyclic`;
- best owner abstraction: the source-facing bridge functor from `K(Fil^f(𝒜))` to `K(Gr(𝒜))`
  induced by the associated graded functor on filtered objects, together with the canonical
  homotopy-category owners `HomotopyCategory.quasiIso` and
  `HomotopyCategory.subcategoryAcyclic` on the target;
- primitive data: the finite-filtered full-subcategory owner and the canonical associated-graded
  functor on filtered objects;
- derived API: the associated-graded homotopy functor and its inverse-image morphism and object
  properties on `K(Fil^f(𝒜))`;
- ambient structure check: the target graded category `GradedObject ℤ 𝒜` is already abelian
  upstream from `[Abelian 𝒜]`, so no separate file-scope assumption
  `[Abelian (GradedObject ℤ 𝒜)]` belongs in this local API;
- source/core/bridge triage:
  `source-facing`: the Stacks notations `FQis(𝒜)` and `FAc(𝒜)` on `K(Fil^f(𝒜))`;
  `core/canonical`: `HomotopyCategory.quasiIso` and `HomotopyCategory.subcategoryAcyclic`;
  `bridge/view`: the associated-graded homotopy functor from `K(Fil^f(𝒜))` to `K(Gr(𝒜))`.

This file therefore owns the associated-graded homotopy bridge used to define the Stacks
properties, so later files can reuse that bridge directly instead of redeclaring the same functor
under a second chapter-level name. -/

variable (𝒜) in
/-- The associated graded functor induced on the homotopy category of finite filtered objects. -/
abbrev filteredAssociatedGradedHomotopyFunctor :
    KFilt ⥤ HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ) :=
  (finiteFilteredObjectAssociatedGradedFunctor 𝒜).mapHomotopyCategory (up ℤ)

/-
Definition 13.13.2 (1): the morphism property of filtered quasi-isomorphisms on the homotopy
category of finite filtered complexes.
-/
variable (𝒜) in
/-- Definition 13.13.2 (1): the owner morphism property of filtered quasi-isomorphisms on the
homotopy category of finite filtered complexes. -/
abbrev filteredQuasiIso : MorphismProperty KFilt :=
  (quasiIso (GradedObject ℤ 𝒜) (up ℤ)).inverseImage
    (filteredAssociatedGradedHomotopyFunctor 𝒜)

scoped notation "FQis(" A:arg ")" => filteredQuasiIso A

/-
Definition 13.13.2 (2): the object property of filtered acyclic complexes on the homotopy
category of finite filtered complexes.
-/
variable (𝒜) in
/-- Definition 13.13.2 (2): the owner object property of filtered acyclic complexes on the
homotopy category of finite filtered complexes. -/
abbrev filteredAcyclic : ObjectProperty KFilt :=
  (subcategoryAcyclic (GradedObject ℤ 𝒜)).inverseImage
    (filteredAssociatedGradedHomotopyFunctor 𝒜)

scoped notation "FAc(" A:arg ")" => filteredAcyclic A

/- Companion checks: the associated-graded homotopy bridge and the Stacks notations `FQis(𝒜)` and
`FAc(𝒜)` are the canonical public owners used in later files. -/
#check
  (filteredAssociatedGradedHomotopyFunctor 𝒜 :
    KFilt ⥤ HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))
#check (filteredQuasiIso 𝒜 : MorphismProperty KFilt)
#check (filteredAcyclic 𝒜 : ObjectProperty KFilt)
#check (FQis(𝒜) : MorphismProperty KFilt)
#check (FAc(𝒜) : ObjectProperty KFilt)

end CategoryTheory
