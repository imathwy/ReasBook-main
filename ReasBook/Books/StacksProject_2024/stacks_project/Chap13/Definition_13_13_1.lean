import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.stacks_project.Chap12.Definition_12_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open scoped CategoryTheory ZeroObject

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroObject 𝒜]

-- Route correction: `Lemma_12_19_12` imports the broken `Lemma_12_19_4` branch in this
-- workspace, so this file keeps only the dependency-closed owner API from
-- `Definition_12_19_1` and restricts the local companion API to the full-subcategory owner and
-- forgetful functor.

/- Domain-style sampling for Definition 13.13.1:
- primary domain: filtered objects in a category with zero object and the full subcategory cut out
  by the finiteness predicate on filtrations;
- sampled owner declarations:
  `FilteredObject`,
  `FilteredObject.IsFinite`,
  `FullSubcategory`;
- owner abstraction: the source-facing owner for this item is the full subcategory
  `finiteFilteredObjectCat 𝒜`, built canonically as
  `(FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))).FullSubcategory`;
- source/core/bridge triage:
  `source-facing`: the category `Fil^f(𝒜)` of finite filtered objects;
  `core/canonical`: `FilteredObject 𝒜` together with the generic owner
    `(FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))).FullSubcategory`;
  `bridge/view`: the notation `Fil^f(𝒜)` for that full subcategory.

Primitive data versus derived API:
- primitive data: the ambient filtered-object owner `FilteredObject 𝒜` and the finiteness
  predicate `FilteredObject.IsFinite`;
- derived API: the full subcategory owner `finiteFilteredObjectCat 𝒜` and the textbook notation
  `Fil^f(𝒜)`.

This item is therefore `source-facing`, not a recall-only bridge: Definition `13.13.1` is the
right owner file for the finite filtered category itself, while later files should reuse this owner
rather than re-declare it. -/

/-- Definition 13.13.1: for a category `𝒜` with zero object, the category of finite filtered
objects is the full subcategory of `FilteredObject 𝒜` on objects whose filtration is finite. -/
abbrev finiteFilteredObjectCat (𝒜 : Type u) [Category.{v} 𝒜] [HasZeroObject 𝒜] :=
  ObjectProperty.FullSubcategory (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))

/- The Stacks Project writes the category of finite filtered objects as `Fil^f(𝒜)`. This is
notation for the source-facing owner `finiteFilteredObjectCat 𝒜`. -/
scoped notation "Fil" "^f" "(" C ")" => finiteFilteredObjectCat C

end CategoryTheory
