import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap12.Lemma_12_10_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open scoped DerivedCategoryWithCohomologyIn

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for 13.17.1.1:
- primary domain: derived categories of full subcategories cut out by object properties, together
  with the canonical factorization of a functor through such a full subcategory;
- sampled owner declarations:
  `ObjectProperty.lift`,
  `ObjectProperty.FullSubcategory`,
  `weakSerreSubcategory_inclusion_exact`,
  `DerivedCategory`,
  `D_{P}`;
- best owner abstraction: the source-facing comparison functor
  `D(P.FullSubcategory) ⥤ D_{P}`, built from `P.ι.mapDerivedCategory` via the canonical lift
  through a full subcategory;
- primitive data: the object property `P : ObjectProperty A`, the inclusion
  `P.ι : P.FullSubcategory ⥤ A`, and the chapter owner
  `D_{P}` cut out by cohomology lying in `P`;
- derived API: the objectwise landing theorem for `P.ι.mapDerivedCategory` and the resulting
  comparison functor;
- source/core/bridge triage:
  `source-facing`: `weakSerreSubcategoryDerivedComparisonFunctor P :
    D(P.FullSubcategory) ⥤ D_P(A)`;
  `core/canonical`: `ObjectProperty.lift`;
  `bridge/view`: the proof that `P.ι.mapDerivedCategory` lands in `D_P(A)`, which lets the
    canonical full-subcategory lift produce the source-facing comparison functor.

The source and target categories are already canonical expressions, so the local alias
`WeakSerreSubcategoryDerivedCategory` was duplicate API and is removed. -/

namespace CategoryTheory

section

open scoped CategoryTheory.ObjectProperty

variable (P : ObjectProperty A) [P.IsWeakSerreClass]

local instance : Limits.PreservesFiniteLimits P.ι :=
  weakSerreSubcategory_inclusion_preservesFiniteLimits P

local instance : Limits.PreservesFiniteColimits P.ι :=
  weakSerreSubcategory_inclusion_preservesFiniteColimits P

-- Proof sketch: exactness of the inclusion `P.ι` identifies the cohomology of
-- `(P.ι.mapDerivedCategory).obj K` with the image under `P.ι` of the cohomology objects
-- of `K`, and those objects lie in `P` by construction of `P.FullSubcategory`.
/-- The derived functor of the inclusion `P.ι : P.FullSubcategory ⥤ A` lands in the full
subcategory `D_{P}` cut out by cohomology lying in `P`. -/
theorem weakSerreSubcategory_mapDerivedCategory_obj_mem_derivedCategoryWithCohomologyIn
    (K : D(P.FullSubcategory)) :
    derivedCategoryCohomologyInProperty P (P.ι.mapDerivedCategory.obj K) := sorry

/-- 13.17.1.1: the canonical comparison functor `D(P.FullSubcategory) ⥤ D_{P}` induced by the
derived functor of the inclusion of the weak Serre full subcategory. -/
noncomputable abbrev weakSerreSubcategoryDerivedComparisonFunctor :
    D(P.FullSubcategory) ⥤ D_{P} :=
  (derivedCategoryCohomologyInProperty P).lift
    P.ι.mapDerivedCategory
    (weakSerreSubcategory_mapDerivedCategory_obj_mem_derivedCategoryWithCohomologyIn P)

end

end CategoryTheory
