import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Subcategory
import stacks_project.Chap12.Definition_12_10_1
import stacks_project.Chap13.Definition_13_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.17.1:
- primary domain: object properties on `DerivedCategory A`, their full subcategories, and the
  canonical triangulated structure induced from the ambient derived category;
- sampled owner declarations:
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.TStructure.t`,
  `ObjectProperty.inverseImage`,
  `ObjectProperty.IsTriangulated`,
  `IsTriangulated P.FullSubcategory`;
- best owner abstraction: the unbounded owner is the object property on `DerivedCategory A` cut
  out degreewise by the chosen `P : ObjectProperty A`, while the bounded source-facing owners are
  its inverse images along the canonical inclusions `D⁺(A) ⥤ D(A)`, `D⁻(A) ⥤ D(A)`, and
  `Dᵇ(A) ⥤ D(A)`;
- primitive-vs-derived split:
  primitive data: the ambient object property `P` and the degreewise cohomology test against
    `DerivedCategory.homologyFunctor`;
  derived API: the bounded variants obtained by pulling this owner back along the canonical
    bounded inclusions, plus the resulting full subcategories and their induced triangulated
    structures;
- source/core/bridge triage:
  `source-facing`: the subcategories `D_{P}`, `D⁺_{P}`, `D⁻_{P}`, `Dᵇ_{P}`;
  `core/canonical`: `ObjectProperty (DerivedCategory A)`, `ObjectProperty.inverseImage`,
    `ObjectProperty.IsTriangulated`, and `P.FullSubcategory`;
  `bridge/view`: the notation and the inclusion functors into the ambient bounded derived
    categories.

The owner layer in this file is therefore the object property on `DerivedCategory A`, together
with its canonical bounded pullbacks, not a second wrapper theorem for the induced triangulated
structure on the full subcategory. -/

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The object property on `D(A)` consisting of those derived objects whose every cohomology
object lies in the chosen object property `P ⊆ A`. -/
abbrev derivedCategoryCohomologyInProperty
    (P : ObjectProperty A) : ObjectProperty (DerivedCategory A) :=
  fun K ↦ ∀ n : ℤ, P ((DerivedCategory.homologyFunctor A n).obj K)

/-- The full subcategory `D_P(A) ⊆ D(A)` cut out by requiring all cohomology objects to lie in
`P`. -/
abbrev DerivedCategoryWithCohomologyIn (P : ObjectProperty A) :=
  (derivedCategoryCohomologyInProperty P).FullSubcategory

scoped[DerivedCategoryWithCohomologyIn] notation3:max "D_{" P "}" =>
  DerivedCategoryWithCohomologyIn P

/-- The cohomology-in-`P` owner on the bounded-below derived category `D⁺(A)`. -/
abbrev derivedCategoryBoundedBelowCohomologyInProperty
    (P : ObjectProperty A) : ObjectProperty (D⁺(A)) :=
  (derivedCategoryCohomologyInProperty P).inverseImage
    ((t.plus : ObjectProperty (DerivedCategory A)).ι)

/-- The bounded-below derived subcategory `D^+_P(A) ⊆ D⁺(A)` cut out by `P`. -/
abbrev DerivedCategoryPlusWithCohomologyIn (P : ObjectProperty A) :=
  (derivedCategoryBoundedBelowCohomologyInProperty P).FullSubcategory

scoped[DerivedCategoryWithCohomologyIn] notation3:max "D⁺_{" P "}" =>
  DerivedCategoryPlusWithCohomologyIn P

/-- The cohomology-in-`P` owner on the bounded-above derived category `D⁻(A)`. -/
abbrev derivedCategoryBoundedAboveCohomologyInProperty
    (P : ObjectProperty A) : ObjectProperty (D⁻(A)) :=
  (derivedCategoryCohomologyInProperty P).inverseImage
    ((t.minus : ObjectProperty (DerivedCategory A)).ι)

/-- The bounded-above derived subcategory `D^-_P(A) ⊆ D⁻(A)` cut out by `P`. -/
abbrev DerivedCategoryMinusWithCohomologyIn (P : ObjectProperty A) :=
  (derivedCategoryBoundedAboveCohomologyInProperty P).FullSubcategory

scoped[DerivedCategoryWithCohomologyIn] notation3:max "D⁻_{" P "}" =>
  DerivedCategoryMinusWithCohomologyIn P

/-- The cohomology-in-`P` owner on the bounded derived category `Dᵇ(A)`. -/
abbrev derivedCategoryBoundedCohomologyInProperty
    (P : ObjectProperty A) : ObjectProperty (Dᵇ(A)) :=
  (derivedCategoryCohomologyInProperty P).inverseImage
    ((t.bounded : ObjectProperty (DerivedCategory A)).ι)

/-- The bounded derived subcategory `D^b_P(A) ⊆ Dᵇ(A)` cut out by `P`. -/
abbrev DerivedCategoryBoundedWithCohomologyIn (P : ObjectProperty A) :=
  (derivedCategoryBoundedCohomologyInProperty P).FullSubcategory

scoped[DerivedCategoryWithCohomologyIn] notation3:max "Dᵇ_{" P "}" =>
  DerivedCategoryBoundedWithCohomologyIn P

open scoped DerivedCategoryWithCohomologyIn

-- Proof sketch: an isomorphism in `D(A)` induces an isomorphism on every cohomology object, so
-- membership in `P` transports degreewise along the cohomology isomorphisms.
/-- The full subcategory `D_P(A)` is strictly full whenever `P` is closed under isomorphisms in
`A`. -/
instance derivedCategoryCohomologyInProperty_isClosedUnderIsomorphisms
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] :
    ObjectProperty.IsClosedUnderIsomorphisms
      (derivedCategoryCohomologyInProperty P) := sorry

-- Proof sketch: a retract in `D(A)` is a direct summand, cohomology preserves biproducts, and a
-- weak Serre subcategory is closed under kernels, hence under direct summands of its objects.
/-- The full subcategory `D_P(A)` is saturated, i.e. stable under retracts. -/
instance derivedCategoryCohomologyInProperty_isSaturated
    (P : ObjectProperty A) [IsWeakSerreClass P] :
    ObjectProperty.IsStableUnderRetracts
      (derivedCategoryCohomologyInProperty P) := sorry

/- The bounded-below, bounded-above, and bounded cohomology-in-`P` owners are inverse images of
`derivedCategoryCohomologyInProperty P` along the canonical inclusions into `D(A)`. Their
strict-fullness, saturation, and triangulatedity are therefore the generic upstream
`ObjectProperty.inverseImage` instances, so no parallel local instance declarations are kept
here. -/

-- Proof sketch: the long exact cohomology sequence of a distinguished triangle and the weak
-- Serre condition on `P` give the two-out-of-three property degreewise; closure under zero and
-- shifts is formal in the derived category.
/-- The object property cutting out `D_P(A)` is triangulated. -/
instance derivedCategoryCohomologyInProperty_isTriangulated
    (P : ObjectProperty A) [IsWeakSerreClass P] :
    ObjectProperty.IsTriangulated
      (derivedCategoryCohomologyInProperty P) := sorry

-- Proof sketch: if each cohomology functor `H^n` preserves `J`-indexed colimits and the
-- coefficient property `P` is already closed under those colimits, then the defining degreewise
-- condition for `D_P(A)` is preserved after taking the colimit of a `J`-shaped diagram.
/-- The derived object property cut out by cohomology lying in `P` is closed under `J`-indexed
colimits whenever `P` is and all cohomology functors preserve those colimits. -/
theorem derivedCategoryCohomologyInProperty_isClosedUnderColimitsOfShape
    (P : ObjectProperty A) (J : Type*) [Category J]
    [P.IsClosedUnderColimitsOfShape J]
    [∀ n : ℤ, PreservesColimitsOfShape J (DerivedCategory.homologyFunctor A n)] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (derivedCategoryCohomologyInProperty P) J := sorry

section

variable (P : ObjectProperty A) [IsWeakSerreClass P]

/- Lemma 13.17.1: if `P` is a weak Serre subcategory of an abelian category `A`, then the full
subcategory `D_P(A) ⊆ D(A)` consisting of objects whose cohomology objects all lie in `P` is
triangulated. This is the generic full-subcategory instance applied to the owner property
`derivedCategoryCohomologyInProperty P`. -/
#check (inferInstance : IsTriangulated D_{P})

/- Companion recall: the bounded-below subcategory `D⁺_{P}` inherits the ambient triangulated
structure from the triangulated owner property
`derivedCategoryBoundedBelowCohomologyInProperty P`. -/
#check (inferInstance : IsTriangulated D⁺_{P})

/- Companion recall: the bounded-above subcategory `D⁻_{P}` inherits the ambient triangulated
structure from the triangulated owner property
`derivedCategoryBoundedAboveCohomologyInProperty P`. -/
#check (inferInstance : IsTriangulated D⁻_{P})

/- Companion recall: the bounded subcategory `Dᵇ_{P}` inherits the ambient triangulated
structure from the triangulated owner property
`derivedCategoryBoundedCohomologyInProperty P`. -/
#check (inferInstance : IsTriangulated Dᵇ_{P})

end

end CategoryTheory
