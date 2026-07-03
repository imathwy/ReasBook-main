import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Subcategory

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_17_1 (from Chap13) -/
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
-- weak LinearRepresentations_Serre_1977 subcategory is closed under kernels, hence under direct summands of its objects.
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
-- LinearRepresentations_Serre_1977 condition on `P` give the two-out-of-three property degreewise; closure under zero and
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

/- Lemma 13.17.1: if `P` is a weak LinearRepresentations_Serre_1977 subcategory of an abelian category `A`, then the full
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

/-! ### Lemma_13_17_2 (from Chap13) -/
open CategoryTheory Limits

noncomputable section

universe wA wQ uA vA

namespace _root_.CategoryTheory.ObjectProperty

open _root_.CategoryTheory.ObjectProperty.SerreClassLocalization

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

local notation "Q" => P.isoModSerre.Q

local instance : Abelian P.isoModSerre.Localization :=
  abelian Q P

local instance : PreservesFiniteLimits Q :=
  preservesFiniteLimits Q P

local instance : PreservesFiniteColimits Q :=
  preservesFiniteColimits Q P

variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wQ} (P.isoModSerre.Localization)]

/- Domain-style sampling for 13.17.2:
- primary domain: LinearRepresentations_Serre_1977 localizations of abelian categories and the induced functor on derived
  categories;
- sampled owner declarations:
  `ObjectProperty.SerreClassLocalization.abelian`,
  `ObjectProperty.SerreClassLocalization.preservesFiniteLimits`,
  `ObjectProperty.SerreClassLocalization.preservesFiniteColimits`,
  `CategoryTheory.Functor.mapDerivedCategory`,
  `CategoryTheory.Functor.EssSurj`;
- best owner abstraction: the derived functor owner `Q.mapDerivedCategory` of the
  canonical LinearRepresentations_Serre_1977 quotient functor `Q := P.isoModSerre.Q`;
- primitive data: the LinearRepresentations_Serre_1977 class `P` and the quotient functor `Q`;
- derived API: the abelian structure on `P.isoModSerre.Localization` and the finite-limit and
  finite-colimit preservation instances for `Q`, supplied canonically by the LinearRepresentations_Serre_1977-localization
  owner API and consumed directly by `Q.mapDerivedCategory`;
- source/core/bridge triage:
  `source-facing`: the essential-surjectivity statement for the derived LinearRepresentations_Serre_1977 quotient functor;
  `core/canonical`: `Q.mapDerivedCategory`;
  `bridge/view`: objectwise preimages in the underived LinearRepresentations_Serre_1977 quotient, transported to the derived
  category through complex representatives and the localization map `DerivedCategory.Q`.

This file therefore uses the LinearRepresentations_Serre_1977-localization owner instances directly instead of repackaging
them through a local exactness wrapper. -/

-- Proof sketch: represent an object of `D(A / P)` by a complex in the LinearRepresentations_Serre_1977 quotient, then use
-- Lemma 12.10.6 degreewise to lift the differential data to a quasi-isomorphic complex in `A`.
-- The lifted complex becomes isomorphic to the original object after applying the derived functor,
-- producing the canonical owner witness `Q.mapDerivedCategory.EssSurj`.
/-- Lemma 13.17.2: if `P` is a LinearRepresentations_Serre_1977 subcategory of an abelian category `A`, then the canonical
functor `D(A) ⟶ D(A/P)` induced by the LinearRepresentations_Serre_1977 quotient functor is essentially surjective. -/
theorem serreQuotientDerivedFunctor_essSurj :
    Functor.EssSurj ((Q).mapDerivedCategory) := sorry

end _root_.CategoryTheory.ObjectProperty

/-! ### Lemma_13_17_3 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open _root_.CategoryTheory.ObjectProperty.SerreClassLocalization
open scoped DerivedCategoryWithCohomologyIn

noncomputable section

universe uA vA

attribute [local instance] HasDerivedCategory.standard

namespace _root_.CategoryTheory.ObjectProperty

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

local notation "Q" => P.isoModSerre.Q

local instance : Abelian P.isoModSerre.Localization :=
  abelian Q P

local instance : PreservesFiniteLimits Q :=
  preservesFiniteLimits Q P

local instance : PreservesFiniteColimits Q :=
  preservesFiniteColimits Q P

/- Domain-style sampling for 13.17.3:
- primary domain: LinearRepresentations_Serre_1977 localizations of abelian categories and the induced functors on the
  ordinary and bounded derived categories;
- sampled owner declarations:
  `Adjunction.derived`,
  `Adjunction.isLocalization'`,
  `Functor.kernel`,
  `kernel_trW_eq_self`,
  `Functor.mapDerivedCategory`,
  `derivedCategoryBoundedBelowCohomologyInProperty`,
  `derivedCategoryBoundedAboveCohomologyInProperty`,
  `derivedCategoryBoundedCohomologyInProperty`,
  `ObjectProperty.lift`,
  `D⁺_{P}`,
  `D⁻_{P}`,
  `Dᵇ_{P}`;
- best owner abstraction: the canonical derived LinearRepresentations_Serre_1977 quotient functor
  `(Q).mapDerivedCategory`, together with the canonical localization owner
  `Adjunction.isLocalization'` on the derived adjunction and the canonical kernel owner
  `Functor.kernel ((Q).mapDerivedCategory)`; the chapter owners `D⁺_{P}`, `D⁻_{P}`, `Dᵇ_{P}`
  then supply the bounded kernel subcategories, and on the bounded source categories the
  corresponding chapter-owned bounded properties
  `derivedCategoryBoundedBelowCohomologyInProperty P`,
  `derivedCategoryBoundedAboveCohomologyInProperty P`,
  `derivedCategoryBoundedCohomologyInProperty P`;
- primitive-vs-derived split:
  primitive data: the LinearRepresentations_Serre_1977 quotient functor `Q`, its derived functor
    `(Q).mapDerivedCategory`, the canonical localization owner
    `Adjunction.isLocalization'` on the derived adjunction, the kernel owner
    `Functor.kernel ((Q).mapDerivedCategory)`, and the canonical bounded derived-category owners
    `t.plus`, `t.minus`, `t.bounded`;
  derived API: the restricted derived quotient functors on `D⁺(A)`, `D⁻(A)`, `Dᵇ(A)`, and the
    corresponding kernel identifications via the chapter-owned cohomology-in-`P` properties on
    `D(A)`, `D⁺(A)`, `D⁻(A)`, and `Dᵇ(A)`;
- source/core/bridge triage:
  `source-facing`: the localization statements on `D(A)`, `D⁺(A)`, `D⁻(A)`, `Dᵇ(A)`;
  `core/canonical`: `(Q).mapDerivedCategory`, `Adjunction.isLocalization'`,
    `Functor.kernel ((Q).mapDerivedCategory)`, `D⁺(-)`, `D⁻(-)`, `Dᵇ(-)`,
    `D⁺_{P}`, `D⁻_{P}`, `Dᵇ_{P}`,
    `derivedCategoryBoundedBelowCohomologyInProperty`,
    `derivedCategoryBoundedAboveCohomologyInProperty`,
    `derivedCategoryBoundedCohomologyInProperty`, and `ObjectProperty.lift`;
  `bridge/view`: the kernel identifications from `Functor.kernel ((Q).mapDerivedCategory)` to
    `derivedCategoryCohomologyInProperty P` and from the bounded restricted kernels to
    `derivedCategoryBoundedBelowCohomologyInProperty P`,
    `derivedCategoryBoundedAboveCohomologyInProperty P`, and
    `derivedCategoryBoundedCohomologyInProperty P`, together with the canonical inclusion
    functors from `D⁺_{P}`, `D⁻_{P}`, `Dᵇ_{P}` into `D⁺(A)`, `D⁻(A)`, and `Dᵇ(A)`.

This file therefore keeps the bounded kernel vocabulary from `Lemma_13_17_1` central and uses the
bounded source-category owners
`derivedCategoryBoundedBelowCohomologyInProperty P`,
`derivedCategoryBoundedAboveCohomologyInProperty P`, and
`derivedCategoryBoundedCohomologyInProperty P` in the main kernel and localization statements,
while the unbounded localization statement passes through the canonical kernel owner of
`(Q).mapDerivedCategory` before being restated in source-facing `D_{P}(A)` language. The
canonical inclusions of `D⁺_{P}`, `D⁻_{P}`, and `Dᵇ_{P}` remain bridge/view API rather than the
main theorem interface. -/

section

-- Proof sketch: apply `Adjunction.derived` to `u ⊣ P.isoModSerre.Q` to obtain an adjunction on
-- derived categories, then use the canonical localization theorem `Adjunction.isLocalization'`
-- for the right adjoint `(Q).mapDerivedCategory`. Finally rewrite the canonical kernel owner via
-- `kernel_serreQuotientDerivedFunctor` so that the localization statement is expressed in the
-- source-facing `D_{P}(A)` language.
/-- Lemma 13.17.3: if the LinearRepresentations_Serre_1977 quotient functor `A ⥤ A/P` admits a fully faithful left adjoint,
then the induced functor on derived categories identifies `D(A/P)` with the Verdier quotient
`D(A) / D_P(A)`, formalized as localization at the morphisms whose cone lies in `D_P(A)`. -/
theorem serreQuotientDerivedFunctor_isLocalization_of_fullyFaithfulLeftAdjoint
    (u : P.isoModSerre.Localization ⥤ A) (adj : u ⊣ Q) [u.Full] [u.Faithful]
    :
    Functor.IsLocalization
      (Q).mapDerivedCategory
      (derivedCategoryCohomologyInProperty P).trW :=
  sorry

-- Proof sketch: the canonical owner for objects killed by an exact triangulated functor is
-- `Functor.kernel`; for `Q.mapDerivedCategory`, vanishing in the quotient derived category is
-- equivalent to all cohomology objects vanishing in the LinearRepresentations_Serre_1977 quotient, hence to their lying in
-- `P`.
/-- The kernel of the derived LinearRepresentations_Serre_1977 quotient functor is the cohomology-in-`P` owner on `D(A)`.
This is the bridge from the canonical kernel owner to the source-facing subcategory `D_{P}(A)`.
-/
theorem kernel_serreQuotientDerivedFunctor :
    Functor.kernel ((Q).mapDerivedCategory) =
      derivedCategoryCohomologyInProperty P := sorry

-- Proof sketch: exact functors preserve cohomology vanishing in sufficiently negative degrees, so
-- applying the derived LinearRepresentations_Serre_1977 quotient functor to a bounded-below object again yields a
-- bounded-below object in the quotient derived category.
/-- The derived LinearRepresentations_Serre_1977 quotient functor sends bounded-below objects to bounded-below objects. -/
theorem serreQuotientDerivedFunctor_obj_mem_boundedBelowDerivedCategory
    (X : D⁺(A)) :
    (t.plus : ObjectProperty _) ((t.plus.ι ⋙ (Q).mapDerivedCategory).obj X) := sorry

/-- The derived LinearRepresentations_Serre_1977 quotient functor restricted to bounded-below objects. -/
abbrev serreQuotientDerivedFunctorPlus :
    D⁺(A) ⥤ D⁺(P.isoModSerre.Localization) :=
  (t.plus : ObjectProperty _).lift
    (t.plus.ι ⋙ (Q).mapDerivedCategory)
    (serreQuotientDerivedFunctor_obj_mem_boundedBelowDerivedCategory P)

-- Proof sketch: apply the unbounded localization statement to the bounded-below full
-- subcategories, using that the derived LinearRepresentations_Serre_1977 quotient functor preserves bounded-below objects
-- and that `D^+_P(A)` is the kernel subcategory inside `D^+(A)`.
/-- The kernel of the bounded-below derived LinearRepresentations_Serre_1977 quotient functor is the bounded-below
cohomology-in-`P` object property on `D^+(A)`, equivalently the image of `D^+_P(A)`. -/
theorem kernel_serreQuotientDerivedFunctorPlus :
    Functor.kernel (serreQuotientDerivedFunctorPlus P) =
      derivedCategoryBoundedBelowCohomologyInProperty P := sorry

/-- The bounded-below derived LinearRepresentations_Serre_1977 quotient functor realizes `D^+(A/P)` as the Verdier quotient
`D^+(A) / D^+_P(A)`. -/
theorem serreQuotientDerivedFunctorPlus_isLocalization_of_fullyFaithfulLeftAdjoint
    (u : P.isoModSerre.Localization ⥤ A) (adj : u ⊣ Q) [u.Full] [u.Faithful]
    :
    Functor.IsLocalization
      (serreQuotientDerivedFunctorPlus P)
      (derivedCategoryBoundedBelowCohomologyInProperty P).trW := sorry

-- Proof sketch: exact functors preserve cohomology vanishing in sufficiently positive degrees, so
-- bounded-above objects remain bounded above after applying the derived LinearRepresentations_Serre_1977 quotient functor.
/-- The derived LinearRepresentations_Serre_1977 quotient functor sends bounded-above objects to bounded-above objects. -/
theorem serreQuotientDerivedFunctor_obj_mem_boundedAboveDerivedCategory
    (X : D⁻(A)) :
    (t.minus : ObjectProperty _) ((t.minus.ι ⋙ (Q).mapDerivedCategory).obj X) := sorry

/-- The derived LinearRepresentations_Serre_1977 quotient functor restricted to bounded-above objects. -/
abbrev serreQuotientDerivedFunctorMinus :
    D⁻(A) ⥤ D⁻(P.isoModSerre.Localization) :=
  (t.minus : ObjectProperty _).lift
    (t.minus.ι ⋙ (Q).mapDerivedCategory)
    (serreQuotientDerivedFunctor_obj_mem_boundedAboveDerivedCategory P)

-- Proof sketch: combine the unbounded localization statement with preservation of bounded-above
-- cohomology and identify `D^-_P(A)` as the kernel subcategory in `D^-(A)`.
/-- The kernel of the bounded-above derived LinearRepresentations_Serre_1977 quotient functor is the bounded-above
cohomology-in-`P` object property on `D^-(A)`, equivalently the image of `D^-_P(A)`. -/
theorem kernel_serreQuotientDerivedFunctorMinus :
    Functor.kernel (serreQuotientDerivedFunctorMinus P) =
      derivedCategoryBoundedAboveCohomologyInProperty P := sorry

/-- The bounded-above derived LinearRepresentations_Serre_1977 quotient functor realizes `D^-(A/P)` as the Verdier quotient
`D^-(A) / D^-_P(A)`. -/
theorem serreQuotientDerivedFunctorMinus_isLocalization_of_fullyFaithfulLeftAdjoint
    (u : P.isoModSerre.Localization ⥤ A) (adj : u ⊣ Q) [u.Full] [u.Faithful]
    :
    Functor.IsLocalization
      (serreQuotientDerivedFunctorMinus P)
      (derivedCategoryBoundedAboveCohomologyInProperty P).trW := sorry

-- Proof sketch: preserve both the bounded-below and bounded-above vanishing ranges under the
-- derived LinearRepresentations_Serre_1977 quotient functor to obtain preservation of boundedness.
/-- The derived LinearRepresentations_Serre_1977 quotient functor sends bounded objects to bounded objects. -/
theorem serreQuotientDerivedFunctor_obj_mem_boundedDerivedCategory
    (X : Dᵇ(A)) :
    (t.bounded : ObjectProperty _) ((t.bounded.ι ⋙ (Q).mapDerivedCategory).obj X) := sorry

/-- The derived LinearRepresentations_Serre_1977 quotient functor restricted to bounded objects. -/
abbrev serreQuotientDerivedFunctorBounded :
    Dᵇ(A) ⥤ Dᵇ(P.isoModSerre.Localization) :=
  (t.bounded : ObjectProperty _).lift
    (t.bounded.ι ⋙ (Q).mapDerivedCategory)
    (serreQuotientDerivedFunctor_obj_mem_boundedDerivedCategory P)

-- Proof sketch: combine the unbounded localization statement with preservation of boundedness and
-- identify `D^b_P(A)` as the Verdier kernel inside `D^b(A)`.
/-- The kernel of the bounded derived LinearRepresentations_Serre_1977 quotient functor is the bounded cohomology-in-`P`
object property on `D^b(A)`, equivalently the image of `D^b_P(A)`. -/
theorem kernel_serreQuotientDerivedFunctorBounded :
    Functor.kernel (serreQuotientDerivedFunctorBounded P) =
      derivedCategoryBoundedCohomologyInProperty P := sorry

/-- The bounded derived LinearRepresentations_Serre_1977 quotient functor realizes `D^b(A/P)` as the Verdier quotient
`D^b(A) / D^b_P(A)`. -/
theorem serreQuotientDerivedFunctorBounded_isLocalization_of_fullyFaithfulLeftAdjoint
    (u : P.isoModSerre.Localization ⥤ A) (adj : u ⊣ Q) [u.Full] [u.Faithful]
    :
    Functor.IsLocalization
      (serreQuotientDerivedFunctorBounded P)
      (derivedCategoryBoundedCohomologyInProperty P).trW := sorry

end

end _root_.CategoryTheory.ObjectProperty

/-! ### Lemma_13_17_4 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open scoped DerivedCategoryWithCohomologyIn

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace _root_.CategoryTheory.ObjectProperty

section

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsWeakSerreClass]

/- Domain-style sampling for Lemma 13.17.4:
- primary domain: bounded-above derived categories of a LinearRepresentations_Serre_1977 full subcategory and the canonical
  comparison with the bounded-above part of `D_{P}(A)`;
- sampled owner declarations:
  `P.ι.mapDerivedCategory`,
  `weakSerreSubcategory_mapDerivedCategory_obj_mem_derivedCategoryWithCohomologyIn`,
  `derivedCategoryBoundedAboveCohomologyInProperty`,
  `ObjectProperty.lift`;
- best owner abstraction: the primitive owner is the derived functor
  `P.ι.mapDerivedCategory : D(P.FullSubcategory) ⥤ D(A)` of the inclusion
  `P.ι : P.FullSubcategory ⥤ A`, together with the chapter owner
  `derivedCategoryBoundedAboveCohomologyInProperty P` on `D⁻(A)`;
- primitive-vs-derived split:
  primitive data: the inclusion `P.ι : P.FullSubcategory ⥤ A`, its derived functor
    `P.ι.mapDerivedCategory`, and the owner property
    `derivedCategoryBoundedAboveCohomologyInProperty P` on `D⁻(A)`;
  derived API: the bounded-above landing theorem and the induced lift
    `D⁻(P.FullSubcategory) ⥤ D⁻_{P}`;
- source/core/bridge triage:
  `source-facing`: the bounded-above comparison functor and its equivalence criterion;
  `core/canonical`: `P.ι.mapDerivedCategory`,
    `weakSerreSubcategory_mapDerivedCategory_obj_mem_derivedCategoryWithCohomologyIn P`,
    `derivedCategoryBoundedAboveCohomologyInProperty P`, and `ObjectProperty.lift`;
  `bridge/view`: the bounded-above lift of the primitive derived inclusion functor.

The local `Abelian P.FullSubcategory` wrapper was duplicate API: for a weak LinearRepresentations_Serre_1977 class, the canonical
mathlib instance on `P.FullSubcategory` is already available and is reused directly here. -/

local instance : PreservesFiniteLimits P.ι :=
  weakSerreSubcategory_inclusion_preservesFiniteLimits P

local instance : PreservesFiniteColimits P.ι :=
  weakSerreSubcategory_inclusion_preservesFiniteColimits P

-- Proof sketch: `13_17_1_1` already proves the cohomology-in-`P` half for
-- `P.ι.mapDerivedCategory`. For bounded-above-ness, represent `X` by a bounded-above cochain
-- complex in `P.FullSubcategory`; applying `P.ι` termwise preserves strict bounded-above support,
-- so the image in `D(A)` still lies in `t.minus`.
/-- The derived functor of the inclusion `P.ι : P.FullSubcategory ⥤ A` preserves
bounded-above-ness. -/
theorem weakSerreSubcategory_mapDerivedCategory_obj_mem_boundedAboveDerivedCategory
    (X : D⁻(P.FullSubcategory)) :
    (t.minus : ObjectProperty (D(A))) ((t.minus.ι ⋙ P.ι.mapDerivedCategory).obj X) := by
  change (t.minus : ObjectProperty (D(A))) ((P.ι.mapDerivedCategory).obj X.obj)
  rcases X.property with ⟨n, hX⟩
  let _ : X.obj.IsLE n := hX
  obtain ⟨K, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X.obj n
  let e' :
      ((P.ι.mapDerivedCategory).obj X.obj) ≅
        DerivedCategory.Q.obj
          ((P.ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (P.ι.mapDerivedCategory).mapIso e ≪≫ (P.ι.mapDerivedCategoryFactors.app K)
  exact ⟨n, t.isLE_of_iso e'.symm n⟩

/-- The bounded-above restriction of the canonical comparison functor
`D⁻(P.FullSubcategory) ⥤ D⁻_{P}`. -/
noncomputable abbrev weakSerreSubcategoryDerivedComparisonFunctorMinus :
    D⁻(P.FullSubcategory) ⥤ D⁻_{P} :=
  (derivedCategoryBoundedAboveCohomologyInProperty P).lift
    ((t.minus : ObjectProperty (D(A))).lift
      (t.minus.ι ⋙ P.ι.mapDerivedCategory)
      (weakSerreSubcategory_mapDerivedCategory_obj_mem_boundedAboveDerivedCategory P))
    (fun X ↦ by
      simpa using
        weakSerreSubcategory_mapDerivedCategory_obj_mem_derivedCategoryWithCohomologyIn P
          (((t.minus : ObjectProperty (D(P.FullSubcategory))).ι).obj X))

end

section

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

-- Proof sketch: the hypothesis lets one replace a bounded-above complex in `A` with cohomology in
-- `P` by a quasi-isomorphic bounded-above subcomplex whose terms lie in `P.FullSubcategory`.
-- This gives essential surjectivity of the comparison functor, and the same replacement applied to
-- mapping cones and homotopies yields faithfulness and fullness.
/-- Lemma 13.17.4: let `P` be a LinearRepresentations_Serre_1977 subcategory of an abelian category `A`. Assume that for
every epimorphism `f : X ⟶ Y` with `Y` an object of `P.FullSubcategory`, there exist an object
`X'` of `P.FullSubcategory`, a monomorphism `ι : X' ⟶ X`, and an epimorphism `X' ⟶ Y` given by
`ι ≫ f`. Then the canonical comparison functor `D^-(P) ⟶ D^-_P(A)` is an equivalence. -/
theorem serreSubcategoryDerivedComparisonFunctorMinus_isEquivalence_of_epi_lift
    (hP :
      ∀ ⦃X : A⦄ (Y : P.FullSubcategory) (f : X ⟶ Y.obj) [Epi f],
        ∃ (X' : P.FullSubcategory) (ι : X'.obj ⟶ X), Mono ι ∧ Epi (ι ≫ f)) :
    Functor.IsEquivalence (weakSerreSubcategoryDerivedComparisonFunctorMinus P) := sorry

end

end _root_.CategoryTheory.ObjectProperty
