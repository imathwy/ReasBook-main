import stacks_project.Chap13.Lemma_13_17_1
import stacks_project.Chap13.Lemma_13_17_2

-- Declarations for this item will be appended below by the statement pipeline.

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
- primary domain: Serre localizations of abelian categories and the induced functors on the
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
- best owner abstraction: the canonical derived Serre quotient functor
  `(Q).mapDerivedCategory`, together with the canonical localization owner
  `Adjunction.isLocalization'` on the derived adjunction and the canonical kernel owner
  `Functor.kernel ((Q).mapDerivedCategory)`; the chapter owners `D⁺_{P}`, `D⁻_{P}`, `Dᵇ_{P}`
  then supply the bounded kernel subcategories, and on the bounded source categories the
  corresponding chapter-owned bounded properties
  `derivedCategoryBoundedBelowCohomologyInProperty P`,
  `derivedCategoryBoundedAboveCohomologyInProperty P`,
  `derivedCategoryBoundedCohomologyInProperty P`;
- primitive-vs-derived split:
  primitive data: the Serre quotient functor `Q`, its derived functor
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
/-- Lemma 13.17.3: if the Serre quotient functor `A ⥤ A/P` admits a fully faithful left adjoint,
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
-- equivalent to all cohomology objects vanishing in the Serre quotient, hence to their lying in
-- `P`.
/-- The kernel of the derived Serre quotient functor is the cohomology-in-`P` owner on `D(A)`.
This is the bridge from the canonical kernel owner to the source-facing subcategory `D_{P}(A)`.
-/
theorem kernel_serreQuotientDerivedFunctor :
    Functor.kernel ((Q).mapDerivedCategory) =
      derivedCategoryCohomologyInProperty P := sorry

-- Proof sketch: exact functors preserve cohomology vanishing in sufficiently negative degrees, so
-- applying the derived Serre quotient functor to a bounded-below object again yields a
-- bounded-below object in the quotient derived category.
/-- The derived Serre quotient functor sends bounded-below objects to bounded-below objects. -/
theorem serreQuotientDerivedFunctor_obj_mem_boundedBelowDerivedCategory
    (X : D⁺(A)) :
    (t.plus : ObjectProperty _) ((t.plus.ι ⋙ (Q).mapDerivedCategory).obj X) := sorry

/-- The derived Serre quotient functor restricted to bounded-below objects. -/
abbrev serreQuotientDerivedFunctorPlus :
    D⁺(A) ⥤ D⁺(P.isoModSerre.Localization) :=
  (t.plus : ObjectProperty _).lift
    (t.plus.ι ⋙ (Q).mapDerivedCategory)
    (serreQuotientDerivedFunctor_obj_mem_boundedBelowDerivedCategory P)

-- Proof sketch: apply the unbounded localization statement to the bounded-below full
-- subcategories, using that the derived Serre quotient functor preserves bounded-below objects
-- and that `D^+_P(A)` is the kernel subcategory inside `D^+(A)`.
/-- The kernel of the bounded-below derived Serre quotient functor is the bounded-below
cohomology-in-`P` object property on `D^+(A)`, equivalently the image of `D^+_P(A)`. -/
theorem kernel_serreQuotientDerivedFunctorPlus :
    Functor.kernel (serreQuotientDerivedFunctorPlus P) =
      derivedCategoryBoundedBelowCohomologyInProperty P := sorry

/-- The bounded-below derived Serre quotient functor realizes `D^+(A/P)` as the Verdier quotient
`D^+(A) / D^+_P(A)`. -/
theorem serreQuotientDerivedFunctorPlus_isLocalization_of_fullyFaithfulLeftAdjoint
    (u : P.isoModSerre.Localization ⥤ A) (adj : u ⊣ Q) [u.Full] [u.Faithful]
    :
    Functor.IsLocalization
      (serreQuotientDerivedFunctorPlus P)
      (derivedCategoryBoundedBelowCohomologyInProperty P).trW := sorry

-- Proof sketch: exact functors preserve cohomology vanishing in sufficiently positive degrees, so
-- bounded-above objects remain bounded above after applying the derived Serre quotient functor.
/-- The derived Serre quotient functor sends bounded-above objects to bounded-above objects. -/
theorem serreQuotientDerivedFunctor_obj_mem_boundedAboveDerivedCategory
    (X : D⁻(A)) :
    (t.minus : ObjectProperty _) ((t.minus.ι ⋙ (Q).mapDerivedCategory).obj X) := sorry

/-- The derived Serre quotient functor restricted to bounded-above objects. -/
abbrev serreQuotientDerivedFunctorMinus :
    D⁻(A) ⥤ D⁻(P.isoModSerre.Localization) :=
  (t.minus : ObjectProperty _).lift
    (t.minus.ι ⋙ (Q).mapDerivedCategory)
    (serreQuotientDerivedFunctor_obj_mem_boundedAboveDerivedCategory P)

-- Proof sketch: combine the unbounded localization statement with preservation of bounded-above
-- cohomology and identify `D^-_P(A)` as the kernel subcategory in `D^-(A)`.
/-- The kernel of the bounded-above derived Serre quotient functor is the bounded-above
cohomology-in-`P` object property on `D^-(A)`, equivalently the image of `D^-_P(A)`. -/
theorem kernel_serreQuotientDerivedFunctorMinus :
    Functor.kernel (serreQuotientDerivedFunctorMinus P) =
      derivedCategoryBoundedAboveCohomologyInProperty P := sorry

/-- The bounded-above derived Serre quotient functor realizes `D^-(A/P)` as the Verdier quotient
`D^-(A) / D^-_P(A)`. -/
theorem serreQuotientDerivedFunctorMinus_isLocalization_of_fullyFaithfulLeftAdjoint
    (u : P.isoModSerre.Localization ⥤ A) (adj : u ⊣ Q) [u.Full] [u.Faithful]
    :
    Functor.IsLocalization
      (serreQuotientDerivedFunctorMinus P)
      (derivedCategoryBoundedAboveCohomologyInProperty P).trW := sorry

-- Proof sketch: preserve both the bounded-below and bounded-above vanishing ranges under the
-- derived Serre quotient functor to obtain preservation of boundedness.
/-- The derived Serre quotient functor sends bounded objects to bounded objects. -/
theorem serreQuotientDerivedFunctor_obj_mem_boundedDerivedCategory
    (X : Dᵇ(A)) :
    (t.bounded : ObjectProperty _) ((t.bounded.ι ⋙ (Q).mapDerivedCategory).obj X) := sorry

/-- The derived Serre quotient functor restricted to bounded objects. -/
abbrev serreQuotientDerivedFunctorBounded :
    Dᵇ(A) ⥤ Dᵇ(P.isoModSerre.Localization) :=
  (t.bounded : ObjectProperty _).lift
    (t.bounded.ι ⋙ (Q).mapDerivedCategory)
    (serreQuotientDerivedFunctor_obj_mem_boundedDerivedCategory P)

-- Proof sketch: combine the unbounded localization statement with preservation of boundedness and
-- identify `D^b_P(A)` as the Verdier kernel inside `D^b(A)`.
/-- The kernel of the bounded derived Serre quotient functor is the bounded cohomology-in-`P`
object property on `D^b(A)`, equivalently the image of `D^b_P(A)`. -/
theorem kernel_serreQuotientDerivedFunctorBounded :
    Functor.kernel (serreQuotientDerivedFunctorBounded P) =
      derivedCategoryBoundedCohomologyInProperty P := sorry

/-- The bounded derived Serre quotient functor realizes `D^b(A/P)` as the Verdier quotient
`D^b(A) / D^b_P(A)`. -/
theorem serreQuotientDerivedFunctorBounded_isLocalization_of_fullyFaithfulLeftAdjoint
    (u : P.isoModSerre.Localization ⥤ A) (adj : u ⊣ Q) [u.Full] [u.Faithful]
    :
    Functor.IsLocalization
      (serreQuotientDerivedFunctorBounded P)
      (derivedCategoryBoundedCohomologyInProperty P).trW := sorry

end

end _root_.CategoryTheory.ObjectProperty
