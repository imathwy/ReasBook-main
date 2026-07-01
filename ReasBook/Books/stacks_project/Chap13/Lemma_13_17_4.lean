import Mathlib
import stacks_project.Chap13.«13_17_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

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
- primary domain: bounded-above derived categories of a Serre full subcategory and the canonical
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

The local `Abelian P.FullSubcategory` wrapper was duplicate API: for a weak Serre class, the canonical
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
/-- Lemma 13.17.4: let `P` be a Serre subcategory of an abelian category `A`. Assume that for
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
