import Mathlib
import stacks_project.Chap12.Definition_12_11_1
import stacks_project.Chap12.Lemma_12_10_3
import stacks_project.Chap13.Lemma_13_17_1
import stacks_project.Chap13.Definition_13_28_1
import stacks_project.Chap13.Lemma_13_28_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure
open scoped DerivedCategoryWithCohomologyIn

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

local notation "H" => DerivedCategory.homologyFunctor A

section WeakSerreSingleBridge

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/- Domain-style sampling for Lemma 13.28.5:
- primary domain: the bounded derived subcategory cut out by a weak Serre object property and the
  induced Grothendieck-group comparison map;
- sampled owner declarations:
  `derivedCategoryCohomologyInProperty`,
  `derivedCategoryBoundedCohomologyInProperty`,
  `Dᵇ_{P}`,
  `ObjectProperty.IsTriangulated`,
  `Functor.eulerK0Map`,
  `Functor.shiftVanishingBounded`;
- best owner abstraction: the Chapter 13 owner object property on `DerivedCategory A` together
  with its canonical full subcategory `Dᵇ_{P}`; the Euler map on `K₀(Dᵇ_{P})` should be routed
  through the owner-functor construction
  `(derivedBoundedWithCohomologyInZeroHomologyFunctor P).eulerK0Map`;
- primitive-vs-derived split:
  primitive data: the object property `P`, its zero-object and iso-stability owners used by the
    degree-zero bridge, and the chapter owner
    `derivedCategoryBoundedCohomologyInProperty P`, whose full subcategory owner is the chapter
    notation `Dᵇ_{P}`;
  derived API: the degree-zero embedding obtained by restricting the Chapter 13 owner
    `singleFunctorToBoundedDerived A` along `P.ι`, the induced maps on `K₀`, and the Euler
    characteristic inverse;
- source/core/bridge triage:
  `source-facing`: the `K₀` comparison between `P` and `Dᵇ_{P}`;
  `core/canonical`: the owner declarations from `Lemma_13_17_1`;
  `bridge/view`: the restricted degree-zero functor
    `P.FullSubcategory ⥤ Dᵇ(A) ⥤ Dᵇ_{P}` and the resulting additive maps.

This file therefore reuses the Chapter 13 owner API rather than redeclaring a second bounded
cohomology-in-`P` object property. -/

/-- The degree-zero complex attached to an object of `P.FullSubcategory` lies in
`Dᵇ_{P}`. -/
theorem weakSerreSingle_obj_mem_derivedCategoryBoundedCohomologyInProperty
    (X : P.FullSubcategory) :
    derivedCategoryBoundedCohomologyInProperty P
      ((P.ι ⋙ singleFunctorToBoundedDerived A).obj X) := by
  intro i
  by_cases hi : i = 0
  · subst hi
    simpa [derivedCategoryBoundedCohomologyInProperty, derivedCategoryCohomologyInProperty,
      Functor.comp_obj] using
        P.prop_of_iso ((singleFunctorCompHomologyFunctorIso A 0).app X.obj).symm X.property
  · have hzero :
        IsZero
          ((H i).obj
            ((ObjectProperty.ι t.bounded).obj
              ((P.ι ⋙ singleFunctorToBoundedDerived A).obj X))) := by
      by_cases hlt : i < 0
      · change IsZero ((H i).obj ((singleFunctor A 0).obj X.obj))
        letI : ((singleFunctor A 0).obj X.obj).IsGE 0 := inferInstance
        exact DerivedCategory.isZero_of_isGE _ 0 i hlt
      · have hgt : 0 < i := by omega
        change IsZero ((H i).obj ((singleFunctor A 0).obj X.obj))
        letI : ((singleFunctor A 0).obj X.obj).IsLE 0 := inferInstance
        exact DerivedCategory.isZero_of_isLE _ 0 i hgt
    simpa [derivedCategoryBoundedCohomologyInProperty, derivedCategoryCohomologyInProperty,
      Functor.comp_obj] using P.prop_of_isZero hzero

/-- The canonical functor `P.FullSubcategory ⥤ Dᵇ_{P}` sending `X` to the degree-zero object
`X[0]` in the ambient derived category. -/
abbrev weakSerreSingleFunctorToDerivedBounded :
    P.FullSubcategory ⥤ Dᵇ_{P} :=
  ObjectProperty.lift
    (derivedCategoryBoundedCohomologyInProperty P)
    (P.ι ⋙ singleFunctorToBoundedDerived A)
    (weakSerreSingle_obj_mem_derivedCategoryBoundedCohomologyInProperty P)

end WeakSerreSingleBridge

section WeakSerreBoundedDerivedBridge

variable (P : ObjectProperty A)

/-- The `i`-th cohomology functor on `Dᵇ_{P}` lifted to the weak Serre full subcategory
`P.FullSubcategory`. -/
abbrev derivedBoundedWithCohomologyInHomologyFunctor (i : ℤ) :
    Dᵇ_{P} ⥤ P.FullSubcategory :=
  P.lift
    ((derivedCategoryBoundedCohomologyInProperty P).ι ⋙
      ObjectProperty.ι (t.bounded : ObjectProperty (D(A))) ⋙ H i)
    (fun X ↦ X.property i)

/-- The degree-zero cohomology functor on `Dᵇ_{P}` lifted to `P.FullSubcategory`. -/
abbrev derivedBoundedWithCohomologyInZeroHomologyFunctor :
    Dᵇ_{P} ⥤ P.FullSubcategory :=
  derivedBoundedWithCohomologyInHomologyFunctor P 0

end WeakSerreBoundedDerivedBridge

section WeakSerreBoundedDerivedK0

variable (P : ObjectProperty A) [P.IsWeakSerreClass]

noncomputable local instance derivedBoundedWithCohomologyInZeroHomologyFunctor_shiftSequence :
    (derivedBoundedWithCohomologyInZeroHomologyFunctor P).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

-- Proof sketch: a short exact sequence in `P.FullSubcategory` gives the canonical distinguished
-- triangle of degree-zero objects in `D(A)`, and each vertex lies in `Dᵇ_{P}`. Hence the
-- corresponding Grothendieck relation vanishes in the triangulated `K₀`.
private theorem relations_le_ker_weakSerreToDerivedBoundedK0 :
    AbelianK0.relations P.FullSubcategory ≤
      (FreeAbelianGroup.lift fun X ↦
        TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj X)).ker := by
  sorry

/-- The canonical map `K₀(P) → K₀(Dᵇ_{P})` induced by `X ↦ X[0]`. -/
def weakSerreToDerivedBoundedK0 :
    AbelianK0 P.FullSubcategory →+ TriangulatedK0 (Dᵇ_{P}) :=
  AbelianK0.lift
    (fun X ↦ TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj X))
    (relations_le_ker_weakSerreToDerivedBoundedK0 P)

-- Proof sketch: `weakSerreToDerivedBoundedK0` is the owner lift `AbelianK0.lift` applied to the
-- object-level formula `X ↦ [X[0]]`, so evaluation on `AbelianK0.of X` is the canonical owner
-- lemma `AbelianK0.lift_of`.
/-- The canonical map on `K₀` sends `[X]` to the class of `X[0]` in `Dᵇ_{P}`. -/
@[simp] theorem weakSerreToDerivedBoundedK0_apply_of
    (X : P.FullSubcategory) :
    weakSerreToDerivedBoundedK0 P K₀[X] =
      TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj X) := by
  simpa using
    AbelianK0.lift_of
      (fun Y : P.FullSubcategory ↦
        TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj Y))
      (relations_le_ker_weakSerreToDerivedBoundedK0 P)
      X

-- Proof sketch: `Dᵇ_P(A)` inherits its triangulated structure from the ambient derived category,
-- and the lifted degree-zero cohomology functor is the source-facing `H⁰` functor valued in the
-- weak Serre full subcategory. Exactness is therefore the same long exact cohomology sequence as
-- for `DerivedCategory.homologyFunctor A 0`, viewed inside `P.FullSubcategory`.
local instance derivedBoundedWithCohomologyInZeroHomologyFunctor_isHomological :
    (derivedBoundedWithCohomologyInZeroHomologyFunctor P).IsHomological := by
  sorry

/-- On generators, the Euler-characteristic map sends a bounded derived object with cohomology in
`P` to the alternating sum of the classes of its cohomology objects in `K₀(P)`. -/
noncomputable abbrev derivedBoundedWithCohomologyInEulerClass
    (X : Dᵇ_{P}) :
    AbelianK0 P.FullSubcategory :=
  ∑ᶠ i : ℤ, i.negOnePow •
    K₀[((derivedBoundedWithCohomologyInHomologyFunctor P i).obj X)]

-- Proof sketch: boundedness gives integers `a ≤ b` such that `H^i(X) = 0` outside `[a, b]`.
-- Since the tautological shift sequence on the lifted degree-zero cohomology functor computes the
-- degree-`i` cohomology objects up to the standard derived-category shift identification, only
-- finitely many shifts contribute.
/-- The lifted degree-zero cohomology functor has finite shift support on `Dᵇ_{P}`. -/
theorem derivedBoundedWithCohomologyInZeroHomologyFunctor_hasFiniteShiftSupport :
    ∀ X : Dᵇ_{P},
      (derivedBoundedWithCohomologyInZeroHomologyFunctor P).shiftVanishingBounded X := sorry

-- Proof sketch: with the tautological shift sequence on the lifted degree-zero cohomology
-- functor, the `i`-th shifted value is `H⁰(X[i])`, canonically identified with `H^i(X)`. The
-- Euler class from `Lemma 13.28.4` is therefore exactly the textbook alternating sum of the
-- cohomology classes.
/-- The Euler class coming from the general homological-functor owner for the lifted degree-zero
cohomology functor agrees with the textbook alternating sum of the cohomology objects. -/
theorem derivedBoundedWithCohomologyInZeroHomologyFunctor_eulerClass_eq
    (X : Dᵇ_{P}) :
    (derivedBoundedWithCohomologyInZeroHomologyFunctor P).eulerClass X =
      derivedBoundedWithCohomologyInEulerClass P X := sorry

/-- The Euler-characteristic map `K₀(Dᵇ_{P}) → K₀(P)`. -/
def derivedBoundedWithCohomologyInEulerK0 :
    TriangulatedK0 (Dᵇ_{P}) →+ AbelianK0 P.FullSubcategory :=
  (derivedBoundedWithCohomologyInZeroHomologyFunctor P).eulerK0Map
    (derivedBoundedWithCohomologyInZeroHomologyFunctor_hasFiniteShiftSupport P)

-- Proof sketch: `derivedBoundedWithCohomologyInEulerK0` is the general owner
-- `H0.eulerK0Map` applied to the lifted degree-zero cohomology functor on `Dᵇ_P(A)`;
-- the companion comparison theorem identifies the resulting Euler class with the textbook
-- alternating sum of cohomology classes.
/-- The Euler-characteristic map sends the class of `X` to the alternating sum of the classes of
its cohomology objects. -/
@[simp] theorem derivedBoundedWithCohomologyInEulerK0_apply_of
    (X : Dᵇ_{P}) :
    derivedBoundedWithCohomologyInEulerK0 P (TriangulatedK0.of X) =
      derivedBoundedWithCohomologyInEulerClass P X := by
  simpa [derivedBoundedWithCohomologyInEulerK0] using
    (Functor.eulerK0Map_apply_of (derivedBoundedWithCohomologyInZeroHomologyFunctor P)
      (derivedBoundedWithCohomologyInZeroHomologyFunctor_hasFiniteShiftSupport P) X).trans
        (derivedBoundedWithCohomologyInZeroHomologyFunctor_eulerClass_eq P X)

-- Proof sketch: evaluate the Euler characteristic of the degree-zero object `X[0]`; all
-- cohomology groups vanish except in degree `0`, where the cohomology object is `X` itself.
/-- The Euler-characteristic map is a left inverse to the degree-zero embedding on `K₀(P)`. -/
theorem weakSerreToDerivedBoundedK0_leftInverse :
    Function.LeftInverse
      (derivedBoundedWithCohomologyInEulerK0 P)
      (weakSerreToDerivedBoundedK0 P) := sorry

-- Proof sketch: use the truncation triangles from Remark 13.12.4 to express the class of a
-- bounded derived object as the alternating sum of the classes of its shifted cohomology objects;
-- this is the same expression used by `derivedBoundedWithCohomologyInEulerK0`.
/-- The degree-zero embedding on `K₀(P)` is a right inverse to the Euler-characteristic map on
`K₀(Dᵇ_{P})`. -/
theorem weakSerreToDerivedBoundedK0_rightInverse :
    Function.RightInverse
      (derivedBoundedWithCohomologyInEulerK0 P)
      (weakSerreToDerivedBoundedK0 P) := sorry

/-- Lemma 13.28.5: for a weak Serre subcategory `P` of an abelian category `A`, the canonical map
`K₀(P) → K₀(Dᵇ_{P})` sending `[X]` to `[X[0]]` is an isomorphism. Its inverse sends the class
of `X` to the alternating sum `\sum_i (-1)^i [H^i(X)]`. -/
noncomputable def weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn :
    AbelianK0 P.FullSubcategory ≃+ TriangulatedK0 (Dᵇ_{P}) where
  toFun := weakSerreToDerivedBoundedK0 P
  invFun := derivedBoundedWithCohomologyInEulerK0 P
  left_inv := weakSerreToDerivedBoundedK0_leftInverse P
  right_inv := weakSerreToDerivedBoundedK0_rightInverse P
  map_add' := (weakSerreToDerivedBoundedK0 P).map_add

-- Proof sketch: this is the `toFun` field of
-- `weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn`, evaluated on the generator class
-- `AbelianK0.of X`.
/-- The canonical equivalence sends the class of `X` to the class of the degree-zero object
`X[0]` in `Dᵇ_{P}`. -/
theorem weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn_apply_of
    (X : P.FullSubcategory) :
    weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn P K₀[X] =
      TriangulatedK0.of ((weakSerreSingleFunctorToDerivedBounded P).obj X) :=
  weakSerreToDerivedBoundedK0_apply_of P X

-- Proof sketch: this is the `invFun` field of
-- `weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn`, evaluated on the class of `X`;
-- the value is exactly the defining Euler characteristic formula.
/-- The inverse equivalence sends the class of `X` to the alternating sum of the classes of the
cohomology objects `H^i(X)`. -/
theorem weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn_symm_apply_of
    (X : Dᵇ_{P}) :
    (weakSerreSubcategoryK0EquivDerivedBoundedWithCohomologyIn P).symm (TriangulatedK0.of X) =
      derivedBoundedWithCohomologyInEulerClass P X :=
  derivedBoundedWithCohomologyInEulerK0_apply_of P X

end WeakSerreBoundedDerivedK0

end CategoryTheory
