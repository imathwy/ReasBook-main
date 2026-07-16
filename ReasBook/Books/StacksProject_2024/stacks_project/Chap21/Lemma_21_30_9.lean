import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.stacks_project.Chap21.Lemma_21_30_2
import StacksProject_2024.stacks_project.Chap21.Lemma_21_30_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty
open scoped DerivedCategoryWithCohomologyIn
open scoped CategoryTheory.GrothendieckTopology

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

universe u

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}

variable (hle : τ' ≤ τ)
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))

variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (τ'.over X) (τ'.over Y))]

/- Domain-style sampling for Lemma 21.30.9:
- primary domain:
  bounded-below derived full subcategories cut out by object properties on localized sheaf
  categories;
- sampled owner declarations:
  `comparisonObjectProperty`,
  `derivedCategoryBoundedBelowCohomologyInProperty`,
  `comparisonTopologyPullbackDerivedPlus`,
  `comparisonTopologyPushforwardDerivedPlus`,
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.lift`,
  `targetWeakSerreSubcategory_of_pullbackEquivalence_of_pushforwardExact`;
- best owner abstraction:
  the Chapter `13` bounded-below cohomology-in-property owner
  `derivedCategoryBoundedBelowCohomologyInProperty`, specialized to the object properties
  `A[hle, A']_(X)` and `A' X`, together with the canonical full subcategories
  `D⁺_{A[hle, A']_(X)}` and `D⁺_{A' X}`; the localized comparison derived
  inverse/direct images are already owned upstream in Lemma `21.30.8` by
  `comparisonTopologyPullbackDerivedPlus hle X` and
  `comparisonTopologyPushforwardDerivedPlus hle X`;
- primitive data:
  the target-side comparison subcategories `A' X` and their pulled-back source-side owner
  `A[hle, A']_(X)`;
- derived API:
  the weak-Serre instance on `A[hle, A']_(X)`, the two restricted derived
  functors, and the resulting equivalence statement.

Source/core/bridge triage:
- `source-facing`:
  the weak-Serre statement and the equivalence on the bounded-below comparison subcategories;
- `core/canonical`:
  `derivedCategoryBoundedBelowCohomologyInProperty`, `ObjectProperty.FullSubcategory`, and
  `ObjectProperty.lift`, `comparisonTopologyPullbackDerivedPlus`, and
  `comparisonTopologyPushforwardDerivedPlus`;
- `bridge/view`:
  the canonical `ObjectProperty.lift` restrictions of `comparisonTopologyPullbackDerivedPlus hle X`
  and `comparisonTopologyPushforwardDerivedPlus hle X`, obtained by lifting `ε_X⁻¹` and
  `Rε_{X,*}` through those full subcategories.

The file therefore keeps the source-facing comparison theorems, but clause `(1)` now lives in the
smaller underived comparison context determined by `CohomologyComparisonSituation`, while clause
`(2)` stays in the later derived section, where the restricted functor terms appear only as local
notation. The file still reuses the canonical derived comparison owners from Lemma `21.30.8`
instead of rebuilding private total-right-derived abbreviations. -/

-- Proof sketch: transport kernels and cokernels in `A_X` by applying `ε_{X,*}` and use that
-- `A'_X` is weak Serre by the comparison situation. For extensions, apply `ε_{X,*}` to a short
-- exact sequence in `Ab(C_τ/X)`, use the underived comparison transfer from Lemma `21.29.1`,
-- and then pull the middle term back along `ε_X^{-1}`.
/-- Lemma 21.30.9 (1): in Situation `21.30.1`, for every `X ∈ 𝒞` the pulled-back
comparison subcategory `A_X ⊂ Ab(𝒞_τ / X)` is a weak Serre
subcategory. -/
@[stacks 0EZG]
theorem comparisonObjectProperty_isWeakSerreSubcategory
    (h : CohomologyComparisonSituation τ τ' P A')
    (X : C) :
    IsWeakSerreClass (A[hle, A']_(X)) := sorry

/-- The pulled-back comparison subcategory `A_X` inherits a weak Serre structure from
Lemma `21.30.9 (1)`. -/
instance instComparisonObjectPropertyIsWeakSerreClass
    (h : CohomologyComparisonSituation τ τ' P A')
    (X : C) :
    IsWeakSerreClass (A[hle, A']_(X)) :=
  comparisonObjectProperty_isWeakSerreSubcategory hle P A' h X

end

section

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}

variable (hle : τ' ≤ τ)
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))

variable [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasWeakSheafify (τ'.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{u})]
variable [∀ X : C, HasExt (Sheaf (τ'.over X) AddCommGrpCat.{u})]
variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ.over X) AddCommGrpCat.{u})]
variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (τ.over X) (τ.over Y))]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (τ'.over X) (τ'.over Y))]
variable [∀ X : C,
  Functor.HasRightDerivedFunctor
    (mapHomotopyCategoryToDerived (comparisonTopologyPushforwardAb hle X))
    (HomotopyCategory.quasiIso
      (Sheaf (τ.over X) AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
variable [∀ X : C,
  Functor.HasRightDerivedFunctor
    (mapBoundedBelowHomotopyCategoryToDerivedBelow (comparisonTopologyPullbackAb hle X))
    (boundedBelowHomotopyQuasiIso
      (Sheaf (τ'.over X) AddCommGrpCat.{u}))]
variable [∀ X : C,
  Functor.HasRightDerivedFunctor
    (mapBoundedBelowHomotopyCategoryToDerivedBelow (comparisonTopologyPushforwardAb hle X))
    (boundedBelowHomotopyQuasiIso
      (Sheaf (τ.over X) AddCommGrpCat.{u}))]

section

variable (X : C)

local notation "PX" => derivedCategoryBoundedBelowCohomologyInProperty (A[hle, A']_(X))
local notation "PY" => derivedCategoryBoundedBelowCohomologyInProperty (A' X)

-- Proof sketch: exact inverse image preserves bounded-belowness and commutes with cohomology.
-- For each cohomology sheaf in `A'_X`, the degree-zero case of Lemma `21.30.8 (2)` identifies
-- `ε_{X,*}(ε_X⁻¹ ℱ')` with an object of `A'_X`, which is exactly the defining
-- condition for membership in `A_X`.
/-- The landing-property statement showing that `ε_X⁻¹` sends
`D⁺_{A'_X}(𝒞_{τ'}/X)` into `D⁺_{A_X}(𝒞_τ/X)`. -/
theorem comparisonPullbackDerived_obj_mem_plusCohomologyIn
    (h : CohomologyComparisonSituation τ τ' P A')
    (K : D⁺_{A' X}) :
    PX ((comparisonTopologyPullbackDerivedPlus hle X).obj K.toBoundedBelow) := sorry

section

variable (h : CohomologyComparisonSituation τ τ' P A')

/-- The restricted inverse-image functor `ε_X⁻¹` on the bounded-below derived
subcategory with cohomology in `A'_X`. -/
abbrev comparisonPullbackDerivedPlusOnPlusCohomologyIn :
    D⁺_{A' X} ⥤ D⁺_{A[hle, A']_(X)} :=
  ObjectProperty.lift
    PX
    (ObjectProperty.ι PY ⋙ comparisonTopologyPullbackDerivedPlus hle X)
    (comparisonPullbackDerived_obj_mem_plusCohomologyIn hle P A' X h)

-- Proof sketch: apply the bounded-below comparison theorem from Lemma `21.28.5` in the localized
-- setting, with source weak Serre subcategory `A_X`, target weak Serre subcategory `A'_X`, exact
-- inverse image `ε_X⁻¹`, and unit isomorphisms supplied by Lemma `21.30.8 (2)`.
/-- The landing-property statement showing that `Rε_{X,*}` sends
`D⁺_{A_X}(𝒞_τ / X)` into `D⁺_{A'_X}(𝒞_{τ'}/X)`. -/
theorem comparisonPushforwardDerived_obj_mem_plusCohomologyIn
    (h : CohomologyComparisonSituation τ τ' P A')
    (K : D⁺_{A[hle, A']_(X)}) :
    PY ((comparisonTopologyPushforwardDerivedPlus hle X).obj K.toBoundedBelow) := sorry

/-- The restricted right-derived direct image `Rε_{X,*}` on the bounded-below derived
subcategory with cohomology in `A_X`. It is the quasi-inverse promised by Lemma `21.30.9 (2)`. -/
abbrev comparisonPushforwardDerivedPlusOnPlusCohomologyIn :
    D⁺_{A[hle, A']_(X)} ⥤ D⁺_{A' X} :=
  ObjectProperty.lift
    PY
    (ObjectProperty.ι PX ⋙ comparisonTopologyPushforwardDerivedPlus hle X)
    (comparisonPushforwardDerived_obj_mem_plusCohomologyIn hle P A' X h)

/-- Lemma 21.30.9 (2): in Situation `21.30.1`, for every `X ∈ 𝒞` the functor
`Rε_{X,*} : D⁺_{A_X}(𝒞_τ / X) ⟶ D⁺_{A'_X}(𝒞_{τ'}/X)` is an equivalence of categories, with
quasi-inverse given by the restricted inverse-image functor `ε_X⁻¹`. -/
@[stacks 0EZG]
theorem comparisonPushforwardDerivedPlusOnPlusCohomologyIn_isEquivalence
    : Functor.IsEquivalence
        (comparisonPushforwardDerivedPlusOnPlusCohomologyIn hle P A' X h) := by
  sorry

instance instComparisonPushforwardDerivedPlusOnPlusCohomologyInIsEquivalence
    : Functor.IsEquivalence
        (comparisonPushforwardDerivedPlusOnPlusCohomologyIn hle P A' X h) :=
  comparisonPushforwardDerivedPlusOnPlusCohomologyIn_isEquivalence hle P A' X h

/-- Companion to Lemma `21.30.9 (2)`: the restricted inverse-image functor `ε_X⁻¹` is
itself an equivalence, with quasi-inverse the restricted right-derived direct image
`Rε_{X,*}`. -/
theorem comparisonPullbackDerivedPlusOnPlusCohomologyIn_isEquivalence
    : Functor.IsEquivalence
        (comparisonPullbackDerivedPlusOnPlusCohomologyIn hle P A' X h) := by
  sorry

instance instComparisonPullbackDerivedPlusOnPlusCohomologyInIsEquivalence
    : Functor.IsEquivalence
        (comparisonPullbackDerivedPlusOnPlusCohomologyIn hle P A' X h) :=
  comparisonPullbackDerivedPlusOnPlusCohomologyIn_isEquivalence hle P A' X h

end

end

end

end CategoryTheory.GrothendieckTopology
