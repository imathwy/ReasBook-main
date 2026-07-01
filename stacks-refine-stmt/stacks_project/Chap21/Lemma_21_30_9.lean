import Mathlib
import stacks_project.Chap18.Lemma_18_24_4
import stacks_project.Chap21.Lemma_21_30_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

variable (hle : τ' ≤ τ)
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))

variable [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasWeakSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasExt (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ.over X) (τ.over Y))]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ'.over X) (τ'.over Y))]
variable [∀ X : C,
  Functor.HasRightDerivedFunctor
    (comparisonTopologyPushforwardToDerived hle X)
    (HomotopyCategory.quasiIso
      (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ))]
variable [∀ {J : GrothendieckTopology C} {X Y : C} (f : X ⟶ Y),
  Functor.HasRightDerivedFunctor
    (localizedPushforwardToDerived J f)
    (HomotopyCategory.quasiIso
      (Sheaf (J.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ))]

/-- The source-side comparison subcategory `A_X ⊂ \operatorname{Ab}(\mathcal C_\tau/X)` obtained
by pulling back `A'_X` along the localized comparison direct image `\epsilon_{X,*}`. -/
abbrev comparisonSourceObjectProperty
    (hle : τ' ≤ τ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (X : C) :
    ObjectProperty (Sheaf (τ.over X) AddCommGrpCat.{max u v}) :=
  (A' X).inverseImage (comparisonTopologyPushforwardAb hle X)

/-- The bounded-below derived full subcategory on `(C_τ/X)` cut out by the pulled-back
comparison subcategory `A_X`. -/
abbrev comparisonSourceDerivedPlus
    (hle : τ' ≤ τ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (X : C) :=
  (localizedDerivedPlusCohomologyInProperty (τ.over X)
    (comparisonSourceObjectProperty hle A' X)).FullSubcategory

/-- The bounded-below derived full subcategory on `(C_{τ'}/X)` cut out by `A'_X`. -/
abbrev comparisonTargetDerivedPlus
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (X : C) :=
  (localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X)).FullSubcategory

-- Proof sketch: transport kernels and cokernels in `A_X` by applying `ε_{X,*}` and use that
-- `A'_X` is weak Serre by the comparison situation. For extensions, apply `ε_{X,*}` to a short
-- exact sequence in `Ab(C_τ/X)`, use Lemma `21.30.8` to kill `R¹ ε_{X,*}` on the left term, and
-- then pull the middle term back along `ε_X^{-1}`.
/-- Lemma 21.30.9 (1): in Situation `21.30.1`, for every `X ∈ \mathcal C` the pulled-back
comparison subcategory `\mathcal A_X ⊂ \operatorname{Ab}(\mathcal C_\tau / X)` is a weak Serre
subcategory. -/
theorem comparisonObjectProperty_isWeakSerreSubcategory
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C) :
    IsWeakSerreClass (comparisonSourceObjectProperty hle A' X) := sorry

/-- The pulled-back comparison subcategory `A_X` inherits a weak Serre structure from
Lemma `21.30.9 (1)`. -/
instance instComparisonObjectPropertyIsWeakSerreClass
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C) :
    IsWeakSerreClass (comparisonSourceObjectProperty hle A' X) :=
  comparisonObjectProperty_isWeakSerreSubcategory hle P A' h X

-- Proof sketch: exact inverse image preserves bounded-belowness and commutes with cohomology.
-- For each cohomology sheaf in `A'_X`, the degree-zero case of Lemma `21.30.8 (2)` identifies
-- `ε_{X,*}(ε_X^{-1} \mathcal F')` with an object of `A'_X`, which is exactly the defining
-- condition for membership in `A_X`.
/-- The restricted inverse-image functor `\epsilon_X^{-1}` sends
`D^+_{\mathcal A'_X}(\mathcal C_{\tau'}/X)` into `D^+_{\mathcal A_X}(\mathcal C_\tau/X)`. -/
theorem comparisonPullbackDerived_obj_mem_plusCohomologyIn
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C)
    (K : comparisonTargetDerivedPlus A' X) :
    localizedDerivedPlusCohomologyInProperty (τ.over X)
      (comparisonSourceObjectProperty hle A' X)
      ((ObjectProperty.ι
        (localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X)) ⋙
          epsilonInvDerived hle X).obj K) := sorry

/-- The restriction of `\epsilon_X^{-1}` to the bounded-below derived subcategory with cohomology
in `A'_X`. -/
abbrev comparisonPullbackDerivedPlusWithCohomologyIn
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C) :
    comparisonTargetDerivedPlus A' X ⥤ comparisonSourceDerivedPlus hle A' X :=
  ObjectProperty.lift
    (localizedDerivedPlusCohomologyInProperty (τ.over X)
      (comparisonSourceObjectProperty hle A' X))
    (ObjectProperty.ι (localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X)) ⋙
      epsilonInvDerived hle X)
    (comparisonPullbackDerived_obj_mem_plusCohomologyIn hle P A' h X)

-- Proof sketch: apply the bounded-below comparison theorem from Lemma `21.28.5` in the localized
-- setting, with source weak Serre subcategory `A_X`, target weak Serre subcategory `A'_X`, exact
-- inverse image `ε_X^{-1}`, and unit isomorphisms supplied by Lemma `21.30.8 (2)`.
/-- The restricted right-derived direct image `R\epsilon_{X,*}` on the bounded-below derived
subcategory with cohomology in `A_X`. It is the quasi-inverse promised by Lemma `21.30.9 (2)`. -/
theorem comparisonPushforwardDerived_obj_mem_plusCohomologyIn
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C)
    (K : comparisonSourceDerivedPlus hle A' X) :
    localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X)
      ((ObjectProperty.ι
        (localizedDerivedPlusCohomologyInProperty (τ.over X)
          (comparisonSourceObjectProperty hle A' X)) ⋙
          rEpsilonDerived hle X).obj K) := sorry

/-- The restriction of `R\epsilon_{X,*}` to the bounded-below derived subcategory with cohomology
in `A_X`. -/
abbrev comparisonPushforwardDerivedPlusWithCohomologyIn
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C) :
    comparisonSourceDerivedPlus hle A' X ⥤ comparisonTargetDerivedPlus A' X :=
  ObjectProperty.lift
    (localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X))
    (ObjectProperty.ι
      (localizedDerivedPlusCohomologyInProperty (τ.over X)
        (comparisonSourceObjectProperty hle A' X)) ⋙
        rEpsilonDerived hle X)
    (comparisonPushforwardDerived_obj_mem_plusCohomologyIn hle P A' h X)

-- Proof sketch: after clause `(1)`, the source subcategory `A_X` is weak Serre. Lemma
-- `21.30.8 (2)` identifies the unit `K' ⟶ R ε_{X,*}(ε_X^{-1} K')` on every object of
-- `D^+_{A'_X}`, and Lemma `21.28.5` then upgrades these unit isomorphisms to an equivalence of
-- bounded-below derived subcategories, with quasi-inverse the restricted `ε_X^{-1}`.
/-- Lemma 21.30.9 (2): in Situation `21.30.1`, for every `X ∈ \mathcal C` the functor
`R\epsilon_{X,*} : D^+_{\mathcal A_X}(\mathcal C_\tau / X) \to
D^+_{\mathcal A'_X}(\mathcal C_{\tau'}/X)` is an equivalence of categories, with quasi-inverse
given by the restricted inverse-image functor `\epsilon_X^{-1}`. -/
theorem comparisonPushforwardDerivedPlusWithCohomologyIn_isEquivalence
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C) :
    Functor.IsEquivalence
      (comparisonPushforwardDerivedPlusWithCohomologyIn hle P A' h X) := sorry

end

end CategoryTheory.GrothendieckTopology
