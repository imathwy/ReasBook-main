import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.stacks_project.Chap13.Lemma_13_17_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_30_3
import StacksProject_2024.stacks_project.Chap18.Lemma_18_16_6
import StacksProject_2024.stacks_project.Chap13.Situation_13_15_1
import StacksProject_2024.stacks_project.Chap21.«21_30_0_1»
import StacksProject_2024.stacks_project.Chap21.Situation_21_30_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_30_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open DerivedCategory
open DerivedCategory.TStructure
open Opposite
open ComplexShape
open scoped CategoryTheory
open scoped DerivedCategoryWithCohomologyIn
open scoped CategoryTheory.GrothendieckTopology

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

universe u v

namespace CategoryTheory.GrothendieckTopology

section LocalizedDerivedOwners

variable {C : Type u} [Category.{v} C]
variable {J τ τ' : GrothendieckTopology C}

/-- The bounded-below localized derived direct image `R f_*` on abelian sheaves over slice sites.
-/
abbrev overMapPushforwardDerivedPlus
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)
    [∀ F : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}, (Over.map f).op.HasPointwiseRightKanExtension F]
    [Functor.Additive
      ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
        (J.over X) (J.over Y))]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
          (J.over X) (J.over Y)))
      (boundedBelowHomotopyQuasiIso (Sheaf (J.over X) AddCommGrpCat.{max u v}))] :
    boundedBelowDerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max u v}) ⥤
      boundedBelowDerivedCategory (Sheaf (J.over Y) AddCommGrpCat.{max u v}) :=
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategoryToDerivedBelow
      ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
        (J.over X) (J.over Y)))
    mapBoundedBelowHomotopyToDerivedBelow
    (boundedBelowHomotopyQuasiIso (Sheaf (J.over X) AddCommGrpCat.{max u v}))

/-- The localized topology-comparison derived direct image `R ε_{X,*}` on the ambient derived
category of abelian sheaves over `X`. -/
noncomputable abbrev comparisonTopologyPushforwardDerived
    (hle : τ' ≤ τ) (X : C)
    [Functor.Additive (comparisonTopologyPushforwardAb hle X)]
    [Functor.HasRightDerivedFunctor
      (mapHomotopyCategoryToDerived (comparisonTopologyPushforwardAb hle X))
      (HomotopyCategory.quasiIso
        (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ))] :
    DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) :=
  Functor.totalRightDerived
    (mapHomotopyCategoryToDerived (comparisonTopologyPushforwardAb hle X))
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ))

/-- The bounded-below localized topology-comparison derived direct image `R ε_{X,*}`. -/
abbrev comparisonTopologyPushforwardDerivedPlus
    (hle : τ' ≤ τ) (X : C)
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow
        (comparisonTopologyPushforwardAb hle X))
      (boundedBelowHomotopyQuasiIso (Sheaf (τ.over X) AddCommGrpCat.{max u v}))] :
    boundedBelowDerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) ⥤
      boundedBelowDerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) :=
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategoryToDerivedBelow
      (comparisonTopologyPushforwardAb hle X))
    mapBoundedBelowHomotopyToDerivedBelow
    (boundedBelowHomotopyQuasiIso (Sheaf (τ.over X) AddCommGrpCat.{max u v}))

/-- The bounded-below localized topology-comparison derived inverse image `ε_X^{-1}`. -/
abbrev comparisonTopologyPullbackDerivedPlus
    (hle : τ' ≤ τ) (X : C)
    [HasWeakSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow
        (comparisonTopologyPullbackAb hle X))
      (boundedBelowHomotopyQuasiIso (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))] :
    boundedBelowDerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) ⥤
      boundedBelowDerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) :=
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategoryToDerivedBelow
      (comparisonTopologyPullbackAb hle X))
    mapBoundedBelowHomotopyToDerivedBelow
    (boundedBelowHomotopyQuasiIso (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))

end LocalizedDerivedOwners

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}

variable (hle : τ' ≤ τ)
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))

/-
Domain-style sampling for Lemma 21.30.8:
- primary domain:
  bounded-below derived categories cut out by cohomology-in-property owners, together with the
  localized topology-comparison pullback/pushforward adjunction on derived categories;
- sampled owner declarations:
  `derivedCategoryBoundedBelowCohomologyInProperty`,
  `GrothendieckTopology.overMapPushforward`,
  `Functor.mapDerivedCategory`,
  `CategoryTheory.mapHomotopyCategoryToDerived`,
  `Functor.totalRightDerived`,
  `CategoryTheory.Adjunction.derived`,
  `CategoryTheory.unit_isIso_of_boundedBelow_of_cohomology`;
- best owner abstraction:
  the chapter/project owner for the bounded-below comparison layer is
  `derivedCategoryBoundedBelowCohomologyInProperty`, i.e. the source-facing subcategories
  `D⁺_{A' X}`, while the comparison map in clause `(2)` is the adjunction unit for the canonical
  derived adjunction built from `Adjunction.derived` and the localized derived direct-image owners
  `comparisonTopologyPushforwardDerived hle X`,
  `comparisonTopologyPushforwardDerivedPlus hle X`, and
  `GrothendieckTopology.overMapPushforwardDerivedPlus τ' f`;
- primitive data:
  the object properties `A' X`, the exact inverse-image functor `comparisonTopologyPullbackAb hle X`,
  the localized direct-image functor `τ'.overMapPushforward AddCommGrpCat f`, and the canonical
  right-derived direct-image functors `comparisonTopologyPushforwardDerived hle X`,
  `comparisonTopologyPushforwardDerivedPlus hle X`, and `τ'.overMapPushforwardDerivedPlus f`;
- derived API:
  the all-`n` vanishing theorem, the unit-isomorphism statement on `D⁺_{A' X}`, the pushforward
  stability statement, and the pushforward/pullback comparison in clause `(4)`.

Source/core/bridge triage:
  the four clauses of Lemma `21.30.8`;
- `core/canonical`:
  `derivedCategoryBoundedBelowCohomologyInProperty`, `D⁺_{A' X}`,
  `(comparisonTopologyPullbackAb hle X).mapDerivedCategory`,
  `comparisonTopologyPushforwardDerived hle X`,
  `comparisonTopologyPushforwardDerivedPlus hle X`,
  and `τ'.overMapPushforwardDerivedPlus f`,
  and the corresponding derived adjunction from `Adjunction.derived`;
- `bridge/view`:
  the source comparison morphism identified with the adjunction unit of that canonical derived
  adjunction.

The previous public abbreviation `localizedDerivedPlusCohomologyInProperty` duplicated the Chapter
13 bounded-below owner. This file now keeps the Chapter 13 owner, adds only the localized
derived-pushforward owners needed repeatedly downstream, and identifies the comparison morphism
with the adjunction unit of the canonical derived adjunction. -/

-- Proof sketch: `(V_0)` is the empty vanishing condition. Apply Lemma `21.30.7` inductively to
-- propagate `(V_n)` from `n` to `n + 1`.
/-- Lemma 21.30.8 (1): in Situation `21.30.1`, the local comparison vanishing condition `(V_n)`
holds for every `n`. -/
@[stacks 0EZF]
theorem localizedComparisonLocalVanishingCondition_all
    [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{u}]
    [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
    [∀ {X Y : C} (f : X ⟶ Y),
      Functor.Additive
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
          (τ'.over X) (τ'.over Y))]
    (h : CohomologyComparisonSituation τ τ' P A')
    (n : ℕ) :
    h.LocalVanishing n := sorry

section ComparisonTopologyPullbackPushforwardAdjunction

variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{u}]

section

variable (X : C)

private abbrev comparisonTopologyPrimeQh :
    HomotopyCategory (Sheaf (τ'.over X) AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{u}) :=
  DerivedCategory.Qh

private abbrev comparisonTopologyQh :
    HomotopyCategory (Sheaf (τ.over X) AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{u}) :=
  DerivedCategory.Qh

private abbrev comparisonTopologyPrimeQis :
    MorphismProperty
      (HomotopyCategory (Sheaf (τ'.over X) AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso (Sheaf (τ'.over X) AddCommGrpCat.{u}) (ComplexShape.up ℤ)

private abbrev comparisonTopologyQis :
    MorphismProperty
      (HomotopyCategory (Sheaf (τ.over X) AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso (Sheaf (τ.over X) AddCommGrpCat.{u}) (ComplexShape.up ℤ)

private abbrev comparisonTopologyPushforwardToDerived :
    HomotopyCategory (Sheaf (τ.over X) AddCommGrpCat.{u}) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{u}) :=
  mapHomotopyCategoryToDerived (comparisonTopologyPushforwardAb hle X)

local notation "R_epsPush" =>
  Functor.totalRightDerived
    (comparisonTopologyPushforwardToDerived hle X)
    (comparisonTopologyQh X)
    (comparisonTopologyQis X)

local notation "α_epsPush" =>
  Functor.totalRightDerivedUnit
    (comparisonTopologyPushforwardToDerived hle X)
    (comparisonTopologyQh X)
    (comparisonTopologyQis X)

private theorem comparisonTopologyPullbackMapDerivedCategory_hasLeftDerivedFunctor
    [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{u}]
    : ((comparisonTopologyPullbackAb hle X).mapDerivedCategory).IsLeftDerivedFunctor
      ((comparisonTopologyPullbackAb hle X).mapDerivedCategoryFactorsh.hom)
      (comparisonTopologyPrimeQis X) := by
  let F : Sheaf (τ'.over X) AddCommGrpCat.{u} ⥤ Sheaf (τ.over X) AddCommGrpCat.{u} :=
    comparisonTopologyPullbackAb hle X
  simpa [F] using
    (Functor.isLeftDerivedFunctor_of_inverts
      (comparisonTopologyPrimeQis X)
      F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh)

attribute [local instance] comparisonTopologyPullbackMapDerivedCategory_hasLeftDerivedFunctor

private instance comparisonTopologyPushforwardAb_isRightAdjoint
    [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{u}]
    : Functor.IsRightAdjoint (comparisonTopologyPushforwardAb hle X) := by
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    id_isContinuous_of_le (comparisonOver_le hle X)
  letI (F : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
      ((𝟭 (Over X)).op).HasPointwiseLeftKanExtension F :=
    comparisonTopologyPullbackHasPointwiseLeftKanExtension X F
  letI (F : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
      ((𝟭 (Over X)).op).HasLeftKanExtension F :=
    comparisonTopologyPullbackHasLeftKanExtension X F
  infer_instance

private noncomputable def comparisonTopologyPullback_pushforward_adjunctionAb
    [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{u}] :
    comparisonTopologyPullbackAb hle X ⊣ comparisonTopologyPushforwardAb hle X := by
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    id_isContinuous_of_le (comparisonOver_le hle X)
  letI (F : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
      ((𝟭 (Over X)).op).HasPointwiseLeftKanExtension F :=
    comparisonTopologyPullbackHasPointwiseLeftKanExtension X F
  letI (F : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
      ((𝟭 (Over X)).op).HasLeftKanExtension F :=
    comparisonTopologyPullbackHasLeftKanExtension X F
  simpa using
    (Adjunction.ofIsRightAdjoint (comparisonTopologyPushforwardAb hle X))

private theorem comparisonTopologyPushforwardDerived_isRightDerivedFunctor
    [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{u}]
    [∀ X : C,
      Functor.HasRightDerivedFunctor
        (mapHomotopyCategoryToDerived (comparisonTopologyPushforwardAb hle X))
        (comparisonTopologyQis X)] :
    (comparisonTopologyPushforwardDerived hle X).IsRightDerivedFunctor
      α_epsPush (comparisonTopologyQis X) := by
  infer_instance

attribute [local instance] comparisonTopologyPushforwardDerived_isRightDerivedFunctor

private theorem
    comparisonTopologyPullbackMapDerivedCategory_comp_comparisonTopologyPushforwardDerived_isLeftDerivedFunctor
    [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{u}]
    [∀ X : C,
      Functor.HasRightDerivedFunctor
        (mapHomotopyCategoryToDerived (comparisonTopologyPushforwardAb hle X))
        (comparisonTopologyQis X)] :
    ((((comparisonTopologyPullbackAb hle X).mapDerivedCategory) ⋙
        comparisonTopologyPushforwardDerived hle X)).IsLeftDerivedFunctor
      ((Functor.associator
          (comparisonTopologyPrimeQh X)
          ((comparisonTopologyPullbackAb hle X).mapDerivedCategory)
          (comparisonTopologyPushforwardDerived hle X)).inv ≫
        Functor.whiskerRight
          ((comparisonTopologyPullbackAb hle X).mapDerivedCategoryFactorsh.hom)
          (comparisonTopologyPushforwardDerived hle X))
      (comparisonTopologyPrimeQis X) := by
  sorry

attribute [local instance]
  comparisonTopologyPullbackMapDerivedCategory_comp_comparisonTopologyPushforwardDerived_isLeftDerivedFunctor

private theorem
    comparisonTopologyPushforwardDerived_comp_comparisonTopologyPullbackMapDerivedCategory_isRightDerivedFunctor
    [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{u}]
    [∀ X : C,
      Functor.HasRightDerivedFunctor
        (mapHomotopyCategoryToDerived (comparisonTopologyPushforwardAb hle X))
        (comparisonTopologyQis X)] :
    ((comparisonTopologyPushforwardDerived hle X ⋙
        ((comparisonTopologyPullbackAb hle X).mapDerivedCategory))).IsRightDerivedFunctor
      (Functor.whiskerRight
          α_epsPush
          ((comparisonTopologyPullbackAb hle X).mapDerivedCategory) ≫
        (Functor.associator
          (comparisonTopologyQh X)
          (comparisonTopologyPushforwardDerived hle X)
          ((comparisonTopologyPullbackAb hle X).mapDerivedCategory)).hom)
      (comparisonTopologyQis X) := by
  sorry

attribute [local instance]
  comparisonTopologyPushforwardDerived_comp_comparisonTopologyPullbackMapDerivedCategory_isRightDerivedFunctor

/-- The canonical derived comparison unit
`𝟭 ⟶ ε_X⁻¹ ⋙ R ε_{X,*}` on the ambient derived category of abelian sheaves over `X`. -/
noncomputable def comparisonTopologyPullback_pushforward_unit
    [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{u}]
    [∀ X : C,
      Functor.HasRightDerivedFunctor
        (mapHomotopyCategoryToDerived (comparisonTopologyPushforwardAb hle X))
        (HomotopyCategory.quasiIso
          (Sheaf (τ.over X) AddCommGrpCat.{u}) (ComplexShape.up ℤ))] :
    𝟭 (DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{u})) ⟶
      (comparisonTopologyPullbackAb hle X).mapDerivedCategory ⋙
        comparisonTopologyPushforwardDerived hle X :=
  letI := comparisonTopologyPushforwardAb_isRightAdjoint hle X
  letI := comparisonTopologyPullbackMapDerivedCategory_hasLeftDerivedFunctor hle X
  letI := comparisonTopologyPushforwardDerived_isRightDerivedFunctor hle X
  letI :=
    comparisonTopologyPullbackMapDerivedCategory_comp_comparisonTopologyPushforwardDerived_isLeftDerivedFunctor
      hle X
  letI :=
    comparisonTopologyPushforwardDerived_comp_comparisonTopologyPullbackMapDerivedCategory_isRightDerivedFunctor
      hle X
  (Adjunction.derived
      ((comparisonTopologyPullback_pushforward_adjunctionAb hle X).mapHomotopyCategory)
      (comparisonTopologyPrimeQis X)
      (comparisonTopologyQis X)
      ((comparisonTopologyPullbackAb hle X).mapDerivedCategoryFactorsh.hom)
      ((comparisonTopologyPushforwardToDerived hle X).totalRightDerivedUnit
        (comparisonTopologyQh X)
        (comparisonTopologyQis X))).unit

-- Proof sketch: write `K := ε_X^{-1} K'` using the exact inverse-image functor. Its cohomology
-- sheaves remain in the pulled-back comparison subcategory, so the spectral sequence for
-- `R ε_{X,*}` degenerates by `(V_n)` for all `n`. This identifies every cohomology sheaf of
-- `R ε_{X,*} K` with the corresponding cohomology sheaf of `K'`, giving the claimed
-- isomorphism in the derived category.
/-- Lemma 21.30.8 (2): for `X ∈ 𝒞` and `K' ∈ D⁺_{A' X}`, the canonical comparison
`K' ⟶ R ε_{X,*}(ε_X⁻¹ K')` is an isomorphism. Here this map is formalized as
`(comparisonTopologyPullback_pushforward_unit hle X).app K'.toDerived`. -/
@[stacks 0EZF]
theorem comparisonTopologyPullback_pushforward_isomorphic_of_plusCohomologyIn
    [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
    [∀ {X Y : C} (f : X ⟶ Y),
      Functor.Additive
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
          (τ'.over X) (τ'.over Y))]
    [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{u}]
    [∀ X : C,
      Functor.HasRightDerivedFunctor
        (mapHomotopyCategoryToDerived (comparisonTopologyPushforwardAb hle X))
        (HomotopyCategory.quasiIso
          (Sheaf (τ.over X) AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
    (h : CohomologyComparisonSituation τ τ' P A')
    (K' : D⁺_{A' X}) :
    IsIso ((comparisonTopologyPullback_pushforward_unit hle X).app K'.toDerived) := sorry

end

end ComparisonTopologyPullbackPushforwardAdjunction

section BoundedBelowComparison

-- Proof sketch: use the spectral sequence
-- `R^p f_{τ',*} H^q(K') ⇒ H^{p+q}(R f_{τ',*} K')`. The cohomology sheaves `H^q(K')` lie in
-- `A'_X`, higher direct images of objects of `A'_X` stay in `A'_Y` by Situation `21.30.1`, and
-- the weak Serre property then places every cohomology sheaf of `R f_{τ',*} K'` back in
-- `A'_Y`; bounded-belowness is preserved by the same spectral-sequence argument.
/-- Lemma 21.30.8 (3): for `f : X ⟶ Y` in `P` and `K' ∈ D⁺_{A' X}`, the derived direct image
`R f_{τ',*} K'` belongs to `D⁺_{A' Y}`. -/
@[stacks 0EZF]
theorem localizedPushforwardDerived_mem_plusCohomologyIn_of_morphismProperty
    [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
    [∀ {X Y : C} (f : X ⟶ Y),
      Functor.Additive
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
          (τ'.over X) (τ'.over Y))]
    (h : CohomologyComparisonSituation τ τ' P A')
    {X Y : C} (f : X ⟶ Y)
    (hf : P f)
    [∀ F : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.map f).op.HasPointwiseRightKanExtension F]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
          (τ'.over X) (τ'.over Y)))
      (boundedBelowHomotopyQuasiIso (Sheaf (τ'.over X) AddCommGrpCat.{u}))]
    (K' : D⁺_{A' X}) :
    derivedCategoryBoundedBelowCohomologyInProperty (A' Y)
      ((overMapPushforwardDerivedPlus τ' f).obj K'.toBoundedBelow) := sorry

-- Proof sketch: compare the spectral sequence for `R f_{τ',*} K'` with the one for
-- `R f_{τ,*} (ε_X⁻¹ K')`. By the previous clause, it is enough to treat the case
-- where `K'` has a single nonzero cohomology sheaf in `A'_X`; then Lemma `21.30.3` identifies
-- the higher direct images after applying `ε_Y^{-1}`, and the resulting comparison is an
-- isomorphism in the derived category.
/-- Lemma 21.30.8 (4): for `f : X ⟶ Y` in `P` and `K' ∈ D⁺_{A' X}`, the inverse image of the
derived direct image along `ε_Y` is canonically isomorphic to the derived direct image of
`ε_X⁻¹ K'` along `f_τ`. -/
@[stacks 0EZF]
theorem comparisonTopologyPullback_localizedPushforwardDerived_isomorphic
    [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
    [∀ {X Y : C} (f : X ⟶ Y),
      Functor.Additive
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
          (τ'.over X) (τ'.over Y))]
    [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{u}]
    [∀ X : C,
      Functor.HasRightDerivedFunctor
        (mapBoundedBelowHomotopyCategoryToDerivedBelow
          (comparisonTopologyPullbackAb hle X))
        (boundedBelowHomotopyQuasiIso (Sheaf (τ'.over X) AddCommGrpCat.{u}))]
    (h : CohomologyComparisonSituation τ τ' P A')
    {X Y : C} (f : X ⟶ Y)
    (hf : P f)
    [∀ F : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u}, (Over.map f).op.HasPointwiseRightKanExtension F]
    [Functor.Additive
      ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
        (τ.over X) (τ.over Y))]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
          (τ'.over X) (τ'.over Y)))
      (boundedBelowHomotopyQuasiIso (Sheaf (τ'.over X) AddCommGrpCat.{u}))]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow
        ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
          (τ.over X) (τ.over Y)))
      (boundedBelowHomotopyQuasiIso (Sheaf (τ.over X) AddCommGrpCat.{u}))]
    (K' : D⁺_{A' X}) :
    IsIsomorphic
      ((comparisonTopologyPullbackDerivedPlus hle Y).obj
        ((overMapPushforwardDerivedPlus τ' f).obj K'.toBoundedBelow))
      ((overMapPushforwardDerivedPlus τ f).obj
        ((comparisonTopologyPullbackDerivedPlus hle X).obj K'.toBoundedBelow)) := sorry

end BoundedBelowComparison

end CategoryTheory.GrothendieckTopology
