import StacksProject_2024.stacks_project.Chap13.Lemma_13_17_1
import StacksProject_2024.stacks_project.Chap21.SiteAbelianDerived
import StacksProject_2024.stacks_project.Chap21.Situation_21_30_1
import StacksProject_2024.stacks_project.Chap21.«21_30_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory
open DerivedCategory.TStructure
open ComplexShape
open scoped DerivedCategoryWithCohomologyIn
open scoped GrothendieckTopologyDerivedSections

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}

variable (hle : τ' ≤ τ)
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))

section

variable [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{u})]
variable [∀ X : C, HasExt (Sheaf (τ'.over X) AddCommGrpCat.{u})]
variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (τ'.over X) (τ'.over Y))]

/- Domain-style sampling for Lemma 21.30.10 (1):
- primary domain: ordinary sheaf cohomology on slice sites under topology comparison;
- sampled owner declarations:
  `ε[hle]_(X)⁻¹`,
  `Sheaf.cohomologyFunctor`,
  `Sheaf.sheafPushforwardContinuous_globalCohomology_isomorphic`,
  `CohomologyComparisonSituation`,
  `comparisonTopologyPullback_pushforward_isomorphic_of_plusCohomologyIn`;
- best owner abstraction:
  clause `(1)` is a `source-facing` degreewise cohomology statement whose `core/canonical`
  owners are exactly `Sheaf.cohomologyFunctor` and `ε[hle]_(X)⁻¹`; the heavier
  derived pushforward and derived-sections owners belong only to clause `(2)`;
- primitive data:
  the comparison situation `h`, the slice object `X`, the sheaf `F'`, and the membership
  hypothesis `hF' : A' X F'`;
- derived API:
  the Prop-level comparison isomorphism below.

Source/core/bridge triage:
- `source-facing`: the degree-`n` cohomology comparison for `F'`;
- `core/canonical`: `CohomologyComparisonSituation`, `Sheaf.cohomologyFunctor`, and
  `ε[hle]_(X)⁻¹`;
- `bridge/view`: the proof route may combine the general site-comparison theorem
  `Sheaf.sheafPushforwardContinuous_globalCohomology_isomorphic` with the comparison-unit
  isomorphism from Lemma `21.30.8`, but those are proof-side bridges rather than extra owner
  data for the public statement. -/

-- Proof sketch: combine the ordinary site-level global cohomology comparison for the localized
-- topology morphism with the fact that, for `F' ∈ A'_X`, the comparison unit
-- `F' ⟶ ε_{X,*}(ε_X⁻¹ F')` is an isomorphism.
/-- Lemma 21.30.10 (1): in Situation `21.30.1`, for `F' ∈ A'_X` the degree-`n` cohomology of
`F'` on `(C_{τ'}/X)` is canonically isomorphic to the degree-`n` cohomology of `ε_X⁻¹ F'` on
`(C_τ/X)`. -/
@[stacks 0EZH]
theorem comparisonTopologyPullback_cohomology_isomorphic_of_mem
    (h : CohomologyComparisonSituation τ τ' P A')
    (X : C)
    (F' : Sheaf (τ'.over X) AddCommGrpCat.{u})
    (hF' : A' X F')
    (n : ℕ) :
    IsIsomorphic
      ((Sheaf.cohomologyFunctor (τ'.over X) n).obj F')
      ((Sheaf.cohomologyFunctor (τ.over X) n).obj
        ((ε[hle]_(X)⁻¹).obj F')) := sorry

end

section Derived

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
variable [∀ X : C, IsGrothendieckAbelian.{u} (SiteAbelianSheafCat (τ.over X))]
variable [∀ X : C, IsGrothendieckAbelian.{u} (SiteAbelianSheafCat (τ'.over X))]
variable [∀ X : C,
  (siteAbelianSectionsFunctor (τ.over X) (Over.mk (𝟙 X))).Additive]
variable [∀ X : C,
  (siteAbelianSectionsFunctor (τ'.over X) (Over.mk (𝟙 X))).Additive]

/- Domain-style sampling for Lemma 21.30.10 (2):
- primary domain: hypercohomology comparison on slice sites in the bounded-below derived
  comparison subcategories;
- sampled owner declarations:
  `derivedCategoryBoundedBelowCohomologyInProperty`,
  `(ε[hle]_(X)⁻¹).mapDerivedCategory`,
  `siteAbelianSectionsDerived`,
  `comparisonTopologyPullback_pushforward_isomorphic_of_plusCohomologyIn`;
- best owner abstraction:
  clause `(2)` is the `source-facing` hypercohomology comparison on the Chapter 13 bounded-below
  owner `D⁺_{A' X}`, using the canonical derived pullback and derived-sections owners directly;
- primitive data:
  the comparison situation `h`, the slice object `X`, the bounded-below derived object `K'`, and
  the canonical functors `(ε[hle]_(X)⁻¹).mapDerivedCategory` and
  `siteAbelianSectionsDerived _ (Over.mk (𝟙 X))`;
- derived API:
  the Prop-level hypercohomology comparison below.

Source/core/bridge triage:
- `source-facing`: the degree-`n` hypercohomology comparison for `K'`;
- `core/canonical`: `derivedCategoryBoundedBelowCohomologyInProperty`,
  `(ε[hle]_(X)⁻¹).mapDerivedCategory`, and
  `siteAbelianSectionsDerived`;
- `bridge/view`: the proof route passes through Lemmas `21.30.4` and `21.30.8`, but the public
  statement already uses the canonical owners directly. -/

-- Proof sketch: an object of `D⁺_{A' X}` satisfies the cohomology-range hypothesis from
-- Lemma `21.30.4` in every degree `n`. Apply that source-facing theorem together with the
-- all-degree vanishing result `localizedComparisonLocalVanishingCondition_all h n`, and compute
-- hypercohomology with the canonical slice-site owner
-- `siteAbelianSectionsDerived _ (Over.mk (𝟙 X))`; on the right, use the exact inverse-image
-- functor's canonical derived functor directly rather than the chapter-local abbreviation from
-- Lemma `21.30.8`.
/-- Lemma 21.30.10 (2): in Situation `21.30.1`, if `K' ∈ D⁺_{A' X}`, then the degree-`n`
hypercohomology of `K'` on `(C_{τ'}/X)` is canonically isomorphic to the degree-`n`
hypercohomology of `ε_X⁻¹ K'` on `(C_τ/X)`. -/
@[stacks 0EZH]
theorem comparisonTopologyPullback_hypercohomology_isomorphic_of_plusCohomologyIn
    (h : CohomologyComparisonSituation τ τ' P A')
    (X : C)
    (K' : D⁺_{A' X})
    (n : ℕ) :
    IsIsomorphic
      ((homologyFunctor AddCommGrpCat.{u} (n : ℤ)).obj
        ((RΓ[τ'.over X](Over.mk (𝟙 X))).obj K'.toDerived))
      ((homologyFunctor AddCommGrpCat.{u} (n : ℤ)).obj
        ((RΓ[τ.over X](Over.mk (𝟙 X))).obj
          (((ε[hle]_(X)⁻¹).mapDerivedCategory).obj K'.toDerived))) := sorry

end Derived

end CategoryTheory.GrothendieckTopology
