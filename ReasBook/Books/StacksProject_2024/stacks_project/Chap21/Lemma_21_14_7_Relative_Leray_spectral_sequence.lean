import StacksProject_2024.Chap21.Lemma_21_7_4_core
import StacksProject_2024.Chap21.Lemma_21_14_5_Leray_spectral_sequence

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped RingedSite.Hom

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

namespace RingedSite.Hom

variable {X Y Z : RingedSite.{u, v}}

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y
local notation "ModZ" => ModuleCat Z
local notation "DModX" => D⁺(ModX)
local notation "QX" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ModX) ⥤ DModX)
local notation "QisX" => boundedBelowHomotopyQuasiIso ModX

variable [IsGrothendieckAbelian.{max u v} ModX]
variable [IsGrothendieckAbelian.{max u v} ModY]
variable [IsGrothendieckAbelian.{max u v} ModZ]

/- Domain-style sampling:
- primary domain: Grothendieck and Leray spectral sequences for direct images of module sheaves on
  ringed topoi, formalized here by ringed sites;
- sampled owner declarations:
  `Functor.totalRightDerived`,
  `CategoryTheory.exists_grothendieckSpectralSequence`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.convergesToCohomology`;
- best owner abstraction: the Chapter `13` Grothendieck spectral-sequence owner, specialized to
  the Chapter `21` higher direct image owner `R^{q}_[f](ℱ)` and to the bounded-below derived
  direct-image owner `modulePushforwardDerivedPlus`;
- primitive data here: the module categories on `X`, `Y`, and `Z`, the additive pushforward
  functors `f_*`, `g_*`, and `(f ≫ g)_*`, together with a module sheaf `ℱ` or a bounded-below
  derived object `K`;
- derived API here: the bounded-below derived direct image `Rf_[f] K`, its cohomology sheaves, and
  the source-facing relative Leray spectral-sequence existence theorems.

Source/core/bridge triage:
- `source-facing`: `exists_relativeLeraySpectralSequence` and
  `exists_relativeLeraySpectralSequence_boundedBelow`;
- `core/canonical`: `higherDirectImageModule`, `Functor.totalRightDerived`,
  `CategoryTheory.exists_grothendieckSpectralSequence`, `CohomologicalSpectralSequence`,
  `IsAssociatedToFilteredComplex`, `FilteredComplex.cohomologyFiltrationIsFinite`, and
  `FilteredComplex.convergesToCohomology`;
- `bridge/view`: the bounded-below owner `modulePushforwardDerivedPlus`, the cohomology-sheaf
  surface `H^q(Rf_[f] K)`, and the page-two/abutment comparison isomorphisms expressing the
  Grothendieck package in relative Leray form.

The deleted local `RelativeLeraySpectralSequence` wrapper structures were duplicate packaging over
the Chapter `12/13` spectral-sequence owners. This file now states the source-facing existence
results directly on those owners, reusing the bounded-below derived direct-image owner introduced
in Lemma `21.14.5`. -/

-- Proof sketch: apply the Grothendieck spectral sequence to the composite
-- `SheafOfModules.pushforward f.structureSheafMap ⋙ SheafOfModules.pushforward g.structureSheafMap`.
-- Lemma `21.14.1` shows that the pushforward of an injective module sheaf is totally acyclic on
-- the intermediate ringed topos, and Lemma `21.14.3` upgrades total acyclicity to right
-- acyclicity for the second pushforward. The Chapter `13` Grothendieck spectral sequence then
-- yields the usual relative Leray package.
/-- Lemma 21.14.7 (Relative Leray spectral sequence): for composable morphisms of ringed topoi,
formalized here by ringed-site morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, and an `𝒪_X`-module `ℱ`,
there is a bounded cohomological spectral sequence with
`E₂^{p,q} = R^p g_* (R^q f_* ℱ)` converging to `R^{p + q} (g ∘ f)_* ℱ`. -/
@[stacks 0734]
theorem exists_relativeLeraySpectralSequence
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInjectiveResolutions ModX]
    [HasInjectiveResolutions ModY]
    [f.modulePushforward.Additive]
    [g.modulePushforward.Additive]
    [(f ≫ g).modulePushforward.Additive]
    [LocallySmall ModZ]
    [WellPowered ModZ]
    [HasWidePullbacks ModZ]
    [HasCoproducts ModZ]
    [InitialMonoClass ModZ]
    (ℱ : ModX) :
    ∃ (filteredComplex : FilteredComplex ModZ)
      (spectralSequence : CohomologicalSpectralSequence ModZ 0)
      (hAssoc : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageTwoIso : ∀ p q : ℕ,
        (spectralSequence.page 2).X (Int.ofNat p, Int.ofNat q) ≅
          R^{p}_[g](R^{q}_[f](ℱ)))
      (targetIso : ∀ n : ℕ,
        filteredComplex.underlying.homology (Int.ofNat n) ≅
          R^{n}_[f ≫ g](ℱ)),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        filteredComplex.cohomologyFiltrationIsFinite ∧
        filteredComplex.convergesToCohomology spectralSequence := sorry

-- Proof sketch: apply Lemma `13.22.2` directly to the bounded-below derived categories of module
-- sheaves and to the composable direct-image functors `f_*` and `g_*`. The same acyclicity input
-- yields the `E₂`-page `R^p g_* (H^q(Rf_* K))`, and the abutment is the cohomology sheaf of the
-- bounded-below derived direct image `R(f ≫ g)_* K`.
/-- The bounded-below derived version of the relative Leray spectral sequence for module sheaves on
ringed sites. -/
theorem exists_relativeLeraySpectralSequence_boundedBelow
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.modulePushforward.Additive]
    [g.modulePushforward.Additive]
    [(f ≫ g).modulePushforward.Additive]
    [LocallySmall ModZ]
    [WellPowered ModZ]
    [HasWidePullbacks ModZ]
    [HasCoproducts ModZ]
    [InitialMonoClass ModZ]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow f.modulePushforward)
      QisX]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (g.modulePushforward))
      (boundedBelowHomotopyQuasiIso ModY)]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (f ≫ g).modulePushforward)
      QisX]
    [HasInjectiveResolutions ModY]
    (K : DModX) :
    ∃ (filteredComplex : FilteredComplex ModZ)
      (spectralSequence : CohomologicalSpectralSequence ModZ 0)
      (hAssoc : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageTwoIso : ∀ (p : ℕ) (q : ℤ),
        (spectralSequence.page 2).X (Int.ofNat p, q) ≅
          R^{p}_[g](H^q(Rf_[f] K)))
      (targetIso : ∀ n : ℤ,
        filteredComplex.underlying.homology n ≅
          H^n(Rf_[f ≫ g] K)),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        filteredComplex.cohomologyFiltrationIsFinite ∧
        filteredComplex.convergesToCohomology spectralSequence := sorry

end RingedSite.Hom
