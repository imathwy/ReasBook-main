import StacksProject_2024.Chap13.Lemma_13_22_2_Grothendieck_spectral_sequence
import StacksProject_2024.Chap20.«20_2_0_4»
import StacksProject_2024.Chap20.«20_3_0_4»
import StacksProject_2024.Chap20.Global_sections_module_owners_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

namespace AlgebraicGeometry.RingedSpace

variable {X Y Z : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y
local notation "ModZ" => RingedSpace.Modules Z
local notation "DModX" => D⁺(ModX)
local notation "DModZ" => D⁺(ModZ)

/- Domain-style sampling:
- primary domain: Grothendieck and Leray spectral sequences for direct images of module sheaves on
  ringed spaces;
- sampled owner declarations:
  `higherDirectImageModule`,
  `Functor.totalRightDerived`,
  `exists_grothendieckSpectralSequence`,
  `exists_leraySpectralSequence_boundedBelow`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.convergesToCohomology`;
- best owner abstraction: the Chapter `13` Grothendieck spectral-sequence owner specialized to the
  Chapter `20` higher direct image owner `higherDirectImageModule` and the bounded-below
  direct-image specialization of `Functor.totalRightDerived` for module sheaves, reused through
  the chapter Leray owner surface of Lemma `20.13.4` and exposed on the theorem surface through
  the source-facing bounded-below cohomology owner `H^q(Rf_[f] K)`;
- primitive data here: only the relative Leray spectral-sequence existence statements;
- derived API here: the source-facing higher direct images `R^q f_* ℱ`,
  `R^p g_* (R^q f_* ℱ)`, and the bounded-below cohomology-sheaf bridges
  `H^q(Rf_[f] K)` and `H^n(Rf_[f ≫ g] K)`;
- source/core/bridge triage:
  `source-facing`: the relative Leray existence statements;
  `core/canonical`: `higherDirectImageModule`, `Functor.totalRightDerived`,
    `exists_grothendieckSpectralSequence`, and the bounded-below derived-category owners
    `D⁺(ModX)`, `D⁺(ModY)`, `D⁺(ModZ)`, together with
    `IsAssociatedToFilteredComplex`, `FilteredComplex.cohomologyFiltrationIsFinite`, and
    `FilteredComplex.convergesToCohomology`;
  `bridge/view`: the notation `Rf_[f] K` and its cohomology-sheaf bridge `H^q(Rf_[f] K)`,
    together with the specialization from the generic Grothendieck package to direct images of
    `𝒪_X`-modules on ringed spaces.

The Grothendieck spectral sequence already converges through the Chapter `12/13` owner package, and
the Chapter `20` Leray file already provides the corresponding local theorem surface. This file
should therefore expose that package through the source-facing higher direct image owner
`higherDirectImageModule` and write the bounded-below cohomology-sheaf bridge on the theorem
surface with the canonical owner expressions `H^q(Rf_[f] K)` and `H^n(Rf_[f ≫ g] K)`, rather
than through lower-level bounded-below inclusion bookkeeping, a parallel local alias, or a raw
derived-functor composite.
-/

-- Proof sketch: apply the Grothendieck spectral sequence of Lemma `13.22.2` to the composite
-- of the two direct-image functors on sheaves of modules. Lemma `20.13.7` identifies the right
-- derived direct image of the composite with the composite of the right derived direct images, so
-- the `E₂`-page becomes `R^p g_* (R^q f_* ℱ)`. Naturality of the Grothendieck
-- construction gives the usual relative Leray spectral sequence.
/-- Lemma 20.13.8 (Relative Leray spectral sequence): for composable morphisms of ringed spaces
`f : X ⟶ Y`, `g : Y ⟶ Z`, and an `𝒪_X`-module `ℱ`, there is a bounded cohomological spectral
sequence with `E_2^{p,q} = R^p g_* (R^q f_* ℱ)` converging to `R^{p + q} (g ∘ f)_* ℱ`. -/
@[stacks 01F6]
theorem exists_relativeLeraySpectralSequence
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInjectiveResolutions ModX]
    [HasInjectiveResolutions ModY]
    (ℱ : ModX) :
    ∃ (filteredComplex : FilteredComplex ModZ)
      (spectralSequence : CohomologicalSpectralSequence ModZ 0)
      (_ : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageTwoIso :
        ∀ p q : ℕ,
          (spectralSequence.page 2).X (Int.ofNat p, Int.ofNat q) ≅
            R^{p}_[g](R^{q}_[f](ℱ)))
      (targetIso :
        ∀ n : ℕ,
          filteredComplex.underlying.homology (Int.ofNat n) ≅
            R^{n}_[f ≫ g](ℱ)),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        filteredComplex.cohomologyFiltrationIsFinite ∧
        filteredComplex.convergesToCohomology spectralSequence := sorry

-- Proof sketch: apply the bounded-below Grothendieck spectral sequence to the composable
-- direct-image functors `f_*` and `g_*` on sheaves of modules. The same comparison from Lemma
-- `20.13.7` identifies the abutment with the cohomology sheaves of `R(g ∘ f)_* K`, and the
-- `E₂`-page is obtained by taking higher direct images of the cohomology sheaves of `Rf_[f] K`.
/-- A bounded-below derived version of the relative Leray spectral sequence for module sheaves on
ringed spaces. -/
theorem exists_relativeLeraySpectralSequence_boundedBelow
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInjectiveResolutions ModY]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (f _*))
      (Qis⁺(ModX))]
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow ((f ≫ g) _*))
      (Qis⁺(ModX))]
    (K : DModX) :
    ∃ (filteredComplex : FilteredComplex ModZ)
      (spectralSequence : CohomologicalSpectralSequence ModZ 0)
      (_ : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageTwoIso :
        ∀ p : ℕ, ∀ q : ℤ,
          (spectralSequence.page 2).X (Int.ofNat p, q) ≅
            R^{p}_[g](H^q(Rf_[f] K)))
      (targetIso :
        ∀ n : ℤ,
          filteredComplex.underlying.homology n ≅
            H^n(Rf_[f ≫ g] K)),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        filteredComplex.cohomologyFiltrationIsFinite ∧
        filteredComplex.convergesToCohomology spectralSequence := sorry

end AlgebraicGeometry.RingedSpace
