import StacksProject_2024.stacks_project.Chap13.Lemma_13_22_2_Grothendieck_spectral_sequence
import StacksProject_2024.stacks_project.Chap20.«20_3_0_4»
import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core
import StacksProject_2024.stacks_project.Chap20.Sections_on_open

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DerivedCategory.TStructure
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

namespace AlgebraicGeometry.RingedSpace

open scoped RingedSpaceOpenHypercohomology

variable {X Y : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "DModX" => D⁺(ModX)
local notation "TopOpenX" => (⊤ : Opens X.carrier)
local notation "TopOpenY" => (⊤ : Opens Y.carrier)
local notation "ΓModY" => ModuleCat (sectionsRingOnOpen Y TopOpenY)

/- Domain-style sampling for Lemma `20.13.4`.
- primary domain: bounded-below Leray spectral sequences and open hypercohomology for module
  sheaves on ringed spaces;
- sampled owner declarations:
  `Functor.totalRightDerived`,
  `exists_grothendieckSpectralSequence`,
  `Rf_[f]`,
  `moduleCohomologyAtOpen`,
  `moduleOpenHypercohomology`;
- best owner abstraction: the Chapter `13` bounded-below Grothendieck spectral-sequence owner
  specialized to `f _*`, with the Leray `E₂`-page expressed through the source-facing cohomology
  sheaf `H^q(Rf_[f] K)` and the top-open module-cohomology owner
  `moduleCohomologyAtOpen TopOpenY`, while the abutment is expressed through the Chapter `20`
  open-hypercohomology owner written on the theorem surface as `H^n(TopOpenX, K.toDerived)`;
- primitive data: the bounded-below derived object `K : D⁺(ModX)`, the additive functor `f _*`,
  and the canonical owners `Rf_[f]`, `moduleCohomologyAtOpen`, and
  `moduleOpenHypercohomology`;
- derived API in this file: the source-facing Leray spectral-sequence existence theorem with its
  page-two and abutment comparison isomorphisms written directly through those canonical owners;
- source/core/bridge triage:
  `source-facing`: `exists_leraySpectralSequence_boundedBelow`;
  `core/canonical`: `Functor.totalRightDerived`, `moduleCohomologyAtOpen`,
    `moduleOpenHypercohomology`, `CohomologicalSpectralSequence`,
    `IsAssociatedToFilteredComplex`, and `FilteredComplex.convergesToCohomology`;
  `bridge/view`: the cohomology-sheaf bridge `H^q(Rf_[f] K)` and the page-two and abutment
    isomorphisms expressing those owners in the Leray form. -/

-- Proof sketch: apply the Grothendieck spectral sequence of Lemma `13.22.2` to the composite of
-- `f _*` with the additive global-sections functor on `Y`. The `E₂`-page is the top-open module
-- cohomology of the cohomology sheaf `H^q(Rf_[f] K)`, and the abutment is the top-open
-- hypercohomology `H^n(TopOpenX, K.toDerived)`.
/-- Lemma 20.13.4 (Leray spectral sequence): for a morphism of ringed spaces `f : X ⟶ Y` and a
bounded-below derived `𝒪_X`-module `K`, there is a cohomological spectral sequence with
`E₂^{p,q} = H^p(Y, R^q f_* K)` converging to the hypercohomology `H^{p + q}(X, K)`. -/
@[stacks 01F2]
theorem exists_leraySpectralSequence_boundedBelow
    (f : X ⟶ Y)
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (f _*))
      (boundedBelowHomotopyQuasiIso ModX)]
    (K : DModX) :
    ∃ (filteredComplex : FilteredComplex AddCommGrpCat.{u})
      (spectralSequence : CohomologicalSpectralSequence AddCommGrpCat.{u} 0)
      (_ : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageTwoIso :
        ∀ p : ℕ, ∀ q : ℤ,
          (spectralSequence.page 2).X (Int.ofNat p, q) ≅
            (forget₂ ΓModY AddCommGrpCat.{u}).obj
              (moduleCohomologyAtOpen TopOpenY (H^q(Rf_[f] K)) p))
      (targetIso :
        ∀ n : ℤ,
          filteredComplex.underlying.homology n ≅ H^n(TopOpenX, K.toDerived)),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        filteredComplex.cohomologyFiltrationIsFinite ∧
        filteredComplex.convergesToCohomology spectralSequence := sorry

end AlgebraicGeometry.RingedSpace
