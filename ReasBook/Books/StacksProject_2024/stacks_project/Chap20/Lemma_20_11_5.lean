import StacksProject_2024.Chap13.Lemma_13_22_2_Grothendieck_spectral_sequence
import StacksProject_2024.Chap20.Lemma_20_11_2

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Modules X)]
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Opens X.carrier)

/- Domain-style sampling for Lemma 20.11.5:
- primary domain: first-quadrant cohomological spectral sequences for `𝒪_X`-modules on a ringed
  space, with `E₂`-page given by Čech cohomology and abutment given by derived sections;
- sampled owner declarations:
  `sectionsRingOnOpen`,
  `moduleCohomologyAtOpen`,
  `presheafModuleCechCohomologyAtOpen`,
  `exists_grothendieckSpectralSequence`,
  `IsAssociatedToFilteredComplex`,
  `FilteredComplex.convergesToCohomology`;
- best owner abstraction:
  `source-facing`: the direct existence theorem asserting a Čech-to-cohomology spectral sequence
    for one `𝒪_X`-module and one open covering family of `U`;
  `core/canonical`: `sectionsRingOnOpen`, the sections functor
    `moduleCohomologyAtOpen`, the open-family Čech cohomology owner
    `presheafModuleCechCohomologyAtOpen`, the Chapter `13` Grothendieck spectral-sequence theorem,
    and the Chapter `12` owner predicate `IsAssociatedToFilteredComplex`;
  `bridge/view`: the internal passage from the source-facing open family `𝒰` with `iSup 𝒰 = U`
    to the slice-site cover used by the underlying Čech construction, together with the
    cohomology-presheaf term on the `E₂`-page and the abutment comparison isomorphisms.
- primitive data: the open-sections ring owner `sectionsRingOnOpen X U`, the indexed open family
  `𝒰 : ι → Opens X.carrier`, the cover equality `iSup 𝒰 = U`, and the derived sections functor
  on `U`;
- derived API: the abutment term and the bounded convergent associated spectral sequence with its
  page-two and abutment comparisons.

The sections functor on `U` is already canonically owned by `SheafOfModules.evaluation`, and the
section ring is already owned by `sectionsRingOnOpen`, while the abutment and convergence data are
already canonically owned by `IsAssociatedToFilteredComplex` and
`FilteredComplex.convergesToCohomology`, so this file should use those owners directly rather than
introduce a parallel functor-plus-abutment package.
-/
local notation "ΓModU" => ModuleCat (sectionsRingOnOpen X U)

-- Proof sketch: apply the Grothendieck spectral sequence to the composite of the left exact
-- inclusion `Mod(𝒪_X) ⥤ PMod(𝒪_X)` with degree-zero Čech cohomology for the cover `𝒰`. The
-- cover hypothesis `h𝒰 : iSup 𝒰 = U` is what lets Lemma
-- `20.9.2` identify degree-zero Čech cohomology with sections on `U`; Lemma `20.11.1` shows that
-- injective `𝒪_X`-modules are Čech-acyclic for the cover, and Lemmas `20.10.5` and `20.11.4`
-- identify the `E₂`-page with Čech cohomology of the degree-`q` cohomology presheaf of `ℱ`.
-- The Chapter `13` Grothendieck construction produces an associated filtered complex whose
-- abutment is the cohomology on `U`, and the Chapter `12`
-- owners `IsAssociatedToFilteredComplex` and `FilteredComplex.convergesToCohomology` record the
-- canonical convergence data.
/-- Lemma 20.11.5: for a ringed space `X`, an open subset `U`, an open covering family `𝒰` of
`U`, and an `𝒪_X`-module `ℱ`, there is a cohomological spectral sequence whose `E₂`-page is the
degree-`p` Čech cohomology of the degree-`q` cohomology presheaf of `ℱ`, converging to the
degree-`p + q` cohomology of `ℱ` on `U`. -/
@[stacks 01ES]
theorem exists_cechToModuleCohomologySpectralSequence
    (h𝒰 : iSup 𝒰 = U) (ℱ : Modules X) :
    ∃ (filteredComplex : FilteredComplex ΓModU)
      (spectralSequence : CohomologicalSpectralSequence ΓModU 0)
      (associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (pageTwo :
        ∀ p q : ℕ,
          (spectralSequence.page 2).X (Int.ofNat p, Int.ofNat q) ≅
            presheafModuleCechCohomologyAtOpen U 𝒰 h𝒰
              (((SheafOfModules.forget X.ringCatSheaf).rightDerived q).obj ℱ) p)
      (abutment :
        ∀ n : ℕ,
          filteredComplex.underlying.homology (Int.ofNat n) ≅
            moduleCohomologyAtOpen U ℱ n),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        filteredComplex.cohomologyFiltrationIsFinite ∧
        filteredComplex.convergesToCohomology spectralSequence := by
  sorry

end AlgebraicGeometry.RingedSpace
