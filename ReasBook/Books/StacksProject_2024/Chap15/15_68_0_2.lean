import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap19.Remark_19_13_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open DerivedCategory
open CategoryTheory.Limits
open scoped CategoryTheory

universe u

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

attribute [local instance] HasDerivedCategory.standard

local notation "ModR" => ModuleCat R
local notation "single₀" => singleFunctor ModR (0 : ℤ)

/- 
Domain-style sampling for `15.68.0.2`.
- primary domain: cohomological spectral sequences computing hyper-`Ext` from a bounded-below
  cochain complex of `R`-modules;
- sampled owner/canonical declarations in the same domain:
  `CategoryTheory.DerivedExtTermwiseSpectralSequenceData`,
  `CategoryTheory.derivedExtTermwiseSpectralSequence_exists`,
  `CategoryTheory.FilteredComplex.convergesToCohomology`,
  `CategoryTheory.IsAssociatedToFilteredComplex`;
- best owner abstraction: the Chapter `12` convergence owner `F.convergesToCohomology E` for an
  associated filtered complex `F`, with the Chapter `19` package
  `DerivedExtTermwiseSpectralSequenceData (M[0]) K` serving as the bridge that supplies the
  filtered-complex model, the associated spectral sequence, the page-one identification, the
  abutment cohomology identification, and the convergence witness under boundedness hypotheses;
- primitive data for the source-facing statement below: a spectral sequence `E`, a filtered
  complex `F`, the owner witness `IsAssociatedToFilteredComplex F E`, the page-one
  identifications, the convergence owner `F.convergesToCohomology E`, and the abutment
  cohomology identifications;
- derived API: the specialized Chapter `19` existence recall together with the convergence
  companion below, which applies the package field `converges_of_boundedness` to the source
  bounded-belowness hypothesis.
- source/core/bridge triage:
  `source-facing`: `exists_termwise_ext_spectral_sequence`;
  `core/canonical`: `IsAssociatedToFilteredComplex`,
    `FilteredComplex.convergesToCohomology`;
  `bridge/view`: `DerivedExtTermwiseSpectralSequenceData`, used directly as the owner package for
    the recalled existence statement and for the convergence companion.
-/

/- 15.68.0.2: for an `R`-module `M` and a bounded-below cochain complex `K^•`, the Chapter `19`
owner package `DerivedExtTermwiseSpectralSequenceData` specialized to `M[0]` records the
spectral sequence with `E₁^{i,j} = \operatorname{Ext}^j_R(M, K^i)`, and bounded-belowness of
`K^•` upgrades that package to the Chapter `12` convergence owner. -/
variable (M : ModR) (K : CochainComplex ModR ℤ)

recall derivedExtTermwiseSpectralSequence_exists :
  Nonempty
    (DerivedExtTermwiseSpectralSequenceData
      ((single₀).obj M)
      K)

-- Proof sketch: every degree-zero derived object `M[0]` is bounded above by construction, so the
-- convergence field bundled in the Chapter `19` owner package applies as soon as `K^•` is
-- bounded below.
theorem termwise_ext_spectral_sequence_converges
    (M : ModR) (K : CochainComplex ModR ℤ)
    (S :
      DerivedExtTermwiseSpectralSequenceData
        ((single₀).obj M)
        K)
    (hK : ∃ a : ℤ, K.IsStrictlyGE a) :
    S.filteredComplex.convergesToCohomology S.spectralSequence := by
  have hM : DerivedCategoryIsBoundedAbove ((single₀).obj M) :=
    ⟨0, fun i hi ↦
      isZero_of_isLE ((single₀).obj M) 0 i hi⟩
  exact S.converges_of_boundedness hM hK

end

end CategoryTheory
