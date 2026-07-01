import Mathlib
import stacks_project.Chap12.Definition_12_24_9
import stacks_project.Chap12.Lemma_12_24_11
import stacks_project.Chap15.Remark_15_92_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A]
variable [LocallySmall.{0} (ModuleCat A)] [WellPowered.{0} (ModuleCat A)]
variable [HasWidePullbacks (ModuleCat A)] [HasCoproducts (ModuleCat A)]
variable [InitialMonoClass (ModuleCat A)]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling for Example `15.92.23`.
- primary domain: cohomological spectral sequences in `ModuleCat A` computing the cohomology of
  the derived completion of an object of `D(A)`;
- sampled owner/canonical declarations in this domain:
  `CohomologicalSpectralSequence`,
  `CohomologicalSpectralSequence.IsBounded`,
  `FilteredComplex.convergesToCohomology`,
  `DerivedCategory.derivedCompletionOf`;
- best owner abstraction: the cohomological spectral sequence
  `E : CohomologicalSpectralSequence (ModuleCat A) 0`, with the Chapter `12` convergence owner
  `F.convergesToCohomology E` on an associated filtered complex `F`;
- primitive data: only `E` and the auxiliary filtered-complex witness `F` occurring in the
  convergence clause;
- derived API: the `E₂`-page identification, pagewise derived-completeness, and the abutment
  identification with `H^*(K^∧)`;
- source/core/bridge triage:
  `source-facing`: `ConvergesToDerivedCompletionCohomology` and
    `IsDerivedCompletionCohomologySpectralSequence`;
  `core/canonical`: `CohomologicalSpectralSequence`,
    `CohomologicalSpectralSequence.IsBounded`,
    `FilteredComplex.convergesToCohomology`, and `DerivedCategory.derivedCompletionOf`;
  `bridge/view`: the auxiliary filtered complex in the convergence clause together with the
    internal page-two and abutment abbreviations. -/

/-- The `E₂`-term `H^i((H^j(K)[0])^∧)` of Example `15.92.23`. -/
private abbrev derivedCompletionCohomologyPageTwo
    (I : Ideal A) (hI : I.FG) (K : DMod) (i j : ℤ) : ModuleCat A :=
  (H i).obj (((single₀).obj ((H j).obj K))^∧[I, hI])

/-- The abutment term `H^n(K^∧)` of Example `15.92.23`. -/
private abbrev derivedCompletionCohomologyAbutment
    (I : Ideal A) (hI : I.FG) (K : DMod) (n : ℤ) : ModuleCat A :=
  (H n).obj (K^∧[I, hI])

/-- A cohomological spectral sequence converges to the derived-completion cohomology of `K` if it
is associated to a filtered complex whose cohomology identifies with `H^*(K^∧)` and which
satisfies the Chapter `12` convergence owner. -/
def ConvergesToDerivedCompletionCohomology
    (E : CohomologicalSpectralSequence (ModuleCat A) 0)
    (I : Ideal A) (hI : I.FG) (K : DMod) : Prop :=
  ∃ (F : FilteredComplex (ModuleCat A)) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ n : ℤ,
        Nonempty (F.underlying.homology n ≅ derivedCompletionCohomologyAbutment I hI K n)

/-- A cohomological spectral sequence over `ModuleCat A` is a derived-completion cohomology
spectral sequence for `K ∈ D(A)` if it is bounded, every page `E_r` for `r ≥ 2` consists of
modules that are derived complete with respect to `I`, its `E₂`-page is
`H^i((H^j(K)[0])^∧)`, and it converges to `H^{i + j}(K^∧)`. -/
def IsDerivedCompletionCohomologySpectralSequence
    (E : CohomologicalSpectralSequence (ModuleCat A) 0)
    (I : Ideal A) (hI : I.FG) (K : DMod) : Prop :=
  CohomologicalSpectralSequence.IsBounded E ∧
    (∀ i j : ℤ,
      Nonempty ((E.page 2).X (i, j) ≅ derivedCompletionCohomologyPageTwo I hI K i j)) ∧
    (∀ r : ℕ, 2 ≤ r → ∀ i j : ℤ,
      ((E.page r).X (i, j)).IsDerivedCompleteWithRespectTo I) ∧
    ConvergesToDerivedCompletionCohomology E I hI K

/-- A derived-completion cohomology spectral sequence is bounded. -/
theorem IsDerivedCompletionCohomologySpectralSequence.isBounded
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {I : Ideal A} {hI : I.FG} {K : DMod}
    (hE : IsDerivedCompletionCohomologySpectralSequence E I hI K) :
    CohomologicalSpectralSequence.IsBounded E :=
  hE.1

/-- The second page of a derived-completion cohomology spectral sequence computes the cohomology
of the derived completions of the cohomology modules of `K`. -/
theorem IsDerivedCompletionCohomologySpectralSequence.pageTwoIso
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {I : Ideal A} {hI : I.FG} {K : DMod}
    (hE : IsDerivedCompletionCohomologySpectralSequence E I hI K)
    (i j : ℤ) :
    Nonempty ((E.page 2).X (i, j) ≅ (H i).obj (((single₀).obj ((H j).obj K))^∧[I, hI])) :=
  hE.2.1 i j

/-- Every page from `E₂` onward of a derived-completion cohomology spectral sequence consists of
modules that are derived complete with respect to `I`. -/
theorem IsDerivedCompletionCohomologySpectralSequence.page_isDerivedComplete
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {I : Ideal A} {hI : I.FG} {K : DMod}
    (hE : IsDerivedCompletionCohomologySpectralSequence E I hI K)
    (r : ℕ) (hr : 2 ≤ r) (i j : ℤ) :
    ((E.page r).X (i, j)).IsDerivedCompleteWithRespectTo I :=
  hE.2.2.1 r hr i j

/-- A derived-completion cohomology spectral sequence converges to the cohomology of the derived
completion of `K`. -/
theorem IsDerivedCompletionCohomologySpectralSequence.converges
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {I : Ideal A} {hI : I.FG} {K : DMod}
    (hE : IsDerivedCompletionCohomologySpectralSequence E I hI K) :
    ConvergesToDerivedCompletionCohomology E I hI K :=
  hE.2.2.2

-- Proof sketch: apply Lemma `15.92.22` to the filtration `F^p K = τ_{≤ -p} K`, identify the
-- graded piece `gr^p(K)` with `H^{-p}(K)[p]`, and then renumber by `p = -j` and `q = i + 2j`.
-- The boundedness, derived-completeness of the pages, and convergence to `H^*(K^∧)` are inherited
-- from Lemma `15.92.22` after this reindexing.
/-- Example 15.92.23: for a finitely generated ideal `I ⊆ A` and any object `K ∈ D(A)`, there
is a bounded cohomological spectral sequence of bigraded derived-complete `A`-modules whose
`E_2^{i,j}`-term is `H^i(H^j(K)^∧)` and which converges to `H^{i + j}(K^∧)`. The differentials
are those of a cohomological spectral sequence, so they have bidegree `(r, -r + 1)`. -/
theorem exists_derivedCompletion_cohomology_spectralSequence
    (I : Ideal A) (hI : I.FG) (K : DMod) :
    ∃ E : CohomologicalSpectralSequence (ModuleCat A) 0,
      IsDerivedCompletionCohomologySpectralSequence E I hI K := sorry

end

end DerivedCategory
