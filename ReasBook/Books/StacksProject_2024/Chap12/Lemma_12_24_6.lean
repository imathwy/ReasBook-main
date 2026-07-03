import Mathlib
import stacks_project.Chap12.Aux_12_20_2_1
import stacks_project.Chap12.Definition_12_20_2
import stacks_project.Chap12.Lemma_12_24_2
import stacks_project.Chap12.Definition_12_24_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped SpectralSequence

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace CohomologicalSpectralSequence

variable [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜]

/-- Lemma 12.24.6 (1): in every bidegree, the limit term is the quotient
`E_∞^{p,q} = Z_∞^{p,q} / B_∞^{p,q}`. -/
theorem infinityPage_def
    (E : CohomologicalSpectralSequence 𝒜 0) (pq : ℤ × ℤ) :
    (E.toPageOneSpectralSequence).infinityPage pq =
      cokernel
        (Subobject.ofLE
          ((E.toPageOneSpectralSequence).boundaryInfinity pq)
          ((E.toPageOneSpectralSequence).cycleInfinity pq)
          ((E.toPageOneSpectralSequence).boundaryInfinity_le_cycleInfinity pq)) := by
  simpa using
    SpectralSequence.infinityPage_def E.toPageOneSpectralSequence pq

end CohomologicalSpectralSequence

namespace FilteredComplex

variable [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜]

/-
Domain-style sampling for Lemma `12.24.6` in the filtered-complex layer.
- primary domain: the `E_∞`-comparison between the induced cohomology filtration and the infinity
  page of an associated cohomological spectral sequence;
- sampled owner declarations:
  `FilteredComplex.inducedCohomologyFiltration`,
  `SpectralSequence.infinityPage`,
  `IsAssociatedToFilteredComplex`,
  `CategoryTheory.IsSubquotient`;
- best owner abstraction:
  the graded piece of `K.inducedCohomologyFiltration n` and the canonical infinity-page object
  `(E.toPageOneSpectralSequence).infinityPage (p, n - p)`;
- primitive data: a filtered complex `K`, an associated spectral sequence `E`, and the indices
  `n`, `p`;
- derived API: the source-facing subquotient comparison below;
- source/core/bridge triage:
  `source-facing`: `cohomologyGradedPiece_isSubquotient_limitTerm`;
  `core/canonical`: `inducedCohomologyFiltration`, `infinityPage`,
    `IsAssociatedToFilteredComplex`;
  `bridge/view`: the subquotient comparison induced by the always-true inclusions
    `(12.24.6.2)` and `(12.24.6.1)`.

The weak-convergence equalities belong to the stronger isomorphism criterion of
`FilteredComplex.weaklyConvergesToCohomology_iff`; they are not primitive input for the
unconditional subquotient statement here. -/

/-- Lemma 12.24.6 (2): for an associated cohomological spectral sequence, the always-true
inclusions `(12.24.6.2)` and `(12.24.6.1)` make the graded piece `gr^p H^n(K^•)` of the induced
cohomology filtration a subquotient of the antidiagonal limit term `E_∞^{p,n-p}`. -/
theorem cohomologyGradedPiece_isSubquotient_limitTerm
    (K : FilteredComplex 𝒜) (E : CohomologicalSpectralSequence 𝒜 0)
    [IsAssociatedToFilteredComplex K E]
    (n p : ℤ) :
    IsSubquotient ((K.inducedCohomologyFiltration n).gradedPiece p)
      ((E.toPageOneSpectralSequence).infinityPage (p, n - p)) := sorry

end FilteredComplex

end CategoryTheory
