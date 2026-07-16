import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_9
import StacksProject_2024.stacks_project.Chap12.Lemma_12_25_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open ComplexShape
open CategoryTheory.Limits

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜]

/- Domain-style sampling for Definition `12.25.2`.
- primary domain: convergence of the two spectral sequences attached to a double complex, expressed
  through the canonical first and second filtered complexes on `Tot(K)`;
- sampled owner/canonical declarations:
  `FilteredComplex.weaklyConvergesToCohomology`,
  `FilteredComplex.abutsToCohomology`,
  `FilteredComplex.convergesToCohomology`,
  `firstDoubleComplexFilteredComplex`,
  `secondDoubleComplexFilteredComplex`;
- best owner abstraction: the canonical filtered-complex owners
  `firstDoubleComplexFilteredComplex K` and `secondDoubleComplexFilteredComplex K`, with an
  associated spectral sequence `E` only when the full convergence predicate is needed;
- primitive data: a double complex `K`, and optionally an associated spectral sequence `E` of one
  of the two canonical filtrations on `Tot(K)`;
- derived API: the convergence predicates on those two canonical filtered-complex owners;
- source/core/bridge triage:
  `source-facing`: the first and second spectral sequences of a double complex;
  `core/canonical`: the filtered-complex convergence owners on
    `firstDoubleComplexFilteredComplex K` and `secondDoubleComplexFilteredComplex K`;
  `bridge/view`: the two canonical filtered-complex constructions on `Tot(K)`.

This item is recall-only: once the filtered-complex model is fixed, the chapter's canonical
filtered-complex convergence owners already express exactly the textbook notions. -/

section First

variable (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]

/- Definition 12.25.2 (1): for the canonical first filtered complex on `Tot(K)`, weak
convergence of the first spectral sequence to `H^*(Tot(K))` is recalled canonically by
`(firstDoubleComplexFilteredComplex K).weaklyConvergesToCohomology`. -/
#check (firstDoubleComplexFilteredComplex K).weaklyConvergesToCohomology

/- Definition 12.25.2 (2): for the same canonical first filtered complex, abutment of the first
spectral sequence to `H^*(Tot(K))` is recalled canonically by
`(firstDoubleComplexFilteredComplex K).abutsToCohomology`. -/
#check (firstDoubleComplexFilteredComplex K).abutsToCohomology

variable (E : CohomologicalSpectralSequence 𝒜 0)
variable [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]

/- Definition 12.25.2 (3): for an associated spectral sequence `E` of the canonical first
filtered complex, convergence to `H^*(Tot(K))` is recalled canonically by
`(firstDoubleComplexFilteredComplex K).convergesToCohomology E`. -/
#check (firstDoubleComplexFilteredComplex K).convergesToCohomology E

end First

section Second

variable (K : HomologicalComplex₂ 𝒜 (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]

/- Definition 12.25.2 (4): for the canonical second filtered complex on `Tot(K)`, weak
convergence of the second spectral sequence to `H^*(Tot(K))` is recalled canonically by
`(secondDoubleComplexFilteredComplex K).weaklyConvergesToCohomology`. -/
#check (secondDoubleComplexFilteredComplex K).weaklyConvergesToCohomology

/- Definition 12.25.2 (5): for the same canonical second filtered complex, abutment of the
second spectral sequence to `H^*(Tot(K))` is recalled canonically by
`(secondDoubleComplexFilteredComplex K).abutsToCohomology`. -/
#check (secondDoubleComplexFilteredComplex K).abutsToCohomology

variable (E : CohomologicalSpectralSequence 𝒜 0)
variable [IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex K) E]

/- Definition 12.25.2 (6): for an associated spectral sequence `E` of the canonical second
filtered complex, convergence to `H^*(Tot(K))` is recalled canonically by
`(secondDoubleComplexFilteredComplex K).convergesToCohomology E`. -/
#check (secondDoubleComplexFilteredComplex K).convergesToCohomology E

end Second

end CategoryTheory
