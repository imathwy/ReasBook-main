import Mathlib
import stacks_project.Chap12.Definition_12_10_1
import stacks_project.Chap12.Definition_12_24_9
import stacks_project.Chap12.Lemma_12_24_2
import stacks_project.Chap12.Lemma_12_24_8
import stacks_project.Chap12.Lemma_12_24_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace CategoryTheory
namespace FilteredComplex

section FiniteFiltrations

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasZeroObject 𝒜]

/- Domain-style sampling for Lemma `12.24.11`.
- primary domain: filtered complexes in an abelian category, their associated cohomological
  spectral sequences, and the induced filtrations on cohomology;
- sampled owner/canonical declarations in this domain:
  `FilteredObject.IsFinite`,
  `FilteredComplex.inducedCohomologyFiltration`,
  `FilteredComplex.abutsToCohomology`,
  `FilteredComplex.convergesToCohomology`,
  `CohomologicalSpectralSequence.IsBounded`;
- best owner abstraction: the filtered-complex owner `K : FilteredComplex 𝒜`, with termwise
  finiteness and cohomology-filtration finiteness attached directly to that owner;
- primitive data: only the filtered complex `K`, a chosen associated spectral sequence `E`, and
  the object property `P`;
- derived API: boundedness of `E`, finiteness of the induced cohomology filtration, and the weak
  Serre membership and convergence consequences for the cohomology objects.
Source/core/bridge triage:
- `source-facing`: `HasFiniteFiltrations` and the four lemmas below;
- `core/canonical`: `FilteredComplex`, `FilteredObject.IsFinite`,
  `FilteredComplex.inducedCohomologyFiltration`, and
  `FilteredComplex.convergesToCohomology`,
  `CohomologicalSpectralSequence.IsBounded`;
- `bridge/view`: the passage from a page of an associated spectral sequence to the cohomology
  objects of the underlying complex via the induced filtration.

The file therefore keeps the source-facing hypotheses and consequences, but it places them on the
canonical `FilteredComplex` owner instead of a parallel root-level wrapper vocabulary. -/

/-- Each term `K^n` of a filtered complex has a finite filtration when some stage is the whole
object and some stage is zero. -/
abbrev HasFiniteFiltrations (K : FilteredComplex 𝒜) : Prop :=
  ∀ n : ℤ, (K.X n).IsFinite

end FiniteFiltrations

section Abelian

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The induced filtration on the cohomology in degree `n` is finite when the owner filtration on
`H^n(K^•)` has a top stage and a bottom stage. -/
abbrev cohomologyFiltrationIsFinite (K : FilteredComplex 𝒜) : Prop :=
  ∀ n : ℤ, (K.inducedCohomologyFiltration n).IsFinite

variable (K : FilteredComplex 𝒜)

section AssociatedSpectralSequence

variable (E : CohomologicalSpectralSequence 𝒜 0) [IsAssociatedToFilteredComplex K E]

-- Proof sketch: on the initial page of total degree `n`, the entry `E₀^{p,n-p}` is the graded
-- piece `gr^p K^n`; finite filtrations on each `K^n` therefore give only finitely many nonzero
-- terms on every antidiagonal.
/-- Lemma 12.24.11 (1): if every term `K^n` of a filtered complex has a finite filtration, then
the associated spectral sequence is bounded. -/
theorem associatedSpectralSequence_isBounded_of_hasFiniteFiltrations
    (hfin : K.HasFiniteFiltrations) :
    CohomologicalSpectralSequence.IsBounded E := sorry

-- Proof sketch: Equation `(12.24.5.1)` identifies the induced filtration on cohomology with the
-- images of the finite stages of the filtration on `K^n`; once the filtration on `K^n` is finite,
-- the induced one has top stage the cycles and bottom stage the boundaries.
/-- Lemma 12.24.11 (2): if every term `K^n` has a finite filtration, then the induced filtration
on each cohomology object `H^n(K^•)` is finite. -/
theorem cohomologyFiltrationIsFinite_of_hasFiniteFiltrations
    (hfin : K.HasFiniteFiltrations) :
    K.cohomologyFiltrationIsFinite := sorry

section Convergence

variable [LocallySmall 𝒜] [WellPowered 𝒜] [HasWidePullbacks 𝒜] [HasCoproducts 𝒜]
  [InitialMonoClass 𝒜]

-- Proof sketch: finite filtrations on the terms of `K` force boundedness of the associated
-- spectral sequence, hence regularity; part (2) gives the corresponding finiteness of the induced
-- cohomology filtration, which yields the completeness required in Definition `12.24.9`.
/-- Lemma 12.24.11 (3): if every term `K^n` of a filtered complex has a finite filtration, then
the associated spectral sequence converges to the cohomology of the underlying complex in the
sense of Definition `12.24.9`. -/
theorem convergesToCohomology_of_hasFiniteFiltrations
    (hfin : K.HasFiniteFiltrations) :
    K.convergesToCohomology E := sorry

end Convergence

-- Proof sketch: boundedness implies eventual stabilization, so a page `E_r` lying in a weak
-- Serre subcategory forces the corresponding `E_∞`-graded pieces to lie there as well. The
-- finite cohomology filtration from part (2) then shows `H^n(K^•)` itself belongs to the weak
-- Serre subcategory by closure under extensions.
/-- Lemma 12.24.11 (4): let `\mathcal C` be a weak Serre subcategory of the ambient abelian
category. If for some page `r` all terms `E_r^{p,q}` of the spectral sequence associated to the
filtered complex lie in `\mathcal C`, then every cohomology object `H^n(K^•)` lies in
`\mathcal C`. -/
theorem cohomologyObject_mem_of_page_mem_of_hasFiniteFiltrations
    (P : ObjectProperty 𝒜)
    [IsWeakSerreClass P]
    (hfin : K.HasFiniteFiltrations)
    (r : ℤ) (hr : 0 ≤ r)
    (hpage : ∀ p q : ℤ, P ((E.page r hr).X (p, q))) :
    ∀ n : ℤ, P (K.underlying.homology n) := sorry

end AssociatedSpectralSequence

end Abelian

end FilteredComplex
end CategoryTheory
