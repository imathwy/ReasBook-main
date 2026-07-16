import stacks_proof.stacks_project.Chap12.Lemma_12_24_2

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: filtered complexes in an abelian category and the associated cohomological
  spectral sequence construction;
- sampled owner declarations:
  `FilteredComplex`,
  `exists_filteredComplexAssociatedSpectralSequence`,
  `IsAssociatedToFilteredComplex`;
- best owner abstraction: the source object is a filtered complex, already canonically owned in
  the project by `FilteredComplex 𝒜`; Chapter `12` already supplies the owner-level existence
  theorem for associated spectral sequences, while the spectral-sequence side itself is owned by
  `CohomologicalSpectralSequence 𝒜 0`;
- primitive data: a filtered complex `K : FilteredComplex 𝒜`;
- derived API: an associated spectral sequence together with its comparison maps/pages, recorded
  through `IsAssociatedToFilteredComplex`.

Source/core/bridge triage:
- `source-facing`: this remark only points back to the general filtered-complex construction
  underlying Lemma `13.21.3`;
- `core/canonical`: `FilteredComplex 𝒜` and `exists_filteredComplexAssociatedSpectralSequence`;
- `bridge/view`: `IsAssociatedToFilteredComplex`.

This remark is therefore recall-only: the correct surface is to reuse the Chapter `12` owner
declarations directly, not to introduce a parallel local wrapper or a fake local functor owner. -/
/- Remark 13.21.4: the two spectral sequences attached in Lemma 13.21.3 should be regarded as
instances of the general construction sending a filtered complex of `𝒜` to an associated
cohomological spectral sequence, so the correct owner-level reference here is the Chapter `12`
existence theorem for associated spectral sequences. -/
#check exists_filteredComplexAssociatedSpectralSequence

end CategoryTheory
