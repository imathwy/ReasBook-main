import Mathlib.Topology.ContinuousMap.T0Sierpinski
import StacksProject_2024.Chap05.Lemma_5_23_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology

/- Domain-style sampling for spectral Sierpinski-product embeddings:
- primary domain: spectral spaces, constructible topology, and the canonical Sierpinski product
  map;
- sampled owner declarations:
  `SpectralSpace`,
  `TopologicalSpace.productOfMemOpens`,
  `IsSpectralMap.isClosed_range_constructibleTopology`,
  `spectralSpace_subtype_of_isClosed_constructibleTopology`;
- best owner abstraction: the primitive owner data for the reverse direction are an embedding
  `f : X → ι → Prop` together with constructible-topology closedness of its range, while the
  forward spectral witness should use the canonical owner `TopologicalSpace.productOfMemOpens X`
  rather than a parallel local copy;
- primitive-vs-derived split: the embedding and range-closedness are the source-facing primitive
  data, while the existential packaging of a witness is derived API.

Layer triage:
- `source-facing`: Lemma 5.23.13, the existential embedding characterization of spectral spaces;
- `core/canonical`: `SpectralSpace`, `constructibleTopology`, and
  `TopologicalSpace.productOfMemOpens`;
- `bridge/view`: the constructible-closed range bridge for spectral maps and the spectral-subspace
  bridge for constructibly closed subspaces.
-/

section

variable (X : Type u) [TopologicalSpace X]

-- Proof sketch: for the forward implication, use the canonical map
-- `TopologicalSpace.productOfMemOpens X : C(X, Opens X → Prop)` to the product of copies of the
-- Sierpinski space `Prop`, prove it is a spectral embedding for spectral `X`, and apply the
-- constructible-closed range lemma for spectral maps. For the reverse implication, show that a
-- product of copies of the Sierpinski space is spectral and then apply the lemma that a subspace
-- closed in the constructible topology of a spectral space is spectral.
/-- Lemma 5.23.13: a space is spectral if and only if it embeds into a product of copies of the
Sierpinski space `Prop` with range closed in the constructible topology on that product. -/
theorem spectralSpace_iff_exists_sierpinski_product_embedding_closed_in_constructible_topology :
    SpectralSpace X ↔
      ∃ (ι : Type u) (f : C(X, ι → Prop)),
        IsEmbedding f ∧
          IsClosed[constructibleTopology (ι → Prop)] (range f) := sorry

end
