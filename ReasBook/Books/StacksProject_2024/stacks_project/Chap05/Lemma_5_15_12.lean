import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace Topology

namespace Topology

section

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X] {E : Set X} {F : Set E}

/- Domain-style sampling for constructible subsets inside constructible subspaces:
- primary domain: constructible subsets, subtype inclusions, and the owner `Topology.IsConstructible`
  API for passing between a subspace and the ambient space;
- sampled canonical declarations:
  `Topology.IsConstructible.image_of_isOpenEmbedding`,
  `Topology.IsConstructible.image_of_isClosedEmbedding`,
  `Topology.IsConstructible.preimage_subtypeVal_of_isConstructible`,
  `Topology.IsConstructible.isRetrocompact`;
- best owner abstraction: the public statement should be the constructible image of the canonical
  map `Subtype.val : E → X`, not a separate global coercion wrapper;
- primitive-vs-derived split: the primitive data are the constructible ambient subspace `E` and
  the constructible subset `F ⊆ E`. The ambient subset `(F : Set X)` is derived from the owner
  map as `Subtype.val '' F`.

Layer triage:
- `source-facing`: Lemma 5.15.12, asserting that a constructible subset of a constructible
  subspace is constructible in the ambient space;
- `core/canonical`: `Topology.IsConstructible` together with image theorems for maps such as
  `Subtype.val`;
- `bridge/view`: the coercion `Set E → Set X`, which should be secondary to the image statement.
-/

/-- Lemma 5.15.12: in a topological space whose quasi-compact opens form a basis, equivalently
`[PrespectralSpace X]`, the image in `X` of a constructible subset of a constructible subspace `E`
is constructible. The canonical public surface uses the subtype inclusion `Subtype.val : E → X`
rather than a separate coercion wrapper. -/
theorem IsConstructible.image_subtypeVal_of_isConstructible
    (hF : IsConstructible F) (hE : IsConstructible E) :
    IsConstructible (Subtype.val '' F) := sorry

end

end Topology
