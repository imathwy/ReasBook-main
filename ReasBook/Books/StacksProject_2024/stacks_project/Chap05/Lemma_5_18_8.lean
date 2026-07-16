import Mathlib
import StacksProject_2024.stacks_project.Chap05.Definition_5_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace Topology
open scoped Set.Notation TopologicalSpace

universe u

section

variable {X : Type u} [TopologicalSpace X] [JacobsonSpace X]

local macro "X₀" : term => `(closedPoints X)

/-
Domain-style sampling for constructible traces on the closed-point subspace of a Jacobson space:
- primary domain: constructible subsets, retrocompact opens, and closed-point traces in Jacobson
  spaces;
- sampled owner-level declarations:
  `closedPoints`,
  `JacobsonSpace`,
  `Topology.IsConstructible.isFiniteUnionOfLocallyClosed`,
  `finiteUnionOfLocallyClosed_preimage_closedPoints_bijOn`;
- best owner abstractions: the ambient Jacobson owner `JacobsonSpace X` and the constructible-set
  owner predicate `Topology.IsConstructible`; the closed-point trace itself is the canonical bridge
  `X₀ ↓∩ E`.

Layer triage:
- `source-facing`: the constructible closed-point trace correspondence of Lemma 5.18.8;
- `core/canonical`: `JacobsonSpace X` and `IsConstructible`;
- `bridge/view`: the subtype trace `X₀ ↓∩ E` together with the finite-union bridge from
  `Lemma_5_18_7`.

Primitive data is only the ambient Jacobson structure and the owner predicate `IsConstructible`.
The finite-union-of-locally-closed decomposition and the closed-point trace bijection on those
finite unions are derived API, so this file should phrase its public statements through the
canonical trace notation `X₀ ↓∩ E` and reuse the upstream owner-facing bridge rather than spelling
out a parallel subtype-preimage surface.
-/

-- Proof sketch: combine `finiteUnionOfLocallyClosed_preimage_closedPoints_bijOn` with
-- `Topology.IsConstructible.isFiniteUnionOfLocallyClosed` and the canonical generator description
-- of constructible subsets by open retrocompact subsets. The trace surface should be stated using
-- the canonical subtype-trace notation `X₀ ↓∩ E`.
/-- Lemma 5.18.8: for a Jacobson space `X`, tracing a subset to the closed-point subspace `X₀`
induces a bijective, inclusion-preserving correspondence between constructible subsets of `X` and
constructible subsets of `X₀`. -/
theorem isConstructible_preimage_closedPoints_bijOn :
    Set.BijOn
      (fun E : Set X ↦ X₀ ↓∩ E)
      {E : Set X | IsConstructible E}
      {F : Set X₀ | IsConstructible F} := sorry

-- Proof sketch: monotonicity of subtype trace gives the forward implication. For the converse, apply
-- injectivity from the constructible bijection theorem to `E \ E'`, using that constructible
-- subsets are closed under Boolean operations.
/-- The constructible closed-point trace correspondence reflects and preserves inclusion. -/
theorem isConstructible_preimage_closedPoints_subset_iff
    {E E' : Set X} (hE : IsConstructible E) (hE' : IsConstructible E') :
    X₀ ↓∩ E ⊆ X₀ ↓∩ E' ↔ E ⊆ E' := sorry

-- Proof sketch: the forward implication is the `MapsTo` direction of the constructible
-- closed-point trace bijection above. For the converse, use its surjectivity.
/-- A subset of a Jacobson space is constructible if and only if its trace on the closed-point
subspace is constructible. -/
theorem isConstructible_iff_preimage_closedPoints_subtypeVal {E : Set X} :
    IsConstructible E ↔ IsConstructible (X₀ ↓∩ E) := sorry

-- Proof sketch: for an open subset `U`, constructibility is equivalent to retrocompactness, so the
-- previous constructible closed-point trace equivalence upgrades directly to the open
-- retrocompactness statement.
/-- Tracing an open subset to the closed-point subspace preserves and reflects retrocompactness in
a Jacobson space. -/
theorem isRetrocompact_iff_preimage_closedPoints_subtypeVal_of_isOpen {U : Set X} (hU : IsOpen U) :
    IsRetrocompact U ↔ IsRetrocompact (X₀ ↓∩ U) := sorry

end
