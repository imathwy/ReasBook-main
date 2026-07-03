import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_17_3_1 (from Chap04) -/
/-!
Source/core/bridge triage:

- `source-facing`: Corollary 17.3.1 gives the same half-space intersection reformulation as the
  earlier chapter corollary, under the same hypotheses and with the same represented set
  `linearInequalitySolutionSet SStar`.
- `core/canonical`: the owner abstractions are the represented set
  `linearInequalitySolutionSet SStar`, the half-space constructor `closedHalfSpaceLE`, and the
  earlier owner theorem
  `dualCaratheodory_subset_closedHalfSpaceLE_iff_exists_n_halfspaces_intersection_subset`.
- `bridge/view`: this file is only a textbook-location marker of that earlier owner theorem; it
  adds no new mathematical data or wrapper declaration.

Domain-style sampling used here:
- `linearInequalitySolutionSet`;
- `closedHalfSpaceLE`;
- `dualCaratheodory_subset_closedHalfSpaceLE_iff_exists_n_halfspaces_intersection_subset`.

Primitive data vs derived API:
- primitive data already owned upstream: `SStar`, the target half-space, and the finite family of
  half-spaces coming from a finite subset of `SStar`;
- derived API here: none. The duplicate local theorem is removed in favor of direct reuse of the
  upstream owner corollary.

Layer target: `bridge/view`.

Abstraction checks for this item:
- Codomain/ambient concreteness: this item is set-valued and introduces no new ordered-extended
  codomain owner (no extra `EReal`/`WithBotTop` layer is introduced here).
- Scalar layer: the owner theorem already lives over the scalar-generic layer
  (`R`, `Field R`, `LinearOrder R`, finite-dimensional bound `Module.finrank R X`); this bridge
  keeps that owner layer and does not introduce a new concrete specialization.
- Ambient structure strength: the `TopologicalSpace`/`Bornology` assumptions occur only through
  the primitive hypotheses `IsClosed SStar` and `Bornology.IsBounded SStar` in the owner theorem;
  this file keeps that exact layer and does not repackage it as a stronger local interface.
- Owner choice: remain on the pairing-based owner layer inherited from the upstream owner
  corollary, rather than introducing a concrete inner-product-model owner.
- Ambient vs intrinsic topology: no new ambient `closure`/`interior` reformulation is introduced;
  this bridge only references the existing owner theorem.
- Owner naming surface: keep the textbook bridge as a direct marker of the canonical owner theorem,
  without introducing a second local theorem alias.
-/

/- Corollary 17.3.1 is a direct bridge recall of the canonical owner corollary
`dualCaratheodory_subset_closedHalfSpaceLE_iff_exists_n_halfspaces_intersection_subset`, with no
parallel chapter-local wrapper. -/
recall dualCaratheodory_subset_closedHalfSpaceLE_iff_exists_n_halfspaces_intersection_subset

/-! ### Theorem_17_3 (from Chap04) -/
/-!
Source/core/bridge triage:

- `source-facing`: Theorem 17.3 is a location marker for the finite dual-Caratheodory
  half-space-containment criterion on `linearInequalitySolutionSet`.
- `core/canonical`: the intended owner surface is still
  `subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_conicCombination`.
- `bridge/view`: this file intentionally carries no theorem-level `recall` while the upstream
  owner theorem remains backed by deferred proofs in `Theorem_17_2_11`.

Domain-style sampling used here:
- `linearInequalitySolutionSet`;
- `closedHalfSpaceLE`;
- `mem_generated_cone_iff_exists_conicCombination`.

Primitive data vs derived API:
- primitive data already owned upstream: the inequality family `SStar`, the containing half-space,
  and the finite conic-combination certificate data;
- derived API here: none.

Layer target: `bridge/view`. The numbered item is recorded as a direct canonical location marker
for the owner theorem rather than a second public owner or wrapper API.

Abstraction checks for this item:
- Codomain/ambient layer: this item is set-valued and introduces no extra ordered-extended
  codomain owner (`EReal`/`WithBotTop`), so no codomain over-concretization is introduced here.
- Scalar/ambient structure: this bridge does not add any new scalar specialization; it reuses the
  exact scalar/ambient layer of the upstream owner theorem.
- Owner model choice: the intended owner theorem stays on the canonical pairing owner layer inherited
  upstream (`HasPairing ...` in the current owner theorem), rather than introducing a concrete
  inner-product-space wrapper in this bridge file.
- Ambient vs intrinsic topology: this file introduces no new ambient `closure`/`interior` API and
  therefore does not suppress an intrinsic/relative reformulation.
- Owner naming: no parallel long local owner is introduced; the bridge reuses the canonical
  upstream owner target directly.
- Notation surface: no new notation is needed because this file contributes no new mathematical
  owner.

Validation note:
- Until `Theorem_17_2_11` is fully discharged, exposing a theorem-level `recall` here would make
  this source-facing marker depend on deferred proof work. This bridge file therefore stays
  documentation-only for now, with no parallel wrapper theorem and no theorem-level restatement.
-/
