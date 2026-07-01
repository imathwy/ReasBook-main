import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Corollary_17_2_12

-- Declarations for this item will be appended below by the statement pipeline.

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
