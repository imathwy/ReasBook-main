import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
