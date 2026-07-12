import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- 
Source/core/bridge triage:
- `source-facing`: Theorem 21.6 is Helly's theorem for a finite collection of convex subsets of a
  finite-dimensional vector space with threshold `Module.finrank 𝕜 E + 1`.
- `core/canonical`: the owner declaration recalled here is the intrinsic finite-set surface
  `Convex.helly_theorem_set'` (subfamily cardinality form `≤`), which avoids index-family
  scaffolding on the theorem surface.
- `bridge/view`: this owner is obtained from the primitive indexed-family theorem
  `Convex.helly_theorem'`; the classical exact-cardinality surfaces
  (`Convex.helly_theorem`, `Convex.helly_theorem_set`) and concrete coordinate-model
  presentations are downstream specializations.

Domain-style sampling used here:
- `Convex.helly_theorem_set'`;
- `Convex.helly_theorem'`;
- `Convex.helly_theorem_set`.

Primitive data vs derived API:
- primitive upstream data: a finite index set `s : Finset ι`, a family `F : ι → Set E`,
  pointwise convexity on `s`, and nonempty intersections for all subfamilies of cardinality at
  most `Module.finrank 𝕜 E + 1` (`Convex.helly_theorem'`);
- source-facing owner here: the equivalent intrinsic finite-set statement
  (`Convex.helly_theorem_set'`) on `Finset (Set E)`;
- derived API: exact-cardinality-plus-lower-bound classical surfaces are downstream bridges.

Layer target: `core/canonical`. This item is a direct recall of the intrinsic finite-set owner
surface rather than a second public alias.

Abstraction checks for this item:
- Codomain/ambient layer: no ordered-extended-codomain owner is introduced; the statement is
  set-level Helly on `Set E`, so there is no codomain over-specialization to repair here.
- Scalar/ambient structure: the recalled owner already lives over the weaker canonical layer
  `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]` with
  `[FiniteDimensional 𝕜 E]`, so this file does not freeze to a concrete scalar/model.
- Owner model choice: this theorem-surface recall uses the intrinsic finite-set owner
  `Convex.helly_theorem_set'` instead of the more implementation-facing indexed-family scaffold.
- Ambient vs intrinsic topology: no ambient `closure`/`interior` formulation is introduced, so no
  intrinsic/relative-topology promotion is missing here.
- Owner naming surface: no long local owner name is introduced; the canonical upstream owner name
  is used verbatim.
- Notation surface: no new notation is needed because no new owner is introduced; direct recall
  keeps the theorem surface minimal.
-/

/- Theorem 21.6 is recalled at the intrinsic finite-set owner layer as
`Convex.helly_theorem_set'`; indexed-family and exact-cardinality surfaces are downstream bridge
views. -/
recall Convex.helly_theorem_set'
