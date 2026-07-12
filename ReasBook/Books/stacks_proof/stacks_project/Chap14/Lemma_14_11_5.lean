import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.MonoidalCategory

universe u

section

variable (U V : SSet.{u}) (a b : ℕ) [U.HasDimensionLE a] [V.HasDimensionLE b]

/- Domain-style sampling for Lemma 14.11.5:
- primary domain: simplicial sets, their dimension bounds, and behavior under the cartesian
  product `⊗`;
- sampled owner declarations:
  `SSet.HasDimensionLT`,
  `SSet.HasDimensionLE`,
  `SSet.hasDimensionLE_prod`,
  the canonical instance giving `(U ⊗ V).HasDimensionLE (a + b)`;
- best owner abstraction: the mathlib owner theorem `SSet.hasDimensionLE_prod`, whose
  specialization at `n := a + b` is the exact textbook statement;
- primitive data: simplicial sets `U`, `V` together with the bounds `U.HasDimensionLE a` and
  `V.HasDimensionLE b`;
- derived API: the target statement is exactly the specialization `(U ⊗ V).HasDimensionLE (a + b)`,
  so the deleted local theorem was only a duplicate shell around the owner theorem rather than new
  source-facing data.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma says that the product of simplicial sets of dimensions at most
  `a` and `b` has dimension at most `a + b`;
- `core/canonical`: `SSet.hasDimensionLE_prod`;
- `bridge/view`: none; the main entry below is already the exact source-facing specialization of
  the canonical owner theorem.

The correct refinement is therefore to expose the exact specialized instance rather than keep a
parallel local theorem or only recall the broader owner theorem. -/

/- Lemma 14.11.5: if simplicial sets `U` and `V` have dimension at most `a` and `b`, then their
cartesian product has dimension at most `a + b`. In mathlib this is exactly the specialization of
`SSet.hasDimensionLE_prod` at `n := a + b`. -/
#check (SSet.hasDimensionLE_prod U V a b (a + b) : (U ⊗ V).HasDimensionLE (a + b))

end
