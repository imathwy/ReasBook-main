import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap05.Definition_5_11_4

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

variable (S : Scheme.{u})

/- Semantic recall / analogue check:
- canonical owner: `CatenarySpace` from `Chap05/Definition_5_11_4`;
- local scheme precedent: `Chap29/Definition_29_17_1` uses the same owner for catenary schemes;
- this item is therefore a pure canonical recall, not a place for a parallel scheme-level alias.
-/

/- Definition 28.11.1: a scheme `S` is catenary if the underlying topological space of `S` is
catenary. In this project that source-facing notion is exactly the canonical owner
`CatenarySpace S`, so this item is recorded as a recall-only block. -/
recall CatenarySpace

end AlgebraicGeometry
