import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap05.Definition_5_18_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/- Semantic recall / analogue check:
- `lean_leansearch` returned the canonical topological-space owner `JacobsonSpace`;
- `lean_run_code` verified that the scheme-level surface is exactly `JacobsonSpace S`;
- `Chap05/Definition_5_18_1` already records the ambient-space notion, so this item is a pure
  scheme-level recall rather than a new wrapper definition.
-/

/- Definition 28.6.1: a scheme `S` is Jacobson if its underlying topological space is Jacobson.
In this project that source-facing notion is exactly the canonical owner `JacobsonSpace S`, so
this item is recorded as a recall-only block. -/
recall JacobsonSpace

end AlgebraicGeometry
