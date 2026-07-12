import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the exact canonical theorem
  `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`;
- `Chap28/Definition_28_6_1` fixes the scheme-level Jacobson owner as `JacobsonSpace`;
- this item is therefore a pure recall of the existing mathlib theorem rather than a new wrapper.
-/

/- Lemma 29.16.9 (Stacks tag `02J5`): let `S` be a Jacobson scheme. Any scheme locally of finite
type over `S` is Jacobson. This is exactly the canonical theorem
`AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`. -/
recall AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
