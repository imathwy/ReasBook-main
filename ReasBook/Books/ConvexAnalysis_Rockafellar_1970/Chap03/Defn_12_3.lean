import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Abstraction checks:
- codomain/ambient layer: no codomain structure is part of the notion; `Function.Even` only needs
  the domain negation structure `[Neg α]`.
- scalar/ambient structure: no scalar field, topology, or linear structure is needed.
- owner choice: the intrinsic owner is exactly `Function.Even`; introducing a local synonym would
  be a redundant abstraction layer.
- topology/intrinsic language: not applicable for this item.
- naming/notation: `Function.Even` is already the short canonical owner and no extra notation is
  mathematically primary here.

Source/core/bridge triage:
- `source-facing`: Defn 12.3 names symmetric (even) functions via `f (-x) = f x` for all `x`.
- `core/canonical`: this condition is definitionally the owner predicate `Function.Even`.
- `bridge/view`: no bridge theorem is needed; this item is a direct canonical recall.
- Primitive data vs derived API: the item introduces no data beyond that owner, so this file
  should expose only the canonical predicate, not a wrapper.
-/

/- Defn 12.3: a function is symmetric, or even, precisely when it satisfies
`f (-x) = f x` for every `x`; this is the canonical mathlib predicate `Function.Even`. -/
recall Function.Even
