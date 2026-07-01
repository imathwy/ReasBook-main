import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Example 9.3.1:
- primary domain: basic field structure on the rational numbers;
- sampled owner API:
  `Rat.instField`,
  `Rat.instCharZero`,
  `RatFunc`,
  `AdjoinRoot.instField`;
- best owner abstraction: the canonical type `ℚ` equipped with the upstream owner instance
  `Rat.instField : Field ℚ`.

Primitive-vs-derived split:
- primitive data: the type `ℚ`;
- derived API: the field operations and axioms supplied by `Rat.instField`, with companions such
  as `Rat.instCharZero`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that the rational numbers form a field;
- `core/canonical`: `Rat.instField`;
- `bridge/view`: the notation `ℚ` presenting the source object.

There is no extra source-facing data to package locally, so this file should recall the owner
instance directly rather than use an anonymous `inferInstance` check.
-/

/- Example 9.3.1 (Rational numbers): the rational numbers form a field, represented in Lean by the
canonical type `ℚ`. The field structure is the upstream owner instance `Rat.instField`. -/
recall Rat.instField
