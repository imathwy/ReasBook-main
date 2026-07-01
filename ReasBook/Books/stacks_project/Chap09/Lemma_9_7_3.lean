import Mathlib.FieldTheory.Tower
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
* primary domain: finite-dimensional field extensions in a scalar tower;
* sampled owner declarations:
  `Module.Finite.right`,
  `FiniteDimensional.right`,
  `FiniteDimensional.trans`;
* best owner abstraction: the field-extension owner theorem `FiniteDimensional.right`, which is the
  chapter-natural field-specialized surface over the more primitive module-theoretic owner
  `Module.Finite.right`;
* primitive data: a tower of fields `F ⟶ E ⟶ K` and finite dimensionality of `K` over `F`;
* derived API: finiteness of `K` over the intermediate field `E`.

Layer triage:
* `source-facing`: Lemma 9.7.3 is the textbook tower-law finiteness statement for field
  extensions;
* `core/canonical`: `Module.Finite.right`;
* `bridge/view`: the field-specialized alias `FiniteDimensional.right`.

So this file should stay as a direct recall of the field-level owner theorem rather than introduce a
local wrapper or restate the module-theoretic theorem under a second chapter-specific name. -/
/- Lemma 9.7.3: if `K/E/F` is a tower of algebraic field extensions and `K` is finite over `F`,
then `K` is finite over `E`. This is exactly the canonical scalar-tower finiteness theorem
`FiniteDimensional.right`; the algebraicity assumptions from the source text are ambient and are
not needed for the formal statement. -/
recall FiniteDimensional.right
