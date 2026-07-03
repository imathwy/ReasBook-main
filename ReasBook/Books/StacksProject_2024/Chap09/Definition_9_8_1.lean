import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 9.8.1:
- primary domain: algebraic elements and algebraic field extensions;
- sampled owner declarations:
  `IsAlgebraic`,
  `Algebra.IsAlgebraic`,
  `Algebra.isAlgebraic_def`;
- sampled derived/specification API:
  `Transcendental`,
  `transcendental_iff`,
  `Algebra.isAlgebraic_iff`;
- best owner abstraction: the pointwise owner predicate `IsAlgebraic`, with the extension-level
  owner `Algebra.IsAlgebraic` derived by quantifying pointwise algebraicity over the top field;
- primitive data: none locally, since Definition 9.8.1 is already owned upstream by mathlib;
- derived API: the extension-level owner and its specification theorem
  `Algebra.isAlgebraic_def`.

Source/core/bridge triage:
- `source-facing`: the textbook notions "an element is algebraic over the base field" and "the
  extension is algebraic";
- `core/canonical`: `IsAlgebraic` and `Algebra.IsAlgebraic`;
- `bridge/view`: `Algebra.isAlgebraic_def`, which restates the extension-level owner as the
  textbook pointwise condition.

This file should therefore remain a pure recall surface: the source statement is already the
canonical owner declaration, so any local wrapper or rephrased duplicate would only create
parallel API without adding mathematics. -/

/- Definition 9.8.1 (Tag 09GC): for a field extension `F/E`, an element `α ∈ F` is algebraic
over `E` exactly when it is the root of a nonzero polynomial with coefficients in `E`; this is
the canonical mathlib predicate `IsAlgebraic`. -/
recall IsAlgebraic

/- Companion recall: an algebraic extension in the sense of Definition 9.8.1 is the canonical
mathlib typeclass `Algebra.IsAlgebraic`, whose fields are exactly the pointwise algebraicity
statements for elements of the top field. -/
recall Algebra.IsAlgebraic

/- Companion recall: the extension `F/E` is algebraic exactly when every element of `F` is
algebraic over `E`, as expressed by `Algebra.isAlgebraic_def`. -/
recall Algebra.isAlgebraic_def
