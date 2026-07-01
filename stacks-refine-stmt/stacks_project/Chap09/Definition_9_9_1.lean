import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for minimal polynomials in field extensions:
- primary domain: the minimal polynomial of an element in a field extension;
- sampled owner declaration:
  `minpoly`;
- sampled derived/specification API:
  `minpoly.monic`,
  `minpoly.aeval`,
  `minpoly.irreducible`;
- best owner abstraction: the canonical owner `minpoly`, with monicity, the root property,
  and irreducibility all derived from that owner instead of stored as primitive local data;
- primitive data: only the polynomial `minpoly k α`;
- derived API: algebraicity/integrality consequences and degree-theoretic consequences such as
  `IntermediateField.adjoin.finrank`.

Source/core/bridge triage:
- `source-facing`: the textbook minimal polynomial of an algebraic element `α` over `k`;
- `core/canonical`: `minpoly`;
- `bridge/view`: downstream field-theoretic comparisons such as
  `IntermediateField.adjoin.finrank`.

This file should therefore remain a pure recall surface: Definition 9.9.1 does not introduce new
primitive data beyond the canonical owner already present in mathlib, so any local wrapper would
only duplicate the chapter API.
-/

/- Definition 9.9.1: for an algebraic element `α` of a field extension `K/k`, the polynomial
called the minimal polynomial of `α` over `k` is the canonical mathlib polynomial `minpoly k α`. -/
recall minpoly
