import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 9.14.1:
- primary domain: purely inseparable algebraic elements and purely inseparable field extensions;
- sampled owner declarations:
  `IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem`,
  `IsPurelyInseparable`,
  `isPurelyInseparable_iff_pow_mem`,
  `isPurelyInseparable_self`;
- best owner abstraction: the extension-level owner is the canonical mathlib typeclass
  `IsPurelyInseparable F K`, while the simple-extension theorem
  `IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem` gives the source's
  one-element criterion without introducing a second owner;
- primitive data: none locally, since both the extension predicate and its simple-extension /
  pointwise characterizations are already owned upstream in mathlib;
- derived API: the source-style power-membership criteria for simple and general extensions, plus
  the trivial-extension instance.

Source/core/bridge triage:
- `source-facing`: the textbook notions "an element is purely inseparable over `F`" and "the
  extension `K/F` is purely inseparable";
- `core/canonical`: `IsPurelyInseparable`;
- `bridge/view`: the power-membership characterization theorems for simple extensions and general
  extensions, together with the trivial-extension instance.

This file should therefore remain a pure recall surface. Any local wrapper or restated owner
declaration would only duplicate the existing mathlib API without adding new mathematics. -/

/- Definition 9.14.1 (1): for `α ∈ K`, the textbook notion that `α` is purely inseparable over
`F` is canonically expressed by the simple extension `F⟮α⟯ / F` being purely inseparable. In
exponential characteristic `q`, the source criterion that `α ^ (q ^ n) ∈ F` for some `n` is
exactly `IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem`. -/
recall IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem

/- Definition 9.14.1 (2): in characteristic `p > 0`, the textbook notion that the extension `K/F`
is purely inseparable is the canonical mathlib typeclass `IsPurelyInseparable F K`. -/
recall IsPurelyInseparable

/- Companion recall for Definition 9.14.1 (2): in exponential characteristic `q`, the textbook
pointwise condition that every element of `K` has some `q^n`-th power in `F` is exactly the
canonical characterization `isPurelyInseparable_iff_pow_mem`. -/
recall isPurelyInseparable_iff_pow_mem

/- Companion recall for the convention following Definition 9.14.1: in arbitrary characteristic,
the trivial extension `F / F` is canonically purely inseparable, via `isPurelyInseparable_self`. -/
recall isPurelyInseparable_self
