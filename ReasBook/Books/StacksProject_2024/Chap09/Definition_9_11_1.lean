import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 9.11.1:
- primary domain: coprimeness of polynomials and its ideal-theoretic reformulation;
- sampled owner declarations:
  `IsCoprime`,
  `Ideal.sup_eq_top_iff_isCoprime`,
  `Ideal.span_insert`,
  `Ideal.mem_span_insert`;
- best owner abstraction: the core owner is `IsCoprime`; the unit-ideal formulation is derived
  bridge API obtained from `Ideal.sup_eq_top_iff_isCoprime` and then rewritten into pair-span form
  with `Ideal.span_insert`;
- primitive data: only the pair of polynomials `p` and `q`;
- derived API: the source-style unit-ideal formulation in `k[X]`, obtained by rewriting the
  singleton-ideal supremum bridge into the pair-span expression.

Source/core/bridge triage:
- `source-facing`: the textbook notion that two polynomials in `k[X]` are relatively prime;
- `core/canonical`: `IsCoprime`;
- `bridge/view`: the theorem that `Ideal.span ({p, q} : Set k[X]) = ⊤`.

This file should therefore keep `IsCoprime` as the main owner and expose the unit-ideal
formulation only through canonical upstream bridge API, not through a new local theorem. The
Stacks Project states the result over fields, but the same equivalence already holds over any
commutative semiring. -/
/- Definition 9.11.1: For polynomials over a field, being relatively prime is the canonical
notion `IsCoprime`; equivalently, the two polynomials generate the unit ideal. -/
recall IsCoprime

/- Companion recall: `Ideal.sup_eq_top_iff_isCoprime` is the direct ideal-theoretic bridge from
element-level coprimeness to the unit-ideal condition on the singleton-generated ideals. The
source pair-span formulation is then just `Ideal.span_insert`. -/
recall Ideal.sup_eq_top_iff_isCoprime

/- Companion recall: `Ideal.span_insert` is the canonical rewrite turning the singleton-span
supremum into the source-style pair-span expression `Ideal.span ({p, q} : Set k[X])`. -/
recall Ideal.span_insert
