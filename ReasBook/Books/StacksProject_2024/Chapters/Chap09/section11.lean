import Mathlib
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_11_1 (from Chap09) -/
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

/-! ### Lemma_9_11_2 (from Chap09) -/
open Polynomial

universe u

variable {k : Type u} [Field k]

/-
Domain-style sampling for Lemma 9.11.2:
- primary domain: polynomial coprimeness detected by vanishing in algebraically closed
  extensions;
- sampled owner/bridge declarations:
  `IsCoprime`,
  `Polynomial.aeval_ne_zero_of_isCoprime`,
  `Polynomial.isCoprime_iff_aeval_ne_zero`,
  `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`;
- best owner abstraction: the primitive owner is `IsCoprime p q`; for this source-facing file, the
  right canonical bridge is `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`; the textbook
  algebraic-closure wording is the specialization obtained by evaluating in `AlgebraicClosure k`,
  rather than additional primitive data in the public API;
- primitive data: only the polynomials `p` and `q`;
- derived API: the textbook “no common root in an algebraic closure” formulation, obtained by
  specializing the canonical `aeval`-nonvanishing bridge to `AlgebraicClosure k` and rewriting `∨`
  as negated simultaneous vanishing, phrased with the object-prefix `p.aeval a` surface.

Source/core/bridge triage:
- `source-facing`: `polynomial_isCoprime_iff_no_common_roots_in_alg_closure`;
- `core/canonical`: `IsCoprime`;
- `bridge/view`: `Polynomial.isCoprime_iff_aeval_ne_zero`, together with its algebraically closed
  specialization to `AlgebraicClosure k`.
-/
recall isCoprime_iff_aeval_ne_zero_of_isAlgClosed

/-- Lemma 9.11.2 in the textbook algebraic-closure form: specialize the canonical algebraically
closed coprimeness criterion to `AlgebraicClosure k` and rewrite the conclusion as
“no common root”. -/
theorem polynomial_isCoprime_iff_no_common_roots_in_alg_closure
    (p q : k[X]) :
    IsCoprime p q ↔ ∀ a : AlgebraicClosure k, ¬ (p.aeval a = 0 ∧ q.aeval a = 0) := by
  simpa only [ne_eq, not_and_or] using
    (isCoprime_iff_aeval_ne_zero_of_isAlgClosed k (AlgebraicClosure k) p q)
