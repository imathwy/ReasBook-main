import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

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
