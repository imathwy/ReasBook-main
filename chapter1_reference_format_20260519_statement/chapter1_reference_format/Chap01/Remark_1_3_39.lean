import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial
open Polynomial

-- Proof sketch: over `ZMod p`, Fermat's little theorem gives `x ^ p = x` for every `x`, so
-- evaluating `X ^ p - X` at any `x` yields `0`; nonzeroness follows because the leading term
-- `X ^ p` cannot cancel with `X` when `p` is prime.
/-- Remark 1.3.39: over the finite field `𝔽_p`, the polynomial `X^p - X` induces the zero
function on `𝔽_p` but is not itself the zero polynomial. This shows that, over finite fields, one
must distinguish polynomial functions from polynomials. -/
theorem fermat_polynomial_zero_function_but_nonzero (p : ℕ) [Fact p.Prime] :
    (∀ x : ZMod p, eval x ((X : Polynomial (ZMod p)) ^ p - X) = 0) ∧
      ((X : Polynomial (ZMod p)) ^ p - X) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · intro x
    simp [ZMod.pow_card]
  · simpa [ZMod.card p] using
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) (Fact.out : p.Prime).one_lt

/-- Over `𝔽_p`, evaluation does not identify polynomials with polynomial functions. -/
-- Proof sketch: the polynomial `X ^ p - X` from the preceding counterexample evaluates to the
-- zero function, while it is itself nonzero.
theorem polynomial_eval_not_injective_over_zmod (p : ℕ) [Fact p.Prime] :
    ¬ Function.Injective
      (fun P : Polynomial (ZMod p) ↦ fun x : ZMod p ↦ eval x P) := by
  intro h_injective
  rcases fermat_polynomial_zero_function_but_nonzero p with ⟨h_zero, h_nonzero⟩
  apply h_nonzero
  apply h_injective
  funext x
  simp [h_zero x]
