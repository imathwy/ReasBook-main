import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Module
open IntermediateField
open scoped IntermediateField

universe u v

namespace Algebra

variable (K : Type u) {L : Type v}
variable [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/- Domain-style sampling for Lemma 9.20.3:
- `source-facing`: norm and trace formulas for an element of a finite field extension in terms of
  the coefficients of its minimal polynomial.
- sampled owner declarations:
  `Algebra.norm`,
  `Algebra.norm_eq_norm_adjoin`,
  `PowerBasis.norm_gen_eq_coeff_zero_minpoly`,
  `trace_eq_finrank_mul_minpoly_nextCoeff`.
- best owner abstraction: `Algebra.norm` and `Algebra.trace` are the primitive owners; the
  textbook formulas are bridge statements obtained by reducing to the canonical simple-extension
  norm/trace owners and then reading the minimal-polynomial coefficients there.

Primitive data is the owner triple `(norm K α, trace K L α, minpoly K α)`. The displayed constant
and next coefficients are derived API, so this file should reuse the existing mathlib owner
theorems for norm transitivity, simple-extension norm, and trace rather than routing through a
parallel local characteristic-polynomial bridge.

Source/core/bridge triage:
- `source-facing`: the textbook coefficient formulas for `norm K α` and `trace K L α`;
- `core/canonical`: the owner operations `norm`, `trace`, `minpoly`, and the canonical simple
  extension `K⟮α⟯`;
- `bridge/view`: `norm_eq_norm_adjoin`, `PowerBasis.norm_gen_eq_coeff_zero_minpoly`,
  `trace_eq_finrank_mul_minpoly_nextCoeff`, and the tower-law degree identity
  `finrank_mul_finrank`.
-/

/-- Lemma 9.20.3 (1): for a finite field extension `L/K`, the norm of `α` is `(-1)^[L:K]`
times the constant coefficient of the minimal polynomial of `α` over `K`, raised to the power
`[L : K(α)]`. In the textbook notation `P = x^d + a₁ x^(d - 1) + ... + a_d`, this constant
coefficient is `a_d`. -/
-- Proof sketch: reduce `norm K α` to the norm of the generator of the simple extension `K(α)/K`
-- via `norm_eq_norm_adjoin`, evaluate that simple-extension norm with
-- `PowerBasis.norm_gen_eq_coeff_zero_minpoly`, and then rewrite the exponent by the tower law.
theorem norm_eq_sign_mul_minpoly_coeff_zero_pow_finrank_adjoin
    (α : L) : norm K α = (-1 : K) ^ finrank K L * (minpoly K α).coeff 0 ^ finrank K⟮α⟯ L := by
  have hα : IsIntegral K α := .of_finite K α
  rw [norm_eq_norm_adjoin K α]
  have hgen : norm K (AdjoinSimple.gen K α) =
      (-1 : K) ^ finrank K K⟮α⟯ * (minpoly K α).coeff 0 := by
    simpa [IntermediateField.adjoin.powerBasis_gen hα, minpoly_gen K α,
      IntermediateField.adjoin.finrank hα] using
      (PowerBasis.norm_gen_eq_coeff_zero_minpoly
        (IntermediateField.adjoin.powerBasis hα : PowerBasis K K⟮α⟯))
  rw [hgen, mul_pow, ← pow_mul]
  congr 1
  rw [finrank_mul_finrank K K⟮α⟯ L]

end Algebra

/- Lemma 9.20.3 (2): for a finite field extension `L/K`, the trace of `α` is minus
`[L : K(α)]` times the next coefficient of the minimal polynomial of `α` over `K`. In the
textbook notation `P = x^d + a₁ x^(d - 1) + ... + a_d`, this next coefficient is `a₁`. The
canonical Lean statement is the existing theorem `trace_eq_finrank_mul_minpoly_nextCoeff`.
-/
recall trace_eq_finrank_mul_minpoly_nextCoeff
