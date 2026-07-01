import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain triage:
* primary domain: module length and finite-length principal quotients in dimension-one local
  domains;
* sampled owner API: `Module.length`, `QuotSMulTop`,
  `isFiniteLength_quotient_span_singleton`, and `Ring.KrullDimLE.eq_bot_or_eq_top`;
* core/canonical owners: `QuotSMulTop x M` for the quotient module and
  `IsFiniteLength R (R ⧸ Ideal.span ({x} : Set R))` for the principal quotient;
* layer split: `QuotSMulTop x M` and the finite-length owner theorem for `R / xR` are primitive,
  while the Stacks inequality is the derived source-facing API.
-/

section

variable {R : Type u} {K : Type v}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Ring.KrullDimLE 1 R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

-- Proof sketch: if `x = 0`, then `QuotSMulTop x M = M`, while in a local domain of Krull
-- dimension at most `1` the zero-dimensional case is a field and the one-dimensional case makes
-- the right-hand side trivially `⊤`; so the inequality is immediate. If `x` is a unit then
-- `QuotSMulTop x M` vanishes. Otherwise `x` lies in the maximal ideal, and the canonical theorem
-- `isFiniteLength_quotient_span_singleton` gives finite length for `R / xR`. For a finite
-- submodule
-- `M ⊆ K^r`, clear denominators to compare `M` with `R^r`, use the filtration by powers of `x`,
-- and compute the asymptotic length growth inside `R^r`. For general `M`, choose a finite
-- submodule whose quotient modulo `x` has any prescribed finite-length subquotient and reduce to
-- the finite case.
/-
Canonical background: in the present dimension-one local-domain setting, the principal
quotient `R / xR` has finite length. This is exactly the owner theorem
`isFiniteLength_quotient_span_singleton`.
-/
recall isFiniteLength_quotient_span_singleton

/-- Lemma 10.119.9: if `R` is a local Noetherian domain of Krull dimension at most
`1`, `M` is an `R`-submodule of `K^{\oplus r}`, then
`length_R (QuotSMulTop x M) ≤ r * length_R(R / xR)`. -/
-- Proof sketch: reduce first to the finite case by approximating a finite-length subquotient of
-- `QuotSMulTop x M` with the image of a finite submodule of `M`, then compare with `R^r` after
-- clearing denominators and use additivity of module length together with finite length of `R/xR`.
theorem length_quotSMulTop_le_finrank_mul_length_quotient_span_singleton
    {r : ℕ} (M : Submodule R (Fin r → K)) {x : R} :
    Module.length R (QuotSMulTop x M) ≤
      r * Module.length R (R ⧸ Ideal.span {x}) := sorry

end
