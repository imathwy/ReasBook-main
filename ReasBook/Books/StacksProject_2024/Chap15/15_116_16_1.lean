import Mathlib
import StacksProject_2024.Chap15.Lemma_15_116_13

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

section

variable {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
local notation "K" => FractionRing B

/- Domain-style sampling:
* primary domain: valuation-theoretic congruences for the quotient polynomial from
  `Lemma_15_116_13`;
* sampled project/chapter declarations:
  `IsOneSubZetaQuotientPolynomial`,
  `IsOneSubZetaQuotientPolynomial.exists_coefficients`,
  `IsOneSubZetaQuotientPolynomial.add_formula`,
  `IsExtensionOfDiscreteValuationRings.fractionRingMap`;
* best owner abstraction: the source-facing predicate `IsOneSubZetaQuotientPolynomial` on the
  quotient polynomial attached to `ζ`, evaluated in the canonical fraction field `FractionRing B`
  of the discrete valuation ring `B`;
* primitive data: the owner hypothesis `hP`, the associated-power hypothesis for `1 - ζ`, and the
  integrality hypothesis `hPz : π^{-n} P(z) ∈ B` in the fraction field;
* derived API: the displayed congruence for `aeval z P`.

Layer triage:
* `source-facing`: the congruence statement for a quotient polynomial satisfying
  `IsOneSubZetaQuotientPolynomial`;
* `bridge/view`: the ambient passage from the discrete valuation ring `B` to its fraction field
  `K = FractionRing B`.
-/

-- Proof sketch: write `P` as `z ^ p - z` plus the intermediate terms from Lemma `15.116.13`.
-- Because each intermediate coefficient of the quotient polynomial from Lemma `15.116.13` lies in
-- `(1 - ζ)` and `1 - ζ` is associated to `π ^ e₁`, those coefficients are divisible by
-- `π ^ e₁`. In the fraction field of the discrete valuation ring `B`, the hypothesis
-- `π ^ (-n) * P(z) ∈ B` bounds the valuation of `z`, so every intermediate term lies in
-- `π ^ (-n + e₁) B`.
/-- 15.116.16.1: if `P` is the quotient polynomial from Lemma `15.116.13` attached to `ζ` over the
discrete valuation ring `B`, its distinguished coefficient `1 - ζ` is associated to `π ^ e₁`, and
`π ^ (-n) P(z)` lies in the fraction field `K = FractionRing B` with value in `B`, then
`P(z) - (z ^ p - z)` lies in `π ^ (-n + e₁) B`. This is the displayed congruence
`P(z) ≡ z^p - z mod π^{-n + e₁} B` from the discrete-valuation/fraction-field setting. -/
theorem oneSubZetaQuotientPolynomial_eval_congruent_sub_frobeniusLinear
    {p e₁ n : ℕ} {π ζ : B} {z : K} {P : B[X]}
    (hP : IsOneSubZetaQuotientPolynomial p ζ P)
    (hw : Associated (1 - ζ) (π ^ e₁))
    (hPz : ∃ b : B,
      (algebraMap B K π) ^ (-(n : ℤ)) * aeval z P = algebraMap B K b) :
    ∃ b : B,
      aeval z P - (z ^ p - z) =
        (algebraMap B K π) ^ (-(n : ℤ) + e₁) * algebraMap B K b := by
  sorry

end
