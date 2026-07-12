import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial PrimeSpectrum

local notation "Iquad" => Ideal.span ({X ^ 2 - C (4 : ℤ)} : Set ℤ[X])
local notation "A" => ℤ[X] ⧸ Iquad
local notation "xbar" => ((Ideal.Quotient.mk Iquad) X : A)

/- 
Domain-style sampling pass for Example 10.27.1.

Primary domain: commutative algebra of prime ideals and points of `Spec` for the quotient
`A = ℤ[X] ⧸ (X^2 - 4)`.

Sampled owner declarations:
* `PrimeSpectrum`;
* `PrimeSpectrum.asIdeal`;
* `PrimeSpectrum.range_asIdeal`;
* `Ideal.span`.

Best owner abstraction: the source-facing statement is a classification of points of `Spec(A)`, so
the canonical owner is `PrimeSpectrum A`. The ideal-valued formulation is only the bridge obtained
by unpacking `PrimeSpectrum.asIdeal`; there is no separate upstream owner for the listed ideal
shapes.

Primitive-vs-derived split:
* primitive data: the quotient ring `A` and the explicit ideals `(2, x)`, `(x - 2)`, `(x + 2)`,
  `(q, x - 2)`, `(q, x + 2)`;
* derived API: the point-level classification on `PrimeSpectrum A`, and the ideal-level
  reformulation via `PrimeSpectrum.asIdeal`.
-/

/- Layering for this item:
* source-facing: classify the points of `Spec(ℤ[X] ⧸ (X^2 - 4))`.
* core/canonical owner: `PrimeSpectrum A`.
* bridge/view: the ideal-level reformulation obtained by unpacking `PrimeSpectrum.asIdeal`.
-/

/-- Example 10.27.1: the points of `Spec(ℤ[X] ⧸ (X^2 - 4))` are exactly `(2, x)`, `(x - 2)`,
`(x + 2)`, or, for some prime `q > 2`, one of `(q, x - 2)` and `(q, x + 2)`. -/
-- Proof sketch: analyze a prime `p` by its contraction to `ℤ`; the contraction is `(0)`, `(2)`,
-- or `(q)` for a prime `q > 2`. Then pass to the corresponding quotient of `ℤ[X]`, factor the
-- image of `X^2 - 4`, and classify the primes lying over each contracted ideal.
theorem prime_spectrum_Zx_mod_xsq_sub_four_cases (p : PrimeSpectrum A) :
    p.asIdeal = Ideal.span ({(2 : A), xbar} : Set A) ∨
      p.asIdeal = Ideal.span ({xbar - 2} : Set A) ∨
        p.asIdeal = Ideal.span ({xbar + 2} : Set A) ∨
          ∃ q : ℕ,
            q.Prime ∧ 2 < q ∧
              (p.asIdeal = Ideal.span ({(q : A), xbar - 2} : Set A) ∨
                p.asIdeal = Ideal.span ({(q : A), xbar + 2} : Set A)) := sorry

/-- Ideal-level reformulation of Example 10.27.1 obtained by unpacking `PrimeSpectrum`. -/
theorem prime_ideal_Zx_mod_xsq_sub_four_cases (I : Ideal A) :
    I.IsPrime ↔
      I = Ideal.span ({(2 : A), xbar} : Set A) ∨
        I = Ideal.span ({xbar - 2} : Set A) ∨
          I = Ideal.span ({xbar + 2} : Set A) ∨
            ∃ q : ℕ,
              q.Prime ∧ 2 < q ∧
                (I = Ideal.span ({(q : A), xbar - 2} : Set A) ∨
                  I = Ideal.span ({(q : A), xbar + 2} : Set A)) := by
  constructor
  · intro hI
    simpa using prime_spectrum_Zx_mod_xsq_sub_four_cases ⟨I, hI⟩
  · intro hI
    sorry
