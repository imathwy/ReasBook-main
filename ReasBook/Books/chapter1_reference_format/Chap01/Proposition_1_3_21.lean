import Mathlib
import chapter1_reference_format.Chap01.Lemma_1_3_15
import chapter1_reference_format.Chap01.Proposition_1_3_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial

/-- Proposition 1.3.21: if `a` is coprime to a polynomial `f` over a finite field `K`, then the
class of `a` in `AdjoinRoot f = K[X] / (f)` raised to the polynomial totient is `1`. This is the
canonical quotient-owner form of the textbook congruence `a ^ Φ(f) ≡ 1 mod f`; on this owner
surface the source's nonzero hypothesis on `f` is redundant. -/
-- Proof sketch: `ha` and `polynomial_quotient_mk_isUnit_iff` show that `AdjoinRoot.mk f a` is a
-- unit, and Euler's theorem for the unit group gives the displayed equality.
theorem polynomial_isCoprime_pow_totient_eq_one_mod
    {K : Type*} [Field K] [Finite K] {f a : K[X]} (ha : IsCoprime a f) :
    (AdjoinRoot.mk f a) ^ Polynomial.totient f = 1 := by
  rcases (polynomial_quotient_mk_isUnit_iff a).2 ha with ⟨u, hu⟩
  have hu_pow : u ^ Polynomial.totient f = 1 := by
    rw [Polynomial.totient]
    exact pow_card_eq_one'
  rw [← hu]
  change (((u ^ Polynomial.totient f : (AdjoinRoot f)ˣ) : AdjoinRoot f) = 1)
  exact congrArg (fun x : (AdjoinRoot f)ˣ ↦ (x : AdjoinRoot f)) hu_pow
