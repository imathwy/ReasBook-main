import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped ArithmeticFunction.Moebius

/-- Lemma 1.3.18: Möbius inversion recovers a number-theoretic function `f` from its divisor-sum
transform `F`. -/
-- Proof sketch: apply `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` to the divisor-sum
-- hypothesis, then rewrite the resulting antidiagonal sum as `∑ d ∈ n.divisors, (μ d : R) *
-- F (n / d)` using the standard divisor reindexing lemmas for `Nat.divisorsAntidiagonal`.
theorem mobius_inversion_formula {R : Type u} [NonAssocRing R] {f F : ℕ → R}
    (hF : ∀ n > 0, F n = ∑ d ∈ n.divisors, f d) :
    ∀ n > 0, f n = ∑ d ∈ n.divisors, (μ d : R) * F (n / d) := by
  intro n hn
  have h :=
    ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
      (fun n hn ↦ (hF n hn).symm) n hn
  calc
    f n = ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : R) * F x.2 := h.symm
    _ = ∑ d ∈ n.divisors, (μ d : R) * F (n / d) :=
      Nat.sum_divisorsAntidiagonal fun d m ↦ (μ d : R) * F m
