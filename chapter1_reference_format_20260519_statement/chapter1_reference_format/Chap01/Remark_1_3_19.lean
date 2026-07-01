import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped ArithmeticFunction.Moebius

/-- Remark 1.3.19: a function `F` is the divisor-sum transform of `f` exactly when `f` is
recovered from `F` by the usual Möbius inversion formula over divisors. -/
theorem mobius_transform_iff_inverse_formula
    {R : Type u} [NonAssocRing R] {f F : ℕ → R} :
    (∀ n > 0, F n = ∑ d ∈ n.divisors, f d) ↔
      ∀ n > 0, f n = ∑ d ∈ n.divisors, (μ d : R) * F (n / d) := by
  constructor
  · intro hF n hn
    have h :=
      ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
        (fun m hm ↦ (hF m hm).symm) n hn
    calc
      f n = ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : R) * F x.2 := h.symm
      _ = ∑ d ∈ n.divisors, (μ d : R) * F (n / d) :=
        Nat.sum_divisorsAntidiagonal fun d m ↦ (μ d : R) * F m
  · intro hf
    have hμ :
        ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : R) * F x.2 = f n := by
      intro n hn
      calc
        ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : R) * F x.2 =
            ∑ d ∈ n.divisors, (μ d : R) * F (n / d) :=
          Nat.sum_divisorsAntidiagonal fun d m ↦ (μ d : R) * F m
        _ = f n := (hf n hn).symm
    intro n hn
    exact (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mpr hμ n hn).symm
