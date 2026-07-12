import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for PI-09:
- primary domain: finite-sum norm bounds in a normed additive group, specialized to complex-valued
  exponential and polynomial-evaluation terms;
- sampled owner declarations:
  `norm_sum_le`,
  `Finset.sum_le_sum`,
  `mul_sum`,
  `Finset.sum_sub_distrib`;
- best owner abstraction: the canonical finite-sum norm bound `norm_sum_le` on `Finset.univ`;
- primitive data: the pointwise approximation bound for each `β j`;
- derived API: the summed approximation bound after rewriting the target as a single sum of termwise
  differences.

Source/core/bridge triage:
- `source-facing`: the PI-09 summed approximation inequality below;
- `core/canonical`: `norm_sum_le`;
- `bridge/view`: the elementary finite-sum rewrites expressing the source formula as a single sum;
- `layer`: `source-facing`.
-/

-- Semantic recall note: `lean_leansearch` was unavailable in this environment; the statement
-- below was checked against the local `Polynomial.aeval`/finite-sum API and follows the source.

/-- Lemma PI-09: if each term of the finite family satisfies the analytic approximation bound
`‖(n : ℂ) * Complex.exp (β j) - (p : ℂ) * Polynomial.aeval (β j) g‖ ≤ ε`, then the summed
expression satisfies the bound `m * ε`. -/
theorem norm_sum_exp_sub_sum_aeval_le (m : ℕ) (β : Fin m → ℂ) (n p : ℤ) (g : Polynomial ℤ)
    {ε : ℝ}
    (hβ : ∀ j, ‖(n : ℂ) * Complex.exp (β j) - (p : ℂ) * Polynomial.aeval (β j) g‖ ≤ ε) :
    ‖(n : ℂ) * ∑ j, Complex.exp (β j) - (p : ℂ) * ∑ j, Polynomial.aeval (β j) g‖ ≤ m * ε := by
  calc
    ‖(n : ℂ) * ∑ j, Complex.exp (β j) - (p : ℂ) * ∑ j, Polynomial.aeval (β j) g‖
        = ‖∑ j, ((n : ℂ) * Complex.exp (β j) - (p : ℂ) * Polynomial.aeval (β j) g)‖ := by
            simp [Finset.mul_sum, Finset.sum_sub_distrib]
    _ ≤ ∑ j, ‖(n : ℂ) * Complex.exp (β j) - (p : ℂ) * Polynomial.aeval (β j) g‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, ε := Finset.sum_le_sum fun j _ ↦ hβ j
    _ = m * ε := by
      simp [Finset.sum_const, nsmul_eq_mul]
