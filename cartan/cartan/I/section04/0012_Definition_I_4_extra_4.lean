import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u

/- Definition I.4-extra-4: the order of multiplicity of a nontrivial analytic zero is the
canonical vanishing-order function `analyticOrderAt`; the local factorization
`f x = (x - x₀)^k g x` with `g x₀ ≠ 0` and the derivative criterion are encoded by the standard
analytic-order API, and a simple zero is the case `k = 1`. -/
recall analyticOrderAt

namespace AnalyticAt

variable {𝕜 : Type u} [RCLike 𝕜] {f : 𝕜 → 𝕜} {x₀ : 𝕜}

-- Proof sketch: specialize `AnalyticAt.analyticOrderAt_eq_natCast` to scalar-valued functions and
-- rewrite scalar multiplication on `𝕜` as ordinary multiplication.
/-- An analytic scalar-valued function has analytic order `k` at `x₀` exactly when it factors
locally as `(x - x₀)^k` times an analytic function that does not vanish at `x₀`. -/
theorem analyticOrderAt_eq_nat_iff_exists_eventuallyEq_pow_mul_nonzero
    {k : ℕ} (hf : AnalyticAt 𝕜 f x₀) :
    analyticOrderAt f x₀ = k ↔
      ∃ g : 𝕜 → 𝕜, AnalyticAt 𝕜 g x₀ ∧ g x₀ ≠ 0 ∧
        f =ᶠ[𝓝 x₀] fun x ↦ (x - x₀) ^ k * g x := by
  simpa [smul_eq_mul] using hf.analyticOrderAt_eq_natCast

-- Proof sketch: combine `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero` with the
-- corresponding statement at `k + 1` to turn equality of the analytic order into vanishing of the
-- lower iterated derivatives and nonvanishing of the `k`-th derivative.
/-- The analytic order equals `k` exactly when the iterated derivatives of orders `< k` vanish at
`x₀` and the `k`-th iterated derivative does not. -/
theorem analyticOrderAt_eq_nat_iff_iteratedDeriv
    {k : ℕ} (hf : AnalyticAt 𝕜 f x₀) :
    analyticOrderAt f x₀ = k ↔
      (∀ n < k, iteratedDeriv n f x₀ = 0) ∧ iteratedDeriv k f x₀ ≠ 0 := by
  have hle {n : ℕ} :
      n ≤ analyticOrderAt f x₀ ↔ ∀ i < n, iteratedDeriv i f x₀ = 0 :=
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf
  constructor
  · intro horder
    have hvanish : ∀ n < k, iteratedDeriv n f x₀ = 0 :=
      hle.1 (by simp [horder])
    constructor
    · exact hvanish
    · intro hkzero
      have hk_succ : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f x₀ := by
        rw [hle]
        intro n hn
        rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
        · exact hvanish n hn
        · exact hkzero
      have hk_lt : (k : ℕ∞) < k + 1 := by exact_mod_cast Nat.lt_succ_self k
      exact (not_le_of_gt hk_lt) (by simpa [horder] using hk_succ)
  · rintro ⟨hvanish, hkzero⟩
    have hk_le : k ≤ analyticOrderAt f x₀ := hle.2 hvanish
    have hk_succ_not_le : ¬ ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f x₀ := by
      intro hk_succ
      exact hkzero <| hle.1 hk_succ k (Nat.lt_succ_self k)
    cases horder : analyticOrderAt f x₀ with
    | top =>
        exact (hk_succ_not_le (by simp [horder])).elim
    | coe r =>
        have hk_le' : k ≤ r := by simpa [horder] using hk_le
        have hk_succ_not_le' : ¬ k + 1 ≤ r := by
          intro h
          exact hk_succ_not_le <| by
            rw [horder]
            exact_mod_cast h
        have hr_le : r ≤ k := Nat.lt_succ_iff.mp (lt_of_not_ge hk_succ_not_le')
        have hr : r = k := le_antisymm hr_le hk_le'
        simp [hr]

-- Proof sketch: specialize `analyticOrderAt_eq_nat_iff_iteratedDeriv` to `k = 1` and rewrite
-- `iteratedDeriv 0 f x₀` and `iteratedDeriv 1 f x₀`.
/-- A simple zero is characterized by vanishing at the point and a nonvanishing first derivative. -/
theorem analyticOrderAt_eq_one_iff_zero_and_deriv_ne_zero
    (hf : AnalyticAt 𝕜 f x₀) :
    analyticOrderAt f x₀ = 1 ↔ f x₀ = 0 ∧ deriv f x₀ ≠ 0 := by
  constructor
  · intro horder
    have hone :
        analyticOrderAt f x₀ = 1 ↔
          (∀ n < 1, iteratedDeriv n f x₀ = 0) ∧ iteratedDeriv 1 f x₀ ≠ 0 :=
      hf.analyticOrderAt_eq_nat_iff_iteratedDeriv
    simpa [iteratedDeriv_zero, iteratedDeriv_one] using
      hone.1 horder
  · rintro ⟨hfx, hderiv⟩
    exact hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hfx hderiv

end AnalyticAt
