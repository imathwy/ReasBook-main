import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace Complex

/-- The textbook logarithmic power series
`T(u) = ∑_{n ≥ 1} (-1)^(n - 1) u^n / n`, reindexed over `ℕ`. -/
noncomputable def logarithmicPowerSeries (u : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n * u ^ (n + 1) / (n + 1)

end Complex

-- Proof sketch: reindex `Complex.hasSum_taylorSeries_log hu` from the mathlib convention
-- to the textbook series `T(u) = ∑_{n≥1} (-1)^(n-1) u^n / n`, written in Lean as the
-- shifted `ℕ`-indexed series `∑_{n≥0} (-1)^n u^(n+1) / (n+1)`.
/-- The textbook logarithmic series
`T(u) = ∑_{n ≥ 1} (-1)^(n - 1) u^n / n`, reindexed over `ℕ`, has sum
`Complex.log (1 + u)` on the open unit disk. -/
theorem logarithmic_power_series_hasSum (u : ℂ) (hu : ‖u‖ < 1) :
    HasSum (fun n : ℕ ↦ (-1 : ℂ) ^ n * u ^ (n + 1) / (n + 1)) (Complex.log (1 + u)) := by
  let f : ℕ → ℂ := fun n ↦ (-1 : ℂ) ^ (n + 1) * u ^ n / n
  have hf : HasSum f (Complex.log (1 + u)) := by
    simpa [f] using Complex.hasSum_taylorSeries_log hu
  have hf' : HasSum f (Complex.log (1 + u) + ∑ i ∈ Finset.range 1, f i) := by
    simpa [f] using hf
  have hshift : HasSum (fun n : ℕ ↦ f (n + 1)) (Complex.log (1 + u)) :=
    (hasSum_nat_add_iff 1).2 hf'
  simpa [f, pow_succ', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift

-- Proof sketch: apply `HasSum.tsum_eq` to `logarithmic_power_series_hasSum u hu`.
/-- Proposition 6.1: for `‖u‖ < 1`, the sum of the power series
`T(u) = ∑_{n ≥ 1} (-1)^(n - 1) u^n / n` is the principal branch
`Complex.log (1 + u)`. -/
theorem logarithmic_power_series_tsum_eq (u : ℂ) (hu : ‖u‖ < 1) :
    Complex.logarithmicPowerSeries u = Complex.log (1 + u) := by
  simpa [Complex.logarithmicPowerSeries] using (logarithmic_power_series_hasSum u hu).tsum_eq
