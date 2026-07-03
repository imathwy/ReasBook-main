import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open ContinuousMultilinearMap

universe u

/- Definition 1.1: in the scalar one-variable setting, “having a power series expansion at `x₀`”
is the canonical notion `AnalyticAt 𝕜 f x₀`. -/
recall AnalyticAt

/-- In the scalar one-variable setting, `AnalyticAt` is equivalent to admitting a locally
convergent scalar power series `∑ a n (x - x₀)^n`. -/
theorem analyticAt_iff_exists_hasFPowerSeriesAt_ofScalars
    {𝕜 : Type u} [NontriviallyNormedField 𝕜] {f : 𝕜 → 𝕜} {x₀ : 𝕜} :
    AnalyticAt 𝕜 f x₀ ↔ ∃ a : ℕ → 𝕜, HasFPowerSeriesAt f (ofScalars 𝕜 a) x₀ := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.coeff, ?_⟩
    convert hp using 1
    ext n
    rw [← mkPiRing_coeff_eq p n, ← mkPiRing_coeff_eq (ofScalars 𝕜 p.coeff) n,
      coeff_ofScalars]
  · rintro ⟨a, ha⟩
    exact ha.analyticAt

/-- Two scalar power series expansions of the same function at the same point have the same
coefficients. -/
theorem power_series_coefficients_unique
    {𝕜 : Type u} [NontriviallyNormedField 𝕜] {f : 𝕜 → 𝕜} {x₀ : 𝕜} {a b : ℕ → 𝕜}
    (ha : HasFPowerSeriesAt f (ofScalars 𝕜 a) x₀)
    (hb : HasFPowerSeriesAt f (ofScalars 𝕜 b) x₀) :
    a = b :=
  ofScalars_series_injective 𝕜 𝕜 <| ha.eq_formalMultilinearSeries hb
