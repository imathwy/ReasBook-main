module

import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

-- Declarations for this item will be appended below by the statement pipeline.

open Equiv
open FormalMultilinearSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

-- Semantic recall note: the owner/API choice was checked against Mathlib's
-- `HasFPowerSeriesAt.eq_formalMultilinearSeries`,
-- `AnalyticAt.hasFPowerSeriesAt`,
-- `iteratedDeriv_eq_iteratedFDeriv`, and
-- `FormalMultilinearSeries.ofScalars_series_injective`.

/-- Proposition I.2-extra-8 (2): a scalar function has at most one convergent power-series
expansion at `0`; equivalently, two locally convergent scalar power series representing the same
function near `0` have the same coefficient sequence. -/
theorem coeffs_eq_of_hasFPowerSeriesAt_zero
    {f : 𝕜 → 𝕜} {a b : ℕ → 𝕜}
    (ha : HasFPowerSeriesAt f (ofScalars 𝕜 a) 0)
    (hb : HasFPowerSeriesAt f (ofScalars 𝕜 b) 0) :
    a = b :=
  ofScalars_series_injective 𝕜 𝕜 (ha.eq_formalMultilinearSeries hb)

section CoeffFormula

variable [CompleteSpace 𝕜] [CharZero 𝕜]

/-- Proposition I.2-extra-8 (1): if a scalar function is represented near `0` by the convergent
power series `∑ n, a n * z ^ n`, then its coefficient `a n` is obtained from the `n`-th derivative
at `0` by the formula `a n = (n!)⁻¹ * S^(n)(0)`. -/
theorem coeff_eq_inv_factorial_mul_iteratedDeriv_zero
    {f : 𝕜 → 𝕜} {a : ℕ → 𝕜}
    (ha : HasFPowerSeriesAt f (ofScalars 𝕜 a) 0)
    (n : ℕ) :
    a n = (n.factorial : 𝕜)⁻¹ * iteratedDeriv n f 0 := by
  have hcanonical :
      HasFPowerSeriesAt
        f
        (ofScalars 𝕜 (fun m ↦ iteratedDeriv m f 0 / m.factorial))
        0 :=
    ha.analyticAt.hasFPowerSeriesAt
  have hcoeff :
      a n = iteratedDeriv n f 0 / n.factorial := by
    simpa [FormalMultilinearSeries.coeff_ofScalars] using
      congrArg
        (fun p : FormalMultilinearSeries 𝕜 𝕜 𝕜 ↦ p.coeff n)
        (ha.eq_formalMultilinearSeries hcanonical)
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcoeff

end CoeffFormula
