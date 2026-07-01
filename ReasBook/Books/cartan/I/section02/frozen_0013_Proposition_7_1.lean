import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries Filter
open scoped NNReal ENNReal

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

namespace FormalMultilinearSeries

/-- Bridge from the canonical derivative series of a scalar power series to the source-facing
derived scalar coefficient sequence, obtained by applying each coefficient to `1`. -/
theorem apply_one_comp_derivSeries_ofScalars (a : ℕ → 𝕜) :
    (ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries
        ((ofScalars 𝕜 a).derivSeries) =
      ofScalars 𝕜 (fun n ↦ (n.succ : 𝕜) * a n.succ) := by
  ext n
  simp [coeff_ofScalars, derivSeries_coeff_one, smul_eq_mul]

variable [CompleteSpace 𝕜]

/-- Evaluating the canonical derivative series of a scalar power series at `1` recovers the sum of
the source-facing derived scalar series. -/
theorem derivSeries_sum_apply_one_ofScalars (a : ℕ → 𝕜) {z : 𝕜}
    (hz : (‖z‖₊ : ℝ≥0∞) < (ofScalars 𝕜 a).derivSeries.radius) :
    (ofScalars 𝕜 a).derivSeries.sum z 1 =
      ofScalarsSum (fun n ↦ (n.succ : 𝕜) * a n.succ) z := by
  have hsummable : Summable (fun n : ℕ ↦ (ofScalars 𝕜 a).derivSeries n fun _ ↦ z) := by
    apply FormalMultilinearSeries.summable
    simpa [Metric.mem_eball, edist_zero_right] using hz
  have hmap := hsummable.hasSum.mapL (ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜))
  have hsum :
      (((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries
          ((ofScalars 𝕜 a).derivSeries)).sum z) =
        (ofScalars 𝕜 a).derivSeries.sum z 1 := by
    simpa [FormalMultilinearSeries.sum, ContinuousLinearMap.compFormalMultilinearSeries_apply] using
      hmap.tsum_eq
  calc
    (ofScalars 𝕜 a).derivSeries.sum z 1 =
        (((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries
            ((ofScalars 𝕜 a).derivSeries)).sum z) := hsum.symm
    _ = ofScalarsSum (fun n ↦ (n.succ : 𝕜) * a n.succ) z := by
      simpa [ofScalarsSum] using
        congrArg (fun p : FormalMultilinearSeries 𝕜 𝕜 𝕜 ↦ p.sum z)
          (apply_one_comp_derivSeries_ofScalars a)

end FormalMultilinearSeries

/-- Helper for Proposition 7.1: applying `1` to the derivative formal power series gives the
source-facing derived scalar coefficients, so the derived scalar series has at least the derivative
radius. -/
theorem derivSeries_radius_le_scalar_derived_radius [CharZero 𝕜] (a : ℕ → 𝕜) :
    ((ofScalars 𝕜 a).derivSeries).radius ≤
      (ofScalars 𝕜 (fun n ↦ (n.succ : 𝕜) * a n.succ)).radius := by
  -- Compose with evaluation at `1` and then identify the coefficients termwise.
  calc
    ((ofScalars 𝕜 a).derivSeries).radius ≤
        ((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries
          ((ofScalars 𝕜 a).derivSeries)).radius :=
      radius_le_radius_continuousLinearMap_comp _ _
    _ = (ofScalars 𝕜 (fun n ↦ (n.succ : 𝕜) * a n.succ)).radius := by
      simpa using
        congrArg FormalMultilinearSeries.radius
          (FormalMultilinearSeries.apply_one_comp_derivSeries_ofScalars (𝕜 := 𝕜) a)

/-- Proposition 7.1 (1): over characteristic zero, a scalar power series and its derived scalar
power series have the same radius of convergence. -/
theorem ofScalars_radius_eq_radius_of_derived_series [CharZero 𝕜] (a : ℕ → 𝕜) :
    (ofScalars 𝕜 a).radius =
      (ofScalars 𝕜 (fun n ↦ (n.succ : 𝕜) * a n.succ)).radius := by
  apply le_antisymm
  · -- The easy direction is the formal derivative inequality from the analytic API.
    calc
      (ofScalars 𝕜 a).radius ≤ ((ofScalars 𝕜 a).derivSeries).radius :=
        (ofScalars 𝕜 a).radius_le_radius_derivSeries
      _ ≤ (ofScalars 𝕜 (fun n ↦ (n.succ : 𝕜) * a n.succ)).radius :=
        derivSeries_radius_le_scalar_derived_radius (𝕜 := 𝕜) a
  · -- Route correction: the generic reverse inequality must use the root-growth behavior of
    -- `‖(n + 1 : 𝕜)‖`, because the Archimedean estimate `‖(n + 1 : 𝕜)‖ ≥ 1` fails in
    -- nonarchimedean fields.
    -- TODO: prove the reverse inequality by combining a shift/tail radius comparison with
    -- `ofScalars_radius_inv_eq_limsup` and the subexponential fact
    -- `‖(n + 1 : 𝕜)‖ ^ (1 / n) → 1` (equivalently for reciprocal coefficients).
    sorry

variable [CompleteSpace 𝕜]

/-- Proposition 7.1 (2): if `z` lies strictly inside the disk of convergence, then the derivative
of the summed scalar power series is given by the sum of the derived scalar power series, i.e. the
text's relation `(7.1)`. -/
-- Proof sketch: realize `∑ a_n z^n` as `ofScalarsSum a`, apply the analytic derivative theorem on
-- the open ball of convergence, and identify the coefficient of the derived series termwise as
-- `(n + 1) * a (n + 1)`.
theorem hasDerivAt_ofScalarsSum_of_mem_radius (a : ℕ → 𝕜) {z : 𝕜}
    (hz : (‖z‖₊ : ℝ≥0∞) < (ofScalars 𝕜 a).radius) :
    HasDerivAt (ofScalarsSum a) (ofScalarsSum (fun n ↦ (n.succ : 𝕜) * a n.succ) z) z := by
  let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := ofScalars 𝕜 a
  have hzp : (‖z‖₊ : ℝ≥0∞) < p.radius := by
    simpa [p] using hz
  have hzp_mem : z ∈ Metric.eball (0 : 𝕜) p.radius := by
    simpa [Metric.mem_eball, edist_zero_right] using hzp
  have hp0 : 0 < p.radius := lt_of_le_of_lt (by simp) hzp
  have hp : HasFPowerSeriesOnBall (ofScalarsSum a) p 0 p.radius := p.hasFPowerSeriesOnBall hp0
  have hf : HasFDerivAt (ofScalarsSum a)
      (continuousMultilinearCurryFin1 𝕜 𝕜 𝕜 (p.changeOrigin z 1)) z := by
    simpa [p] using hp.hasFDerivAt hzp
  have hs :
      fderiv 𝕜 (ofScalarsSum a) z = p.derivSeries.sum z := by
    simpa [p] using hp.fderiv.sum hzp_mem
  have hs' :
      continuousMultilinearCurryFin1 𝕜 𝕜 𝕜 (p.changeOrigin z 1) 1 =
        ofScalarsSum (fun n ↦ (n.succ : 𝕜) * a n.succ) z := by
    calc
      continuousMultilinearCurryFin1 𝕜 𝕜 𝕜 (p.changeOrigin z 1) 1 = p.derivSeries.sum z 1 := by
        rw [← hs]
        exact (congrArg (fun f ↦ f 1) hf.fderiv).symm
      _ = ofScalarsSum (fun n ↦ (n.succ : 𝕜) * a n.succ) z := by
        apply derivSeries_sum_apply_one_ofScalars
        simpa [p] using hz.trans_le p.radius_le_radius_derivSeries
  simpa using hf.hasDerivAt.congr_deriv hs'
