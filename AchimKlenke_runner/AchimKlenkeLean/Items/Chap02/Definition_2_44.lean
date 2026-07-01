import Mathlib

open scoped unitInterval
open unitInterval

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition 2.44: the critical value `p_c` is the infimum of the percolation parameters
`p ∈ [0,1]` for which the origin-percolation probability `θ(p)` is strictly positive. We encode
`p_c` directly as a point of the canonical mathlib type `unitInterval`, so the empty-set case is
handled by `sInf ∅ = 1` in `[0,1]`. -/
noncomputable def criticalPercolationValue (theta : unitInterval → NNReal) : unitInterval :=
  sInf {p : unitInterval | 0 < theta p}

/-- The critical value is the infimum, inside `[0,1]`, of the parameters with positive
origin-percolation probability. -/
theorem criticalPercolationValue_def (theta : unitInterval → NNReal) :
    criticalPercolationValue theta = sInf {p : unitInterval | 0 < theta p} := rfl

-- Proof sketch: coerce the defining `sInf` in `unitInterval` to `ℝ`; this identifies the
-- underlying real number of `p_c` with the infimum of the corresponding subset of `ℝ`.
/-- The underlying real number of the critical value is the infimum of the parameter values in
`[0,1]` where `θ` is strictly positive. -/
theorem criticalPercolationValue_eq_sInf_theta_pos (theta : unitInterval → NNReal) :
    (criticalPercolationValue theta : ℝ) =
      sInf ((↑) '' {p : unitInterval | 0 < theta p}) := sorry

-- Proof sketch: for monotone `θ`, the zero set in `[0,1]` is an initial segment and the positive
-- set is the complementary final segment, so they have the same boundary point.
/-- For a monotone origin-percolation probability `θ`, the critical value is also the supremum of
the parameters in `[0,1]` where `θ` vanishes. -/
theorem criticalPercolationValue_eq_sSup_theta_zero (theta : unitInterval → NNReal)
    (h_theta_mono : Monotone theta) :
    criticalPercolationValue theta = sSup {p : unitInterval | theta p = 0} := sorry

-- Proof sketch: replace the condition `0 < theta p` by the equivalent condition `psi p = 1`, then
-- rewrite the defining threshold set of `criticalPercolationValue`.
/-- If `ψ(p) = 1` is equivalent to `θ(p) > 0` on `[0,1]`, then the critical value is the infimum
of the parameters where `ψ` equals `1`. -/
theorem criticalPercolationValue_eq_sInf_psi_one (theta psi : unitInterval → NNReal)
    (h_theta_psi : ∀ p : unitInterval, 0 < theta p ↔ psi p = 1) :
    criticalPercolationValue theta = sInf {p : unitInterval | psi p = 1} := sorry

-- Proof sketch: first rewrite the threshold set using `0 < theta p ↔ psi p = 1`; then use that a
-- monotone `{0,1}`-valued function has complementary zero and one sets whose common boundary is
-- the critical threshold.
/-- If `ψ` is monotone and takes only the values `0` and `1` on `[0,1]`, and if `ψ(p) = 1` is
equivalent to `θ(p) > 0`, then the critical value is also the supremum of the parameters where
`ψ` vanishes. -/
theorem criticalPercolationValue_eq_sSup_psi_zero (theta psi : unitInterval → NNReal)
    (h_theta_psi : ∀ p : unitInterval, 0 < theta p ↔ psi p = 1)
    (h_psi_mono : Monotone psi)
    (h_psi_zero_or_one : ∀ p : unitInterval, psi p = 0 ∨ psi p = 1) :
    criticalPercolationValue theta = sSup {p : unitInterval | psi p = 0} := sorry
