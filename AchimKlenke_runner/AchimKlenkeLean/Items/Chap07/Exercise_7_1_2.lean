import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Exercise 7.1.2 (1): canonical `MemLp` form of clause (i). If `f` belongs to `L^p(μ)` for some
positive finite exponent, then its finite-exponent seminorms converge to the `L^∞` seminorm as
`p → ∞`. -/
-- Proof sketch: compare the seminorms for different exponents using the standard `eLpNorm`
-- comparison inequalities, use the finite-exponent hypothesis to control all large exponents, and
-- identify the limiting upper and lower bounds with `eLpNorm f ∞ μ`.
theorem tendsto_eLpNorm_atTop_of_exists_memLp {f : Ω → ℝ}
    (hfin : ∃ p : NNReal, 0 < p ∧ MemLp f p μ) :
    Tendsto (fun p : NNReal ↦ eLpNorm f p μ) atTop (𝓝 (eLpNorm f ∞ μ)) := sorry

/-- Exercise 7.1.2 (1): source-facing bridge from measurable finite-exponent data to the
canonical `MemLp` statement. -/
theorem tendsto_eLpNorm_atTop_of_finite_exponent {f : Ω → ℝ} (hf_meas : Measurable f)
    (hfin : ∃ p : NNReal, 0 < p ∧ eLpNorm f p μ < ∞) :
    Tendsto (fun p : NNReal ↦ eLpNorm f p μ) atTop (𝓝 (eLpNorm f ∞ μ)) :=
  tendsto_eLpNorm_atTop_of_exists_memLp <| by
    rcases hfin with ⟨p, hp, hpfin⟩
    exact ⟨p, hp, ⟨hf_meas.aestronglyMeasurable, hpfin⟩⟩

/-- Exercise 7.1.2 (2): Clause (ii). On `ℝ` with Lebesgue measure, the measurable constant
function `1` shows that the finite-exponent integrability assumption in clause (i) is necessary. -/
-- Proof sketch: for the constant function `1` on `ℝ`, every finite `L^p` seminorm is infinite
-- because `volume univ = ∞`, while the `L^∞` seminorm is `1`; hence the finite-exponent seminorms
-- cannot converge to the `L^∞` seminorm as `p → ∞`.
theorem not_tendsto_eLpNorm_const_one_atTop :
    ¬ Tendsto (fun p : NNReal ↦ eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) p volume) atTop
      (𝓝 (eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) ∞ volume)) := by
  intro h
  have hconst :
      (fun p : NNReal ↦ eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) p volume) =ᶠ[atTop]
        fun _ ↦ (∞ : ℝ≥0∞) := by
    filter_upwards [eventually_gt_atTop (0 : NNReal)] with p hp
    rw [eLpNorm_const' (1 : ℝ) (by exact_mod_cast hp.ne') (by simp)]
    simp [hp, one_div]
  have h' : Tendsto (fun _ : NNReal ↦ (∞ : ℝ≥0∞)) atTop
      (𝓝 (eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) ∞ volume)) :=
    (tendsto_congr' hconst).mp h
  have hEq : (∞ : ℝ≥0∞) = eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) ∞ volume :=
    tendsto_const_nhds_iff.mp h'
  rw [eLpNorm_exponent_top, eLpNormEssSup_const _] at hEq
  · norm_num at hEq
  · intro hvolume
    simpa [hvolume] using (Real.volume_univ : volume (Set.univ : Set ℝ) = ∞)

end MeasureTheory
