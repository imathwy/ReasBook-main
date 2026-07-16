import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap07.Definition_7_2

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace Filter MeasureTheory.Filtration
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

universe u

variable {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ} {p : ℝ}

/- Theorem 11.10 is `source-facing`: it concerns a discrete martingale and its canonical terminal
limit random variable `ℱ.limitProcess X μ`. Its `core/canonical` owner layers are the existing
martingale API around `Filtration.limitProcess`, `Submartingale.memLp_limitProcess`, and
`Submartingale.ae_tendsto_limitProcess`, together with the Chapter 7 convergence owner
`TendstoInLp`. Its local `bridge/view` statements are the passage from the textbook `L^p` bound
`∃ C, ∀ n, eLpNorm (X n) p μ ≤ C` to the owner `L¹` boundedness input, and the raw `eLpNorm`
convergence reformulation of `TendstoInLp`; the theorems below keep the source statement public
and derive the shorter owner-level companions from it. -/

section

variable [IsProbabilityMeasure μ]

private theorem submartingale_eLpNorm_one_bounded_of_lp_bounded
    (hf : Submartingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ C) :
    ∃ R : ℝ≥0, ∀ n, eLpNorm (X n) 1 μ ≤ R := by
  rcases hbounded with ⟨C, hC⟩
  refine ⟨C, fun n ↦ ?_⟩
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have h1_le_p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hcompare :
      eLpNorm (X n) 1 μ ≤ eLpNorm (X n) (ENNReal.ofReal p) μ * μ Set.univ ^ (1 - 1 / p) := by
    simpa [hp0.ne', ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le, one_div] using
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ h1_le_p
        (((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable) :
          eLpNorm (X n) 1 μ ≤
            eLpNorm (X n) (ENNReal.ofReal p) μ *
              μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal))
  calc
    eLpNorm (X n) 1 μ
        ≤ eLpNorm (X n) (ENNReal.ofReal p) μ * μ Set.univ ^ (1 - 1 / p) := hcompare
    _ = eLpNorm (X n) (ENNReal.ofReal p) μ := by simp
    _ ≤ C := hC n

private theorem fact_one_le_ofReal_of_one_lt (hp : 1 < p) :
    Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨by
    simpa [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩

-- Proof sketch: upgrade the uniform `L^p` bound to the canonical `L¹`-boundedness input for the
-- owner martingale convergence theorem, deduce almost-sure convergence to `ℱ.limitProcess X μ`,
-- use the owner `MemLp` theorem for the limit, and conclude `L^p` convergence by Vitali on the
-- finite measure space.
/-- Theorem 11.10: if a real-valued discrete martingale is uniformly bounded in `L^p` for some
`p > 1`, then its canonical limit process is `⨆ n, ℱ n`-measurable, belongs to `L^p(μ)`, and the
martingale converges to it both almost surely and in `L^p`. -/
theorem martingale_convergence_to_memLp_limitProcess_of_lp_bounded
    (hf : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ C) :
    StronglyMeasurable[⨆ n, ℱ n] (ℱ.limitProcess X μ) ∧
      MemLp (ℱ.limitProcess X μ) (ENNReal.ofReal p) μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
      (letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_lt hp
       TendstoInLp (ENNReal.ofReal p) μ X (ℱ.limitProcess X μ)) :=
  sorry

/-- Theorem 11.10, owner-level `L^p`-convergence component: an `L^p`-bounded martingale with
`1 < p` converges in `L^p` to its canonical limit process. -/
theorem martingale_tendstoInLp_limitProcess_of_lp_bounded
    (hf : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ C) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_lt hp
    TendstoInLp (ENNReal.ofReal p) μ X (ℱ.limitProcess X μ) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_lt hp
  obtain ⟨_, _, _, h_tendsto⟩ :=
    martingale_convergence_to_memLp_limitProcess_of_lp_bounded hf hp hbounded
  exact h_tendsto

/-- Theorem 11.10, bridge `eLpNorm` formulation of the owner-level `L^p` convergence theorem. -/
theorem martingale_tendsto_eLpNorm_limitProcess_of_lp_bounded
    (hf : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ C) :
    Tendsto (fun n ↦ eLpNorm (X n - ℱ.limitProcess X μ) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := fact_one_le_ofReal_of_one_lt hp
  exact (martingale_tendstoInLp_limitProcess_of_lp_bounded hf hp hbounded).tendsto_eLpNorm

-- Proof sketch: first pass from `L^p` convergence to `ℱ.limitProcess X μ` to the conditional
-- expectation representation of each `X n`, then apply conditional Jensen to dominate
-- `|X n| ^ p` by the conditional expectations of `|ℱ.limitProcess X μ| ^ p`; the latter family is
-- uniformly integrable by the owner theorem `Integrable.uniformIntegrable_condExp_filtration`.
/-- Theorem 11.10, companion consequence: for an `L^p`-bounded martingale with `1 < p`, the
family `(|X_n| ^ p)_n` is uniformly integrable. -/
theorem martingale_uniformIntegrable_abs_rpow_of_lp_bounded
    (hf : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ n, eLpNorm (X n) (ENNReal.ofReal p) μ ≤ C) :
    UniformIntegrable (fun n ω ↦ |X n ω| ^ p) 1 μ := sorry

end

/- The source-facing theorem above exposes the full canonical limit-process conclusion publicly.
The shorter owner-level `TendstoInLp` consequence, its `eLpNorm` bridge, and the
uniform-integrability statement remain thin companions. -/

end MeasureTheory
