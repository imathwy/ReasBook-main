import ProbabilityTheory_Klenke_2020.Chap06.Definition_6_16

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {ι : Type v}

-- Proof sketch: compare the textbook majorant criterion with mathlib's indicator-tail
-- characterization of `UniformIntegrable` at exponent `1`, using nonnegative `L¹` majorants to pass
-- between variable cutoffs and indicator tails.
/-- Theorem 6.17: a family in `L¹(μ)` is uniformly integrable exactly when the infimum of the
uniform tail integrals over all nonnegative `L¹` majorants is zero. -/
theorem uniformIntegrable_iff_majorant_tail_inf_eq_zero (F : ι → Lp ℝ 1 μ) :
    UniformIntegrable (fun i ↦ (F i : Ω → ℝ)) 1 μ ↔
      (⨅ g : {g : Lp ℝ 1 μ // 0 ≤ᵐ[μ] (g : Ω → ℝ)},
        ⨆ i : ι, ∫⁻ x in {x | g.1 x < |F i x|}, ‖F i x‖ₑ ∂μ) = 0 := sorry

/-- Theorem 6.17, finite-measure addendum: on a finite measure space, uniform integrability is
equivalent to vanishing constant-cutoff excess integrals. -/
theorem uniformIntegrable_iff_cutoff_excess_sInf_eq_zero [IsFiniteMeasure μ]
    (F : ι → Lp ℝ 1 μ) :
    UniformIntegrable (fun i ↦ (F i : Ω → ℝ)) 1 μ ↔
      sInf (Set.range fun a : ℝ≥0 ↦
        iSup fun i : ι ↦ ∫ x, max (|F i x| - (a : ℝ)) 0 ∂μ) = 0 := sorry

/-- Theorem 6.17, finite-measure addendum: the two constant-cutoff formulations from the
textbook are equivalent. -/
theorem cutoff_excess_sInf_eq_zero_iff_cutoff_tail_integral_sInf_eq_zero [IsFiniteMeasure μ]
    (F : ι → Lp ℝ 1 μ) :
    sInf (Set.range fun a : ℝ≥0 ↦
      iSup fun i : ι ↦ ∫ x, max (|F i x| - (a : ℝ)) 0 ∂μ) = 0 ↔
        sInf (Set.range fun a : ℝ≥0 ↦
          iSup fun i : ι ↦ ∫ x in {x | (a : ℝ) < |F i x|}, |F i x| ∂μ) = 0 := sorry

/-- Theorem 6.17, finite-measure addendum: on a finite measure space, uniform integrability is
equivalent to vanishing constant-cutoff restricted tail integrals. -/
theorem uniformIntegrable_iff_cutoff_tail_integral_sInf_eq_zero [IsFiniteMeasure μ]
    (F : ι → Lp ℝ 1 μ) :
    UniformIntegrable (fun i ↦ (F i : Ω → ℝ)) 1 μ ↔
      sInf (Set.range fun a : ℝ≥0 ↦
        iSup fun i : ι ↦ ∫ x in {x | (a : ℝ) < |F i x|}, |F i x| ∂μ) = 0 := sorry

end
