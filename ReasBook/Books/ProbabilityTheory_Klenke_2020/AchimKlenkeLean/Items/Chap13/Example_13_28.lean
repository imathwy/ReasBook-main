import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap13.Definition_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory

open scoped ENNReal

universe u v

/- Item (iv) lives in the tightness domain for laws on `ℝ`. The source-facing object is a family
of probability distributions, so the canonical owner abstraction is `ProbabilityMeasure ℝ`; the
raw measure view is derived via `ProbabilityMeasure.toMeasure`. -/
/-- The uniform probability law on the symmetric interval `[-n,n]`, with the degenerate case
`n = 0` realized as the Dirac law at `0`. -/
noncomputable def symmetricIntervalUniformLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  if h : n = 0 then
    diracProba 0
  else
    ⟨ENNReal.ofReal (1 / (2 * n : ℝ)) • volume.restrict (Icc (-(n : ℝ)) n), by
      rw [isProbabilityMeasure_iff]
      calc
        (ENNReal.ofReal (1 / (2 * n : ℝ)) • volume.restrict (Icc (-(n : ℝ)) n)) Set.univ
            = ENNReal.ofReal (1 / (2 * n : ℝ)) * volume (Icc (-(n : ℝ)) n) := by
                simp [Measure.smul_apply]
        _ = ENNReal.ofReal (1 / (2 * n : ℝ)) * ENNReal.ofReal ((n : ℝ) + n) := by
              simp [Real.volume_Icc]
        _ = ENNReal.ofReal ((1 / (2 * n : ℝ)) * ((n : ℝ) + n)) := by
              rw [← ENNReal.ofReal_mul]
              positivity
        _ = 1 := by
              have hn : (n : ℝ) ≠ 0 := by
                exact_mod_cast h
              have hmul : (1 / (2 * n : ℝ)) * ((n : ℝ) + n) = 1 := by
                field_simp [hn]
                ring
              rw [hmul]
              norm_num⟩

-- Proof sketch: unfold the definition and simplify the nonzero branch.
/-- On a nondegenerate interval, the law `symmetricIntervalUniformLaw n` has as underlying measure
the normalized restriction of Lebesgue measure to `[-n,n]`. -/
theorem symmetricIntervalUniformLaw_toMeasure_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (symmetricIntervalUniformLaw n : Measure ℝ) =
      ENNReal.ofReal (1 / (2 * n : ℝ)) •
        volume.restrict (Icc (-(n : ℝ)) n) := by
  simp [symmetricIntervalUniformLaw, hn]

section Compact

variable (E : Type u) [MeasurableSpace E] [TopologicalSpace E] [CompactSpace E]

-- Proof sketch: apply `IsTightMeasureSet.of_compactSpace` to the image of the canonical owner type
-- `ProbabilityMeasure E` in `Measure E`.
/-- Example 13.28 (1): Item (i). If `E` is compact, then the family `𝓜₁(E)` of probability
measures on `E` is tight. -/
theorem compact_probability_measures_are_tight :
    IsTightMeasureSet (Set.range
      (ProbabilityMeasure.toMeasure : ProbabilityMeasure E → Measure E)) := by
  exact IsTightMeasureSet.of_compactSpace

-- Proof sketch: apply `IsTightMeasureSet.of_compactSpace` to the image in `Measure E` of the
-- canonical mass bound `μ.mass ≤ 1` on `FiniteMeasure E`.
/-- Example 13.28 (2): Item (i). If `E` is compact, then the family `𝓜_{≤ 1}(E)` of
subprobability measures on `E` is tight. -/
theorem compact_subprobability_measures_are_tight :
    IsTightMeasureSet (FiniteMeasure.toMeasure ''
      {μ : FiniteMeasure E | μ.mass ≤ 1}) := by
  exact IsTightMeasureSet.of_compactSpace

end Compact

-- Proof sketch: use the canonical tightness criterion on `ℝ` together with Markov's inequality for
-- the nonnegative function `x ↦ ENNReal.ofReal |x|`, obtaining a uniform tail bound from the
-- finite extended first-moment bound.
/-- Example 13.28 (3): Item (ii). A family of laws on `ℝ` with uniformly bounded first absolute
moment, expressed as a finite extended nonnegative expectation, is tight. -/
theorem laws_with_bounded_first_moment_are_tight {I : Type v}
    (μ : I → ProbabilityMeasure ℝ) {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∀ i, ∫⁻ x, ENNReal.ofReal |x| ∂(μ i : Measure ℝ) ≤ C) :
    IsTightMeasureSet (ProbabilityMeasure.toMeasure '' Set.range μ) := sorry

-- Proof sketch: for any compact set `K ⊆ ℝ`, choose `n` outside a bounded interval containing
-- `K`; then the Dirac mass at `n` gives mass `1` to `Kᶜ`.
/-- Example 13.28 (4): Item (iii). The family `(δₙ)ₙ` of Dirac probability measures on `ℝ` is not
tight. -/
theorem dirac_nat_family_not_tight :
    ¬ IsTightMeasureSet
      (ProbabilityMeasure.toMeasure '' Set.range (fun n : ℕ ↦ diracProba (n : ℝ))) := sorry

-- Proof sketch: any compact set is contained in some bounded interval, and for sufficiently large
-- `n` the normalized Lebesgue mass of that compact set inside `[-n,n]` stays strictly below `1`.
/-- Example 13.28 (5): Item (iv). The family of uniform distributions on the intervals `[-n,n]`
is not tight. -/
theorem symmetric_interval_uniform_family_not_tight :
    ¬ IsTightMeasureSet (ProbabilityMeasure.toMeasure '' Set.range symmetricIntervalUniformLaw) :=
  sorry
