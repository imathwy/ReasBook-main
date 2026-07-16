import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap06.Definition_6_2

open Filter MeasureTheory
open scoped ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The canonical weighted owner measure attached to a real-valued density `H`. -/
def weightedMeasure (μ : Measure Ω) (H : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun ω ↦ ENNReal.ofReal (H ω))

section PseudoMetric

variable {E : Type v} [PseudoMetricSpace E]
variable (μ : Measure Ω) (H : Ω → ℝ)

/-- Exercise 6.2.1: `weightedTruncDist μ H` is the truncated integral distance on
almost-everywhere measurable `E`-valued functions, computed with respect to the canonical
weighted measure `weightedMeasure μ H`. Integrability of `H` is used only in the
metric and convergence results below, where one needs the weighted measure to be finite. -/
def weightedTruncDist (f g : Ω →ₘ[μ] E) : ℝ :=
  ∫ ω, min (1 : ℝ) (dist (f ω) (g ω)) ∂ weightedMeasure μ H

/-- The weighted truncated distance from a function to itself is zero. -/
@[simp] theorem weightedTruncDist_self
    (f : Ω →ₘ[μ] E) :
    weightedTruncDist μ H f f = 0 := sorry

/-- The weighted truncated distance is symmetric. -/
theorem weightedTruncDist_comm
    (f g : Ω →ₘ[μ] E) :
    weightedTruncDist μ H f g = weightedTruncDist μ H g f := sorry

/-- The weighted truncated distance satisfies the triangle inequality for an integrable
real-valued weight. -/
theorem weightedTruncDist_triangle
    (hH_int : Integrable H μ)
    (f g h : Ω →ₘ[μ] E) :
    weightedTruncDist μ H f h ≤
      weightedTruncDist μ H f g + weightedTruncDist μ H g h := sorry

/-- For an integrable weight, `weightedTruncDist` defines the canonical pseudometric
structure on `Ω →ₘ[μ] E` attached to the weighted truncated integral distance. -/
@[reducible]
def weightedTruncPseudoMetricSpace
    (hH_int : Integrable H μ)
    : PseudoMetricSpace (Ω →ₘ[μ] E) where
  dist := weightedTruncDist μ H
  dist_self := weightedTruncDist_self μ H
  dist_comm := weightedTruncDist_comm μ H
  dist_triangle := weightedTruncDist_triangle μ H hH_int

end PseudoMetric

section Metric

variable {E : Type v} [MetricSpace E]
variable (μ : Measure Ω) (H : Ω → ℝ)

/-- An integrable weight that is strictly positive `μ`-almost everywhere separates
almost-everywhere classes. -/
@[simp] theorem weightedTruncDist_eq_zero_iff
    (hH_int : Integrable H μ) (hH_pos : ∀ᵐ ω ∂μ, 0 < H ω) {f g : Ω →ₘ[μ] E} :
    weightedTruncDist μ H f g = 0 ↔ f = g := sorry

/-- The weighted truncated distance induces a metric structure on `Ω →ₘ[μ] E` once the weight is
integrable and strictly positive `μ`-almost everywhere. This is a named metric structure rather
than a global instance, since different choices of `H` give different metrics on the same type. -/
@[reducible]
def weightedTruncMetricSpace
    (hH_int : Integrable H μ)
    (hH_pos : ∀ᵐ ω ∂μ, 0 < H ω) :
    MetricSpace (Ω →ₘ[μ] E) where
  toPseudoMetricSpace := weightedTruncPseudoMetricSpace μ H hH_int
  eq_of_dist_eq_zero := fun hfg ↦ (weightedTruncDist_eq_zero_iff μ H hH_int hH_pos).1 hfg

end Metric

section MeasureTheoretic

variable {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace.SeparableSpace E]
variable (μ : Measure Ω) (H : Ω → ℝ)

/-- Exercise 6.2.1 (i): convergence of the weighted truncated distance to `0` is equivalent to
convergence in `μ`-measure on every measurable set of finite `μ`-measure. -/
theorem tendsto_weightedTruncDist_iff_tendstoInMeasureOnFiniteMeasureSets
    (hH_int : Integrable H μ) (hH_pos : ∀ᵐ ω ∂μ, 0 < H ω)
    {fSeq : ℕ → Ω →ₘ[μ] E} {f : Ω →ₘ[μ] E} :
    Tendsto (fun n ↦ weightedTruncDist μ H (fSeq n) f) atTop (𝓝 0) ↔
      TendstoInMeasureOnFiniteMeasureSets μ (fun n ↦ fSeq n) f := sorry

/-- On a finite measure space, the weighted truncated distance also detects mathlib's canonical
global convergence-in-measure notion. -/
theorem tendsto_weightedTruncDist_iff_tendstoInMeasure
    [IsFiniteMeasure μ]
    (hH_int : Integrable H μ) (hH_pos : ∀ᵐ ω ∂μ, 0 < H ω)
    {fSeq : ℕ → Ω →ₘ[μ] E} {f : Ω →ₘ[μ] E} :
    Tendsto (fun n ↦ weightedTruncDist μ H (fSeq n) f) atTop (𝓝 0) ↔
      TendstoInMeasure μ (fun n ↦ fSeq n) atTop f := sorry

/-- Exercise 6.2.1 (ii): if `E` is complete, then the named metric space
`weightedTruncMetricSpace μ H hH_int hH_pos` is complete. -/
theorem weightedTruncMetricSpace_complete [CompleteSpace E]
    (hH_int : Integrable H μ) (hH_pos : ∀ᵐ ω ∂μ, 0 < H ω) :
    by
      letI : MetricSpace (Ω →ₘ[μ] E) := weightedTruncMetricSpace μ H hH_int hH_pos
      exact CompleteSpace (Ω →ₘ[μ] E) := by
  letI : MetricSpace (Ω →ₘ[μ] E) := weightedTruncMetricSpace μ H hH_int hH_pos
  sorry

end MeasureTheoretic
