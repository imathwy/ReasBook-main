import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_6_2_1 (from Items/Chap06) -/
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

/-! ### Definition_6_2 (from Items/Chap06) -/
open Filter MeasureTheory
open scoped ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {β : Type v} [PseudoMetricSpace β]
variable {E : Type v} [TopologicalSpace E]

/-- Definition 6.2 (1): A sequence `fₙ : Ω → β` converges to `f` in local `μ`-measure if it
converges in the canonical mathlib sense for every restricted finite measure `μ.restrict A` with
`μ A < ∞`. For a probability measure, this is convergence in probability. -/
abbrev TendstoInMeasureOnFiniteMeasureSets
    (μ : Measure Ω) (fSeq : ℕ → Ω → β) (f : Ω → β) : Prop :=
  ∀ A, μ A < ∞ → TendstoInMeasure (μ.restrict A) fSeq atTop f

/-- A sequence `fₙ : Ω → β` is Cauchy in local `μ`-measure if, on every restricted finite measure
`μ.restrict A`, the pairwise deviation measures tend to `0` along `atTop ×ˢ atTop`. -/
abbrev CauchyInMeasureOnFiniteMeasureSets
    (μ : Measure Ω) (fSeq : ℕ → Ω → β) : Prop :=
  ∀ A, μ A < ∞ →
    ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun p : ℕ × ℕ ↦
          (μ.restrict A) {ω | ε < dist (fSeq p.1 ω) (fSeq p.2 ω)})
        (atTop ×ˢ atTop) (𝓝 0)

/-- The measurable-set formulation of local convergence in measure is recovered by replacing a set
with its measurable hull, since this does not change the restricted finite measure. -/
theorem tendstoInMeasureOnFiniteMeasureSets_iff_forall_measurable
    (μ : Measure Ω) {fSeq : ℕ → Ω → β} {f : Ω → β} :
    TendstoInMeasureOnFiniteMeasureSets μ fSeq f ↔
      ∀ A, MeasurableSet A → μ A < ∞ → TendstoInMeasure (μ.restrict A) fSeq atTop f := by
  refine ⟨fun h A _hA hA_fin ↦ h A hA_fin, fun h A hA_fin ↦ ?_⟩
  simpa [Measure.restrict_toMeasurable hA_fin.ne] using
    h (toMeasurable μ A) (measurableSet_toMeasurable μ A)
      (by simpa [measure_toMeasurable] using hA_fin)

/-- The measurable-set formulation of local Cauchy convergence in measure is recovered by
replacing a set with its measurable hull, since this does not change the restricted finite
measure. -/
theorem cauchyInMeasureOnFiniteMeasureSets_iff_forall_measurable
    (μ : Measure Ω) {fSeq : ℕ → Ω → β}
    [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
    (hSeq : ∀ n, Measurable (fSeq n)) :
    CauchyInMeasureOnFiniteMeasureSets μ fSeq ↔
      ∀ A, MeasurableSet A → μ A < ∞ →
        ∀ ε : ℝ, 0 < ε →
          Tendsto
            (fun p : ℕ × ℕ ↦
              μ (A ∩ {ω | ε < dist (fSeq p.1 ω) (fSeq p.2 ω)}))
            (atTop ×ˢ atTop) (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · intro h A hA hA_fin ε hε
    have h_event :
        ∀ p : ℕ × ℕ,
          MeasurableSet {ω | ε < dist (fSeq p.1 ω) (fSeq p.2 ω)} := fun p ↦
            measurableSet_lt measurable_const ((hSeq p.1).dist (hSeq p.2))
    simpa [CauchyInMeasureOnFiniteMeasureSets, Measure.restrict_apply, Set.inter_comm, hA, h_event]
      using
      h A hA_fin ε hε
  · intro h A hA_fin ε hε
    have h_event :
        ∀ p : ℕ × ℕ,
          MeasurableSet {ω | ε < dist (fSeq p.1 ω) (fSeq p.2 ω)} := fun p ↦
            measurableSet_lt measurable_const ((hSeq p.1).dist (hSeq p.2))
    have h_meas :
        Tendsto
          (fun p : ℕ × ℕ ↦
            μ (toMeasurable μ A ∩ {ω | ε < dist (fSeq p.1 ω) (fSeq p.2 ω)}))
          (atTop ×ˢ atTop) (𝓝 0) :=
      h (toMeasurable μ A) (measurableSet_toMeasurable μ A)
        (by simpa [measure_toMeasurable] using hA_fin) ε hε
    have h_restrict :
        Tendsto
          (fun p : ℕ × ℕ ↦
            (μ.restrict (toMeasurable μ A)) {ω | ε < dist (fSeq p.1 ω) (fSeq p.2 ω)})
          (atTop ×ˢ atTop) (𝓝 0) := by
      simpa [Measure.restrict_apply, Set.inter_comm, h_event] using h_meas
    simpa [CauchyInMeasureOnFiniteMeasureSets, Measure.restrict_toMeasurable hA_fin.ne] using
      h_restrict

section

variable (μ : Measure Ω) (fSeq : ℕ → Ω → E) (f : Ω → E)

/- Definition 6.2 (2): A sequence `fₙ : Ω → E` converges to `f` `μ`-almost everywhere if for
`μ`-almost every `ω`, the pointwise sequence `fₙ ω` tends to `f ω`. For a probability measure,
this is almost sure convergence. -/
#check (∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)))

end

/-- On a finite measure space, the local textbook notion of convergence in `μ`-measure agrees
with mathlib's canonical `MeasureTheory.TendstoInMeasure`. -/
theorem tendstoInMeasureOnFiniteMeasureSets_iff_mathlib_tendstoInMeasure
    (μ : Measure Ω) [IsFiniteMeasure μ] {fSeq : ℕ → Ω → β} {f : Ω → β} :
    TendstoInMeasureOnFiniteMeasureSets μ fSeq f ↔
      TendstoInMeasure μ fSeq atTop f := by
  refine ⟨fun h ↦ ?_, fun h A _hA_fin ↦ ?_⟩
  · simpa [TendstoInMeasureOnFiniteMeasureSets, Measure.restrict_univ] using
      h Set.univ (measure_lt_top μ Set.univ)
  · rw [tendstoInMeasure_iff_dist] at h ⊢
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
      (fun _ ↦ zero_le _) ?_
    intro n
    exact Measure.restrict_apply_le A {ω | ε ≤ dist (fSeq n ω) (f ω)}

/-- Almost-everywhere convergence is equivalently convergence outside a measurable `μ`-null set. -/
theorem tendstoAlmostEverywhere_iff_exists_measurable_null
    (μ : Measure Ω) {fSeq : ℕ → Ω → E} {f : Ω → E} :
    (∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))) ↔
      ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧
        ∀ ω ∈ Nᶜ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := by
  let P : Ω → Prop := fun ω ↦ Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h_null : μ {ω | ¬ P ω} = 0 := by
      simpa [P] using (ae_iff.mp h)
    obtain ⟨N, h_subset, hN, hμN⟩ := exists_measurable_superset_of_null h_null
    refine ⟨N, hN, hμN, fun ω hω ↦ ?_⟩
    have hωN : ω ∉ N := by
      simpa using hω
    by_contra hP
    exact hωN (h_subset hP)
  · rcases h with ⟨N, hN, hμN, h_outside⟩
    have h_null : μ {ω | ¬ P ω} = 0 := by
      refine measure_mono_null (fun ω hω ↦ ?_) hμN
      by_contra hωN
      exact hω (h_outside ω (by simpa using hωN))
    simpa [P] using (ae_iff.mpr h_null)
