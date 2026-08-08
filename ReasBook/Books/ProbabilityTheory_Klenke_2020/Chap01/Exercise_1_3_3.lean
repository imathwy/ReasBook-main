import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory

open scoped ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: each measure in the sequence vanishes on `∅`, so the constant zero sequence is the
-- unique limit of the values on `∅`.
private theorem finiteMeasurePointwiseLimit_empty
    (μ : ℕ → Measure Ω)
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x)) :
    limUnder atTop (fun n ↦ μ n ∅) = 0 := by
  have hμlim : Tendsto (fun n ↦ μ n ∅) atTop (𝓝 (limUnder atTop (fun n ↦ μ n ∅))) :=
    tendsto_nhds_limUnder (hlim ∅ MeasurableSet.empty)
  have hμ : Tendsto (fun n ↦ μ n ∅) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simp
  exact tendsto_nhds_unique hμlim hμ

-- Proof sketch: for each `n`, use countable additivity of `μ n` on the disjoint measurable family
-- `f`; then pass to the limit in `n`. Finiteness of the measures gives the continuity-from-above
-- control needed to justify exchanging the setwise limit with the infinite sum.
private theorem finiteMeasurePointwiseLimit_iUnion
    (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x))
    (f : ℕ → Set Ω) (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (fun i j ↦ Disjoint (f i) (f j))) :
    limUnder atTop (fun n ↦ μ n (⋃ i, f i)) =
      ∑' i, limUnder atTop (fun n ↦ μ n (f i)) := sorry

/-- The measure obtained by taking the measurable-setwise limit of a sequence of finite measures. -/
noncomputable def finiteMeasurePointwiseLimitMeasure
    (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x)) :
    Measure Ω :=
  Measure.ofMeasurable
    (fun A _ ↦ limUnder atTop (fun n ↦ μ n A))
    (finiteMeasurePointwiseLimit_empty μ hlim)
    (fun f hf hd ↦ finiteMeasurePointwiseLimit_iUnion μ hlim f hf hd)

/-- On each measurable set, `finiteMeasurePointwiseLimitMeasure μ hlim` is given by the setwise
limit of the values `μ n A`. -/
theorem finiteMeasurePointwiseLimitMeasure_apply
    (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x))
    (A : Set Ω) (hA : MeasurableSet A) :
    finiteMeasurePointwiseLimitMeasure μ hlim A = limUnder atTop (fun n ↦ μ n A) := by
  rw [finiteMeasurePointwiseLimitMeasure]
  exact Measure.ofMeasurable_apply A hA

-- Proof sketch: combine `finiteMeasurePointwiseLimitMeasure_apply` with the general fact that a
-- convergent net tends to its `limUnder` value.
/-- Exercise 1.3.3: If a sequence of finite measures converges setwise on every measurable set,
then the pointwise limit is again a measure, namely `finiteMeasurePointwiseLimitMeasure μ hlim`. -/
theorem tendsto_finiteMeasurePointwiseLimitMeasure_apply
    (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    (hlim : ∀ A : Set Ω, MeasurableSet A → ∃ x : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 x))
    (A : Set Ω) (hA : MeasurableSet A) :
    Tendsto (fun n ↦ μ n A) atTop (𝓝 (finiteMeasurePointwiseLimitMeasure μ hlim A)) := by
  rw [finiteMeasurePointwiseLimitMeasure_apply μ hlim A hA]
  exact tendsto_nhds_limUnder (hlim A hA)
