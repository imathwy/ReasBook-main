import ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_2
import ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The Lebesgue measure restricted to `(0, 1]`, used for the typewriter example. -/
def typewriterMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc (0 : ℝ) 1)

/-- The dyadic interval supporting the `n`-th term of the typewriter sequence. -/
private def typewriterSupport (n : ℕ) : Set ℝ :=
  let m := Nat.log2 (n + 1)
  let k := n + 1 - 2 ^ m
  Set.Ioc ((k : ℝ) / (2 : ℝ) ^ m) (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m)

/-- The typewriter sequence on `(0, 1]`, viewed as indicator functions of dyadic intervals. -/
def typewriterSequence (n : ℕ) : ℝ → ℝ :=
  (typewriterSupport n).indicator (fun _ ↦ (1 : ℝ))

-- Proof sketch: the support of `typewriterSequence n` is a bounded measurable interval inside
-- `(0, 1]`, so its indicator is measurable and has finite integral against `typewriterMeasure`.
/-- Each term of the typewriter sequence is integrable on `(0, 1]`. -/
private theorem typewriterSequence_integrable (n : ℕ) :
    Integrable (typewriterSequence n) typewriterMeasure := sorry

-- Proof sketch: compute the `L¹` norm of `typewriterSequence n` as the length of its dyadic
-- support, which tends to `0`, while every point of `(0, 1]` lies in exactly one dyadic interval
-- at each generation, so the pointwise values oscillate between `0` and `1` and fail to converge.
/-- The typewriter sequence converges to `0` in mean (`L¹`) on `(0, 1]`. -/
private theorem typewriterSequence_tendstoInMean :
    TendstoInMean typewriterMeasure typewriterSequence 0 := sorry

/-- The typewriter sequence does not converge to `0` almost everywhere on `(0, 1]`. -/
private theorem typewriterSequence_not_tendstoAlmostEverywhere :
    ¬ ∀ᵐ ω ∂typewriterMeasure, Tendsto (fun n ↦ typewriterSequence n ω) atTop (𝓝 (0 : ℝ)) := sorry

/-- Exercise 6.1.2 (1): the typewriter sequence converges to `0` in mean (`L¹`) but does not
converge to `0` almost everywhere. -/
theorem typewriter_sequence_converges_inL1_not_ae :
    TendstoInMean typewriterMeasure typewriterSequence 0 ∧
      ¬ ∀ᵐ ω ∂typewriterMeasure, Tendsto (fun n ↦ typewriterSequence n ω) atTop (𝓝 (0 : ℝ)) :=
  ⟨typewriterSequence_tendstoInMean, typewriterSequence_not_tendstoAlmostEverywhere⟩

/-- The indicator functions of the unit intervals translated to the right along the real line. -/
def escapingIndicatorSequence (n : ℕ) : ℝ → ℝ :=
  (Set.Icc (n : ℝ) (n + 1)).indicator (fun _ ↦ (1 : ℝ))

-- Proof sketch: each translated unit interval is measurable and has finite Lebesgue measure, so
-- its indicator function is Lebesgue integrable.
/-- Each translated interval indicator is integrable with respect to Lebesgue measure. -/
private theorem escapingIndicatorSequence_integrable (n : ℕ) :
    Integrable (escapingIndicatorSequence n) (volume : Measure ℝ) := sorry

-- Proof sketch: for each fixed `x : ℝ`, the intervals `[n, n + 1]` eventually lie to the right of
-- `x`, so the sequence is eventually `0` at `x`; however every term has `L¹` norm equal to `1`,
-- so the sequence cannot converge to `0` in `L¹`.
/-- The translated unit-interval indicators converge to `0` almost everywhere. -/
private theorem escapingIndicatorSequence_tendstoAlmostEverywhere :
    ∀ᵐ ω ∂volume, Tendsto (fun n ↦ escapingIndicatorSequence n ω) atTop (𝓝 (0 : ℝ)) := sorry

/-- The translated unit-interval indicators do not converge to `0` in mean (`L¹`). -/
private theorem escapingIndicatorSequence_not_tendstoInMean :
    ¬ TendstoInMean volume escapingIndicatorSequence 0 := sorry

/-- Exercise 6.1.2 (2): the translated unit-interval indicators converge to `0` almost
everywhere but do not converge to `0` in mean (`L¹`). -/
theorem escaping_indicator_sequence_tendsto_ae_not_inL1 :
    (∀ᵐ ω ∂volume, Tendsto (fun n ↦ escapingIndicatorSequence n ω) atTop (𝓝 (0 : ℝ))) ∧
      ¬ TendstoInMean volume escapingIndicatorSequence 0 :=
  ⟨escapingIndicatorSequence_tendstoAlmostEverywhere,
    escapingIndicatorSequence_not_tendstoInMean⟩

end
