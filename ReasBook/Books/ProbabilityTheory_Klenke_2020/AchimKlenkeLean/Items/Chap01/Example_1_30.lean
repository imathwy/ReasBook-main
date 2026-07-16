import Mathlib
import Mathlib.Probability.UniformOn
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap01.Definition_1_28
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap01.Example_1_11
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap01.Example_1_37

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory ProbabilityTheory

open scoped ENNReal

universe u

variable {Ω : Type u} {C : Set (Set Ω)}

-- Proof sketch: every summand vanishes on `∅`, so the weighted series also vanishes on `∅`.
/-- The empty-set value needed to define weighted sums of additive contents. -/
private theorem weightedAddContentSeries_empty (w : ℕ → NNReal) (m : ℕ → AddContent ℝ≥0∞ C) :
    (∑' n, (w n : ℝ≥0∞) * m n ∅) = 0 := sorry

-- Proof sketch: use finite additivity for each `m n`, then exchange the finite sum with the
-- infinite weighted sum.
/-- The finite additivity clause needed to define weighted sums of additive contents. -/
private theorem weightedAddContentSeries_sUnion (w : ℕ → NNReal) (m : ℕ → AddContent ℝ≥0∞ C)
    (I : Finset (Set Ω)) (hI : ↑I ⊆ C)
    (h_dis : PairwiseDisjoint (I : Set (Set Ω)) id)
    (h_mem : ⋃₀ ↑I ∈ C) :
    (∑' n, (w n : ℝ≥0∞) * m n (⋃₀ ↑I)) =
      ∑ s ∈ I, (∑' n, (w n : ℝ≥0∞) * m n s) := sorry

-- Proof sketch: apply `Measure.sum_apply` to the canonical measure
-- `Measure.sum fun n ↦ w n • μ n`.
/-- Example 1.30 (7): Item (iv). The canonical countable nonnegative linear combination
`Measure.sum fun n ↦ w n • μ n` evaluates on measurable sets as the corresponding weighted
series. -/
theorem weightedMeasureSeries_apply [MeasurableSpace Ω] (w : ℕ → NNReal) (μ : ℕ → Measure Ω)
    {s : Set Ω} (hs : MeasurableSet s) :
    (Measure.sum fun n ↦ w n • μ n) s = ∑' n, (w n : ℝ≥0∞) * μ n s := by
  simp [Measure.sum_apply, hs, Measure.smul_apply]

/-- Example 1.30 (8): Item (iv). A countable nonnegative linear combination of additive contents is
again an additive content on the same family of sets. -/
noncomputable def weightedAddContentSeries (w : ℕ → NNReal) (m : ℕ → AddContent ℝ≥0∞ C) :
    AddContent ℝ≥0∞ C :=
  { toFun := fun s ↦ ∑' n, (w n : ℝ≥0∞) * m n s
    empty' := weightedAddContentSeries_empty w m
    sUnion' := weightedAddContentSeries_sUnion w m }

/- Example 1.30 (1): Item (i). The Dirac measure at a point is a probability measure; this is the
canonical mathlib instance `Measure.dirac.isProbabilityMeasure`. -/
recall Measure.dirac.isProbabilityMeasure [MeasurableSpace Ω] (ω : Ω) :
  IsProbabilityMeasure (Measure.dirac ω)

-- Proof sketch: use the explicit formula for the uniform counting measure on the whole finite
-- space.
/-- Example 1.30 (2): Item (ii). On a finite space, the uniform distribution on the whole space
assigns mass `#A / #Ω` to a set `A`. -/
theorem uniformOn_univ_eq_encard_div [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω]
    (A : Set Ω) :
    uniformOn (Set.univ : Set Ω) A = A.encard / Fintype.card Ω := by
  have h :
      uniformOn (Set.univ : Set Ω) A = Measure.count A / Fintype.card Ω :=
    uniformOn_univ
  simpa [Measure.count_apply (Set.toFinite A).measurableSet] using
    h

/- Example 1.30 (3): Item (ii). On a finite nonempty space, the uniform distribution on the whole
space is a probability measure; this is the canonical mathlib instance
`ProbabilityTheory.instIsProbabilityMeasure_uniformOn_univ`. -/
recall ProbabilityTheory.instIsProbabilityMeasure_uniformOn_univ [MeasurableSpace Ω] [Finite Ω]
    [Nonempty Ω] :
  IsProbabilityMeasure (uniformOn (Set.univ : Set Ω))

/- Example 1.30 (4): Item (iii). On a countably infinite space, the finite-or-cofinite subsets
form an algebra of sets; this is the canonical earlier-project theorem
`finiteOrCofiniteFamily_isSetAlgebra`. -/
recall finiteOrCofiniteFamily_isSetAlgebra

-- Proof sketch: evaluate the content on the disjoint union of singleton sets and compare with the
-- corresponding series of values.
/- Example 1.30 (6): Item (iii). On a countably infinite space, the finite-or-cofinite content is
not a premeasure; this is the canonical earlier-project theorem
`finiteCofiniteZeroInfiniteContent_not_isSigmaSubadditive`. -/
recall finiteCofiniteZeroInfiniteContent_not_isSigmaSubadditive

-- Proof sketch: apply the premeasure property termwise and exchange the countable weighted sum
-- with the countable union formula.
/-- Example 1.30 (9): Item (iv). A countable nonnegative linear combination of premeasures is again
a premeasure. -/
theorem weightedAddContentSeries_isPremeasureOn (w : ℕ → NNReal) (m : ℕ → AddContent ℝ≥0∞ C)
    (hm : ∀ n, (m n).IsSigmaSubadditive) :
    (weightedAddContentSeries w m).IsSigmaSubadditive := sorry

-- Proof sketch: expand the canonical weighted counting measure
-- `Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)`.
/-- Example 1.30 (10): Item (v). On a countable space, the canonical weighted counting measure
`Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)` sends a set `A` to the sum of the weights over
the points of `A`. -/
theorem weightedCountMeasure_apply [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Countable Ω] (p : Ω → NNReal) (A : Set Ω) :
    (Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)) A = ∑' ω : A, (p ω : ℝ≥0∞) := by
  rw [withDensity_apply' _ A, lintegral_countable]
  · simp
  · exact Set.to_countable A

/- Example 1.30 (11): Item (v). On a countable space, the canonical weighted counting measure
`Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)` is sigma-finite, by the generic
`SigmaFinite.withDensity` instance. -/
theorem weightedCountMeasure_sigmaFinite [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Countable Ω] (p : Ω → NNReal) :
    SigmaFinite (Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)) := inferInstance

-- Proof sketch: compute the mass of the whole space as the total sum of the weights and use the
-- hypothesis that this sum is `1`.
/-- Example 1.30 (12): Item (vi). If the total weight is `1`, then the canonical weighted counting
measure `Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)` is a probability measure. -/
theorem weightedCountMeasure_isProbabilityMeasure [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : Ω → NNReal) (hp : (∑' ω, (p ω : ℝ≥0∞)) = 1) :
    IsProbabilityMeasure (Measure.count.withDensity fun ω ↦ (p ω : ℝ≥0∞)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]
  exact hp

/- Example 1.30 (13): Item (vii). Constant weight `1` recovers the underlying measure; the
counting-measure case is the specialization of the canonical theorem `withDensity_one`. -/
recall withDensity_one {α : Type u} [MeasurableSpace α] {μ : Measure α} :
  μ.withDensity 1 = μ

-- Proof sketch: on a finite space the counting measure has finite total mass, so the constant-one
-- weighted counting measure is finite.
/-- Example 1.30 (14): Item (vii). On a finite space, counting measure is finite. -/
theorem weightedCountMeasure_const_one_isFiniteMeasure
    [MeasurableSpace Ω] [Finite Ω] :
    IsFiniteMeasure
      (Measure.count.withDensity fun _ : Ω ↦ (1 : ℝ≥0∞)) := by
  simpa [withDensity_one] using (inferInstance : IsFiniteMeasure (Measure.count : Measure Ω))

/- Example 1.30 (15): Item (viii). Lebesgue measure gives an interval `(a, b]` mass `b - a`,
realizing the textbook interval-length content; this is the canonical theorem `Real.volume_Ioc`. -/
recall Real.volume_Ioc (a b : ℝ) :
  volume (Set.Ioc a b) = ENNReal.ofReal (b - a)

/- Example 1.30 (16): Item (viii). Lebesgue measure on `ℝ` is sigma-finite. -/
theorem real_volume_sigmaFinite : SigmaFinite (volume : Measure ℝ) := inferInstance

-- Proof sketch: unfold `withDensity` on the interval `(a, b]` and rewrite the result as the
-- interval integral of the continuous nonnegative density.
/-- Example 1.30 (17): Item (ix). A continuous nonnegative density defines a measure whose mass on
`(a, b]` is the integral of the density over that interval. -/
theorem continuousDensity_measure_Ioc (f : ℝ → ℝ) (hf : Continuous f)
    (hf_nonneg : ∀ x, 0 ≤ f x) (a b : ℝ) :
    (volume.withDensity fun x ↦ ENNReal.ofReal (f x)) (Set.Ioc a b) =
      ENNReal.ofReal (∫ x in a..b, f x ∂volume) := sorry

/- Example 1.30 (18): Item (ix). A continuous nonnegative density on `ℝ` yields a sigma-finite
measure; this is the concrete specialization of the canonical theorem
`MeasureTheory.SigmaFinite.withDensity_ofReal`. -/
recall MeasureTheory.SigmaFinite.withDensity_ofReal {α : Type u} {m0 : MeasurableSpace α}
    {μ : Measure α} [SigmaFinite μ] (f : α → ℝ) :
  SigmaFinite (μ.withDensity fun x ↦ ENNReal.ofReal (f x))
