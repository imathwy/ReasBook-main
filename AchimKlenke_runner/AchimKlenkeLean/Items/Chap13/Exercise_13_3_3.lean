import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

open scoped ENNReal

universe u v

/- Exercise 13.3.3 is `source-facing`: the textbook object is the size-biased probability law of
a law on `[0, ∞)`, obtained by normalizing the weighted measure `x P(dx)` by the first moment.
Its `core/canonical` owner abstractions are `Measure.withDensity` for the weighted law,
`FiniteMeasure.normalize` for the normalization step, `IsTightMeasureSet` for tightness, and
`UniformIntegrable` for the underlying family of nonnegative random variables. The general
formula `\hat P(A) = m_P⁻¹ \int_A x P(dx)` is the main `source-facing` statement below; the
unit-mean specialization is the `bridge/view` in which the normalization factor is `1`, so the
size-biased law is represented directly by the weighted measure. -/

/-- The first moment of a probability law on `NNReal`, written as a Lebesgue integral in
`ℝ≥0∞`. -/
noncomputable def sizeBiasedFirstMoment (μ : ProbabilityMeasure NNReal) : ENNReal :=
  ∫⁻ x, (x : ENNReal) ∂(μ : Measure NNReal)

theorem sizeBiasedFirstMoment_pos
    {μ : ProbabilityMeasure NNReal}
    (hmean : sizeBiasedFirstMoment μ = 1) :
    0 < sizeBiasedFirstMoment μ := by
  simp [hmean]

theorem sizeBiasedFirstMoment_lt_top
    {μ : ProbabilityMeasure NNReal}
    (hmean : sizeBiasedFirstMoment μ = 1) :
    sizeBiasedFirstMoment μ < ∞ := by
  simp [hmean]

private noncomputable def sizeBiasedWeightedMeasure (μ : ProbabilityMeasure NNReal)
    (hmean_finite : sizeBiasedFirstMoment μ < ∞) :
    FiniteMeasure NNReal :=
  ⟨(μ : Measure NNReal).withDensity fun x ↦ (x : ENNReal),
    isFiniteMeasure_withDensity hmean_finite.ne⟩

private theorem sizeBiasedWeightedMeasure_mass (μ : ProbabilityMeasure NNReal)
    (hmean_finite : sizeBiasedFirstMoment μ < ∞) :
    ((sizeBiasedWeightedMeasure μ hmean_finite).mass : ENNReal) =
      sizeBiasedFirstMoment μ := by
  rw [FiniteMeasure.ennreal_mass]
  change ((μ : Measure NNReal).withDensity fun x ↦ (x : ENNReal)) Set.univ =
    sizeBiasedFirstMoment μ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, sizeBiasedFirstMoment]

private theorem sizeBiasedWeightedMeasure_ne_zero (μ : ProbabilityMeasure NNReal)
    (hmean_pos : 0 < sizeBiasedFirstMoment μ)
    (hmean_finite : sizeBiasedFirstMoment μ < ∞) :
    sizeBiasedWeightedMeasure μ hmean_finite ≠ 0 := by
  refine (FiniteMeasure.mass_nonzero_iff _).mp ?_
  rw [← ENNReal.coe_ne_zero, sizeBiasedWeightedMeasure_mass]
  exact hmean_pos.ne'

/-- The size-biased distribution attached to a probability law on `NNReal` is the canonical
normalization of the weighted measure `x μ(dx)` by the first moment. Since
`FiniteMeasure.normalize` uses a default probability measure at zero mass, the textbook hypothesis
`0 < m_P < ∞` is recorded in the specification theorem `sizeBiasedDistribution_apply`, not in the
constructor itself. -/
noncomputable def sizeBiasedDistribution (μ : ProbabilityMeasure NNReal)
    (hmean_finite : sizeBiasedFirstMoment μ < ∞) :
    ProbabilityMeasure NNReal :=
  (sizeBiasedWeightedMeasure μ hmean_finite).normalize

/-- Under the unit-mean hypothesis, the size-biased distribution is the normalization of
`x μ(dx)` with normalization constant `1`. -/
noncomputable def sizeBiasedDistributionOfUnitMean (μ : ProbabilityMeasure NNReal)
    (hmean : sizeBiasedFirstMoment μ = 1) :
    ProbabilityMeasure NNReal :=
  sizeBiasedDistribution μ (sizeBiasedFirstMoment_lt_top hmean)

/-- Formula (13.14): for a measurable set `A`, the size-biased law satisfies
`\hat P(A) = m_P⁻¹ \int_A x \, P(dx)` whenever the first moment `m_P` is positive and finite. -/
theorem sizeBiasedDistribution_apply (μ : ProbabilityMeasure NNReal)
    (hmean_pos : 0 < sizeBiasedFirstMoment μ)
    (hmean_finite : sizeBiasedFirstMoment μ < ∞) {s : Set NNReal}
    (hs : MeasurableSet s) :
    (sizeBiasedDistribution μ hmean_finite : Measure NNReal) s =
      (sizeBiasedFirstMoment μ)⁻¹ *
        ∫⁻ x in s, (x : ENNReal) ∂(μ : Measure NNReal) := by
  rw [sizeBiasedDistribution,
    (sizeBiasedWeightedMeasure μ hmean_finite).toMeasure_normalize_eq_of_nonzero
      (sizeBiasedWeightedMeasure_ne_zero μ hmean_pos hmean_finite),
    Measure.smul_apply]
  change (((sizeBiasedWeightedMeasure μ hmean_finite).mass⁻¹ : NNReal) : ENNReal) *
      ((μ : Measure NNReal).withDensity fun x ↦ (x : ENNReal)) s =
    (sizeBiasedFirstMoment μ)⁻¹ *
      ∫⁻ x in s, (x : ENNReal) ∂(μ : Measure NNReal)
  rw [withDensity_apply _ hs]
  change (((sizeBiasedWeightedMeasure μ hmean_finite).mass⁻¹ : NNReal) : ENNReal) *
      ∫⁻ x in s, (x : ENNReal) ∂(μ : Measure NNReal) =
    (sizeBiasedFirstMoment μ)⁻¹ *
      ∫⁻ x in s, (x : ENNReal) ∂(μ : Measure NNReal)
  rw [← sizeBiasedWeightedMeasure_mass μ hmean_finite]
  simp [sizeBiasedWeightedMeasure_ne_zero μ hmean_pos hmean_finite]

-- Proof sketch: under the unit-mean hypothesis, the normalization constant is `1`, so
-- formula (13.14) reduces to the weighted-measure formula `\hat P(A) = ∫_A x P(dx)`.
/-- Under the unit-mean hypothesis, the general size-biased formula simplifies to
`\hat P(A) = ∫_A x \, P(dx)`. -/
theorem sizeBiasedDistribution_apply_of_unit_mean (μ : ProbabilityMeasure NNReal)
    (hmean : sizeBiasedFirstMoment μ = 1) {s : Set NNReal}
    (hs : MeasurableSet s) :
    (sizeBiasedDistributionOfUnitMean μ hmean : Measure NNReal) s =
      ∫⁻ x in s, (x : ENNReal) ∂(μ : Measure NNReal) := by
  rw [sizeBiasedDistributionOfUnitMean]
  rw [sizeBiasedDistribution_apply μ (sizeBiasedFirstMoment_pos hmean)
    (sizeBiasedFirstMoment_lt_top hmean) hs]
  simp [hmean]

/-- Pushing a probability law forward by a nonnegative random variable turns its first moment into
the integral of that random variable. -/
theorem sizeBiasedFirstMoment_map {Ω : Type v} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    {X : Ω → NNReal} (hX : AEMeasurable X (P : Measure Ω)) :
    sizeBiasedFirstMoment (P.map hX) =
      ∫⁻ ω, X ω ∂(P : Measure Ω) := by
  rw [sizeBiasedFirstMoment, ProbabilityMeasure.toMeasure_map]
  simpa using
    (lintegral_map' measurable_coe_nnreal_ennreal.aemeasurable hX)

/-- If a nonnegative random variable has mean `1`, then the first moment of its pushed-forward law
is also `1`. -/
theorem sizeBiasedFirstMoment_map_eq_one {Ω : Type v} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω)
    {X : Ω → NNReal} (hX : AEMeasurable X (P : Measure Ω))
    (hmean : ∫⁻ ω, X ω ∂(P : Measure Ω) = 1) :
    sizeBiasedFirstMoment (P.map hX) = 1 := by
  rw [sizeBiasedFirstMoment_map P hX]
  exact hmean

/-- The size-biased law of the distribution of a nonnegative unit-mean random variable. This is
the `bridge/view` from a common-space random variable to the law-level owner
`sizeBiasedDistribution`. -/
noncomputable def sizeBiasedDistributionOfUnitMeanMap {Ω : Type v} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω)
    (X : Ω → NNReal) (hX : AEMeasurable X (P : Measure Ω))
    (hmean : ∫⁻ ω, X ω ∂(P : Measure Ω) = 1) :
    ProbabilityMeasure NNReal :=
  sizeBiasedDistributionOfUnitMean (P.map hX) (sizeBiasedFirstMoment_map_eq_one P hX hmean)

-- Proof sketch: transport each `X i` to its law `P.map (X i)` and apply the normed-space
-- tightness criterion on `NNReal` to the corresponding size-biased laws. Since `‖x‖ = x` for
-- `x : NNReal`, the tail mass of the size-biased law outside `(R, ∞)` is exactly the truncated
-- first moment of `X i`, and the canonical owner predicate for this family-level condition is
-- `UniformIntegrable` for the associated real-valued family.
/-- Exercise 13.3.3: for a family of nonnegative unit-mean random variables, the size-biased laws
of their distributions form a tight family if and only if the family is uniformly integrable when
viewed as real-valued random variables. -/
theorem isTightMeasureSet_range_sizeBiasedDistribution_iff_uniformIntegrable
    {I : Type u} {Ω : Type v} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (X : I → Ω → NNReal) (hX : ∀ i, AEMeasurable (X i) (P : Measure Ω))
    (hmean : ∀ i, ∫⁻ ω, X i ω ∂(P : Measure Ω) = 1) :
    IsTightMeasureSet
      (Set.range fun i ↦
        (sizeBiasedDistributionOfUnitMeanMap P (X i) (hX i) (hmean i) : Measure NNReal)) ↔
      UniformIntegrable (fun i ω ↦ (X i ω : ℝ)) 1 (P : Measure Ω) := sorry
