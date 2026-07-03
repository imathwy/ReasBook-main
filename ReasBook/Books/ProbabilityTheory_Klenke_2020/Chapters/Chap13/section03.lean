import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_13_3_1 (from Items/Chap13) -/
open Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory
namespace FiniteMeasure

/- Layer triage for Exercise 13.3.1.
- `source-facing`: existence of a measurable coercive weight with uniformly bounded integrals.
- `core/canonical`: `MeasureTheory.IsTightMeasureSet`.
- `bridge/view`: `tight_family_iff_forall_exists_isCompact_measure_compl_lt` is the chapter's
  compact-control reformulation of the same owner predicate for finite-measure families.
-/

-- Proof sketch: for the forward implication, extract compact sets with uniformly small complement
-- mass and assemble from them a measurable coercive weight by summing suitably scaled indicators of
-- those compacts. For the reverse implication, use Markov-type estimates on the sublevel sets of
-- the coercive weight to obtain compact sets whose complement mass is uniformly small over the
-- family.
/-
This is a source-facing bridge theorem over the canonical owner abstraction
`MeasureTheory.IsTightMeasureSet`, specialized to families of finite measures on `ℝ`.
-/
/-- Exercise 13.3.1: a family `ℱ` of finite measures on `ℝ` is tight if and only if there exists
a measurable weight `f : ℝ → [0, ∞)` that tends to `∞` along `cocompact ℝ` and whose integrals
are uniformly bounded on `ℱ`. -/
theorem tight_family_iff_exists_measurable_coercive_weight (ℱ : Set (FiniteMeasure ℝ)) :
    IsTightMeasureSet (toMeasure '' ℱ) ↔
      ∃ f : ℝ → ℝ≥0,
        Measurable f ∧
          Tendsto f (cocompact ℝ) atTop ∧
            (⨆ μ ∈ ℱ, ∫⁻ x, ↑(f x) ∂μ) < ∞ := sorry

end FiniteMeasure
end MeasureTheory

/-! ### Exercise_13_3_2 (from Items/Chap13) -/
open MeasureTheory ProbabilityTheory
open scoped NNReal

-- Proof sketch: for the forward implication, tightness gives uniform control of Gaussian tails,
-- which forces uniform bounds on both the means and variances. For the reverse implication, a
-- bounded parameter set yields a common compact interval capturing arbitrarily large mass for all
-- Gaussian laws in the family.
/- Exercise 13.3.2 is `source-facing` in the tightness/weak-convergence domain. Its primitive
data are the Gaussian mean and strictly positive variance parameters, while the `core/canonical`
owner abstractions are `ProbabilityTheory.gaussianReal` for the laws and
`MeasureTheory.IsTightMeasureSet` for family tightness. Using `Set.Ioi (0 : ℝ≥0)` keeps strict
positivity as primitive data in the owner parameter type, so the family can be expressed directly
as `p ↦ gaussianReal p.1 p.2` instead of via the bridge `Real.toNNReal`. -/
/-- Exercise 13.3.2: the family of normal distributions with parameter set `L ⊆ ℝ × (0, ∞)` is
tight if and only if the parameter set `L` is bounded. -/
theorem isTightMeasureSet_gaussianReal_image_iff_isBounded
    (L : Set (ℝ × Set.Ioi (0 : ℝ≥0))) :
    IsTightMeasureSet ((fun p ↦ gaussianReal p.1 p.2) '' L) ↔
      Bornology.IsBounded L := sorry

/-! ### Definition_13_3 (from Items/Chap13) -/
universe u

open MeasureTheory Measure

variable {α : Type u} [TopologicalSpace α] [MeasurableSpace α]
variable {μ : Measure α}

/- Definition 13.3 (1): on a Borel space, the textbook "Borel measure" condition is expressed by
the canonical owner predicate `IsLocallyFiniteMeasure`. -/
recall IsLocallyFiniteMeasure

/- Definition 13.3 (2): inner regularity is the canonical owner predicate
`InnerRegular`. -/
recall InnerRegular

/- Definition 13.3 (3): outer regularity is the canonical owner predicate
`OuterRegular`. -/
recall OuterRegular

/-- Definition 13.3 (4): for measures on the Borel `σ`-algebra, the textbook notion "μ is
regular" means that `μ` is `σ`-finite and both inner regular and outer regular. -/
def IsRegularMeasure (μ : Measure α) : Prop :=
  SigmaFinite μ ∧ InnerRegular μ ∧ OuterRegular μ

/-- Definition 13.3 (5): for measures on the Borel `σ`-algebra, the textbook notion of a Radon
measure means that `μ` is `σ`-finite, inner regular, and locally finite. -/
def IsRadonMeasure (μ : Measure α) : Prop :=
  SigmaFinite μ ∧ InnerRegular μ ∧ IsLocallyFiniteMeasure μ

namespace IsRegularMeasure

theorem of_owner (μ : Measure α) [SigmaFinite μ] [InnerRegular μ] [OuterRegular μ] :
    IsRegularMeasure μ :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem sigmaFinite (hμ : IsRegularMeasure μ) : SigmaFinite μ := by
  rcases hμ with ⟨hσ, -, -⟩
  exact hσ

theorem innerRegular (hμ : IsRegularMeasure μ) : InnerRegular μ := by
  rcases hμ with ⟨-, hinner, -⟩
  exact hinner

theorem outerRegular (hμ : IsRegularMeasure μ) : OuterRegular μ := by
  rcases hμ with ⟨-, -, houter⟩
  exact houter

end IsRegularMeasure

namespace IsRadonMeasure

theorem of_owner (μ : Measure α) [SigmaFinite μ] [InnerRegular μ]
    [IsLocallyFiniteMeasure μ] :
    IsRadonMeasure μ :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem sigmaFinite (hμ : IsRadonMeasure μ) : SigmaFinite μ := by
  rcases hμ with ⟨hσ, -, -⟩
  exact hσ

theorem innerRegular (hμ : IsRadonMeasure μ) : InnerRegular μ := by
  rcases hμ with ⟨-, hinner, -⟩
  exact hinner

theorem locallyFinite (hμ : IsRadonMeasure μ) : IsLocallyFiniteMeasure μ := by
  rcases hμ with ⟨-, -, hloc⟩
  exact hloc

end IsRadonMeasure

/- Auxiliary owner recall: mathlib also provides the bundled class `Measure.Regular μ`, which is
organized around finiteness on compact sets, outer regularity, and compact approximation of open
sets. This is not the main source-facing owner for Definition 13.3, but it remains the canonical
stronger bridge for later results. -/
recall Regular

/-! ### Exercise_13_3_3 (from Items/Chap13) -/
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

/-! ### Exercise_13_3_4 (from Items/Chap13) -/
open Filter MeasureTheory Set
open MeasureTheory.FiniteMeasure
open scoped Topology

/-- A real-valued function on `ℝ^d`, modeled as `(Fin d → ℝ) → ℝ`, belongs to the multivariate
Helly class `V_d` when it is coordinatewise monotone, right continuous from the upper orthant
`Set.Ici x` at every `x`, and bounded. -/
class IsCoordinatewiseRightContinuousMonotoneBoundedFunction {d : ℕ}
    (F : (Fin d → ℝ) → ℝ) : Prop where
  right_continuous : ∀ x : Fin d → ℝ, ContinuousWithinAt F (Set.Ici x) x
  monotone : Monotone F
  bounded : ∃ C : ℝ, ∀ x : Fin d → ℝ, ‖F x‖ ≤ C

/-- Constant functions on `ℝ^d` belong to the multivariate Helly class `V_d`. -/
instance instIsCoordinatewiseRightContinuousMonotoneBoundedFunctionConst {d : ℕ} (c : ℝ) :
    IsCoordinatewiseRightContinuousMonotoneBoundedFunction (fun _ : Fin d → ℝ ↦ c) := sorry

/-- A subsequence `u ∘ φ` converges to `F` in the multivariate Helly sense if `φ` is strictly
increasing, the limit function `F` again belongs to `V_d`, and the subsequence converges pointwise
at every continuity point of `F`. -/
class IsHellySubsequenceLimitInRd {d : ℕ}
    (u : ℕ → (Fin d → ℝ) → ℝ) (φ : ℕ → ℕ) (F : (Fin d → ℝ) → ℝ) : Prop where
  strictMono : StrictMono φ
  limit_mem : IsCoordinatewiseRightContinuousMonotoneBoundedFunction F
  tendsto_at_continuity_points :
    ∀ ⦃x : Fin d → ℝ⦄, ContinuousAt F x →
      Tendsto (fun k ↦ u (φ k) x) atTop (𝓝 (F x))

-- Proof sketch: use the multidimensional Helly diagonal extraction on a countable dense subset of
-- `ℝ^d`, define the limit by the upper-orthant envelope of the pointwise subsequential limits, and
-- then use coordinatewise monotonicity together with right continuity to upgrade convergence to
-- every continuity point of the limit function.
/-- Exercise 13.3.4 (1): Item (i). Helly's theorem remains valid for the multivariate class `V_d`
of coordinatewise monotone, bounded, right-continuous functions on `ℝ^d`. -/
theorem exists_helly_subsequence_tendsto_at_continuity_points_in_Rd
    (d : ℕ) (u : ℕ → (Fin d → ℝ) → ℝ)
    (hV : ∀ n : ℕ, IsCoordinatewiseRightContinuousMonotoneBoundedFunction (u n))
    (h_uniform : ∃ C : ℝ, ∀ n (x : Fin d → ℝ), ‖u n x‖ ≤ C) :
    ∃ φ : ℕ → ℕ, ∃ F : (Fin d → ℝ) → ℝ, IsHellySubsequenceLimitInRd u φ F := sorry

-- Proof sketch: identify each subprobability finite measure on `ℝ^d` with its lower-orthant
-- distribution function, apply the multidimensional Helly theorem from part (1) to obtain
-- subsequential weak limits, and use the standard Polish-space converse on `ℝ^d` to recover
-- tightness from weak relative sequential compactness.
/-- Exercise 13.3.4 (2): Item (ii). Prohorov's theorem holds on `ℝ^d`, modeled as `Fin d → ℝ`, so
for subprobability finite measures tightness is equivalent to weak relative sequential
compactness. -/
theorem prohorov_theorem_iff_tight_in_Rd
    (d : ℕ) (ℱ : Set (FiniteMeasure (Fin d → ℝ)))
    (hℱ : ∀ μ ∈ ℱ, μ.mass ≤ 1) :
    IsTightMeasureSet (((↑) : FiniteMeasure (Fin d → ℝ) → Measure (Fin d → ℝ)) '' ℱ) ↔
      (∀ μs : ℕ → FiniteMeasure (Fin d → ℝ), (∀ n, μs n ∈ ℱ) →
        ∃ μ : FiniteMeasure (Fin d → ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (μs ∘ φ) atTop (𝓝 μ)) := by
  constructor
  · exact isWeaklyRelativelySequentiallyCompactFamily_of_isTightMeasureSet ℱ hℱ
  · exact isTightMeasureSet_of_isWeaklyRelativelySequentiallyCompactFamily ℱ hℱ
