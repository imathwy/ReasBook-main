module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.IntermediateValue

public section

open MeasureTheory

open Set Filter Function

/-- Helper for Definition 57.1: the CDF of an atomless probability measure on `ℝ` is
continuous. -/
private lemma continuous_cdf_of_measure_singleton_eq_zero (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) :
    Continuous (ProbabilityTheory.cdf μ) := by
  -- Vanishing singleton mass says that the left limit has no jump at any point.
  rw [continuous_iff_continuousAt]
  intro x
  have hzero : ENNReal.ofReal
      (ProbabilityTheory.cdf μ x - leftLim (ProbabilityTheory.cdf μ) x) = 0 := by
    rw [← StieltjesFunction.measure_singleton, ProbabilityTheory.measure_cdf]
    exact hμ x
  have hjump : ProbabilityTheory.cdf μ x - leftLim (ProbabilityTheory.cdf μ) x ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp hzero
  have hleft : leftLim (ProbabilityTheory.cdf μ) x = ProbabilityTheory.cdf μ x := by
    apply le_antisymm
    · exact (ProbabilityTheory.monotone_cdf μ).leftLim_le le_rfl
    · linarith
  -- Combine left continuity from the jump computation with the built-in right continuity.
  exact continuousAt_iff_continuous_left'_right'.mpr
    ⟨(ProbabilityTheory.monotone_cdf μ).continuousWithinAt_Iio_iff_leftLim_eq.mpr hleft,
      ((ProbabilityTheory.cdf μ).right_continuous x).mono Ioi_subset_Ici_self⟩

namespace MeasureTheory.Measure

/-- Helper for Definition 57.1: a finite atomless measure on `ℝ` has a closed initial
interval carrying half of its total mass. -/
private lemma exists_measure_Iic_eq_half (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] :
    ∃ c : ℝ, μ (Iic c) = μ univ / 2 := by
  -- The zero measure is bisected by every initial interval.
  by_cases hμ : μ = 0
  · use 0
    simp only [hμ, Measure.coe_zero, Pi.zero_apply, ENNReal.zero_div]
  -- Normalize the nonzero finite measure and apply the intermediate value theorem to its CDF.
  letI : NeZero μ := ⟨hμ⟩
  let ν : Measure ℝ := (μ univ)⁻¹ • μ
  have hν_singleton : ∀ x, ν {x} = 0 := by
    intro x
    simp only [ν, Measure.smul_apply, smul_eq_mul, measure_singleton, mul_zero]
  have hν_continuous : Continuous (ProbabilityTheory.cdf ν) :=
    continuous_cdf_of_measure_singleton_eq_zero ν hν_singleton
  have hν_atBot : ProbabilityTheory.cdf ν ≤ᶠ[atBot] fun _ ↦ (1 / 2 : ℝ) :=
    ((ProbabilityTheory.tendsto_cdf_atBot ν).eventually_lt_const (by norm_num)).mono
      fun _ hx ↦ hx.le
  have hν_atTop : (fun _ ↦ (1 / 2 : ℝ)) ≤ᶠ[atTop] ProbabilityTheory.cdf ν :=
    ((ProbabilityTheory.tendsto_cdf_atTop ν).eventually_const_lt (by norm_num)).mono
      fun _ hx ↦ hx.le
  obtain ⟨c, hc⟩ := intermediate_value_univ₂_eventually₂ hν_continuous continuous_const
    hν_atBot hν_atTop
  have hscaled : (μ univ)⁻¹ * μ (Iic c) = ENNReal.ofReal (1 / 2 : ℝ) := by
    calc
      (μ univ)⁻¹ * μ (Iic c) = ν (Iic c) := by
        rfl
      _ = ENNReal.ofReal (ProbabilityTheory.cdf ν c) :=
        (ProbabilityTheory.ofReal_cdf ν c).symm
      _ = ENNReal.ofReal (1 / 2 : ℝ) := by rw [hc]
  use c
  -- Cancel the normalization factor and rewrite the real half as an `ENNReal` division.
  calc
    μ (Iic c) = μ univ * ((μ univ)⁻¹ * μ (Iic c)) := by
      symm
      exact ENNReal.mul_inv_cancel_left (Measure.measure_univ_ne_zero.mpr hμ)
        (measure_ne_top μ univ)
    _ = μ univ * ENNReal.ofReal (1 / 2 : ℝ) := by rw [hscaled]
    _ = μ univ / 2 := by norm_num [ENNReal.ofReal_div_of_pos, div_eq_mul_inv]

end MeasureTheory.Measure

/-- Helper for Definition 57.1: every level set of a Euclidean coordinate has zero
Lebesgue measure. -/
private lemma volume_coordinateFiber_eq_zero {ι : Type*} [Fintype ι] (i : ι) (a : ℝ) :
    volume {x : EuclideanSpace ℝ ι | x i = a} = 0 := by
  -- Pull the coordinate fiber back to the corresponding product-measure hyperplane.
  have hfiber : MeasurableSet {x : EuclideanSpace ℝ ι | x i = a} :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : ι ↦ ℝ) i).measurable
      (measurableSet_singleton a)
  calc
    volume {x : EuclideanSpace ℝ ι | x i = a} =
        volume ((fun x : ι → ℝ ↦ WithLp.toLp 2 x) ⁻¹'
          {x : EuclideanSpace ℝ ι | x i = a}) :=
      ((PiLp.volume_preserving_toLp ι).measure_preimage hfiber.nullMeasurableSet).symm
    _ = volume {x : ι → ℝ | x i = a} := by rfl
    _ = 0 := Measure.pi_hyperplane (fun _ : ι ↦ (volume : Measure ℝ)) i a

/-- Helper for Definition 57.1: projecting restricted Euclidean volume onto a coordinate
produces an atomless measure. -/
private lemma nullSingletonClass_map_apply_restrict_volume {ι : Type*} [Fintype ι]
    (A : Set (EuclideanSpace ℝ ι)) (i : ι) :
    NullSingletonClass ((volume.restrict A).map fun x ↦ x i) := by
  -- Evaluate the pushforward on a singleton and dominate its restricted fiber by the full fiber.
  constructor
  intro a
  have hcoord : Measurable (fun x : EuclideanSpace ℝ ι ↦ x i) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : ι ↦ ℝ) i).measurable
  have hfiber : MeasurableSet {x : EuclideanSpace ℝ ι | x i = a} :=
    hcoord (measurableSet_singleton a)
  have hpreimage : (fun x : EuclideanSpace ℝ ι ↦ x i) ⁻¹' {a} =
      {x : EuclideanSpace ℝ ι | x i = a} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq]
  rw [Measure.map_apply hcoord (measurableSet_singleton a), hpreimage,
    Measure.restrict_apply hfiber]
  exact measure_mono_null inter_subset_left (volume_coordinateFiber_eq_zero i a)

/-- Helper for Definition 57.1: a bounded Euclidean set is bisected by a half-space
defined by any chosen coordinate. -/
private lemma existsCoordinateHalfspaceBisectsVolume {ι : Type*} [Fintype ι]
    (A : Set (EuclideanSpace ℝ ι)) (i : ι) (hA_bounded : Bornology.IsBounded A) :
    ∃ c : ℝ, volume (A ∩ {x | x i ≤ c}) = volume A / 2 := by
  -- Restriction to the bounded set and then coordinate projection both have finite mass.
  have hfinite : (volume.restrict A) univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact hA_bounded.measure_lt_top
  letI : IsFiniteMeasure (volume.restrict A) := ⟨hfinite⟩
  letI : IsFiniteMeasure ((volume.restrict A).map fun x ↦ x i) :=
    Measure.isFiniteMeasure_map (volume.restrict A) (fun x ↦ x i)
  letI : NullSingletonClass ((volume.restrict A).map fun x ↦ x i) :=
    nullSingletonClass_map_apply_restrict_volume A i
  obtain ⟨c, hc⟩ := Measure.exists_measure_Iic_eq_half
    ((volume.restrict A).map fun x ↦ x i)
  use c
  have hcoord : Measurable (fun x : EuclideanSpace ℝ ι ↦ x i) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : ι ↦ ℝ) i).measurable
  have hhalfspace : MeasurableSet {x : EuclideanSpace ℝ ι | x i ≤ c} :=
    hcoord measurableSet_Iic
  -- Rewrite the one-dimensional initial interval back as the desired coordinate half-space.
  calc
    volume (A ∩ {x | x i ≤ c}) = (volume.restrict A) {x | x i ≤ c} := by
      rw [Measure.restrict_apply hhalfspace, inter_comm]
    _ = ((volume.restrict A).map fun x ↦ x i) (Iic c) := by
      rw [Measure.map_apply hcoord measurableSet_Iic]
      rfl
    _ = ((volume.restrict A).map fun x ↦ x i) univ / 2 := hc
    _ = volume A / 2 := by
      rw [Measure.map_apply hcoord MeasurableSet.univ, preimage_univ,
        Measure.restrict_apply_univ]

/-- Definition 57.1: Every bounded measurable region in the plane has an affine line
that bisects its area. The witnesses `v` and `c` describe the line
`{x | inner ℝ v x = c}` and one of its closed half-planes. -/
theorem existsLineBisectsArea (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA_measurable : MeasurableSet A) (hA_bounded : Bornology.IsBounded A) :
    ∃ v : EuclideanSpace ℝ (Fin 2), ∃ c : ℝ,
      ‖v‖ = 1 ∧ volume (A ∩ {x | inner ℝ v x ≤ c}) = volume A / 2 := by
  -- Bisect with the second coordinate and express that coordinate as a unit-normal inner product.
  obtain ⟨c, hc⟩ := existsCoordinateHalfspaceBisectsVolume A 1 hA_bounded
  use EuclideanSpace.single 1 1, c
  constructor
  · simp only [PiLp.norm_single, norm_one]
  · simpa only [EuclideanSpace.inner_single_left, RCLike.conj_ofReal, map_one, one_mul] using hc

/-- A bounded measurable planar region can be bisected by a horizontal line. -/
theorem existsHorizontalLineBisectsArea (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA_measurable : MeasurableSet A) (hA_bounded : Bornology.IsBounded A) :
    ∃ c : ℝ, volume (A ∩ {x | x 1 ≤ c}) = volume A / 2 := by
  -- The horizontal companion is the second-coordinate specialization of the same cut.
  exact existsCoordinateHalfspaceBisectsVolume A 1 hA_bounded
