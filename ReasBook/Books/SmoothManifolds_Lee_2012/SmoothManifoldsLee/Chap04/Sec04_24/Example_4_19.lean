import Mathlib

open Topology
open scoped ContDiff

/-- The ambient parametrization `(sin (2t), sin t)` of the figure-eight curve in `ℝ²`. -/
noncomputable def figureEightCurveMap : ℝ → ℝ × ℝ :=
  fun t ↦ (Real.sin (2 * t), Real.sin t)

/-- Example 4.19: the figure-eight curve `β : (-π, π) → ℝ²` given by `β(t) = (sin (2t), sin t)`. -/
noncomputable def figureEightCurve : Set.Ioo (-Real.pi) Real.pi → ℝ × ℝ :=
  fun t ↦ figureEightCurveMap t

/-- The restricted figure-eight curve is obtained by evaluating the ambient parametrization on the
open interval `(-π, π)`. -/
-- Proof sketch: This is immediate from the definitions of `figureEightCurve` and
-- `figureEightCurveMap`.
theorem figureEightCurve_eq_figureEightCurveMap (t : Set.Ioo (-Real.pi) Real.pi) :
    figureEightCurve t = figureEightCurveMap t := by
  -- Both maps are defined by the same evaluation formula on the subtype.
  rfl

/-- Every point of the figure-eight curve satisfies the lemniscate equation
`x² = 4 y² (1 - y²)`. -/
-- Proof sketch: Expand the coordinates of `figureEightCurve t`, use
-- `Real.sin_two_mul`, and then simplify with `Real.cos_sq` or `Real.sin_sq_add_cos_sq`.
theorem figureEightCurve_satisfies_lemniscate_equation (t : Set.Ioo (-Real.pi) Real.pi) :
    (figureEightCurve t).1 ^ 2 = 4 * (figureEightCurve t).2 ^ 2 * (1 - (figureEightCurve t).2 ^ 2) :=
  by
  -- Rewrite the coordinates explicitly and use `sin (2t) = 2 sin t cos t`.
  change Real.sin (2 * (t : ℝ)) ^ 2 =
    4 * Real.sin (t : ℝ) ^ 2 * (1 - Real.sin (t : ℝ) ^ 2)
  rw [Real.sin_two_mul]
  -- The identity `sin² t + cos² t = 1` converts the remaining `cos² t` factor.
  nlinarith [Real.sin_sq_add_cos_sq (t : ℝ)]

/-- The ambient parametrization of the figure-eight curve is smooth. -/
-- Proof sketch: Compose the smooth function `Real.sin` with the linear map `t ↦ 2 * t` in the
-- first coordinate and with the identity in the second coordinate, then use product smoothness.
theorem figureEightCurveMap_contDiff : ContDiff ℝ ∞ figureEightCurveMap := by
  -- Each coordinate is a smooth sine composition, and the pair is smooth componentwise.
  simpa [figureEightCurveMap] using
    ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).prodMk Real.contDiff_sin)

/-- Helper for Example 4.19: the ambient figure-eight parametrization has derivative
`(2 cos (2t), cos t)` at every real parameter. -/
theorem figureEightCurveMap_hasDerivAt (t : ℝ) :
    HasDerivAt figureEightCurveMap (2 * Real.cos (2 * t), Real.cos t) t := by
  -- Differentiate each coordinate separately and combine the resulting derivatives.
  have hfst : HasDerivAt (fun s : ℝ ↦ Real.sin (s * 2)) (2 * Real.cos (2 * t)) t := by
    simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_sin (t * 2)).comp t (hasDerivAt_mul_const (2 : ℝ))
  have hsnd : HasDerivAt (fun s : ℝ ↦ Real.sin s) (Real.cos t) t := Real.hasDerivAt_sin t
  -- The derivative of the product map is the pair of coordinate derivatives.
  change HasDerivAt (fun s : ℝ ↦ (Real.sin (2 * s), Real.sin s))
    (2 * Real.cos (2 * t), Real.cos t) t
  simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hfst.prodMk hsnd

/-- The figure-eight curve is injective on the open interval `(-π, π)`. -/
-- Proof sketch: Compare second coordinates to get `sin t₁ = sin t₂`; on `(-π, π)` this leaves
-- only the equal-angle and supplementary-angle cases. The first coordinate `sin (2t)` rules out
-- the supplementary case, so the parameters are equal.
theorem figureEightCurve_injective : Function.Injective figureEightCurve := by
  intro t₁ t₂ h
  -- Equality of points gives equality of both coordinates.
  have hfst : Real.sin (2 * (t₁ : ℝ)) = Real.sin (2 * (t₂ : ℝ)) := by
    exact congrArg Prod.fst h
  have hsnd : Real.sin (t₁ : ℝ) = Real.sin (t₂ : ℝ) := by
    exact congrArg Prod.snd h
  by_cases hsin : Real.sin (t₁ : ℝ) = 0
  · -- If the second coordinate vanishes, both parameters must be `0` inside `(-π, π)`.
    have ht₁_zero : (t₁ : ℝ) = 0 :=
      (Real.sin_eq_zero_iff_of_lt_of_lt t₁.2.1 t₁.2.2).mp hsin
    have ht₂_zero : (t₂ : ℝ) = 0 := by
      refine (Real.sin_eq_zero_iff_of_lt_of_lt t₂.2.1 t₂.2.2).mp ?_
      simpa [ht₁_zero] using hsnd.symm
    exact Subtype.ext (by simpa [ht₁_zero, ht₂_zero])
  · -- Otherwise the first coordinate determines the cosine value.
    have hcos_eq : Real.cos (t₁ : ℝ) = Real.cos (t₂ : ℝ) := by
      have hmul_two := hfst
      rw [Real.sin_two_mul, Real.sin_two_mul] at hmul_two
      rw [hsnd] at hmul_two
      have hsin₂ : Real.sin (t₂ : ℝ) ≠ 0 := by
        intro hsin₂
        exact hsin (hsnd.trans hsin₂)
      have hmul : Real.sin (t₂ : ℝ) * Real.cos (t₁ : ℝ) =
          Real.sin (t₂ : ℝ) * Real.cos (t₂ : ℝ) := by
        nlinarith [hmul_two]
      have hmul' : Real.cos (t₁ : ℝ) * Real.sin (t₂ : ℝ) =
          Real.cos (t₂ : ℝ) * Real.sin (t₂ : ℝ) := by
        simpa [mul_comm] using hmul
      exact mul_right_cancel₀ hsin₂ hmul'
    have ht₁_ne_zero : (t₁ : ℝ) ≠ 0 := by
      intro ht₁_zero
      exact hsin (by simpa [ht₁_zero])
    rcases lt_or_gt_of_ne ht₁_ne_zero with ht₁_neg | ht₁_pos
    · -- Negative parameters reduce to the positive interval via the evenness of cosine.
      have hsin_neg : Real.sin (t₁ : ℝ) < 0 := Real.sin_neg_of_neg_of_neg_pi_lt ht₁_neg t₁.2.1
      have ht₂_neg : (t₂ : ℝ) < 0 := by
        by_contra ht₂_not_neg
        have ht₂_nonneg : 0 ≤ (t₂ : ℝ) := le_of_not_gt ht₂_not_neg
        have hsin_nonneg : 0 ≤ Real.sin (t₂ : ℝ) :=
          Real.sin_nonneg_of_nonneg_of_le_pi ht₂_nonneg t₂.2.2.le
        linarith [hsnd, hsin_neg]
      have hcos_neg_eq : Real.cos (-(t₁ : ℝ)) = Real.cos (-(t₂ : ℝ)) := by
        simpa [Real.cos_neg] using hcos_eq
      have hneg_eq : -(t₁ : ℝ) = -(t₂ : ℝ) :=
        Real.injOn_cos
          ⟨by linarith, by linarith [t₁.2.1]⟩
          ⟨by linarith, by linarith [t₂.2.1]⟩
          hcos_neg_eq
      exact Subtype.ext (by linarith)
    · -- Positive parameters lie in `(0, π)`, where `cos` is injective.
      have hsin_pos : 0 < Real.sin (t₁ : ℝ) := Real.sin_pos_of_pos_of_lt_pi ht₁_pos t₁.2.2
      have ht₂_pos : 0 < (t₂ : ℝ) := by
        by_contra ht₂_not_pos
        have ht₂_le : (t₂ : ℝ) ≤ 0 := le_of_not_gt ht₂_not_pos
        have hsin_nonpos : Real.sin (t₂ : ℝ) ≤ 0 :=
          Real.sin_nonpos_of_nonpos_of_neg_pi_le ht₂_le (le_of_lt t₂.2.1)
        linarith [hsnd, hsin_pos]
      have ht_eq : (t₁ : ℝ) = (t₂ : ℝ) :=
        Real.injOn_cos ⟨ht₁_pos.le, t₁.2.2.le⟩ ⟨ht₂_pos.le, t₂.2.2.le⟩ hcos_eq
      exact Subtype.ext ht_eq

/-- Helper for Example 4.19: the range of the closed-interval extension agrees with the actual
figure-eight image, because both endpoints map to the interior point `0`. -/
theorem figureEightCurve_closed_range_eq_restricted_range :
    Set.range (fun t : Set.Icc (-Real.pi) Real.pi ↦ figureEightCurveMap t) = Set.range figureEightCurve := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    by_cases hleft : (t : ℝ) = -Real.pi
    · -- The left endpoint maps to the same point as the interior parameter `0`.
      refine ⟨⟨0, by constructor <;> linarith [Real.pi_pos]⟩, ?_⟩
      simp [figureEightCurve, figureEightCurveMap, hleft, Real.sin_pi, Real.sin_two_pi]
    · by_cases hright : (t : ℝ) = Real.pi
      · -- The right endpoint also maps to the interior parameter `0`.
        refine ⟨⟨0, by constructor <;> linarith [Real.pi_pos]⟩, ?_⟩
        simp [figureEightCurve, figureEightCurveMap, hright, Real.sin_pi, Real.sin_two_pi]
      · -- Any non-endpoint of `[-π, π]` already lies in `(-π, π)`.
        have ht : (t : ℝ) ∈ Set.Ioo (-Real.pi) Real.pi := by
          constructor
          · exact lt_of_le_of_ne t.2.1 (Ne.symm hleft)
          · exact lt_of_le_of_ne t.2.2 hright
        exact ⟨⟨t, ht⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    -- Every parameter in `(-π, π)` also belongs to `[-π, π]`.
    exact ⟨⟨t, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩, rfl⟩

/-- The derivative of the ambient figure-eight parametrization does not vanish on `(-π, π)`. -/
-- Proof sketch: Compute the derivative as `(2 cos (2t), cos t)` and show these two coordinates
-- cannot vanish simultaneously for `t ∈ (-π, π)`.
theorem figureEightCurveMap_fderiv_ne_zero (t : Set.Ioo (-Real.pi) Real.pi) :
    fderiv ℝ figureEightCurveMap t ≠ 0 := by
  -- Convert the Fréchet derivative to the explicit scalar derivative vector.
  have hfderiv :
      fderiv ℝ figureEightCurveMap t =
        (1 : ℝ →L[ℝ] ℝ).smulRight (2 * Real.cos (2 * (t : ℝ)), Real.cos (t : ℝ)) := by
    simpa using (figureEightCurveMap_hasDerivAt (t : ℝ)).hasFDerivAt.fderiv
  intro hzero
  have hvec_zero : (2 * Real.cos (2 * (t : ℝ)), Real.cos (t : ℝ)) = (0, 0) := by
    have happly : (fderiv ℝ figureEightCurveMap t) 1 = 0 := by simpa [hzero]
    rw [hfderiv, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul] at happly
    simpa using happly
  have hcoord₁ : 2 * Real.cos (2 * (t : ℝ)) = 0 := congrArg Prod.fst hvec_zero
  have hcoord₂ : Real.cos (t : ℝ) = 0 := congrArg Prod.snd hvec_zero
  have hcos_zero : Real.cos (t : ℝ) = 0 := hcoord₂
  have hcos_two_zero : Real.cos (2 * (t : ℝ)) = 0 := by
    nlinarith [hcoord₁]
  have hsin_sq : Real.sin (t : ℝ) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (t : ℝ), hcos_zero]
  have hcos_two_neg : Real.cos (2 * (t : ℝ)) = -1 := by
    rw [Real.cos_two_mul]
    nlinarith [hcos_zero, hsin_sq]
  linarith [hcos_two_zero, hcos_two_neg]

/-- The image of the figure-eight curve is compact in the subspace topology of `ℝ²`. -/
-- Proof sketch: Extend the parametrization continuously to the closed interval `[-π, π]`; the
-- endpoints have the same image, so the range over `(-π, π)` is the same compact image.
theorem figureEightCurve_range_compact : IsCompact (Set.range figureEightCurve) := by
  -- The closed-interval extension has compact range as a continuous image of a compact space.
  have hclosed_cont : Continuous (fun t : Set.Icc (-Real.pi) Real.pi ↦ figureEightCurveMap t) := by
    change Continuous (figureEightCurveMap ∘ Subtype.val)
    exact figureEightCurveMap_contDiff.continuous.comp continuous_subtype_val
  have hclosed_range :
      IsCompact (Set.range (fun t : Set.Icc (-Real.pi) Real.pi ↦ figureEightCurveMap t)) :=
    isCompact_range hclosed_cont
  -- The endpoint identification transfers compactness to the actual range.
  simpa [figureEightCurve_closed_range_eq_restricted_range] using hclosed_range

/-- The figure-eight curve is not a topological embedding. -/
-- Proof sketch: If `figureEightCurve` were an embedding, its domain would be homeomorphic to the
-- compact range. That would make `(-π, π)` compact, contradicting the standard noncompactness of
-- the open interval.
theorem figureEightCurve_not_isEmbedding : ¬ IsEmbedding figureEightCurve := by
  intro hEmbedding
  -- An embedding pulls compactness of the range back to compactness of the parameter space.
  have hdomain_compact : IsCompact (Set.univ : Set (Set.Ioo (-Real.pi) Real.pi)) := by
    have hrange_compact :
        IsCompact (figureEightCurve '' (Set.univ : Set (Set.Ioo (-Real.pi) Real.pi))) := by
      simpa [Set.image_univ] using figureEightCurve_range_compact
    exact (hEmbedding.isCompact_iff (s := (Set.univ : Set (Set.Ioo (-Real.pi) Real.pi)))).mpr
      hrange_compact
  have hinterval_compact : IsCompact (Set.Ioo (-Real.pi) Real.pi : Set ℝ) := by
    have himage :
        Subtype.val '' (Set.univ : Set (Set.Ioo (-Real.pi) Real.pi)) =
          (Set.Ioo (-Real.pi) Real.pi : Set ℝ) := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
    simpa [himage] using hdomain_compact.image continuous_subtype_val
  have hinterval_closed : IsClosed (Set.Ioo (-Real.pi) Real.pi : Set ℝ) := hinterval_compact.isClosed
  have hpi_mem_closure : Real.pi ∈ closure (Set.Ioo (-Real.pi) Real.pi : Set ℝ) := by
    rw [closure_Ioo (show (-Real.pi : ℝ) ≠ Real.pi by linarith [Real.pi_pos])]
    exact Set.mem_Icc.mpr ⟨by linarith [Real.pi_pos], le_rfl⟩
  have hpi_mem_interval : Real.pi ∈ (Set.Ioo (-Real.pi) Real.pi : Set ℝ) := by
    simpa [hinterval_closed.closure_eq] using hpi_mem_closure
  exact (show Real.pi ∉ (Set.Ioo (-Real.pi) Real.pi : Set ℝ) by simp) hpi_mem_interval
