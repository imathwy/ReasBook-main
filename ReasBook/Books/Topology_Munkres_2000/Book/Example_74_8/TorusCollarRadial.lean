module

public import Topology_Munkres_2000.Book.Example_74_8.CollarGeometry
public import Topology_Munkres_2000.Book.Example_74_8.TorusFundamentalSquare
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

public section

open Set

namespace ProjectivePlaneTorus

noncomputable section

/-- Helper for Example 74.8: the square gauge of a boundary direction is the product norm
of its scaled torus coordinates. -/
noncomputable def torusBoundaryGauge
    (point : DiscBoundaryGluing.BoundaryCircle) : ℝ :=
  ‖torusModelCoordinates (point : ModelPlane)‖

/-- Helper for Example 74.8: the boundary gauge is the norm of the model coordinates it
packages. -/
lemma torusBoundaryGauge_eq_norm
    (point : DiscBoundaryGluing.BoundaryCircle) :
    torusBoundaryGauge point =
      ‖torusModelCoordinates (point : ModelPlane)‖ := by
  -- Expose the gauge's owner-level formula for downstream geometric estimates.
  rfl

/-- Helper for Example 74.8: the outer scale is the factor taking a boundary direction to
the centered boundary of the fundamental square. -/
noncomputable def torusOuterScale
    (point : DiscBoundaryGluing.BoundaryCircle) : ℝ :=
  (1 / 2 : ℝ) / torusBoundaryGauge point

/-- Helper for Example 74.8: the torus collar scale interpolates affinely from the deleted
circle to the centered boundary of the fundamental square. -/
noncomputable def torusRadialScale
    (point : DiscBoundaryGluing.BoundaryCircle) (t : unitInterval) : ℝ :=
  1 + (t : ℝ) * (torusOuterScale point - 1)

/-- Helper for Example 74.8: the inner endpoint of the torus collar has radial scale one. -/
lemma torusRadialScale_zero
    (point : DiscBoundaryGluing.BoundaryCircle) :
    torusRadialScale point 0 = 1 := by
  -- At parameter zero the affine interpolation has no radial increment.
  rw [torusRadialScale]
  norm_num

/-- Helper for Example 74.8: scaled torus coordinates commute with real scalar
multiplication. -/
lemma torusModelCoordinates_smul (scale : ℝ) (point : ModelPlane) :
    torusModelCoordinates (scale • point) =
      scale • torusModelCoordinates point := by
  -- Compute both coordinate pairs through the owner-level formula.
  rw [torusModelCoordinates_apply, torusModelCoordinates_apply]
  apply Prod.ext
  · simp only [PiLp.smul_apply, smul_eq_mul, Prod.smul_fst]
    ring
  · simp only [PiLp.smul_apply, smul_eq_mul, Prod.smul_snd]
    ring

/-- Helper for Example 74.8: the square gauge of every boundary direction is positive. -/
lemma torusBoundaryGauge_pos (point : DiscBoundaryGluing.BoundaryCircle) :
    0 < torusBoundaryGauge point := by
  -- The boundary point is nonzero, and the coordinate homeomorphism preserves nonzeroness.
  apply norm_pos_iff.mpr
  intro hcoordinates
  have hzeroCoordinates : torusModelCoordinates (0 : ModelPlane) = 0 := by
    rw [torusModelCoordinates_apply]
    norm_num
  have hpointZero : (point : ModelPlane) = 0 :=
    torusModelCoordinates.injective (hcoordinates.trans hzeroCoordinates.symm)
  have hpointNorm : ‖(point : ModelPlane)‖ = 1 / 2 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using point.property
  rw [hpointZero, norm_zero] at hpointNorm
  norm_num at hpointNorm

/-- Helper for Example 74.8: the scaled coordinates of a radius-one-half boundary point
have square gauge at most one eighth. -/
lemma torusBoundaryGauge_le_eighth
    (point : DiscBoundaryGluing.BoundaryCircle) :
    torusBoundaryGauge point ≤ (1 / 8 : ℝ) := by
  -- Each Euclidean coordinate is bounded by the Euclidean norm, and the torus chart scales
  -- both coordinates by one quarter.
  have hpointNorm : ‖(point : ModelPlane)‖ = 1 / 2 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using point.property
  have hzero : ‖(point : ModelPlane) 0‖ ≤ ‖(point : ModelPlane)‖ :=
    PiLp.norm_apply_le (point : ModelPlane) 0
  have hone : ‖(point : ModelPlane) 1‖ ≤ ‖(point : ModelPlane)‖ :=
    PiLp.norm_apply_le (point : ModelPlane) 1
  rw [torusBoundaryGauge, torusModelCoordinates_apply, Prod.norm_def]
  apply max_le
  · change ‖(1 / 4 : ℝ) * (point : ModelPlane) 0‖ ≤ 1 / 8
    calc
      ‖(1 / 4 : ℝ) * (point : ModelPlane) 0‖ =
          ‖(1 / 4 : ℝ)‖ * ‖(point : ModelPlane) 0‖ := norm_mul _ _
      _ ≤ ‖(1 / 4 : ℝ)‖ * ‖(point : ModelPlane)‖ :=
        mul_le_mul_of_nonneg_left hzero (norm_nonneg _)
      _ = 1 / 8 := by
        rw [hpointNorm]
        norm_num
  · change ‖(1 / 4 : ℝ) * (point : ModelPlane) 1‖ ≤ 1 / 8
    calc
      ‖(1 / 4 : ℝ) * (point : ModelPlane) 1‖ =
          ‖(1 / 4 : ℝ)‖ * ‖(point : ModelPlane) 1‖ := norm_mul _ _
      _ ≤ ‖(1 / 4 : ℝ)‖ * ‖(point : ModelPlane)‖ :=
        mul_le_mul_of_nonneg_left hone (norm_nonneg _)
      _ = 1 / 8 := by
        rw [hpointNorm]
        norm_num

/-- Helper for Example 74.8: the outer square scale is strictly larger than the inner
deleted-circle scale. -/
lemma one_lt_torusOuterScale (point : DiscBoundaryGluing.BoundaryCircle) :
    1 < torusOuterScale point := by
  -- The positive gauge is at most one eighth, hence strictly below one half.
  rw [torusOuterScale, one_lt_div (torusBoundaryGauge_pos point)]
  have heighth_lt_half : (1 / 8 : ℝ) < 1 / 2 := by
    norm_num
  exact (torusBoundaryGauge_le_eighth point).trans_lt heighth_lt_half

/-- Helper for Example 74.8: the affine radial scale stays between its two endpoint scales. -/
lemma torusRadialScale_mem (point : DiscBoundaryGluing.BoundaryCircle)
    (t : unitInterval) :
    1 ≤ torusRadialScale point t ∧
      torusRadialScale point t ≤ torusOuterScale point := by
  have hwidth : 0 ≤ torusOuterScale point - 1 :=
    sub_nonneg.mpr (one_lt_torusOuterScale point).le
  have hlowerIncrement : 0 ≤ (t : ℝ) * (torusOuterScale point - 1) :=
    mul_nonneg (unitInterval.nonneg t) hwidth
  have hupperIncrement :
      (t : ℝ) * (torusOuterScale point - 1) ≤
        torusOuterScale point - 1 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (unitInterval.le_one t) hwidth
  -- Add one to the two affine-increment bounds.
  rw [torusRadialScale]
  constructor <;> linarith

/-- Helper for Example 74.8: for a fixed boundary direction, the affine radial scale
determines its interval parameter. -/
lemma torusRadialScale_injective
    (point : DiscBoundaryGluing.BoundaryCircle) :
    Function.Injective (torusRadialScale point) := by
  intro s t hscale
  -- Cancel the strictly positive width of the affine scale interval.
  apply Subtype.ext
  rw [torusRadialScale, torusRadialScale] at hscale
  have hwidth : 0 < torusOuterScale point - 1 :=
    sub_pos.mpr (one_lt_torusOuterScale point)
  nlinarith

/-- Helper for Example 74.8: the centered coordinates along the radial collar stay in the
centered unit square. -/
lemma torusRadialCoordinates_mem (point : DiscBoundaryGluing.BoundaryCircle)
    (t : unitInterval) :
    (torusModelCoordinates
        (torusRadialScale point t • (point : ModelPlane))).1 ∈
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ∧
      (torusModelCoordinates
        (torusRadialScale point t • (point : ModelPlane))).2 ∈
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  have hscale := torusRadialScale_mem point t
  have hscaleNonneg : 0 ≤ torusRadialScale point t := zero_le_one.trans hscale.1
  have hgaugeNonneg : 0 ≤ torusBoundaryGauge point :=
    (torusBoundaryGauge_pos point).le
  have hgaugeNe : torusBoundaryGauge point ≠ 0 :=
    ne_of_gt (torusBoundaryGauge_pos point)
  have hcoordinateNorm :
      ‖torusModelCoordinates
          (torusRadialScale point t • (point : ModelPlane))‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖torusModelCoordinates
          (torusRadialScale point t • (point : ModelPlane))‖ =
          ‖torusRadialScale point t •
            torusModelCoordinates (point : ModelPlane)‖ := by
        rw [torusModelCoordinates_smul]
      _ = torusRadialScale point t * torusBoundaryGauge point := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscaleNonneg,
          torusBoundaryGauge]
      _ ≤ torusOuterScale point * torusBoundaryGauge point :=
        mul_le_mul_of_nonneg_right hscale.2 hgaugeNonneg
      _ = (1 / 2 : ℝ) := by
        rw [torusOuterScale, div_mul_cancel₀ (1 / 2 : ℝ) hgaugeNe]
  have hfirstAbs :
      |(torusModelCoordinates
          (torusRadialScale point t • (point : ModelPlane))).1| ≤ (1 / 2 : ℝ) := by
    rw [← Real.norm_eq_abs]
    exact (norm_fst_le _).trans hcoordinateNorm
  have hsecondAbs :
      |(torusModelCoordinates
          (torusRadialScale point t • (point : ModelPlane))).2| ≤ (1 / 2 : ℝ) := by
    rw [← Real.norm_eq_abs]
    exact (norm_snd_le _).trans hcoordinateNorm
  -- Absolute-value bounds are precisely membership in the centered coordinate intervals.
  exact ⟨⟨(abs_le.mp hfirstAbs).1, (abs_le.mp hfirstAbs).2⟩,
    ⟨(abs_le.mp hsecondAbs).1, (abs_le.mp hsecondAbs).2⟩⟩

/-- Helper for Example 74.8: package the radial centered coordinates as a point of the unit
fundamental square. -/
noncomputable def torusRadialSquarePoint
    (point : DiscBoundaryGluing.BoundaryCircle) (t : unitInterval) :
    unitInterval × unitInterval :=
  (Set.projIcc 0 1 zero_le_one
      ((torusModelCoordinates
        (torusRadialScale point t • (point : ModelPlane))).1 + 1 / 2),
    Set.projIcc 0 1 zero_le_one
      ((torusModelCoordinates
        (torusRadialScale point t • (point : ModelPlane))).2 + 1 / 2))

/-- Helper for Example 74.8: the radial square point is obtained by translating its two
centered model coordinates into the unit square. -/
lemma torusRadialSquarePoint_apply
    (point : DiscBoundaryGluing.BoundaryCircle) (t : unitInterval) :
    torusRadialSquarePoint point t =
      (Set.projIcc 0 1 zero_le_one
          ((torusModelCoordinates
            (torusRadialScale point t • (point : ModelPlane))).1 + 1 / 2),
        Set.projIcc 0 1 zero_le_one
          ((torusModelCoordinates
            (torusRadialScale point t • (point : ModelPlane))).2 + 1 / 2)) := by
  -- This directed computation theorem avoids unfolding the packaged point downstream.
  rfl

/-- Helper for Example 74.8: the radial square point has the intended model-plane value and
lies in the centered fundamental-square complement. -/
lemma torusRadialSquarePoint_spec
    (point : DiscBoundaryGluing.BoundaryCircle) (t : unitInterval) :
    torusFundamentalModelPoint (torusRadialSquarePoint point t) =
        torusRadialScale point t • (point : ModelPlane) ∧
      torusRadialSquarePoint point t ∈ TorusFundamentalComplementSource := by
  have hcoordinates := torusRadialCoordinates_mem point t
  have hfirstMem :
      (torusModelCoordinates
          (torusRadialScale point t • (point : ModelPlane))).1 + 1 / 2 ∈
        Set.Icc (0 : ℝ) 1 := by
    have hlower : 0 ≤
        (torusModelCoordinates
          (torusRadialScale point t • (point : ModelPlane))).1 + 1 / 2 := by
      linarith [hcoordinates.1.1]
    have hupper :
        (torusModelCoordinates
          (torusRadialScale point t • (point : ModelPlane))).1 + 1 / 2 ≤ 1 := by
      linarith [hcoordinates.1.2]
    exact ⟨hlower, hupper⟩
  have hsecondMem :
      (torusModelCoordinates
          (torusRadialScale point t • (point : ModelPlane))).2 + 1 / 2 ∈
        Set.Icc (0 : ℝ) 1 := by
    have hlower : 0 ≤
        (torusModelCoordinates
          (torusRadialScale point t • (point : ModelPlane))).2 + 1 / 2 := by
      linarith [hcoordinates.2.1]
    have hupper :
        (torusModelCoordinates
          (torusRadialScale point t • (point : ModelPlane))).2 + 1 / 2 ≤ 1 := by
      linarith [hcoordinates.2.2]
    exact ⟨hlower, hupper⟩
  have hmodel :
      torusFundamentalModelPoint (torusRadialSquarePoint point t) =
        torusRadialScale point t • (point : ModelPlane) := by
    -- Projecting is inert because both translated coordinates already lie in the interval.
    apply torusModelCoordinates.injective
    rw [torusFundamentalModelPoint_coordinates]
    apply Prod.ext
    · rw [torusRadialSquarePoint, Set.projIcc_of_mem zero_le_one hfirstMem]
      dsimp only
      ring
    · rw [torusRadialSquarePoint, Set.projIcc_of_mem zero_le_one hsecondMem]
      dsimp only
      ring
  refine ⟨hmodel, ?_⟩
  -- The scale is at least one, so the radial point remains outside the deleted open disc.
  rw [torusFundamentalComplement_iff_norm, hmodel, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans (torusRadialScale_mem point t).1)]
  have hpointNorm : ‖(point : ModelPlane)‖ = 1 / 2 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using point.property
  rw [hpointNorm]
  nlinarith [(torusRadialScale_mem point t).1]

/-- Helper for Example 74.8: the boundary-circle cylinder maps into the centered square
annulus through the radial square point. -/
noncomputable def torusSquareAnnulusMap :
    DiscBoundaryGluing.BoundaryCircle × unitInterval →
      TorusFundamentalComplementSource :=
  fun point ↦ ⟨torusRadialSquarePoint point.1 point.2,
    (torusRadialSquarePoint_spec point.1 point.2).2⟩

/-- Helper for Example 74.8: the actual-circle radial presentation of the centered square
annulus is injective. -/
lemma torusSquareAnnulusMap_injective :
    Function.Injective torusSquareAnnulusMap := by
  intro x y hxy
  have hsquarePoint : torusRadialSquarePoint x.1 x.2 =
      torusRadialSquarePoint y.1 y.2 := congrArg Subtype.val hxy
  have hambient :
      torusRadialScale x.1 x.2 • (x.1 : ModelPlane) =
        torusRadialScale y.1 y.2 • (y.1 : ModelPlane) := by
    calc
      torusRadialScale x.1 x.2 • (x.1 : ModelPlane) =
          torusFundamentalModelPoint (torusRadialSquarePoint x.1 x.2) :=
        (torusRadialSquarePoint_spec x.1 x.2).1.symm
      _ = torusFundamentalModelPoint (torusRadialSquarePoint y.1 y.2) :=
        congrArg torusFundamentalModelPoint hsquarePoint
      _ = torusRadialScale y.1 y.2 • (y.1 : ModelPlane) :=
        (torusRadialSquarePoint_spec y.1 y.2).1
  have hxscaleNonneg : 0 ≤ torusRadialScale x.1 x.2 :=
    zero_le_one.trans (torusRadialScale_mem x.1 x.2).1
  have hyscaleNonneg : 0 ≤ torusRadialScale y.1 y.2 :=
    zero_le_one.trans (torusRadialScale_mem y.1 y.2).1
  have hxnorm : ‖(x.1 : ModelPlane)‖ = 1 / 2 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.1.property
  have hynorm : ‖(y.1 : ModelPlane)‖ = 1 / 2 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using y.1.property
  have hscale : torusRadialScale x.1 x.2 = torusRadialScale y.1 y.2 := by
    have hnorm := congrArg norm hambient
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hxscaleNonneg, abs_of_nonneg hyscaleNonneg,
      hxnorm, hynorm] at hnorm
    nlinarith
  have hscaleNe : torusRadialScale y.1 y.2 ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (torusRadialScale_mem y.1 y.2).1)
  have hdirectionAmbient : (x.1 : ModelPlane) = (y.1 : ModelPlane) := by
    apply smul_right_injective ModelPlane hscaleNe
    calc
      torusRadialScale y.1 y.2 • (x.1 : ModelPlane) =
          torusRadialScale x.1 x.2 • (x.1 : ModelPlane) := by
        rw [hscale]
      _ = torusRadialScale y.1 y.2 • (y.1 : ModelPlane) := hambient
  have hdirection : x.1 = y.1 := Subtype.ext hdirectionAmbient
  have hparameter : x.2 = y.2 := by
    apply torusRadialScale_injective y.1
    simpa only [hdirection] using hscale
  exact Prod.ext hdirection hparameter

/-- Helper for Example 74.8: every point of the centered square annulus has a boundary
direction and an affine radial parameter that reconstruct its model-plane representative. -/
lemma exists_torusRadialParameters (target : TorusFundamentalComplementSource) :
    ∃ point : DiscBoundaryGluing.BoundaryCircle, ∃ t : unitInterval,
      torusRadialScale point t • (point : ModelPlane) =
        torusFundamentalModelPoint target.1 := by
  let vector : ModelPlane := torusFundamentalModelPoint target.1
  let radius : ℝ := ‖vector‖
  have hradiusLower : (1 / 2 : ℝ) ≤ radius := by
    exact (torusFundamentalComplement_iff_norm target.1).mp target.2
  have hhalfPos : (0 : ℝ) < 1 / 2 := by
    norm_num
  have hradiusPos : 0 < radius := hhalfPos.trans_le hradiusLower
  let directionScale : ℝ := (1 / 2 : ℝ) / radius
  have hdirectionScalePos : 0 < directionScale := div_pos hhalfPos hradiusPos
  have hdirectionNorm : ‖directionScale • vector‖ = (1 / 2 : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hdirectionScalePos]
    dsimp only [directionScale, radius]
    exact div_mul_cancel₀ (1 / 2 : ℝ) (ne_of_gt hradiusPos)
  have hdirectionMem : directionScale • vector ∈
      DiscBoundaryGluing.BoundaryCircle := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hdirectionNorm
  let point : DiscBoundaryGluing.BoundaryCircle :=
    ⟨directionScale • vector, hdirectionMem⟩
  have hcoordinateNorm : ‖torusModelCoordinates vector‖ ≤ (1 / 2 : ℝ) := by
    exact torusFundamentalModelPoint_coordinateNorm_le_half target.1
  have hgauge : torusBoundaryGauge point =
      directionScale * ‖torusModelCoordinates vector‖ := by
    rw [torusBoundaryGauge, torusModelCoordinates_smul, norm_smul,
      Real.norm_eq_abs, abs_of_pos hdirectionScalePos]
  have htargetScaleLower : 1 ≤ 2 * radius := by
    linarith
  have htargetScaleUpper : 2 * radius ≤ torusOuterScale point := by
    rw [torusOuterScale, le_div_iff₀ (torusBoundaryGauge_pos point)]
    calc
      2 * radius * torusBoundaryGauge point =
          ‖torusModelCoordinates vector‖ := by
        rw [hgauge]
        dsimp only [directionScale]
        field_simp [ne_of_gt hradiusPos]
      _ ≤ 1 / 2 := hcoordinateNorm
  have hwidthPos : 0 < torusOuterScale point - 1 :=
    sub_pos.mpr (one_lt_torusOuterScale point)
  have hparameterNonneg :
      0 ≤ (2 * radius - 1) / (torusOuterScale point - 1) :=
    div_nonneg (sub_nonneg.mpr htargetScaleLower) hwidthPos.le
  have hparameterLeOne :
      (2 * radius - 1) / (torusOuterScale point - 1) ≤ 1 := by
    rw [div_le_one hwidthPos]
    linarith
  have hparameterMem :
      (2 * radius - 1) / (torusOuterScale point - 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hparameterNonneg, hparameterLeOne⟩
  let t : unitInterval :=
    ⟨(2 * radius - 1) / (torusOuterScale point - 1), hparameterMem⟩
  have hscale : torusRadialScale point t = 2 * radius := by
    rw [torusRadialScale]
    dsimp only [t]
    field_simp [ne_of_gt hwidthPos]
    ring
  refine ⟨point, t, ?_⟩
  -- The chosen radius cancels the normalized direction scale.
  rw [hscale]
  change (2 * radius) • (directionScale • vector) = vector
  rw [smul_smul]
  dsimp only [directionScale]
  have hradiusNe : radius ≠ 0 := ne_of_gt hradiusPos
  field_simp [hradiusNe]
  simp only [one_smul]

/-- Helper for Example 74.8: coercing the radial annulus map recovers its square point. -/
lemma torusSquareAnnulusMap_coe
    (point : DiscBoundaryGluing.BoundaryCircle × unitInterval) :
    (torusSquareAnnulusMap point : unitInterval × unitInterval) =
      torusRadialSquarePoint point.1 point.2 := by
  -- The codomain subtype packages exactly the landing proof from the square-point spec.
  rfl

/-- Helper for Example 74.8: the actual-circle radial presentation covers the centered
square annulus. -/
lemma torusSquareAnnulusMap_surjective :
    Function.Surjective torusSquareAnnulusMap := by
  intro target
  obtain ⟨point, t, hreconstruct⟩ := exists_torusRadialParameters target
  refine ⟨(point, t), ?_⟩
  -- Injectivity of centered model representatives turns reconstruction into square equality.
  apply Subtype.ext
  apply torusFundamentalModelPoint_injective
  rw [torusSquareAnnulusMap_coe, (torusRadialSquarePoint_spec point t).1]
  exact hreconstruct

/-- Helper for Example 74.8: the actual-circle radial presentation is a bijection onto the
centered square annulus. -/
lemma torusSquareAnnulusMap_bijective :
    Function.Bijective torusSquareAnnulusMap := by
  -- Combine the direction-radius uniqueness and the explicit radial reconstruction.
  exact ⟨torusSquareAnnulusMap_injective, torusSquareAnnulusMap_surjective⟩

/-- Helper for Example 74.8: the square gauge varies continuously with the boundary
direction. -/
lemma continuous_torusBoundaryGauge : Continuous torusBoundaryGauge := by
  -- Compose the coordinate homeomorphism with subtype inclusion and the norm.
  exact continuous_norm.comp
    (torusModelCoordinates.continuous.comp continuous_subtype_val)

/-- Helper for Example 74.8: the outer radial scale varies continuously with the boundary
direction. -/
lemma continuous_torusOuterScale : Continuous torusOuterScale := by
  -- Division is continuous because the square gauge is everywhere positive.
  apply continuous_const.div continuous_torusBoundaryGauge
  intro point
  exact ne_of_gt (torusBoundaryGauge_pos point)

/-- Helper for Example 74.8: the affine radial scale is continuous on the boundary
cylinder. -/
lemma continuous_torusRadialScale : Continuous
    (fun point : DiscBoundaryGluing.BoundaryCircle × unitInterval ↦
      torusRadialScale point.1 point.2) := by
  -- The scale is an affine expression in the interval parameter and outer scale.
  exact continuous_const.add
    ((continuous_subtype_val.comp continuous_snd).mul
      ((continuous_torusOuterScale.comp continuous_fst).sub continuous_const))

/-- Helper for Example 74.8: the radial square point varies continuously on the boundary
cylinder. -/
lemma continuous_torusRadialSquarePoint : Continuous
    (fun point : DiscBoundaryGluing.BoundaryCircle × unitInterval ↦
      torusRadialSquarePoint point.1 point.2) := by
  have hscaled : Continuous
      (fun point : DiscBoundaryGluing.BoundaryCircle × unitInterval ↦
        torusRadialScale point.1 point.2 • (point.1 : ModelPlane)) :=
    continuous_torusRadialScale.smul
      (continuous_subtype_val.comp continuous_fst)
  have hcoordinates : Continuous
      (fun point : DiscBoundaryGluing.BoundaryCircle × unitInterval ↦
        torusModelCoordinates
          (torusRadialScale point.1 point.2 • (point.1 : ModelPlane))) :=
    torusModelCoordinates.continuous.comp hscaled
  -- Apply the continuous interval projection separately to the two translated coordinates.
  exact (continuous_projIcc.comp
      ((continuous_fst.comp hcoordinates).add continuous_const)).prodMk
    (continuous_projIcc.comp
      ((continuous_snd.comp hcoordinates).add continuous_const))

/-- Helper for Example 74.8: the actual-circle radial presentation is continuous. -/
lemma continuous_torusSquareAnnulusMap : Continuous torusSquareAnnulusMap := by
  -- Package the continuous square point with its already proved complement certificate.
  exact Continuous.subtype_mk continuous_torusRadialSquarePoint _

/-- Helper for Example 74.8: the actual-circle radial presentation is a quotient map onto
the centered square annulus. -/
lemma torusSquareAnnulusMap_isQuotientMap :
    Topology.IsQuotientMap torusSquareAnnulusMap := by
  -- A continuous bijection from the compact boundary cylinder to this Hausdorff subtype is
  -- a quotient map.
  exact Topology.IsQuotientMap.of_surjective_continuous
    torusSquareAnnulusMap_bijective.2 continuous_torusSquareAnnulusMap

/-- Helper for Example 74.8: the interval collar maps to the actual boundary cylinder by
parameterizing its first coordinate. -/
noncomputable def torusBoundaryCylinderMap :
    CollarSquare → DiscBoundaryGluing.BoundaryCircle × unitInterval :=
  fun point ↦ (boundaryCircleParam point.1, point.2)

/-- Helper for Example 74.8: the interval-to-boundary-cylinder map is continuous. -/
lemma continuous_torusBoundaryCylinderMap :
    Continuous torusBoundaryCylinderMap := by
  -- The first component is the standard boundary quotient and the second is unchanged.
  exact (boundaryCircleParam_isQuotientMap.continuous.comp continuous_fst).prodMk
    continuous_snd

/-- Helper for Example 74.8: the interval-to-boundary-cylinder map is surjective. -/
lemma torusBoundaryCylinderMap_surjective :
    Function.Surjective torusBoundaryCylinderMap := by
  intro target
  obtain ⟨s, hs⟩ := boundaryCircleParam_isQuotientMap.surjective target.1
  refine ⟨(s, target.2), ?_⟩
  -- The chosen boundary parameter and unchanged radial coordinate recover the target pair.
  exact Prod.ext hs rfl

/-- Helper for Example 74.8: parameterizing the boundary coordinate gives a quotient
presentation of the actual boundary cylinder. -/
lemma torusBoundaryCylinderMap_isQuotientMap :
    Topology.IsQuotientMap torusBoundaryCylinderMap := by
  -- Compact-to-Hausdorff continuous surjectivity supplies quotientness without invoking a
  -- general product theorem for quotient maps.
  exact Topology.IsQuotientMap.of_surjective_continuous
    torusBoundaryCylinderMap_surjective continuous_torusBoundaryCylinderMap

/-- Helper for Example 74.8: the interval torus collar is the radial annulus presentation
precomposed with the standard boundary-circle parameterization. -/
noncomputable def torusCollarRadialMap :
    CollarSquare → TorusFundamentalComplementSource :=
  torusSquareAnnulusMap ∘ torusBoundaryCylinderMap

/-- Helper for Example 74.8: coercing the interval collar's radial image recovers the
corresponding square point. -/
lemma torusCollarRadialMap_coe (point : CollarSquare) :
    (torusCollarRadialMap point : unitInterval × unitInterval) =
      torusRadialSquarePoint (boundaryCircleParam point.1) point.2 := by
  -- Both composition stages preserve the displayed square representative.
  rfl

/-- Helper for Example 74.8: the interval torus collar is a quotient presentation of the
centered square annulus. -/
lemma torusCollarRadialMap_isQuotientMap :
    Topology.IsQuotientMap torusCollarRadialMap := by
  -- Quotient maps compose through the actual boundary-circle cylinder.
  exact torusSquareAnnulusMap_isQuotientMap.comp
    torusBoundaryCylinderMap_isQuotientMap

/-- Helper for Example 74.8: the exact fibers of the radial interval collar are equality of
radial parameters together with endpoint identification in the circle parameter. -/
lemma torusCollarRadialMap_eq_iff (x y : CollarSquare) :
    torusCollarRadialMap x = torusCollarRadialMap y ↔
      x.2 = y.2 ∧ unitInterval.endpointSetoid x.1 y.1 := by
  constructor
  · intro hxy
    have hcylinder : torusBoundaryCylinderMap x = torusBoundaryCylinderMap y :=
      torusSquareAnnulusMap_injective hxy
    have hradial : x.2 = y.2 :=
      congrArg (fun point : DiscBoundaryGluing.BoundaryCircle × unitInterval ↦
        point.2) hcylinder
    have hboundary : boundaryCircleParam x.1 = boundaryCircleParam y.1 :=
      congrArg (fun point : DiscBoundaryGluing.BoundaryCircle × unitInterval ↦
        point.1) hcylinder
    exact ⟨hradial, (boundaryCircleParam_eq_iff x.1 y.1).mp hboundary⟩
  · rintro ⟨hradial, hboundary⟩
    -- Equal boundary-circle images and equal radial parameters give equal annulus images.
    apply congrArg torusSquareAnnulusMap
    apply Prod.ext
    · exact (boundaryCircleParam_eq_iff x.1 y.1).mpr hboundary
    · exact hradial

/-- Helper for Example 74.8: the radial interval collar varies continuously in the centered
fundamental-square complement. -/
lemma continuous_torusCollarRadialMap : Continuous torusCollarRadialMap := by
  -- Continuity is part of the quotient-map interface proved above.
  exact torusCollarRadialMap_isQuotientMap.continuous

/-- Helper for Example 74.8: compose the radial square-annulus presentation with the
restricted fundamental-square quotient into the deleted-disc torus complement. -/
noncomputable def torusCollarFunction :
    CollarSquare → standardGluing.RightComplement :=
  torusFundamentalComplementMap ∘ torusCollarRadialMap

/-- Helper for Example 74.8: the torus collar function is continuous. -/
lemma continuous_torusCollarFunction : Continuous torusCollarFunction := by
  -- Compose the two already verified quotient presentations.
  exact torusFundamentalComplementMap_isQuotientMap.continuous.comp
    continuous_torusCollarRadialMap

/-- Helper for Example 74.8: the torus collar as a continuous map onto the deleted-disc
complement. -/
noncomputable def torusCollarMap :
    C(CollarSquare, standardGluing.RightComplement) :=
  ⟨torusCollarFunction, continuous_torusCollarFunction⟩

/-- Helper for Example 74.8: the torus collar's underlying torus value is represented by
its explicit radial square point. -/
lemma torusCollarMap_coe (point : CollarSquare) :
    (torusCollarMap point : UnitAddCircle × UnitAddCircle) =
      torusFundamentalMap
        (torusRadialSquarePoint (boundaryCircleParam point.1) point.2) := by
  -- Peel off one wrapper at a time, using propositional coercion lemmas at both subtype
  -- boundaries rather than asking the kernel to normalize the entire composite.
  calc
    (torusCollarMap point : UnitAddCircle × UnitAddCircle) =
        (torusFundamentalComplementMap (torusCollarRadialMap point) :
          UnitAddCircle × UnitAddCircle) := rfl
    _ = torusFundamentalMap (torusCollarRadialMap point) :=
      torusFundamentalComplementMap_coe (torusCollarRadialMap point)
    _ = torusFundamentalMap
        (torusRadialSquarePoint (boundaryCircleParam point.1) point.2) :=
      congrArg torusFundamentalMap (torusCollarRadialMap_coe point)

/-- Helper for Example 74.8: the inner torus collar edge is the attaching boundary used by
the standard deleted-disc gluing. -/
lemma torusCollarMap_inner (s : unitInterval) :
    torusCollarMap (s, 0) =
      standardGluing.rightBoundary (boundaryCircleParam s) := by
  -- Compare the underlying torus points through the fundamental-square model at scale one.
  apply Subtype.ext
  rw [torusCollarMap_coe, standardGluing.rightBoundary_coe,
    torusFundamentalMap_eq_model,
    (torusRadialSquarePoint_spec (boundaryCircleParam s) 0).1,
    torusRadialScale_zero, one_smul, standardGluing_rightChart_apply]

/-- Helper for Example 74.8: the torus collar is a quotient presentation of the deleted-disc
torus complement. -/
lemma torusCollarMap_isQuotientMap :
    Topology.IsQuotientMap torusCollarMap := by
  -- Quotientness is preserved by the composition through the centered square annulus.
  exact torusFundamentalComplementMap_isQuotientMap.comp
    torusCollarRadialMap_isQuotientMap

/-- Helper for Example 74.8: the torus collar fibers are precisely the opposite-edge
relations between their radial fundamental-square representatives. -/
lemma torusCollarMap_eq_iff (x y : CollarSquare) :
    torusCollarMap x = torusCollarMap y ↔
      TorusSquare.identified (torusCollarRadialMap x).1
        (torusCollarRadialMap y).1 := by
  -- Pass directly through the exact kernel theorem for the restricted square quotient.
  exact torusFundamentalComplementMap_eq_iff
    (torusCollarRadialMap x) (torusCollarRadialMap y)

end

end ProjectivePlaneTorus
