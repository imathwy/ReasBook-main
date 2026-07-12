import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»

open Filter MeasureTheory Bornology
open scoped unitInterval

noncomputable section

/-- Helper for Remark III.6-extra-7: the positive-axis keyhole opening angle used to keep the two
boundary values of `Complex.log (-z)` distinct. -/
abbrev positiveAxisKeyholeAngle (R ε : ℝ) : ℝ :=
  Real.arctan (ε / R)

/-- Helper for Remark III.6-extra-7: the upper slit-lip angle of the repaired major-arc keyhole
is the same acute opening angle `θ = arctan (ε / R)` used in the branch-cut separation. -/
abbrev positiveAxisKeyholeUpperAngle (R ε : ℝ) : ℝ :=
  positiveAxisKeyholeAngle R ε

/-- Helper for Remark III.6-extra-7: the lower slit-lip angle of the repaired major-arc keyhole is
written as `2π - θ` so the surviving circular branches pass through the negative real axis. -/
abbrev positiveAxisKeyholeLowerAngle (R ε : ℝ) : ℝ :=
  2 * Real.pi - positiveAxisKeyholeAngle R ε

/-- Helper for Remark III.6-extra-7: writing the lower slit lip as `2π - θ` is geometrically
equivalent to the old `-θ` spelling because `circleMap` is `2π`-periodic in its angle input. -/
lemma positiveAxisKeyhole_circleMap_lowerAngle_eq_old_lower
    (R ε ρ : ℝ) :
    circleMap 0 ρ (positiveAxisKeyholeLowerAngle R ε) =
      circleMap 0 ρ (-positiveAxisKeyholeAngle R ε) := by
  -- Rewrite the repaired lower angle as the old angle plus one full turn, then use the
  -- `2π`-periodicity of `sin` and `cos` on the explicit `circleMap` coordinates.
  dsimp [positiveAxisKeyholeLowerAngle, positiveAxisKeyholeAngle]
  rw [show 2 * Real.pi - Real.arctan (ε / R) = -Real.arctan (ε / R) + 2 * Real.pi by ring]
  rw [Complex.ext_iff]
  constructor
  · simp [circleMap_zero_re, Real.cos_add_two_pi]
  · simp [circleMap_zero_im, Real.sin_add_two_pi]

/-- Helper for Remark III.6-extra-7: for `0 < ε < R`, the repaired lower slit-lip angle lies
strictly above the upper slit-lip angle and still below `2π`, so the major arc between them
contains the negative real axis. -/
lemma positiveAxisKeyhole_majorArc_angle_order
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    positiveAxisKeyholeUpperAngle R ε < positiveAxisKeyholeLowerAngle R ε ∧
      positiveAxisKeyholeLowerAngle R ε < 2 * Real.pi := by
  -- Route correction: the positive-axis contour needs the complementary angular window
  -- `θ < φ < 2π - θ`, not the short principal-branch window `-θ < φ < θ`.
  have hθ :
      0 < positiveAxisKeyholeAngle R ε ∧
        positiveAxisKeyholeAngle R ε < Real.pi / 2 := by
    have hR : 0 < R := lt_trans hε hεR
    constructor
    · simpa [positiveAxisKeyholeAngle] using Real.arctan_pos.mpr (div_pos hε hR)
    · simpa [positiveAxisKeyholeAngle] using Real.arctan_lt_pi_div_two (ε / R)
  constructor
  · dsimp [positiveAxisKeyholeUpperAngle, positiveAxisKeyholeLowerAngle]
    linarith [hθ.1, Real.pi_pos]
  · dsimp [positiveAxisKeyholeLowerAngle]
    linarith [hθ.1]

/-- Helper for Remark III.6-extra-7: the negative real axis angle `π` lies in the repaired
major-arc window between the two slit-lip angles. This is the geometric bridge needed to put the
negative real point back on the contour range after the contour repair. -/
lemma positiveAxisKeyhole_pi_mem_majorArc_interval
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    (Real.pi : ℝ) ∈
      Set.uIcc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) := by
  -- The acute-angle bounds place `π` strictly between `θ` and `2π - θ`.
  have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
  rw [Set.uIcc_of_le (le_of_lt horder.1)]
  refine ⟨?_, ?_⟩
  · dsimp [positiveAxisKeyholeUpperAngle, positiveAxisKeyholeAngle]
    have hθlt : Real.arctan (ε / R) < Real.pi := by
      linarith [Real.arctan_lt_pi_div_two (ε / R), Real.pi_pos]
    linarith
  · dsimp [positiveAxisKeyholeLowerAngle]
    have hθpos :
        0 < positiveAxisKeyholeAngle R ε := by
      have hR : 0 < R := lt_trans hε hεR
      simpa [positiveAxisKeyholeAngle] using Real.arctan_pos.mpr (div_pos hε hR)
    linarith

/-- Helper for Remark III.6-extra-7: once the contour is rewritten with the repaired outer major
arc, the negative real outer point is one of its explicit geometric image points. -/
lemma positiveAxisKeyhole_negative_real_outer_point_mem_repaired_outer_arc
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    circleMap 0 R Real.pi ∈
      (fun φ : ℝ ↦ circleMap 0 R φ) ''
        Set.uIcc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) := by
  -- Route correction: the repaired outer circle should pass through angle `π`, unlike the old
  -- short arc around `0`.
  refine ⟨Real.pi, positiveAxisKeyhole_pi_mem_majorArc_interval (R := R) (ε := ε) hε hεR, rfl⟩

/-- Helper for Remark III.6-extra-7: the repaired inner major arc likewise passes through the
negative real point on the small circle. This is the inner-circle companion to the outer witness
used in the frontier repair. -/
lemma positiveAxisKeyhole_negative_real_inner_point_mem_repaired_inner_arc
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    circleMap 0 ε Real.pi ∈
      (fun φ : ℝ ↦ circleMap 0 ε φ) ''
        Set.uIcc (positiveAxisKeyholeUpperAngle R ε) (positiveAxisKeyholeLowerAngle R ε) := by
  -- The same `π`-membership witness works on the inner radius because only the radius changes.
  refine ⟨Real.pi, positiveAxisKeyhole_pi_mem_majorArc_interval (R := R) (ε := ε) hε hεR, rfl⟩

/-- Helper for Remark III.6-extra-7: the source-faithful keyhole contour for the shifted branch
`z ↦ Complex.log (-z)`. It runs down the upper lip of the positive-axis slit, once around the
small circle clockwise, back along the lower lip, and then around the large circle
anticlockwise. -/
def positiveAxisKeyhole (R ε : ℝ) :
    Path (circleMap 0 R (positiveAxisKeyholeAngle R ε))
      (circleMap 0 R (positiveAxisKeyholeAngle R ε)) :=
  let upper := positiveAxisKeyholeUpperAngle R ε
  let lower := positiveAxisKeyholeLowerAngle R ε
  let upperLip : Path (circleMap 0 R upper) (circleMap 0 ε upper) :=
    Path.segment (circleMap 0 R upper) (circleMap 0 ε upper)
  let innerArc : Path (circleMap 0 ε upper) (circleMap 0 ε lower) :=
    (Path.segment upper lower).map (continuous_circleMap 0 ε)
  let lowerLip : Path (circleMap 0 ε lower)
      (circleMap 0 R lower) :=
    Path.segment (circleMap 0 ε lower) (circleMap 0 R lower)
  let outerArc : Path (circleMap 0 R lower) (circleMap 0 R upper) :=
    (Path.segment lower upper).map (continuous_circleMap 0 R)
  ((upperLip.trans innerArc).trans lowerLip).trans outerArc

/-- Helper for Remark III.6-extra-7: unfold the explicit upper lip, inner arc, lower lip, and
outer arc that make up `positiveAxisKeyhole`. -/
theorem positiveAxisKeyhole_def (R ε : ℝ) :
    positiveAxisKeyhole R ε =
      let upper := positiveAxisKeyholeUpperAngle R ε
      let lower := positiveAxisKeyholeLowerAngle R ε
      let upperLip : Path (circleMap 0 R upper) (circleMap 0 ε upper) :=
        Path.segment (circleMap 0 R upper) (circleMap 0 ε upper)
      let innerArc : Path (circleMap 0 ε upper) (circleMap 0 ε lower) :=
        (Path.segment upper lower).map (continuous_circleMap 0 ε)
      let lowerLip : Path (circleMap 0 ε lower)
          (circleMap 0 R lower) :=
        Path.segment (circleMap 0 ε lower) (circleMap 0 R lower)
      let outerArc : Path (circleMap 0 R lower) (circleMap 0 R upper) :=
        (Path.segment lower upper).map (continuous_circleMap 0 R)
      ((upperLip.trans innerArc).trans lowerLip).trans outerArc := rfl

/-- Helper for Remark III.6-extra-7: on the first quarter-break interval, the explicit keyhole
path follows the upper slit lip with the affine reparametrization `t ↦ 8 t`. -/
lemma positive_axis_keyhole_eq_on_upper_lip (R ε : ℝ) :
    Set.EqOn (positiveAxisKeyhole R ε).extend
      (fun t ↦
        AffineMap.lineMap
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
          (8 * t))
      (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) := by
  intro t ht
  let upperAngle := positiveAxisKeyholeUpperAngle R ε
  let lowerAngle := positiveAxisKeyholeLowerAngle R ε
  let upperLip : Path (circleMap 0 R upperAngle) (circleMap 0 ε upperAngle) :=
    Path.segment (circleMap 0 R upperAngle) (circleMap 0 ε upperAngle)
  let innerArc : Path (circleMap 0 ε upperAngle) (circleMap 0 ε lowerAngle) :=
    (Path.segment upperAngle lowerAngle).map (continuous_circleMap 0 ε)
  let lowerLip : Path (circleMap 0 ε lowerAngle)
      (circleMap 0 R lowerAngle) :=
    Path.segment (circleMap 0 ε lowerAngle) (circleMap 0 R lowerAngle)
  let outerArc : Path (circleMap 0 R lowerAngle) (circleMap 0 R upperAngle) :=
    (Path.segment lowerAngle upperAngle).map (continuous_circleMap 0 R)
  let γ₂ : Path (circleMap 0 R upperAngle) (circleMap 0 R lowerAngle) :=
    (upperLip.trans innerArc).trans lowerLip
  -- Peel off the three concatenations until only the upper segment remains.
  have houter :
      (positiveAxisKeyhole R ε).extend t = γ₂.extend (2 * t) := by
    dsimp [positiveAxisKeyhole, upperAngle, lowerAngle, upperLip, innerArc, lowerLip, outerArc, γ₂]
    exact Path.extend_trans_of_le_half
      (γ₁ := (upperLip.trans innerArc).trans lowerLip) (γ₂ := outerArc) (by linarith [ht.2])
  have hmid :
      γ₂.extend (2 * t) = (upperLip.trans innerArc).extend (2 * (2 * t)) := by
    dsimp [γ₂]
    exact Path.extend_trans_of_le_half (γ₁ := upperLip.trans innerArc) (γ₂ := lowerLip)
      (by linarith [ht.2])
  have hinner :
      (upperLip.trans innerArc).extend (2 * (2 * t)) =
        upperLip.extend (2 * (2 * (2 * t))) := by
    exact Path.extend_trans_of_le_half (γ₁ := upperLip) (γ₂ := innerArc) (by linarith [ht.2])
  have hI : 8 * t ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  rw [houter, hmid, hinner]
  -- Once the path is reduced to a single segment, use the standard segment-extension formula.
  calc
    upperLip.extend (2 * (2 * (2 * t)))
        = upperLip.extend (8 * t) := by
            congr 1
            ring
    _ =
        AffineMap.lineMap
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
          (8 * t) := by
            simpa [upperLip, positiveAxisKeyholeUpperAngle] using
              Path.eqOn_extend_segment
                (circleMap 0 R (positiveAxisKeyholeUpperAngle R ε))
                (circleMap 0 ε (positiveAxisKeyholeUpperAngle R ε))
                hI

/-- Helper for Remark III.6-extra-7: on the second interval, the explicit keyhole path follows the
clockwise inner circle with the affine angle parameter `t ↦ 8 t - 1`. -/
lemma positive_axis_keyhole_eq_on_inner_arc (R ε : ℝ) :
    Set.EqOn (positiveAxisKeyhole R ε).extend
      (fun t ↦
        circleMap 0 ε
          (AffineMap.lineMap
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε)
            (8 * t - 1)))
      (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) := by
  intro t ht
  let upperAngle := positiveAxisKeyholeUpperAngle R ε
  let lowerAngle := positiveAxisKeyholeLowerAngle R ε
  let upperLip : Path (circleMap 0 R upperAngle) (circleMap 0 ε upperAngle) :=
    Path.segment (circleMap 0 R upperAngle) (circleMap 0 ε upperAngle)
  let innerArc : Path (circleMap 0 ε upperAngle) (circleMap 0 ε lowerAngle) :=
    (Path.segment upperAngle lowerAngle).map (continuous_circleMap 0 ε)
  let lowerLip : Path (circleMap 0 ε lowerAngle)
      (circleMap 0 R lowerAngle) :=
    Path.segment (circleMap 0 ε lowerAngle) (circleMap 0 R lowerAngle)
  let outerArc : Path (circleMap 0 R lowerAngle) (circleMap 0 R upperAngle) :=
    (Path.segment lowerAngle upperAngle).map (continuous_circleMap 0 R)
  let γ₂ : Path (circleMap 0 R upperAngle) (circleMap 0 R lowerAngle) :=
    (upperLip.trans innerArc).trans lowerLip
  -- Peel off the outer concatenations, then switch to the second half of `upper.trans inner`.
  have houter :
      (positiveAxisKeyhole R ε).extend t = γ₂.extend (2 * t) := by
    dsimp [positiveAxisKeyhole, upperAngle, lowerAngle, upperLip, innerArc, lowerLip, outerArc, γ₂]
    exact Path.extend_trans_of_le_half
      (γ₁ := (upperLip.trans innerArc).trans lowerLip) (γ₂ := outerArc) (by linarith [ht.2])
  have hmid :
      γ₂.extend (2 * t) = (upperLip.trans innerArc).extend (2 * (2 * t)) := by
    dsimp [γ₂]
    exact Path.extend_trans_of_le_half (γ₁ := upperLip.trans innerArc) (γ₂ := lowerLip)
      (by linarith [ht.2])
  have hinner :
      (upperLip.trans innerArc).extend (2 * (2 * t)) =
        innerArc.extend (2 * (2 * (2 * t)) - 1) := by
    exact Path.extend_trans_of_half_le (γ₁ := upperLip) (γ₂ := innerArc) (by linarith [ht.1])
  have hI : 8 * t - 1 ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  have hI' : 2 * (2 * (2 * t)) - 1 ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  rw [houter, hmid, hinner]
  -- Rewrite the mapped angular segment, then identify the inner parameter by the segment formula.
  calc
    innerArc.extend (2 * (2 * (2 * t)) - 1)
        = innerArc ⟨2 * (2 * (2 * t)) - 1, hI'⟩ := by
            rw [Path.extend_apply]
    _ = circleMap 0 ε
          ((Path.segment upperAngle lowerAngle) ⟨2 * (2 * (2 * t)) - 1, hI'⟩) := by
          simp [innerArc, Path.map_coe]
    _ = circleMap 0 ε ((Path.segment upperAngle lowerAngle).extend (2 * (2 * (2 * t)) - 1)) := by
          rw [Path.extend_apply]
    _ = circleMap 0 ε ((Path.segment upperAngle lowerAngle).extend (8 * t - 1)) := by
          congr 1
          ring_nf
    _ = circleMap 0 ε
          (AffineMap.lineMap
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε)
            (8 * t - 1)) := by
          exact congrArg (circleMap 0 ε) <|
            Path.eqOn_extend_segment
              (positiveAxisKeyholeUpperAngle R ε)
              (positiveAxisKeyholeLowerAngle R ε)
              hI

/-- Helper for Remark III.6-extra-7: on the third interval, the explicit keyhole path follows the
lower slit lip with the affine reparametrization `t ↦ 4 t - 1`. -/
lemma positive_axis_keyhole_eq_on_lower_lip (R ε : ℝ) :
    Set.EqOn (positiveAxisKeyhole R ε).extend
      (fun t ↦
        AffineMap.lineMap
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
          (4 * t - 1))
      (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) := by
  intro t ht
  let upperAngle := positiveAxisKeyholeUpperAngle R ε
  let lowerAngle := positiveAxisKeyholeLowerAngle R ε
  let upperLip : Path (circleMap 0 R upperAngle) (circleMap 0 ε upperAngle) :=
    Path.segment (circleMap 0 R upperAngle) (circleMap 0 ε upperAngle)
  let innerArc : Path (circleMap 0 ε upperAngle) (circleMap 0 ε lowerAngle) :=
    (Path.segment upperAngle lowerAngle).map (continuous_circleMap 0 ε)
  let lowerLip : Path (circleMap 0 ε lowerAngle)
      (circleMap 0 R lowerAngle) :=
    Path.segment (circleMap 0 ε lowerAngle) (circleMap 0 R lowerAngle)
  let outerArc : Path (circleMap 0 R lowerAngle) (circleMap 0 R upperAngle) :=
    (Path.segment lowerAngle upperAngle).map (continuous_circleMap 0 R)
  let γ₂ : Path (circleMap 0 R upperAngle) (circleMap 0 R lowerAngle) :=
    (upperLip.trans innerArc).trans lowerLip
  -- After the first break point of the outer concatenation, the motion is already on the lower lip.
  have houter :
      (positiveAxisKeyhole R ε).extend t = γ₂.extend (2 * t) := by
    dsimp [positiveAxisKeyhole, upperAngle, lowerAngle, upperLip, innerArc, lowerLip, outerArc, γ₂]
    exact Path.extend_trans_of_le_half
      (γ₁ := (upperLip.trans innerArc).trans lowerLip) (γ₂ := outerArc) ht.2
  have hmid :
      γ₂.extend (2 * t) = lowerLip.extend (2 * (2 * t) - 1) := by
    dsimp [γ₂]
    exact Path.extend_trans_of_half_le (γ₁ := upperLip.trans innerArc) (γ₂ := lowerLip)
      (by linarith [ht.1])
  have hI : 4 * t - 1 ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  rw [houter, hmid]
  -- Reduce again to the explicit segment-extension formula.
  calc
    lowerLip.extend (2 * (2 * t) - 1)
        = lowerLip.extend (4 * t - 1) := by
              congr 1
              ring
    _ = AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * t - 1) := by
              simpa [lowerLip, positiveAxisKeyhole_circleMap_lowerAngle_eq_old_lower] using
                Path.eqOn_extend_segment
                  (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε))
                  (circleMap 0 R (positiveAxisKeyholeLowerAngle R ε))
                  hI

/-- Helper for Remark III.6-extra-7: on the final interval, the explicit keyhole path follows the
outer circle with the affine angle parameter `t ↦ 2 t - 1`. -/
lemma positive_axis_keyhole_eq_on_outer_arc (R ε : ℝ) :
    Set.EqOn (positiveAxisKeyhole R ε).extend
      (fun t ↦
        circleMap 0 R
          (AffineMap.lineMap
            (positiveAxisKeyholeLowerAngle R ε)
            (positiveAxisKeyholeUpperAngle R ε)
            (2 * t - 1)))
      (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) := by
  intro t ht
  let upperAngle := positiveAxisKeyholeUpperAngle R ε
  let lowerAngle := positiveAxisKeyholeLowerAngle R ε
  let upperLip : Path (circleMap 0 R upperAngle) (circleMap 0 ε upperAngle) :=
    Path.segment (circleMap 0 R upperAngle) (circleMap 0 ε upperAngle)
  let innerArc : Path (circleMap 0 ε upperAngle) (circleMap 0 ε lowerAngle) :=
    (Path.segment upperAngle lowerAngle).map (continuous_circleMap 0 ε)
  let lowerLip : Path (circleMap 0 ε lowerAngle)
      (circleMap 0 R lowerAngle) :=
    Path.segment (circleMap 0 ε lowerAngle) (circleMap 0 R lowerAngle)
  let outerArc : Path (circleMap 0 R lowerAngle) (circleMap 0 R upperAngle) :=
    (Path.segment lowerAngle upperAngle).map (continuous_circleMap 0 R)
  -- Route correction: isolate the outer arc directly from the last concatenation instead of
  -- forcing later chart proofs to keep unfolding the whole nested keyhole path.
  have houter :
      (positiveAxisKeyhole R ε).extend t = outerArc.extend (2 * t - 1) := by
    dsimp [positiveAxisKeyhole, upperAngle, lowerAngle, upperLip, innerArc, lowerLip, outerArc]
    exact Path.extend_trans_of_half_le
      (γ₁ := (upperLip.trans innerArc).trans lowerLip) (γ₂ := outerArc) ht.1
  have hI : 2 * t - 1 ∈ I := by
    constructor <;> linarith [ht.1, ht.2]
  rw [houter]
  -- The mapped angular segment is again reduced to the standard segment-extension formula.
  calc
    outerArc.extend (2 * t - 1)
        = outerArc ⟨2 * t - 1, hI⟩ := by
            rw [Path.extend_apply]
    _ = circleMap 0 R ((Path.segment lowerAngle upperAngle) ⟨2 * t - 1, hI⟩) := by
          simp [outerArc, Path.map_coe]
    _ = circleMap 0 R ((Path.segment lowerAngle upperAngle).extend (2 * t - 1)) := by
          rw [Path.extend_apply]
    _ = circleMap 0 R
          (AffineMap.lineMap
            (positiveAxisKeyholeLowerAngle R ε)
            (positiveAxisKeyholeUpperAngle R ε)
            (2 * t - 1)) := by
          exact congrArg (circleMap 0 R) <|
            Path.eqOn_extend_segment
              (positiveAxisKeyholeLowerAngle R ε)
              (positiveAxisKeyholeUpperAngle R ε)
              hI

/-- Helper for Remark III.6-extra-7: on the first interval, the real-plane closed-curve model is
the upper slit lip written in explicit coordinates. -/
lemma positive_axis_keyhole_realCurve_eq_on_upper_lip (R ε : ℝ) :
    Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (fun t ↦
        Complex.equivRealProd
          (AffineMap.lineMap
            (circleMap 0 R (positiveAxisKeyholeAngle R ε))
            (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
            (8 * t)))
      (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) := by
  intro t ht
  -- Pass from the complex-valued path formula to the real-plane parametrization by `equivRealProd`.
  simpa [ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
    congrArg Complex.equivRealProd (positive_axis_keyhole_eq_on_upper_lip R ε ht)

/-- Helper for Remark III.6-extra-7: on the second interval, the real-plane closed-curve model is
the clockwise inner circular arc written in explicit coordinates. -/
lemma positive_axis_keyhole_realCurve_eq_on_inner_arc (R ε : ℝ) :
    Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (fun t ↦
        Complex.equivRealProd
          (circleMap 0 ε
            (AffineMap.lineMap
              (positiveAxisKeyholeUpperAngle R ε)
              (positiveAxisKeyholeLowerAngle R ε)
              (8 * t - 1))))
      (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) := by
  intro t ht
  -- The real-curve owner is just the complex formula viewed in `Plane`.
  simpa [ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
    congrArg Complex.equivRealProd (positive_axis_keyhole_eq_on_inner_arc R ε ht)

/-- Helper for Remark III.6-extra-7: on the third interval, the real-plane closed-curve model is
the lower slit lip written in explicit coordinates. -/
lemma positive_axis_keyhole_realCurve_eq_on_lower_lip (R ε : ℝ) :
    Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (fun t ↦
        Complex.equivRealProd
          (AffineMap.lineMap
            (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
            (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
            (4 * t - 1)))
      (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) := by
  intro t ht
  -- The lower lip uses the same `equivRealProd` bridge from the complex path formula.
  simpa [ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
    congrArg Complex.equivRealProd (positive_axis_keyhole_eq_on_lower_lip R ε ht)

/-- Helper for Remark III.6-extra-7: on the final interval, the real-plane closed-curve model is
the outer circular arc written in explicit coordinates. -/
lemma positive_axis_keyhole_realCurve_eq_on_outer_arc (R ε : ℝ) :
    Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (fun t ↦
        Complex.equivRealProd
          (circleMap 0 R
            (AffineMap.lineMap
              (positiveAxisKeyholeLowerAngle R ε)
              (positiveAxisKeyholeUpperAngle R ε)
              (2 * t - 1))))
      (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) := by
  intro t ht
  -- The final branch is again the complex outer-arc formula viewed in `Plane`.
  simpa [ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
    congrArg Complex.equivRealProd (positive_axis_keyhole_eq_on_outer_arc R ε ht)

/-- Helper for Remark III.6-extra-7: package the four closed-interval formulas for the real-plane
parametrization of the positive-axis keyhole contour. These closed-interval owners are stronger
than the open-interval adapters needed later for regular-point arguments. -/
lemma positive_axis_keyhole_realCurve_eqOn_piece_intervals (R ε : ℝ) :
    Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
        (fun t ↦
          Complex.equivRealProd
            (AffineMap.lineMap
              (circleMap 0 R (positiveAxisKeyholeAngle R ε))
              (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
              (8 * t)))
        (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) ∧
      Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
        (fun t ↦
          Complex.equivRealProd
            (circleMap 0 ε
              (AffineMap.lineMap
                (positiveAxisKeyholeUpperAngle R ε)
                (positiveAxisKeyholeLowerAngle R ε)
                (8 * t - 1))))
        (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) ∧
      Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
        (fun t ↦
          Complex.equivRealProd
            (AffineMap.lineMap
              (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
              (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
              (4 * t - 1)))
        (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) ∧
      Set.EqOn ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
        (fun t ↦
          Complex.equivRealProd
            (circleMap 0 R
              (AffineMap.lineMap
                (positiveAxisKeyholeLowerAngle R ε)
                (positiveAxisKeyholeUpperAngle R ε)
                (2 * t - 1))))
        (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) := by
  -- Bundle the four branch formulas so later geometric arguments can case-split once and then
  -- work with concrete branch models instead of the full nested concatenation.
  refine ⟨positive_axis_keyhole_realCurve_eq_on_upper_lip R ε,
    positive_axis_keyhole_realCurve_eq_on_inner_arc R ε,
    positive_axis_keyhole_realCurve_eq_on_lower_lip R ε,
    positive_axis_keyhole_realCurve_eq_on_outer_arc R ε⟩

/-- Helper for Remark III.6-extra-7: every parameter in `I` lies either on one of the four open
branches of the positive-axis keyhole contour or at one of the five distinguished breakpoints
`0`, `1/8`, `1/4`, `1/2`, `1`. This is the stable interval splitter for the later boundary-owner
arguments. -/
lemma positive_axis_keyhole_parameter_cases (t : I) :
    t.1 = 0 ∨
      t.1 ∈ Set.Ioo (0 : ℝ) (1 / 8) ∨
      t.1 = 1 / 8 ∨
      t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) ∨
      t.1 = 1 / 4 ∨
      t.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∨
      t.1 = 1 / 2 ∨
      t.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) ∨
      t.1 = 1 := by
  -- Split first into the global endpoints `0`, `1`, or the interior interval `(0, 1)`.
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc t.2 with ht0 | ht1 | ht
  · exact Or.inl ht0
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ht1
  · by_cases h18 : t.1 < 1 / 8
    · exact Or.inr <| Or.inl ⟨ht.1, h18⟩
    · have h18' : 1 / 8 ≤ t.1 := le_of_not_gt h18
      by_cases h14 : t.1 < 1 / 4
      · -- The next split isolates `1/8` from the open inner-circle interval.
        rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ⟨h18', le_of_lt h14⟩ with hEq | hEq | hmem
        · exact Or.inr <| Or.inr <| Or.inl hEq
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inl hmem
      · have h14' : 1 / 4 ≤ t.1 := le_of_not_gt h14
        by_cases h12 : t.1 < 1 / 2
        · -- The third split isolates `1/4` from the open lower-lip interval.
          rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ⟨h14', le_of_lt h12⟩ with
              hEq | hEq | hmem
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hmem
        · have h12' : 1 / 2 ≤ t.1 := le_of_not_gt h12
          -- The final split isolates `1/2` from the open outer-circle interval and the endpoint
          -- `1`.
          rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc ⟨h12', ht.2.le⟩ with
              hEq | hEq | hmem
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr hEq
          · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hmem

/-- Helper for Remark III.6-extra-7: the five distinguished parameters `0`, `1/8`, `1/4`, `1/2`,
and `1` hit the four geometric corners of the positive-axis keyhole contour in source order. This
packages the endpoint evaluations before the later branchwise injectivity arguments. -/
lemma positive_axis_keyhole_breakpoint_values (R ε : ℝ) :
    positiveAxisKeyhole R ε (0 : I) =
        circleMap 0 R (positiveAxisKeyholeAngle R ε) ∧
      positiveAxisKeyhole R ε (⟨(1 / 8 : ℝ), by norm_num⟩ : I) =
        circleMap 0 ε (positiveAxisKeyholeAngle R ε) ∧
      positiveAxisKeyhole R ε (⟨(1 / 4 : ℝ), by norm_num⟩ : I) =
        circleMap 0 ε (-positiveAxisKeyholeAngle R ε) ∧
      positiveAxisKeyhole R ε (⟨(1 / 2 : ℝ), by norm_num⟩ : I) =
        circleMap 0 R (-positiveAxisKeyholeAngle R ε) ∧
      positiveAxisKeyhole R ε (1 : I) =
        circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
  have h0_segment :
      (positiveAxisKeyhole R ε).extend 0 =
        AffineMap.lineMap
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
          (8 * (0 : ℝ)) := by
    -- Evaluate the upper-lip branch at the initial parameter.
    have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 8 : ℝ) := by simp
    exact positive_axis_keyhole_eq_on_upper_lip R ε hzero
  have h18_segment :
      (positiveAxisKeyhole R ε).extend (1 / 8 : ℝ) =
        AffineMap.lineMap
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
          (8 * (1 / 8 : ℝ)) := by
    -- The endpoint of the upper lip is the first contour corner.
    simpa using
      (positive_axis_keyhole_eq_on_upper_lip R ε
        (by norm_num : (1 / 8 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 8 : ℝ)))
  have h14_arc :
      (positiveAxisKeyhole R ε).extend (1 / 4 : ℝ) =
        circleMap 0 ε
          (AffineMap.lineMap
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε)
            (8 * (1 / 4 : ℝ) - 1)) := by
    -- Evaluating the inner arc at its terminal parameter reaches the lower inner corner.
    simpa using
      (positive_axis_keyhole_eq_on_inner_arc R ε
        (by norm_num : (1 / 4 : ℝ) ∈ Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)))
  have h12_segment :
      (positiveAxisKeyhole R ε).extend (1 / 2 : ℝ) =
        AffineMap.lineMap
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
          (4 * (1 / 2 : ℝ) - 1) := by
    -- The lower lip ends at the outer lower corner.
    simpa using
      (positive_axis_keyhole_eq_on_lower_lip R ε
        (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)))
  have h1_arc :
      (positiveAxisKeyhole R ε).extend (1 : ℝ) =
        circleMap 0 R
          (AffineMap.lineMap
            (positiveAxisKeyholeLowerAngle R ε)
            (positiveAxisKeyholeUpperAngle R ε)
            (2 * (1 : ℝ) - 1)) := by
    -- The outer arc closes the contour back to the starting point.
    simpa using
      (positive_axis_keyhole_eq_on_outer_arc R ε
        (by norm_num : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) (1 : ℝ)))
  have h0_path :
      positiveAxisKeyhole R ε (0 : I) =
        AffineMap.lineMap
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
          (8 * (0 : ℝ)) := by
    -- Convert the endpoint evaluation from `extend` back to the subtype parameter.
    exact
      (Path.extend_apply (positiveAxisKeyhole R ε)
        (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h0_segment
  have h18_path :
      positiveAxisKeyhole R ε (⟨(1 / 8 : ℝ), by norm_num⟩ : I) =
        AffineMap.lineMap
          (circleMap 0 R (positiveAxisKeyholeAngle R ε))
          (circleMap 0 ε (positiveAxisKeyholeAngle R ε))
          (8 * (1 / 8 : ℝ)) := by
    -- The same bridge is needed at the first interior breakpoint.
    exact
      (Path.extend_apply (positiveAxisKeyhole R ε)
        (by norm_num : (1 / 8 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h18_segment
  have h14_path :
      positiveAxisKeyhole R ε (⟨(1 / 4 : ℝ), by norm_num⟩ : I) =
        circleMap 0 ε
          (AffineMap.lineMap
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε)
            (8 * (1 / 4 : ℝ) - 1)) := by
    -- Likewise for the lower endpoint of the inner circular arc.
    exact
      (Path.extend_apply (positiveAxisKeyhole R ε)
        (by norm_num : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h14_arc
  have h12_path :
      positiveAxisKeyhole R ε (⟨(1 / 2 : ℝ), by norm_num⟩ : I) =
        AffineMap.lineMap
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
          (4 * (1 / 2 : ℝ) - 1) := by
    -- And again at the endpoint of the lower slit lip.
    exact
      (Path.extend_apply (positiveAxisKeyhole R ε)
        (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h12_segment
  have h1_path :
      positiveAxisKeyhole R ε (1 : I) =
        circleMap 0 R
          (AffineMap.lineMap
            (positiveAxisKeyholeLowerAngle R ε)
            (positiveAxisKeyholeUpperAngle R ε)
            (2 * (1 : ℝ) - 1)) := by
    -- The final bridge closes the loop at the path endpoint.
    exact
      (Path.extend_apply (positiveAxisKeyhole R ε)
        (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).symm.trans h1_arc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- The affine upper-lip segment starts at the outer upper corner.
    simpa [AffineMap.lineMap_apply_zero] using h0_path
  · -- The affine upper-lip segment ends at the inner upper corner.
    simpa [AffineMap.lineMap_apply_one] using h18_path
  · -- The clockwise inner arc ends at angle `-2π - θ`.
    have h14_param : (8 * (1 / 4 : ℝ) - 1) = 1 := by norm_num
    rw [h14_param, AffineMap.lineMap_apply_one] at h14_path
    simpa [positiveAxisKeyhole_circleMap_lowerAngle_eq_old_lower] using h14_path
  · -- The affine lower-lip segment ends at the outer lower corner.
    have h12_param : (4 * (1 / 2 : ℝ) - 1) = 1 := by norm_num
    rw [h12_param, AffineMap.lineMap_apply_one] at h12_path
    exact h12_path
  · -- The outer arc returns to the initial angle `θ`.
    have h1_param : (2 * (1 : ℝ) - 1) = 1 := by norm_num
    rw [h1_param, AffineMap.lineMap_apply_one] at h1_path
    exact h1_path
