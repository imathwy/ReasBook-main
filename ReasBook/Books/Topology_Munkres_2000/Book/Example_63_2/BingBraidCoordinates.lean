module

public import Topology_Munkres_2000.Book.Example_63_2.HornGeometry

public section

namespace AlexanderHornGeometry

/-- Helper for Example 63.2: the continuous linear cutoff used by a compactly supported
radial twist. -/
noncomputable def radialTwistCutoff (inner outer radius : ℝ) : ℝ :=
  max 0 (min 1 ((outer - radius) / (outer - inner)))

/-- Helper for Example 63.2: the radial cutoff is continuous in the radius variable. -/
lemma continuous_radialTwistCutoff (inner outer : ℝ) :
    Continuous (radialTwistCutoff inner outer) := by
  -- The cutoff is obtained from an affine function by the continuous lattice operations.
  unfold radialTwistCutoff
  fun_prop

/-- Helper for Example 63.2: the radial cutoff equals one on the inner disk. -/
lemma radialTwistCutoff_eq_one_of_le {inner outer radius : ℝ}
    (hio : inner < outer) (hr : radius ≤ inner) :
    radialTwistCutoff inner outer radius = 1 := by
  -- Inside the inner radius, the unclamped affine cutoff is at least one.
  have hden : 0 < outer - inner := sub_pos.mpr hio
  have hratio : 1 ≤ (outer - radius) / (outer - inner) := by
    rw [le_div_iff₀ hden]
    linarith
  rw [radialTwistCutoff, min_eq_left hratio, max_eq_right]
  norm_num

/-- Helper for Example 63.2: the radial cutoff vanishes outside the outer disk. -/
lemma radialTwistCutoff_eq_zero_of_le {inner outer radius : ℝ}
    (hio : inner < outer) (hr : outer ≤ radius) :
    radialTwistCutoff inner outer radius = 0 := by
  -- Outside the outer radius, the unclamped affine cutoff is nonpositive.
  have hden : 0 < outer - inner := sub_pos.mpr hio
  have hratio : (outer - radius) / (outer - inner) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) hden.le
  rw [radialTwistCutoff, min_eq_right (hratio.trans zero_le_one), max_eq_left hratio]

/-- Helper for Example 63.2: rotate every circle centered at `center` through an angle that
depends only on its radius. -/
noncomputable def radialRotation (center : ℂ) (angle : ℝ → ℝ) (z : ℂ) : ℂ :=
  center + (Circle.exp (angle ‖z - center‖) : ℂ) * (z - center)

/-- Helper for Example 63.2: a radial rotation preserves distance from its center. -/
lemma norm_radialRotation_sub_center (center : ℂ) (angle : ℝ → ℝ) (z : ℂ) :
    ‖radialRotation center angle z - center‖ = ‖z - center‖ := by
  -- Translation cancels, and the circle-valued multiplier has norm one.
  rw [radialRotation, add_sub_cancel_left, norm_mul, Circle.norm_coe, one_mul]

/-- Helper for Example 63.2: negating the angular profile gives a left inverse to a radial
rotation. -/
lemma radialRotation_neg_left (center : ℂ) (angle : ℝ → ℝ) (z : ℂ) :
    radialRotation center (fun radius ↦ -angle radius)
        (radialRotation center angle z) = z := by
  -- Radius preservation makes the second rotation use exactly the opposite angle.
  rw [radialRotation, norm_radialRotation_sub_center]
  simp only [radialRotation, add_sub_cancel_left, Circle.coe_exp]
  rw [← mul_assoc, ← Complex.exp_add]
  simp only [Complex.ofReal_neg, neg_mul, neg_add_cancel, Complex.exp_zero, one_mul,
    add_sub_cancel]

/-- Helper for Example 63.2: negating the angular profile also gives a right inverse to a
radial rotation. -/
lemma radialRotation_neg_right (center : ℂ) (angle : ℝ → ℝ) (z : ℂ) :
    radialRotation center angle
        (radialRotation center (fun radius ↦ -angle radius) z) = z := by
  -- Apply the left-inverse computation to the already negated profile.
  simpa only [neg_neg] using
    radialRotation_neg_left center (fun radius ↦ -angle radius) z

/-- Helper for Example 63.2: a continuous angular profile gives a continuous radial
rotation. -/
lemma continuous_radialRotation (center : ℂ) {angle : ℝ → ℝ}
    (hangle : Continuous angle) : Continuous (radialRotation center angle) := by
  -- Norm, angle evaluation, circle exponential, multiplication, and translation are continuous.
  unfold radialRotation
  fun_prop

/-- Helper for Example 63.2: a continuous radial angular profile defines a plane
homeomorphism, with inverse obtained by negating the profile. -/
noncomputable def radialRotationHomeomorph (center : ℂ) (angle : C(ℝ, ℝ)) : ℂ ≃ₜ ℂ :=
  {
    toFun := radialRotation center angle
    invFun := radialRotation center fun radius ↦ -angle radius
    left_inv := radialRotation_neg_left center angle
    right_inv := radialRotation_neg_right center angle
    continuous_toFun := continuous_radialRotation center angle.continuous
    continuous_invFun := continuous_radialRotation center angle.continuous.neg
  }

/-- Helper for Example 63.2: the compactly supported half-twist about a prescribed center,
using the fixed radii from the Bing-braid construction. -/
noncomputable def standardRadialHalfTwist (center : ℂ) : ℂ ≃ₜ ℂ :=
  radialRotationHomeomorph center
    ⟨fun radius ↦ Real.pi * radialTwistCutoff (1 / 4) (1 / 2) radius,
      continuous_const.mul (continuous_radialTwistCutoff (1 / 4) (1 / 2))⟩

/-- Helper for Example 63.2: the standard half-twist evaluates by the underlying radial
rotation formula. -/
lemma standardRadialHalfTwist_apply (center z : ℂ) :
    standardRadialHalfTwist center z =
      radialRotation center
        (fun radius ↦ Real.pi * radialTwistCutoff (1 / 4) (1 / 2) radius) z := by
  -- Expose only the homeomorphism's forward map, keeping its inverse data opaque.
  rfl

/-- Helper for Example 63.2: the standard half-twist is the identity outside its radius
one-half support disk. -/
lemma standardRadialHalfTwist_apply_of_outer_le (center z : ℂ)
    (hz : (1 / 2 : ℝ) ≤ ‖z - center‖) :
    standardRadialHalfTwist center z = z := by
  -- The cutoff vanishes there, so the rotating circle multiplier is one.
  rw [standardRadialHalfTwist_apply, radialRotation,
    radialTwistCutoff_eq_zero_of_le (by norm_num : (1 / 4 : ℝ) < 1 / 2) hz]
  simp only [mul_zero, Circle.exp_zero, Circle.coe_one, one_mul, add_sub_cancel]

/-- Helper for Example 63.2: on the radius one-quarter inner disk the standard half-twist
is the half-turn `z ↦ 2 * center - z`. -/
lemma standardRadialHalfTwist_apply_of_le_inner (center z : ℂ)
    (hz : ‖z - center‖ ≤ (1 / 4 : ℝ)) :
    standardRadialHalfTwist center z = 2 * center - z := by
  -- The cutoff is one there, and complex exponential at angle pi is minus one.
  rw [standardRadialHalfTwist_apply, radialRotation,
    radialTwistCutoff_eq_one_of_le (by norm_num : (1 / 4 : ℝ) < 1 / 2) hz]
  simp only [mul_one, Circle.coe_exp, Complex.exp_pi_mul_I]
  ring

/-- Helper for Example 63.2: the inverse standard half-twist is also the identity outside
the radius one-half support disk. -/
lemma standardRadialHalfTwist_symm_apply_of_outer_le (center z : ℂ)
    (hz : (1 / 2 : ℝ) ≤ ‖z - center‖) :
    (standardRadialHalfTwist center).symm z = z := by
  -- The inverse fixes every point fixed by the forward homeomorphism.
  have hfixed := standardRadialHalfTwist_apply_of_outer_le center z hz
  calc
    (standardRadialHalfTwist center).symm z =
        (standardRadialHalfTwist center).symm
          (standardRadialHalfTwist center z) := congrArg _ hfixed.symm
    _ = z := (standardRadialHalfTwist center).symm_apply_apply z

/-- Helper for Example 63.2: on the inner disk, the inverse standard half-twist is the same
half-turn as the forward map. -/
lemma standardRadialHalfTwist_symm_apply_of_le_inner (center z : ℂ)
    (hz : ‖z - center‖ ≤ (1 / 4 : ℝ)) :
    (standardRadialHalfTwist center).symm z = 2 * center - z := by
  -- The half-turn preserves the inner radius and applying it twice is the identity.
  have hreflect : ‖(2 * center - z) - center‖ = ‖z - center‖ := by
    rw [show (2 * center - z) - center = -(z - center) by ring, norm_neg]
  have hforward : standardRadialHalfTwist center (2 * center - z) = z := by
    rw [standardRadialHalfTwist_apply_of_le_inner center (2 * center - z)
      (hreflect.trans_le hz)]
    ring
  calc
    (standardRadialHalfTwist center).symm z =
        (standardRadialHalfTwist center).symm
          (standardRadialHalfTwist center (2 * center - z)) := congrArg _ hforward.symm
    _ = 2 * center - z :=
      (standardRadialHalfTwist center).symm_apply_apply (2 * center - z)

/-- Helper for Example 63.2: the left rational half-twist center. -/
noncomputable def leftBingTwistCenter : ℂ := -(1 / 4 : ℂ)

/-- Helper for Example 63.2: the right rational half-twist center. -/
noncomputable def rightBingTwistCenter : ℂ := 1 / 4

/-- Helper for Example 63.2: the left half-twist exchanges the marked points `-1/2` and
`0`. -/
lemma leftBingHalfTwist_markedPoints :
    standardRadialHalfTwist leftBingTwistCenter (-(1 / 2 : ℂ)) = 0 ∧
      standardRadialHalfTwist leftBingTwistCenter 0 = -(1 / 2 : ℂ) := by
  -- Both marked points are exactly one quarter from the left twist center.
  constructor
  · rw [standardRadialHalfTwist_apply_of_le_inner]
    · norm_num [leftBingTwistCenter]
    · norm_num [leftBingTwistCenter, Complex.norm_real]
  · rw [standardRadialHalfTwist_apply_of_le_inner]
    · norm_num [leftBingTwistCenter]
    · norm_num [leftBingTwistCenter, Complex.norm_real]

/-- Helper for Example 63.2: the right half-twist exchanges the marked points `0` and
`1/2`. -/
lemma rightBingHalfTwist_markedPoints :
    standardRadialHalfTwist rightBingTwistCenter 0 = (1 / 2 : ℂ) ∧
      standardRadialHalfTwist rightBingTwistCenter (1 / 2 : ℂ) = 0 := by
  -- Both marked points are exactly one quarter from the right twist center.
  constructor
  · rw [standardRadialHalfTwist_apply_of_le_inner]
    · norm_num [rightBingTwistCenter]
    · norm_num [rightBingTwistCenter, Complex.norm_real]
  · rw [standardRadialHalfTwist_apply_of_le_inner]
    · norm_num [rightBingTwistCenter]
    · norm_num [rightBingTwistCenter, Complex.norm_real]

/-- Helper for Example 63.2: the named left compactly supported half-twist. -/
noncomputable def leftBingHalfTwist : ℂ ≃ₜ ℂ :=
  standardRadialHalfTwist leftBingTwistCenter

/-- Helper for Example 63.2: the named right compactly supported half-twist. -/
noncomputable def rightBingHalfTwist : ℂ ≃ₜ ℂ :=
  standardRadialHalfTwist rightBingTwistCenter

/-- Helper for Example 63.2: one positive-left, negative-right pair in the Bing braid
word. -/
noncomputable def bingBraidPair : ℂ ≃ₜ ℂ :=
  leftBingHalfTwist.trans rightBingHalfTwist.symm

/-- Helper for Example 63.2: one braid pair cyclically permutes the three marked fiber
points. -/
lemma bingBraidPair_markedPoints :
    bingBraidPair (-(1 / 2 : ℂ)) = (1 / 2 : ℂ) ∧
      bingBraidPair 0 = -(1 / 2 : ℂ) ∧
        bingBraidPair (1 / 2 : ℂ) = 0 := by
  -- Use the two adjacent transpositions, with the inverse right twist having the same
  -- marked-point action as its forward half-turn.
  rcases leftBingHalfTwist_markedPoints with ⟨hleftNeg, hleftZero⟩
  rcases rightBingHalfTwist_markedPoints with ⟨hrightZero, hrightPos⟩
  have hleftNeg' : leftBingHalfTwist (-(1 / 2 : ℂ)) = 0 := hleftNeg
  have hleftZero' : leftBingHalfTwist 0 = -(1 / 2 : ℂ) := hleftZero
  have hrightInvZero : rightBingHalfTwist.symm 0 = (1 / 2 : ℂ) := by
    have hz : ‖(0 : ℂ) - rightBingTwistCenter‖ ≤ (1 / 4 : ℝ) := by
      norm_num [rightBingTwistCenter, Complex.norm_real]
    have hformula : rightBingHalfTwist.symm 0 = 2 * rightBingTwistCenter - 0 := by
      simpa only [rightBingHalfTwist] using
        standardRadialHalfTwist_symm_apply_of_le_inner rightBingTwistCenter 0 hz
    calc
      rightBingHalfTwist.symm 0 = 2 * rightBingTwistCenter - 0 := hformula
      _ = (1 / 2 : ℂ) := by norm_num [rightBingTwistCenter]
  have hrightInvPos : rightBingHalfTwist.symm (1 / 2 : ℂ) = 0 := by
    have hz : ‖(1 / 2 : ℂ) - rightBingTwistCenter‖ ≤ (1 / 4 : ℝ) := by
      norm_num [rightBingTwistCenter, Complex.norm_real]
    have hformula : rightBingHalfTwist.symm (1 / 2 : ℂ) =
        2 * rightBingTwistCenter - 1 / 2 := by
      simpa only [rightBingHalfTwist] using
        standardRadialHalfTwist_symm_apply_of_le_inner rightBingTwistCenter (1 / 2) hz
    calc
      rightBingHalfTwist.symm (1 / 2 : ℂ) =
          2 * rightBingTwistCenter - 1 / 2 := hformula
      _ = 0 := by norm_num [rightBingTwistCenter]
  have hrightInvNeg : rightBingHalfTwist.symm (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) := by
    apply standardRadialHalfTwist_symm_apply_of_outer_le
    norm_num [rightBingTwistCenter, Complex.norm_real]
  have hleftPos : leftBingHalfTwist (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    apply standardRadialHalfTwist_apply_of_outer_le
    norm_num [leftBingTwistCenter, Complex.norm_real]
  simp only [bingBraidPair, Homeomorph.trans_apply, hleftNeg', hleftZero', hleftPos,
    hrightInvZero, hrightInvPos, hrightInvNeg]
  simp only [true_and]

/-- Helper for Example 63.2: the endpoint homeomorphism of the six-letter word
`(sigma_left sigma_right⁻¹)³`. -/
noncomputable def standardBingBraidMonodromy : ℂ ≃ₜ ℂ :=
  (bingBraidPair.trans bingBraidPair).trans bingBraidPair

/-- Helper for Example 63.2: the six-letter Bing braid closes on all three marked fiber
points. -/
lemma standardBingBraidMonodromy_fixes_markedPoints :
    standardBingBraidMonodromy (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) ∧
      standardBingBraidMonodromy 0 = 0 ∧
        standardBingBraidMonodromy (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
  -- Three applications of the certified three-cycle return each marked point to itself.
  rcases bingBraidPair_markedPoints with ⟨hneg, hzero, hpos⟩
  simp only [standardBingBraidMonodromy, Homeomorph.trans_apply, hneg, hzero, hpos,
    and_self]

end AlexanderHornGeometry
