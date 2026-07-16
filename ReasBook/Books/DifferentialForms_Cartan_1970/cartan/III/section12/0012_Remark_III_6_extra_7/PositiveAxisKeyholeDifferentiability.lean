import DifferentialForms_Cartan_1970.cartan.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeBranchCoordinates

open Filter MeasureTheory Bornology
open scoped unitInterval

noncomputable section

/-- Helper for Remark III.6-extra-7: the first keyhole breakpoint is a genuine corner where the
upper slit lip meets the clockwise inner arc, so the real-plane parametrization is not
differentiable there within `[0, 1]`. -/
lemma positive_axis_keyhole_not_differentiable_at_one_eighth
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    ¬ DifferentiableWithinAt ℝ ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ) := by
  -- Route correction: compare the repaired major-arc tangent on the inner branch against the
  -- unchanged upper-lip tangent, then separate them by the sign of their imaginary parts.
  intro hdiff
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  let upper : ℝ := positiveAxisKeyholeUpperAngle R ε
  let lower : ℝ := positiveAxisKeyholeLowerAngle R ε
  let γ : ℝ → ℂ := (positiveAxisKeyhole R ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ)
  let upperLip : ℝ → ℂ := fun t ↦
    AffineMap.lineMap
      (circleMap 0 R θ)
      (circleMap 0 ε θ)
      (t * 8 - 0)
  let inner : ℝ → ℂ := fun t ↦
    circleMap 0 ε (AffineMap.lineMap upper lower (8 * t - 1))
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ) := by
    -- Move from the real-plane curve back to the complex-valued contour.
    simpa [γ, ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
      (Complex.equivRealProdCLM.comp_differentiableWithinAt_iff.mp hdiff)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ) := by
    -- Record the ambient derivative once before restricting it to the adjacent branches.
    simpa [d, γ] using hγdiff.hasDerivWithinAt
  have hupperMain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) := by
    -- Restrict the ambient derivative to the upper-lip interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hinnerMain : HasDerivWithinAt γ d (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) := by
    -- Restrict the same derivative to the inner-arc interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hupperγ :
      HasDerivWithinAt γ
        ((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ))
        (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) := by
    -- Differentiate the affine upper-lip model and transfer it back to the contour.
    have hmodel :
        HasDerivAt upperLip
          ((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ))
          (1 / 8 : ℝ) := by
      have hmodel' :
          HasDerivAt
            (fun t : ℝ ↦
              AffineMap.lineMap
                (circleMap 0 R θ)
                (circleMap 0 ε θ)
                (t * 8 - 0))
            ((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ))
            (1 / 8 : ℝ) := by
        simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
          two_mul, mul_assoc, mul_left_comm, mul_comm] using
          (AffineMap.hasDerivAt_lineMap
            (a := circleMap 0 R θ)
            (b := circleMap 0 ε θ)
            (x := (1 / 8 : ℝ) * 8 - 0)).scomp
            (1 / 8 : ℝ) (((hasDerivAt_id (1 / 8 : ℝ)).mul_const 8).sub_const 0)
      simpa [upperLip] using hmodel'
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, upperLip, mul_comm] using positive_axis_keyhole_eq_on_upper_lip R ε ht)
      (by constructor <;> norm_num)
  have hinnerγ :
      HasDerivWithinAt γ
        (((8 * (lower - upper)) : ℝ) •
          (circleMap 0 ε upper * Complex.I))
        (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) := by
    -- Differentiate the repaired major inner arc at its initial endpoint.
    have hparam :
        HasDerivAt
          (fun t : ℝ ↦ AffineMap.lineMap upper lower (8 * t - 1))
          (8 * (lower - upper))
          (1 / 8 : ℝ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := upper) (b := lower) (x := (8 : ℝ) * (1 / 8 : ℝ) - 1)).comp
          (1 / 8 : ℝ) (((hasDerivAt_id (1 / 8 : ℝ)).const_mul 8).sub_const 1)
    have hmodel_raw :
        HasDerivAt inner
          (((8 * (lower - upper)) : ℝ) •
            (circleMap 0 ε
              (AffineMap.lineMap upper lower ((8 : ℝ) * (1 / 8 : ℝ) - 1)) *
              Complex.I))
          (1 / 8 : ℝ) := by
      simpa [inner, smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add,
        add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using
        (hasDerivAt_circleMap 0 ε
          (AffineMap.lineMap upper lower ((8 : ℝ) * (1 / 8 : ℝ) - 1))).scomp
          (1 / 8 : ℝ) hparam
    have hstart_param : (8 : ℝ) * (1 / 8 : ℝ) - 1 = 0 := by
      norm_num
    have hmodel :
        HasDerivAt inner
          (((8 * (lower - upper)) : ℝ) •
            (circleMap 0 ε upper * Complex.I))
          (1 / 8 : ℝ) := by
      convert hmodel_raw using 1
      rw [hstart_param, AffineMap.lineMap_apply_zero]
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, inner] using positive_axis_keyhole_eq_on_inner_arc R ε ht)
      (by constructor <;> norm_num)
  have hupperUD :
      UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) :=
    (uniqueDiffOn_Icc (show (0 : ℝ) < 1 / 8 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hinnerUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 8 : ℝ) < 1 / 4 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hcompare :
      ((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ)) =
        (((8 * (lower - upper)) : ℝ) •
          (circleMap 0 ε upper * Complex.I)) := by
    -- Uniqueness of within-derivatives forces the two one-sided tangents to agree.
    calc
      ((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ))
          = derivWithin γ (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) := by
              symm
              exact hupperγ.derivWithin hupperUD
      _ = d := hupperMain.derivWithin hupperUD
      _ = derivWithin γ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) := by
            symm
            exact hinnerMain.derivWithin hinnerUD
      _ =
          (((8 * (lower - upper)) : ℝ) •
            (circleMap 0 ε upper * Complex.I)) :=
            hinnerγ.derivWithin hinnerUD
  have hR : 0 < R := lt_trans hε hεR
  have hθ_pos : 0 < θ := by
    simpa [θ, positiveAxisKeyholeAngle] using Real.arctan_pos.mpr (div_pos hε hR)
  have hupper_im_neg :
      ((((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ)) : ℂ)).im < 0 := by
    have hsin_pos : 0 < Real.sin θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.sin_arctan_pos.mpr (div_pos hε hR)
    have him_diff :
        (circleMap 0 ε θ - circleMap 0 R θ).im = (ε - R) * Real.sin θ := by
      simp [sub_eq_add_neg, circleMap_zero_im]
      ring
    rw [show
      ((((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ)) : ℂ)).im =
        8 * (circleMap 0 ε θ - circleMap 0 R θ).im by
          simp [mul_assoc, mul_left_comm, mul_comm]]
    rw [him_diff]
    nlinarith
  have hinner_im_pos :
      0 <
        ((((8 * (lower - upper)) : ℝ) •
            (circleMap 0 ε upper * Complex.I)) : ℂ).im := by
    have hfactor_pos : 0 < 8 * (lower - upper) := by
      have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
      nlinarith [horder.1]
    have hre_pos : 0 < (circleMap 0 ε upper).re := by
      have hcos_pos : 0 < Real.cos θ := by
        simpa [θ, positiveAxisKeyholeAngle] using Real.cos_arctan_pos (ε / R)
      rw [circleMap_zero_re]
      simpa [upper, positiveAxisKeyholeUpperAngle] using mul_pos hε hcos_pos
    rw [show
      ((((8 * (lower - upper)) : ℝ) •
          (circleMap 0 ε upper * Complex.I)) : ℂ).im =
        (8 * (lower - upper)) * (circleMap 0 ε upper).re by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    exact mul_pos hfactor_pos hre_pos
  have him_eq :
      ((((8 : ℝ) • (circleMap 0 ε θ - circleMap 0 R θ)) : ℂ)).im =
        ((((8 * (lower - upper)) : ℝ) •
            (circleMap 0 ε upper * Complex.I)) : ℂ).im := by
    simpa using congrArg Complex.im hcompare
  linarith

/-- Helper for Remark III.6-extra-7: the explicit clockwise inner-arc model has the expected
one-sided tangent at the quarter breakpoint. -/
lemma positiveAxisKeyhole_inner_arc_hasDerivWithinAt_one_quarter
    (R ε : ℝ) :
    HasDerivWithinAt
      (fun t : ℝ ↦
        circleMap 0 ε
          (AffineMap.lineMap
            (positiveAxisKeyholeUpperAngle R ε)
            (positiveAxisKeyholeLowerAngle R ε)
            (8 * t - 1)))
      (((8 * (positiveAxisKeyholeLowerAngle R ε -
            positiveAxisKeyholeUpperAngle R ε)) : ℝ) •
        (circleMap 0 ε (positiveAxisKeyholeLowerAngle R ε) * Complex.I))
      (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
  let upper : ℝ := positiveAxisKeyholeUpperAngle R ε
  let lower : ℝ := positiveAxisKeyholeLowerAngle R ε
  have hparam :
      HasDerivAt
        (fun t : ℝ ↦ AffineMap.lineMap upper lower (8 * t - 1))
        (8 * (lower - upper)) (1 / 4 : ℝ) := by
    -- Differentiate the affine angle parameter before composing with `circleMap`.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
      mul_assoc, mul_left_comm, mul_comm] using
      (AffineMap.hasDerivAt_lineMap
        (a := upper) (b := lower) (x := (8 : ℝ) * (1 / 4 : ℝ) - 1)).comp
        (1 / 4 : ℝ) (((hasDerivAt_id (1 / 4 : ℝ)).const_mul 8).sub_const 1)
  have hmodel_raw :
      HasDerivAt
        (fun t : ℝ ↦ circleMap 0 ε (AffineMap.lineMap upper lower (8 * t - 1)))
        (((8 * (lower - upper)) : ℝ) •
          (circleMap 0 ε
            (AffineMap.lineMap upper lower ((8 : ℝ) * (1 / 4 : ℝ) - 1)) *
            Complex.I))
        (1 / 4 : ℝ) := by
    -- The circular arc derivative is the usual `circleMap * I` tangent multiplied by the angular
    -- speed.
    simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
      two_mul, mul_assoc, mul_left_comm, mul_comm] using
      (hasDerivAt_circleMap 0 ε
        (AffineMap.lineMap upper lower ((8 : ℝ) * (1 / 4 : ℝ) - 1))).scomp
        (1 / 4 : ℝ) hparam
  have hquarter_param : (8 : ℝ) * (1 / 4 : ℝ) - 1 = 1 := by
    norm_num
  have hmodel :
      HasDerivAt
        (fun t : ℝ ↦ circleMap 0 ε (AffineMap.lineMap upper lower (8 * t - 1)))
        (((8 * (lower - upper)) : ℝ) •
          (circleMap 0 ε lower * Complex.I))
        (1 / 4 : ℝ) := by
    -- At `t = 1/4`, the affine parameter lands at the repaired lower slit-lip angle.
    convert hmodel_raw using 1
    rw [hquarter_param, AffineMap.lineMap_apply_one]
  simpa [upper, lower] using hmodel.hasDerivWithinAt

/-- Helper for Remark III.6-extra-7: the explicit lower-lip model has the expected one-sided
tangent at the quarter breakpoint. -/
lemma positiveAxisKeyhole_lower_lip_hasDerivWithinAt_one_quarter
    (R ε : ℝ) :
    HasDerivWithinAt
      (fun t : ℝ ↦
        AffineMap.lineMap
          (circleMap 0 ε (-positiveAxisKeyholeAngle R ε))
          (circleMap 0 R (-positiveAxisKeyholeAngle R ε))
          (4 * t - 1))
      ((4 : ℝ) •
        (circleMap 0 R (-positiveAxisKeyholeAngle R ε) -
          circleMap 0 ε (-positiveAxisKeyholeAngle R ε)))
      (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  have hmodel :
      HasDerivAt
        (fun t : ℝ ↦
          AffineMap.lineMap
            (circleMap 0 ε (-θ))
            (circleMap 0 R (-θ))
            (4 * t - 1))
        ((4 : ℝ) •
          (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
        (1 / 4 : ℝ) := by
    have hmodel' :
        HasDerivAt
          (fun t : ℝ ↦
            AffineMap.lineMap
              (circleMap 0 ε (-θ))
              (circleMap 0 R (-θ))
              (t * 4 - 1))
          ((4 : ℝ) •
            (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
          (1 / 4 : ℝ) := by
      -- The lower lip is an affine segment, so only the scalar speed `4` matters.
      simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
        two_mul, mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := circleMap 0 ε (-θ))
          (b := circleMap 0 R (-θ))
          (x := (1 / 4 : ℝ) * 4 - 1)).scomp
          (1 / 4 : ℝ) (((hasDerivAt_id (1 / 4 : ℝ)).mul_const 4).sub_const 1)
    simpa [mul_comm] using hmodel'
  simpa [θ] using hmodel.hasDerivWithinAt

/-- Helper for Remark III.6-extra-7: the second keyhole breakpoint is a genuine corner where the
clockwise inner arc meets the lower slit lip, so the real-plane parametrization is not
differentiable there within `[0, 1]`. -/
lemma positive_axis_keyhole_not_differentiable_at_one_quarter
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    ¬ DifferentiableWithinAt ℝ ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ) := by
  -- Route correction: compare the repaired inner-arc tangent against the lower-lip tangent, then
  -- separate them by the sign of their imaginary parts.
  intro hdiff
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  let upper : ℝ := positiveAxisKeyholeUpperAngle R ε
  let lower : ℝ := positiveAxisKeyholeLowerAngle R ε
  let γ : ℝ → ℂ := (positiveAxisKeyhole R ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ)
  let inner : ℝ → ℂ := fun t ↦
    circleMap 0 ε (AffineMap.lineMap upper lower (8 * t - 1))
  let lowerLip : ℝ → ℂ := fun t ↦
    AffineMap.lineMap
      (circleMap 0 ε (-θ))
      (circleMap 0 R (-θ))
      (4 * t - 1)
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ) := by
    -- Move from the real-plane curve back to the complex-valued contour.
    simpa [γ, ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
      (Complex.equivRealProdCLM.comp_differentiableWithinAt_iff.mp hdiff)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ) := by
    -- Record the ambient derivative before comparing the two adjacent branch tangents.
    simpa [d, γ] using hγdiff.hasDerivWithinAt
  have hinnerMain : HasDerivWithinAt γ d (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
    -- Restrict the ambient derivative to the inner-arc interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hlowerMain : HasDerivWithinAt γ d (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
    -- Restrict the same derivative to the lower-lip interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hinnerγ :
      HasDerivWithinAt γ
        (((8 * (lower - upper)) : ℝ) •
          (circleMap 0 ε lower * Complex.I))
        (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
    -- Use the repaired major-arc endpoint derivative helper.
    exact (positiveAxisKeyhole_inner_arc_hasDerivWithinAt_one_quarter R ε).congr_of_mem
      (fun t ht ↦ by simpa [γ, inner] using positive_axis_keyhole_eq_on_inner_arc R ε ht)
      (by constructor <;> norm_num)
  have hlowerγ :
      HasDerivWithinAt γ
        ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
        (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
    -- The lower lip still uses the original straight-segment derivative helper.
    exact (positiveAxisKeyhole_lower_lip_hasDerivWithinAt_one_quarter R ε).congr_of_mem
      (fun t ht ↦ by simpa [γ, lowerLip] using positive_axis_keyhole_eq_on_lower_lip R ε ht)
      (by constructor <;> norm_num)
  have hinnerUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 8 : ℝ) < 1 / 4 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hlowerUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 4 : ℝ) < 1 / 2 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hcompare :
      (((8 * (lower - upper)) : ℝ) •
        (circleMap 0 ε lower * Complex.I)) =
        ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) := by
    -- Uniqueness of within-derivatives forces the two one-sided tangents to agree.
    calc
      (((8 * (lower - upper)) : ℝ) •
          (circleMap 0 ε lower * Complex.I))
          = derivWithin γ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
              symm
              exact hinnerγ.derivWithin hinnerUD
      _ = d := hinnerMain.derivWithin hinnerUD
      _ = derivWithin γ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
            symm
            exact hlowerMain.derivWithin hlowerUD
      _ = ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :=
            hlowerγ.derivWithin hlowerUD
  have hR : 0 < R := lt_trans hε hεR
  have hθ_pos : 0 < θ := by
    simpa [θ, positiveAxisKeyholeAngle] using Real.arctan_pos.mpr (div_pos hε hR)
  have hinner_im_pos :
      0 <
        ((((8 * (lower - upper)) : ℝ) •
            (circleMap 0 ε lower * Complex.I)) : ℂ).im := by
    have hfactor_pos : 0 < 8 * (lower - upper) := by
      have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
      nlinarith [horder.1]
    have hcos_pos : 0 < Real.cos θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.cos_arctan_pos (ε / R)
    have hre_pos : 0 < (circleMap 0 ε lower).re := by
      have hcos :
          Real.cos (positiveAxisKeyholeLowerAngle R ε) = Real.cos θ := by
        dsimp [lower, positiveAxisKeyholeLowerAngle, positiveAxisKeyholeAngle]
        rw [show 2 * Real.pi - Real.arctan (ε / R) = -Real.arctan (ε / R) + 2 * Real.pi by ring,
          Real.cos_add_two_pi, Real.cos_neg]
      rw [show (circleMap 0 ε lower).re = ε * Real.cos θ by
        simp [lower, circleMap_zero_re, hcos]]
      exact mul_pos hε hcos_pos
    rw [show
      ((((8 * (lower - upper)) : ℝ) •
          (circleMap 0 ε lower * Complex.I)) : ℂ).im =
        (8 * (lower - upper)) * (circleMap 0 ε lower).re by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    exact mul_pos hfactor_pos hre_pos
  have hlower_im_neg :
      ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) : ℂ)).im < 0 := by
    have hsin_pos : 0 < Real.sin θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.sin_arctan_pos.mpr (div_pos hε hR)
    have hsin :
        Real.sin (-θ) = -Real.sin θ := by
      simpa using Real.sin_neg θ
    have him_diff :
        (circleMap 0 R (-θ) - circleMap 0 ε (-θ)).im =
          (R - ε) * (-Real.sin θ) := by
      simp [sub_eq_add_neg, circleMap_zero_im, hsin]
      ring
    rw [show
      ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) : ℂ)).im =
        4 * (circleMap 0 R (-θ) - circleMap 0 ε (-θ)).im by
          simp [mul_assoc, mul_left_comm, mul_comm]]
    rw [him_diff]
    have hcore : (R - ε) * (-Real.sin θ) < 0 := by
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hεR) (by linarith)
    exact mul_neg_of_pos_of_neg (by norm_num) hcore
  have him_eq :
      ((((8 * (lower - upper)) : ℝ) •
          (circleMap 0 ε lower * Complex.I)) : ℂ).im =
        ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :
            ℂ)).im := by
    simpa using congrArg Complex.im hcompare
  linarith
  /-
  -- Route correction: compare the inner-arc and lower-lip tangents at the shared breakpoint,
  -- then separate them by the sign of their real parts.
  intro hdiff
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  let γ : ℝ → ℂ := (positiveAxisKeyhole R ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ)
  let inner : ℝ → ℂ := fun t ↦
    circleMap 0 ε (AffineMap.lineMap θ (-θ) (8 * t - 1))
  let lower : ℝ → ℂ := fun t ↦
    AffineMap.lineMap
      (circleMap 0 ε (-θ))
      (circleMap 0 R (-θ))
      (4 * t - 1)
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ) := by
    -- Move from the real-plane curve back to the complex-valued contour.
    simpa [γ, ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
      (Complex.equivRealProdCLM.comp_differentiableWithinAt_iff.mp hdiff)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ) := by
    simpa [d, γ] using hγdiff.hasDerivWithinAt
  have hinnerMain : HasDerivWithinAt γ d (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
    -- Restrict the ambient derivative to the inner-arc interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hlowerMain : HasDerivWithinAt γ d (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
    -- Restrict the same derivative to the lower-lip interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hinnerγ :
      HasDerivWithinAt γ
        (((8 * ((-θ) - θ)) : ℝ) •
          (circleMap 0 ε (-θ) * Complex.I))
        (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
    -- Use the dedicated branch derivative so the main corner proof only does derivative
    -- uniqueness, not repeated elaboration of the branch model.
    exact (positiveAxisKeyhole_inner_arc_hasDerivWithinAt_one_quarter R ε).congr_of_mem
      (fun t ht ↦ by simpa [γ, inner, θ] using positive_axis_keyhole_eq_on_inner_arc R ε ht)
      (by constructor <;> norm_num)
  have hlowerγ :
      HasDerivWithinAt γ
        ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
        (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
    -- The lower lip uses the matching affine-segment derivative helper.
    exact (positiveAxisKeyhole_lower_lip_hasDerivWithinAt_one_quarter R ε).congr_of_mem
      (fun t ht ↦ by simpa [γ, lower, θ] using positive_axis_keyhole_eq_on_lower_lip R ε ht)
      (by constructor <;> norm_num)
  have hinnerUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 8 : ℝ) < 1 / 4 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hlowerUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 4 : ℝ) < 1 / 2 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hcompare :
      (((8 * ((-θ) - θ)) : ℝ) •
        (circleMap 0 ε (-θ) * Complex.I)) =
        ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) := by
    -- Uniqueness of within-derivatives forces the two one-sided tangents to agree.
    calc
      (((8 * ((-θ) - θ)) : ℝ) •
          (circleMap 0 ε (-θ) * Complex.I))
          = derivWithin γ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
              symm
              exact hinnerγ.derivWithin hinnerUD
      _ = d := hinnerMain.derivWithin hinnerUD
      _ = derivWithin γ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
            symm
            exact hlowerMain.derivWithin hlowerUD
      _ = ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :=
            hlowerγ.derivWithin hlowerUD
  have hR : 0 < R := lt_trans hε hεR
  have hθ_pos : 0 < θ := by
    simpa [θ, positiveAxisKeyholeAngle] using Real.arctan_pos.mpr (div_pos hε hR)
  have hinner_re_neg :
      ((((8 * ((-θ) - θ)) : ℝ) •
          (circleMap 0 ε (-θ) * Complex.I)) : ℂ).re < 0 := by
    have hfactor_neg : 8 * ((-θ) - θ) < 0 := by
      nlinarith [Real.pi_pos, hθ_pos]
    have hsin_pos : 0 < Real.sin θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.sin_arctan_pos.mpr (div_pos hε hR)
    have hcore : 0 < ε * Real.sin θ := by
      exact mul_pos hε hsin_pos
    have hsin :
        Real.sin (-θ) = -Real.sin θ := by
      simpa using Real.sin_neg θ
    have him :
        (circleMap 0 ε (-θ)).im = -(ε * Real.sin θ) := by
      rw [circleMap_zero_im, hsin]
      ring
    rw [show
      ((((8 * ((-θ) - θ)) : ℝ) •
          (circleMap 0 ε (-θ) * Complex.I)) : ℂ).re =
        (8 * ((-θ) - θ)) * (-(circleMap 0 ε (-θ)).im) by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    rw [him]
    nlinarith
  have hlower_re_pos :
      0 <
        ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :
            ℂ)).re := by
    have hcos_pos : 0 < Real.cos θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.cos_arctan_pos (ε / R)
    have hcore : 0 < (R - ε) * Real.cos θ := by
      exact mul_pos (sub_pos.mpr hεR) hcos_pos
    have hcos :
        Real.cos (-θ) = Real.cos θ := by
      simpa using Real.cos_neg θ
    have hcos' :
        Real.cos (-θ) = Real.cos θ := hcos
    have hre_diff :
        (circleMap 0 R (-θ) - circleMap 0 ε (-θ)).re =
          (R - ε) * Real.cos θ := by
      simp [sub_eq_add_neg, circleMap_zero_re, hcos']
      ring
    rw [show
      ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :
          ℂ)).re =
        4 * (circleMap 0 R (-θ) - circleMap 0 ε (-θ)).re by
          simp [mul_assoc, mul_left_comm, mul_comm]]
    rw [hre_diff]
    nlinarith
  have hre_eq :
      ((((8 * ((-θ) - θ)) : ℝ) •
          (circleMap 0 ε (-θ) * Complex.I)) : ℂ).re =
        ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :
            ℂ)).re := by
    simpa using congrArg Complex.re hcompare
  linarith
  -/

/-- Helper for Remark III.6-extra-7: the third keyhole breakpoint is a genuine corner where the
lower slit lip meets the outer arc, so the real-plane parametrization is not differentiable there
within `[0, 1]`. -/
lemma positive_axis_keyhole_not_differentiable_at_one_half
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    ¬ DifferentiableWithinAt ℝ ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
  -- Route correction: compare the lower-lip tangent against the repaired outer-arc tangent, then
  -- separate them by the sign of their real parts.
  intro hdiff
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  let upper : ℝ := positiveAxisKeyholeUpperAngle R ε
  let lower : ℝ := positiveAxisKeyholeLowerAngle R ε
  let γ : ℝ → ℂ := (positiveAxisKeyhole R ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ)
  let lowerLip : ℝ → ℂ := fun t ↦
    AffineMap.lineMap
      (circleMap 0 ε (-θ))
      (circleMap 0 R (-θ))
      (4 * t - 1)
  let outer : ℝ → ℂ := fun t ↦
    circleMap 0 R (AffineMap.lineMap lower upper (2 * t - 1))
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
    -- Move from the real-plane curve back to the complex-valued contour.
    simpa [γ, ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
      (Complex.equivRealProdCLM.comp_differentiableWithinAt_iff.mp hdiff)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
    -- Record the ambient derivative before comparing the two adjacent branch tangents.
    simpa [d, γ] using hγdiff.hasDerivWithinAt
  have hlowerMain : HasDerivWithinAt γ d (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    -- Restrict the ambient derivative to the lower-lip interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have houterMain : HasDerivWithinAt γ d (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
    -- Restrict the same derivative to the outer-arc interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hlowerγ :
      HasDerivWithinAt γ
        ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
        (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    -- Differentiate the affine lower-lip model at the terminal endpoint.
    have hmodel :
        HasDerivAt lowerLip
          ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
          (1 / 2 : ℝ) := by
      have hmodel' :
          HasDerivAt
            (fun t : ℝ ↦
              AffineMap.lineMap
                (circleMap 0 ε (-θ))
                (circleMap 0 R (-θ))
                (t * 4 - 1))
            ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
            (1 / 2 : ℝ) := by
        simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
          two_mul, mul_assoc, mul_left_comm, mul_comm] using
          (AffineMap.hasDerivAt_lineMap
            (a := circleMap 0 ε (-θ))
            (b := circleMap 0 R (-θ))
            (x := (1 / 2 : ℝ) * 4 - 1)).scomp
            (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).mul_const 4).sub_const 1)
      simpa [lowerLip, mul_comm] using hmodel'
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, lowerLip] using positive_axis_keyhole_eq_on_lower_lip R ε ht)
      (by constructor <;> norm_num)
  have houterγ :
      HasDerivWithinAt γ
        (((2 * (upper - lower)) : ℝ) •
          (circleMap 0 R lower * Complex.I))
        (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
    -- Differentiate the repaired outer major arc at its initial endpoint.
    have hparam :
        HasDerivAt
          (fun t : ℝ ↦ AffineMap.lineMap lower upper (2 * t - 1))
          (2 * (upper - lower))
          (1 / 2 : ℝ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := lower) (b := upper) (x := (2 : ℝ) * (1 / 2 : ℝ) - 1)).comp
          (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).sub_const 1)
    have hmodel_raw :
        HasDerivAt outer
          (((2 * (upper - lower)) : ℝ) •
            (circleMap 0 R
              (AffineMap.lineMap lower upper ((2 : ℝ) * (1 / 2 : ℝ) - 1)) *
              Complex.I))
          (1 / 2 : ℝ) := by
      simpa [outer, smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add,
        add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using
        (hasDerivAt_circleMap 0 R
          (AffineMap.lineMap lower upper ((2 : ℝ) * (1 / 2 : ℝ) - 1))).scomp
          (1 / 2 : ℝ) hparam
    have hstart_param : (2 : ℝ) * (1 / 2 : ℝ) - 1 = 0 := by
      norm_num
    have hmodel :
        HasDerivAt outer
          (((2 * (upper - lower)) : ℝ) •
            (circleMap 0 R lower * Complex.I))
          (1 / 2 : ℝ) := by
      convert hmodel_raw using 1
      rw [hstart_param, AffineMap.lineMap_apply_zero]
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, outer] using positive_axis_keyhole_eq_on_outer_arc R ε ht)
      (by constructor <;> norm_num)
  have hlowerUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 4 : ℝ) < 1 / 2 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have houterUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 2 : ℝ) < 1 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hcompare :
      ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) =
        (((2 * (upper - lower)) : ℝ) •
          (circleMap 0 R lower * Complex.I)) := by
    -- Uniqueness of within-derivatives forces the two one-sided tangents to agree.
    calc
      ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
          = derivWithin γ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
              symm
              exact hlowerγ.derivWithin hlowerUD
      _ = d := hlowerMain.derivWithin hlowerUD
      _ = derivWithin γ (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
            symm
            exact houterMain.derivWithin houterUD
      _ =
          (((2 * (upper - lower)) : ℝ) •
            (circleMap 0 R lower * Complex.I)) :=
            houterγ.derivWithin houterUD
  have hR : 0 < R := lt_trans hε hεR
  have hθ_pos : 0 < θ := by
    simpa [θ, positiveAxisKeyholeAngle] using Real.arctan_pos.mpr (div_pos hε hR)
  have hlower_re_pos :
      0 <
        ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) : ℂ)).re := by
    have hcos_pos : 0 < Real.cos θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.cos_arctan_pos (ε / R)
    have hcos :
        Real.cos (-θ) = Real.cos θ := by
      simpa using Real.cos_neg θ
    have hre_diff :
        (circleMap 0 R (-θ) - circleMap 0 ε (-θ)).re =
          (R - ε) * Real.cos θ := by
      simp [sub_eq_add_neg, circleMap_zero_re, hcos]
      ring
    rw [show
      ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) : ℂ)).re =
        4 * (circleMap 0 R (-θ) - circleMap 0 ε (-θ)).re by
          simp [mul_assoc, mul_left_comm, mul_comm]]
    rw [hre_diff]
    have hcore : 0 < (R - ε) * Real.cos θ := by
      exact mul_pos (sub_pos.mpr hεR) hcos_pos
    exact mul_pos (by norm_num) hcore
  have houter_re_neg :
      ((((2 * (upper - lower)) : ℝ) •
          (circleMap 0 R lower * Complex.I)) : ℂ).re < 0 := by
    have hfactor_neg : 2 * (upper - lower) < 0 := by
      have horder := positiveAxisKeyhole_majorArc_angle_order (R := R) (ε := ε) hε hεR
      nlinarith [horder.1]
    have hsin_pos : 0 < Real.sin θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.sin_arctan_pos.mpr (div_pos hε hR)
    have him_neg :
        (circleMap 0 R lower).im = -(R * Real.sin θ) := by
      have hsin :
          Real.sin (positiveAxisKeyholeLowerAngle R ε) = -Real.sin θ := by
        dsimp [lower, positiveAxisKeyholeLowerAngle, positiveAxisKeyholeAngle]
        rw [show 2 * Real.pi - Real.arctan (ε / R) = -Real.arctan (ε / R) + 2 * Real.pi by ring,
          Real.sin_add_two_pi, Real.sin_neg]
      rw [circleMap_zero_im, hsin]
      ring
    rw [show
      ((((2 * (upper - lower)) : ℝ) •
          (circleMap 0 R lower * Complex.I)) : ℂ).re =
        (2 * (upper - lower)) * (-(circleMap 0 R lower).im) by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    rw [him_neg]
    have hcore : 0 < R * Real.sin θ := by
      exact mul_pos hR hsin_pos
    nlinarith
  have hre_eq :
      ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) : ℂ)).re =
        ((((2 * (upper - lower)) : ℝ) •
            (circleMap 0 R lower * Complex.I)) : ℂ).re := by
    simpa using congrArg Complex.re hcompare
  linarith
  /-
  -- Route correction: compare the lower-lip and outer-arc tangents at the shared corner, then
  -- separate them by the sign of their imaginary parts.
  intro hdiff
  let θ : ℝ := positiveAxisKeyholeAngle R ε
  let γ : ℝ → ℂ := (positiveAxisKeyhole R ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ)
  let lower : ℝ → ℂ := fun t ↦
    AffineMap.lineMap
      (circleMap 0 ε (-θ))
      (circleMap 0 R (-θ))
      (4 * t - 1)
  let outer : ℝ → ℂ := fun t ↦
    circleMap 0 R
      (AffineMap.lineMap (-θ) θ (2 * t - 1))
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
    -- Move from the real-plane curve back to the complex-valued contour.
    simpa [γ, ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
      (Complex.equivRealProdCLM.comp_differentiableWithinAt_iff.mp hdiff)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
    simpa [d, γ] using hγdiff.hasDerivWithinAt
  have hlowerMain : HasDerivWithinAt γ d (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    -- Restrict the ambient derivative to the lower-lip interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have houterMain : HasDerivWithinAt γ d (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
    -- Restrict the same derivative to the outer-arc interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hlowerγ :
      HasDerivWithinAt γ
        ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
        (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    -- Differentiate the affine lower-lip model and transfer it back to the explicit contour.
    have hmodel :
        HasDerivAt lower
          ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
          (1 / 2 : ℝ) := by
      have hmodel' :
          HasDerivAt
            (fun t : ℝ ↦
              AffineMap.lineMap
                (circleMap 0 ε (-θ))
                (circleMap 0 R (-θ))
                (t * 4 - 1))
            ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
            (1 / 2 : ℝ) := by
        simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
          two_mul, mul_assoc, mul_left_comm, mul_comm] using
          (AffineMap.hasDerivAt_lineMap
            (a := circleMap 0 ε (-θ))
            (b := circleMap 0 R (-θ))
            (x := (1 / 2 : ℝ) * 4 - 1)).scomp
            (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).mul_const 4).sub_const 1)
      simpa [lower, mul_comm] using hmodel'
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, lower] using positive_axis_keyhole_eq_on_lower_lip R ε ht)
      (by constructor <;> norm_num)
  have houterγ :
      HasDerivWithinAt γ
        (((2 * (θ - (-θ))) : ℝ) •
          (circleMap 0 R (-θ) * Complex.I))
        (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
    -- Differentiate the outer circular arc through its affine angle parameter.
    have hparam :
        HasDerivAt
          (fun t : ℝ ↦ AffineMap.lineMap (-θ) θ (2 * t - 1))
          (2 * (θ - (-θ))) (1 / 2 : ℝ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := -θ) (b := θ) (x := (2 : ℝ) * (1 / 2 : ℝ) - 1)).comp
          (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).sub_const 1)
    have hmodel :
        HasDerivAt outer
          (((2 * (θ - (-θ))) : ℝ) •
            (circleMap 0 R (-θ) * Complex.I))
          (1 / 2 : ℝ) := by
      simpa [outer, smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add,
        add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using
        (hasDerivAt_circleMap 0 R
          (AffineMap.lineMap (-θ) θ ((2 : ℝ) * (1 / 2 : ℝ) - 1))).scomp
          (1 / 2 : ℝ) hparam
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, outer] using positive_axis_keyhole_eq_on_outer_arc R ε ht)
      (by constructor <;> norm_num)
  have hlowerUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 4 : ℝ) < 1 / 2 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have houterUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 2 : ℝ) < 1 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hcompare :
      ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) =
        (((2 * (θ - (-θ))) : ℝ) •
          (circleMap 0 R (-θ) * Complex.I)) := by
    -- Uniqueness of within-derivatives forces the two one-sided tangents to agree.
    calc
      ((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ)))
          = derivWithin γ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
              symm
              exact hlowerγ.derivWithin hlowerUD
      _ = d := hlowerMain.derivWithin hlowerUD
      _ = derivWithin γ (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
            symm
            exact houterMain.derivWithin houterUD
      _ =
          (((2 * (θ - (-θ))) : ℝ) •
            (circleMap 0 R (-θ) * Complex.I)) :=
            houterγ.derivWithin houterUD
  have hR : 0 < R := lt_trans hε hεR
  have hθ_pos : 0 < θ := by
    simpa [θ, positiveAxisKeyholeAngle] using Real.arctan_pos.mpr (div_pos hε hR)
  have hlower_im_neg :
      ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :
          ℂ)).im < 0 := by
    have hsin_pos : 0 < Real.sin θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.sin_arctan_pos.mpr (div_pos hε hR)
    have hcore : (R - ε) * (-Real.sin θ) < 0 := by
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hεR) (by linarith)
    have hsin :
        Real.sin (-θ) = -Real.sin θ := by
      simpa using Real.sin_neg θ
    have hsin' :
        Real.sin (-θ) = -Real.sin θ := hsin
    rw [show
      ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :
          ℂ)).im =
        4 * ((R - ε) * (-Real.sin θ)) by
          simp [circleMap_zero_im, sub_eq_add_neg, hsin']
          ring]
    exact mul_neg_of_pos_of_neg (by norm_num) hcore
  have houter_im_pos :
      0 <
        ((((2 * (θ - (-θ))) : ℝ) •
            (circleMap 0 R (-θ) * Complex.I)) : ℂ).im := by
    have hfactor_pos : 0 < 2 * (θ - (-θ)) := by
      nlinarith [Real.pi_pos, hθ_pos]
    have hcos_pos : 0 < Real.cos θ := by
      simpa [θ, positiveAxisKeyholeAngle] using Real.cos_arctan_pos (ε / R)
    have hre_pos : 0 < (circleMap 0 R (-θ)).re := by
      have hcos :
          Real.cos (-θ) = Real.cos θ := by
        simpa using Real.cos_neg θ
      rw [circleMap_zero_re, hcos]
      exact mul_pos hR hcos_pos
    rw [show
      ((((2 * (θ - (-θ))) : ℝ) •
          (circleMap 0 R (-θ) * Complex.I)) : ℂ).im =
        (2 * (θ - (-θ))) * (circleMap 0 R (-θ)).re by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    exact mul_pos hfactor_pos hre_pos
  have him_eq :
      ((((4 : ℝ) • (circleMap 0 R (-θ) - circleMap 0 ε (-θ))) :
          ℂ)).im =
        ((((2 * (θ - (-θ))) : ℝ) •
            (circleMap 0 R (-θ) * Complex.I)) : ℂ).im := by
    simpa using congrArg Complex.im hcompare
  linarith
  -/

/-- Helper for Remark III.6-extra-7: every interior regular parameter of the keyhole contour lies
on exactly one of the four open source branches. This is the branch dispatcher needed before the
later boundary-straightening proof can case-split cleanly. -/
lemma positiveAxisKeyhole_regular_parameter_mem_open_branch
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) {t : I}
    (ht : t.1 ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((positiveAxisKeyhole R ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t.1) :
    t.1 ∈ Set.Ioo (0 : ℝ) (1 / 8) ∨
      t.1 ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) ∨
      t.1 ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∨
      t.1 ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) := by
  -- Route correction: reuse the stable interval dispatcher, then exclude the three interior
  -- breakpoints by the corner nondifferentiability lemmas.
  rcases positive_axis_keyhole_parameter_cases t with
    ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
  · exfalso
    simpa [ht0] using ht.1
  · exact Or.inl htupper
  · exfalso
    exact
      (positive_axis_keyhole_not_differentiable_at_one_eighth hε hεR)
        (by simpa [ht18] using hdiff)
  · exact Or.inr <| Or.inl htinner
  · exfalso
    exact
      (positive_axis_keyhole_not_differentiable_at_one_quarter hε hεR)
        (by simpa [ht14] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inl htlower
  · exfalso
    exact
      (positive_axis_keyhole_not_differentiable_at_one_half hε hεR)
        (by simpa [ht12] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inr htouter
  · exfalso
    simpa [ht1] using ht.2


/-- Helper for Remark III.6-extra-7: points on the upper lip of the keyhole lie on the line of
slope `ε / R`. This is the first concrete bridge from the explicit contour parametrization to the
wedge-annulus boundary geometry. -/
lemma positiveAxisKeyhole_upper_lip_line
    (R ε ρ : ℝ) :
    (circleMap 0 ρ (positiveAxisKeyholeAngle R ε)).im =
      (ε / R) * (circleMap 0 ρ (positiveAxisKeyholeAngle R ε)).re := by
  -- Unfold the circle coordinates at the keyhole angle and use the standard arctangent formulas.
  rw [circleMap_zero_im, circleMap_zero_re, positiveAxisKeyholeAngle,
    Real.sin_arctan, Real.cos_arctan]
  ring_nf

/-- Helper for Remark III.6-extra-7: points on the lower lip of the keyhole lie on the line of
slope `-(ε / R)`. This is the companion boundary equation for the lower slit edge. -/
lemma positiveAxisKeyhole_lower_lip_line
    (R ε ρ : ℝ) :
    (circleMap 0 ρ (-positiveAxisKeyholeAngle R ε)).im =
      -((ε / R) * (circleMap 0 ρ (-positiveAxisKeyholeAngle R ε)).re) := by
  -- Normalize the angle by one full turn, then reduce again to the arctangent identities.
  have hsin :
      Real.sin (-positiveAxisKeyholeAngle R ε) =
        -Real.sin (positiveAxisKeyholeAngle R ε) := by
    simpa using Real.sin_neg (positiveAxisKeyholeAngle R ε)
  have hcos :
      Real.cos (-positiveAxisKeyholeAngle R ε) =
        Real.cos (positiveAxisKeyholeAngle R ε) := by
    simpa using Real.cos_neg (positiveAxisKeyholeAngle R ε)
  rw [circleMap_zero_im, circleMap_zero_re, hsin, hcos, positiveAxisKeyholeAngle,
    Real.sin_arctan, Real.cos_arctan]
  ring_nf

/-- Helper for Remark III.6-extra-7: every nonzero point on the upper lip has positive real part,
so it belongs to the positive-axis side of the wedge model. -/
lemma positiveAxisKeyhole_upper_lip_re_pos
    {R ε ρ : ℝ} (hρ : 0 < ρ) :
    0 < (circleMap 0 ρ (positiveAxisKeyholeAngle R ε)).re := by
  -- The opening angle is an arctangent, so its cosine is always positive.
  rw [circleMap_zero_re, positiveAxisKeyholeAngle]
  exact mul_pos hρ (Real.cos_arctan_pos (ε / R))

/-- Helper for Remark III.6-extra-7: every nonzero point on the lower lip also has positive real
part, which is the remaining sign condition in the wedge-annulus geometry. -/
lemma positiveAxisKeyhole_lower_lip_re_pos
    {R ε ρ : ℝ} (hρ : 0 < ρ) :
    0 < (circleMap 0 ρ (-positiveAxisKeyholeAngle R ε)).re := by
  -- The lower-lip angle differs from the upper one by a full turn and a sign change.
  have hcos :
      Real.cos (-positiveAxisKeyholeAngle R ε) =
        Real.cos (positiveAxisKeyholeAngle R ε) := by
    simpa using Real.cos_neg (positiveAxisKeyholeAngle R ε)
  rw [circleMap_zero_re, hcos, positiveAxisKeyholeAngle]
  exact mul_pos hρ (Real.cos_arctan_pos (ε / R))

/-- Helper for Remark III.6-extra-7: a circular arc obtained by mapping an affine angle segment
through `circleMap` is differentiable as a path. -/
lemma positiveAxisKeyhole_circle_segment_isDifferentiable (ρ α β : ℝ) :
    ((Path.segment α β).map (continuous_circleMap 0 ρ)).IsDifferentiable := by
  -- The angular parameter is affine on `[0, 1]`, so composing it with `circleMap` stays `C¹`.
  rw [Path.IsDifferentiable]
  have hcontDiff :
      ContDiffOn ℝ 1
        (fun t : ℝ ↦ circleMap 0 ρ ((ContinuousAffineMap.lineMap (R := ℝ) α β) t))
        (Set.Icc (0 : ℝ) 1) := by
    simpa [Function.comp] using
      ((contDiff_circleMap 0 ρ).comp
        (ContinuousAffineMap.contDiff (ContinuousAffineMap.lineMap (R := ℝ) α β))).contDiffOn
  refine hcontDiff.congr ?_
  intro t ht
  rw [Path.extend_apply _ ht]
  simp [ContinuousAffineMap.coe_lineMap_eq, Path.map_coe, Path.segment_apply,
    AffineMap.lineMap_apply_module]

/-- Helper for Remark III.6-extra-7: the positive-axis keyhole contour is piecewise
differentiable because it is built from two straight segments and two smooth circular arcs. -/
lemma positiveAxisKeyhole_isPiecewiseDifferentiable (R ε : ℝ) :
    (positiveAxisKeyhole R ε).IsPiecewiseDifferentiable := by
  let upperAngle : ℝ := positiveAxisKeyholeUpperAngle R ε
  let lowerAngle : ℝ := positiveAxisKeyholeLowerAngle R ε
  have hupper :
      (Path.segment
        (circleMap 0 R upperAngle)
        (circleMap 0 ε upperAngle)).IsPiecewiseDifferentiable :=
    Path.segment_isPiecewiseDifferentiable _ _
  have hinner :
      ((Path.segment upperAngle lowerAngle).map
        (continuous_circleMap 0 ε)).IsDifferentiable :=
    positiveAxisKeyhole_circle_segment_isDifferentiable ε upperAngle lowerAngle
  have hlower :
      (Path.segment (circleMap 0 ε lowerAngle)
        (circleMap 0 R lowerAngle)).IsDifferentiable :=
    Path.segment_isDifferentiable _ _
  have houter :
      ((Path.segment lowerAngle upperAngle).map
        (continuous_circleMap 0 R)).IsDifferentiable :=
    positiveAxisKeyhole_circle_segment_isDifferentiable R lowerAngle upperAngle
  -- Append the four smooth pieces in the same source order used to define the keyhole contour.
  have hupper_inner := hupper.trans_of_isDifferentiable hinner
  have hupper_inner_lower := hupper_inner.trans_of_isDifferentiable hlower
  have hall := hupper_inner_lower.trans_of_isDifferentiable houter
  simpa [positiveAxisKeyhole, upperAngle, lowerAngle] using hall
