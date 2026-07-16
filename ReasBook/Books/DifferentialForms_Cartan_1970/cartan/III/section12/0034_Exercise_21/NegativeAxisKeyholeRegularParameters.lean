import DifferentialForms_Cartan_1970.cartan.III.section12.«0034_Exercise_21».NegativeAxisKeyholeSimplicity

noncomputable section

open Complex MeasureTheory
open scoped Real unitInterval

lemma exercise21Delta_not_differentiable_at_one_eighth
    {r ε : ℝ} (hε : 0 < ε) (hεr : ε < r) :
    ¬ DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ) := by
  -- Route correction: compare the upper-lip and inner-arc tangents on their own closed branch
  -- intervals, then use uniqueness of within-derivatives at the shared breakpoint.
  intro hdiff
  let θ : ℝ := Real.arctan (ε / r)
  let γ : ℝ → ℂ := (exercise21Delta r ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ)
  let upper : ℝ → ℂ := fun t ↦
    AffineMap.lineMap (circleMap 0 r (Real.pi - θ)) (circleMap 0 ε (Real.pi - θ)) (8 * t)
  let inner : ℝ → ℂ := fun t ↦
    circleMap 0 ε
      (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) (8 * t - 1))
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ) := by
    -- Undo the `Complex.equivRealProd` wrapper so the tangent comparison happens in `ℂ`.
    simpa [γ, ClosedPath.realCurve, Function.comp, Path.toClosedPath] using
      (Complex.equivRealProdCLM.comp_differentiableWithinAt_iff.mp hdiff)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 8 : ℝ) := by
    simpa [d, γ] using hγdiff.hasDerivWithinAt
  have hupperMain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) := by
    -- Restrict the ambient derivative to the upper-lip branch interval.
    apply hmain.mono
    intro t ht
    constructor
    · exact ht.1
    · linarith [ht.2]
  have hinnerMain : HasDerivWithinAt γ d (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) := by
    -- Restrict the same derivative to the inner-arc branch interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hupperγ :
      HasDerivWithinAt γ ((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ)))
        (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) := by
    -- Differentiate the affine upper-lip model and transfer it back to the explicit contour.
    have hmodel :
        HasDerivAt upper
          ((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ))) (1 / 8 : ℝ) := by
      have hmodel' :
          HasDerivAt
            (fun t : ℝ ↦
              AffineMap.lineMap
                (circleMap 0 r (Real.pi - θ))
                (circleMap 0 ε (Real.pi - θ))
                (t * 8))
            ((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ)))
            (1 / 8 : ℝ) := by
        simpa [smul_eq_mul, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
          (AffineMap.hasDerivAt_lineMap
            (a := circleMap 0 r (Real.pi - θ))
            (b := circleMap 0 ε (Real.pi - θ))
            (x := (1 / 8 : ℝ) * 8)).scomp
            (1 / 8 : ℝ) ((hasDerivAt_id (1 / 8 : ℝ)).mul_const 8)
      simpa [upper, mul_comm] using hmodel'
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, upper] using exercise21Delta_eq_on_upper_lip r ε ht)
      (by constructor <;> norm_num)
  have hinnerγ :
      HasDerivWithinAt γ
        (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (Real.pi - θ) * Complex.I))
        (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) := by
    -- Differentiate the affine angle parameter first, then the clockwise inner circle.
    have hparam :
        HasDerivAt
          (fun t : ℝ ↦ AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) (8 * t - 1))
          (8 * ((-Real.pi + θ) - (Real.pi - θ))) (1 / 8 : ℝ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := Real.pi - θ) (b := -Real.pi + θ) (x := (8 : ℝ) * (1 / 8 : ℝ) - 1)).comp
          (1 / 8 : ℝ) (((hasDerivAt_id (1 / 8 : ℝ)).const_mul 8).sub_const 1)
    have hmodel :
        HasDerivAt inner
          (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
            (circleMap 0 ε (Real.pi - θ) * Complex.I))
          (1 / 8 : ℝ) := by
      simpa [inner, smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add,
        add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using
        (hasDerivAt_circleMap 0 ε
          (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) ((8 : ℝ) * (1 / 8 : ℝ) - 1))).scomp
          (1 / 8 : ℝ) hparam
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, inner] using exercise21Delta_eq_on_inner_arc r ε ht)
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
      ((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ))) =
        (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (Real.pi - θ) * Complex.I)) := by
    -- Uniqueness of within-derivatives on the two branch intervals forces the tangents to agree.
    calc
      ((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ)))
          = derivWithin γ (Set.Icc (0 : ℝ) (1 / 8 : ℝ)) (1 / 8 : ℝ) := by
              symm
              exact hupperγ.derivWithin hupperUD
      _ = d := hupperMain.derivWithin hupperUD
      _ = derivWithin γ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 8 : ℝ) := by
            symm
            exact hinnerMain.derivWithin hinnerUD
      _ =
          (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
            (circleMap 0 ε (Real.pi - θ) * Complex.I)) :=
            hinnerγ.derivWithin hinnerUD
  have hr : 0 < r := lt_trans hε hεr
  have hθ_pos : 0 < θ := by
    simpa [θ] using Real.arctan_pos.mpr (div_pos hε hr)
  have hupper_im_neg :
      ((((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ))) : ℂ)).im < 0 := by
    have hsin_pos : 0 < Real.sin θ := by
      simpa [θ] using (Real.sin_arctan_pos.mpr (div_pos hε hr))
    have hcore : (ε - r) * Real.sin θ < 0 := by
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hεr) hsin_pos
    have him_formula :
        ((((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ))) : ℂ)).im =
          8 * ((ε - r) * Real.sin θ) := by
      have hsin : Real.sin (Real.pi + -θ) = Real.sin θ := by
        have hangle : Real.pi + -θ = Real.pi - θ := by
          ring
        rw [hangle, Real.sin_pi_sub]
      simp [smul_eq_mul, circleMap_zero_im, sub_eq_add_neg]
      rw [hsin]
      ring_nf
    rw [him_formula]
    exact mul_neg_of_pos_of_neg (by norm_num) hcore
  have hinner_im_pos :
      0 <
        ((((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
            (circleMap 0 ε (Real.pi - θ) * Complex.I)) : ℂ).im := by
    have hθ_bounds := exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
    have hpi_sub_pos : 0 < Real.pi - θ := by
      have hθ_lt_pi : θ < Real.pi := by
        linarith [hθ_bounds.2, Real.pi_pos]
      linarith
    have hfactor_neg : 8 * ((-Real.pi + θ) - (Real.pi - θ)) < 0 := by
      have hfactor_eq : 8 * ((-Real.pi + θ) - (Real.pi - θ)) = -16 * (Real.pi - θ) := by
        ring
      rw [hfactor_eq]
      nlinarith
    have hre_neg : (circleMap 0 ε (Real.pi - θ)).re < 0 := by
      simpa [θ] using
        (exercise21Delta_upper_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε)
    rw [show
      ((((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (Real.pi - θ) * Complex.I)) : ℂ).im =
        (8 * ((-Real.pi + θ) - (Real.pi - θ))) *
          (circleMap 0 ε (Real.pi - θ)).re by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    exact mul_pos_of_neg_of_neg hfactor_neg hre_neg
  have him_eq :
      ((((8 : ℝ) • (circleMap 0 ε (Real.pi - θ) - circleMap 0 r (Real.pi - θ))) : ℂ)).im =
        ((((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
            (circleMap 0 ε (Real.pi - θ) * Complex.I)) : ℂ).im := by
    simpa using congrArg Complex.im hcompare
  linarith

lemma exercise21Delta_not_differentiable_at_one_quarter
    {r ε : ℝ} (hε : 0 < ε) (hεr : ε < r) :
    ¬ DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ) := by
  -- Compare the inner-arc and lower-lip tangents at the second corner of the keyhole contour.
  intro hdiff
  let θ : ℝ := Real.arctan (ε / r)
  let γ : ℝ → ℂ := (exercise21Delta r ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ)
  let inner : ℝ → ℂ := fun t ↦
    circleMap 0 ε
      (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) (8 * t - 1))
  let lower : ℝ → ℂ := fun t ↦
    AffineMap.lineMap
      (circleMap 0 ε (-Real.pi + θ))
      (circleMap 0 r (-Real.pi + θ))
      (4 * t - 1)
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 4 : ℝ) := by
    -- Move from the real-plane curve back to the complex-valued path.
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
        (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (-Real.pi + θ) * Complex.I))
        (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
    -- Differentiate the angular branch model and transfer it back to the explicit contour.
    have hparam :
        HasDerivAt
          (fun t : ℝ ↦ AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) (8 * t - 1))
          (8 * ((-Real.pi + θ) - (Real.pi - θ))) (1 / 4 : ℝ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := Real.pi - θ) (b := -Real.pi + θ) (x := (8 : ℝ) * (1 / 4 : ℝ) - 1)).comp
          (1 / 4 : ℝ) (((hasDerivAt_id (1 / 4 : ℝ)).const_mul 8).sub_const 1)
    have hmodel :
        HasDerivAt inner
          (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
            (circleMap 0 ε (-Real.pi + θ) * Complex.I))
          (1 / 4 : ℝ) := by
      have hmodel_raw :
          HasDerivAt inner
            (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
              (circleMap 0 ε
                (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) ((8 : ℝ) * (1 / 4 : ℝ) - 1)) *
                Complex.I))
            (1 / 4 : ℝ) := by
        simpa [inner, smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add,
          add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using
          (hasDerivAt_circleMap 0 ε
            (AffineMap.lineMap (Real.pi - θ) (-Real.pi + θ) ((8 : ℝ) * (1 / 4 : ℝ) - 1))).scomp
            (1 / 4 : ℝ) hparam
      have hquarter_param : (8 : ℝ) * (1 / 4 : ℝ) - 1 = 1 := by
        norm_num
      convert hmodel_raw using 1
      rw [hquarter_param, AffineMap.lineMap_apply_one]
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, inner] using exercise21Delta_eq_on_inner_arc r ε ht)
      (by constructor <;> norm_num)
  have hlowerγ :
      HasDerivWithinAt γ
        ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
        (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
    -- Differentiate the affine lower-lip model and transfer it back to the explicit contour.
    have hmodel :
        HasDerivAt lower
          ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
          (1 / 4 : ℝ) := by
      have hmodel' :
          HasDerivAt
            (fun t : ℝ ↦
              AffineMap.lineMap
                (circleMap 0 ε (-Real.pi + θ))
                (circleMap 0 r (-Real.pi + θ))
                (t * 4 - 1))
            ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
            (1 / 4 : ℝ) := by
        simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
          two_mul, mul_assoc, mul_left_comm, mul_comm] using
          (AffineMap.hasDerivAt_lineMap
            (a := circleMap 0 ε (-Real.pi + θ))
            (b := circleMap 0 r (-Real.pi + θ))
            (x := (1 / 4 : ℝ) * 4 - 1)).scomp
            (1 / 4 : ℝ) (((hasDerivAt_id (1 / 4 : ℝ)).mul_const 4).sub_const 1)
      simpa [lower, mul_comm] using hmodel'
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, lower] using exercise21Delta_eq_on_lower_lip r ε ht)
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
      (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
        (circleMap 0 ε (-Real.pi + θ) * Complex.I)) =
        ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) := by
    -- Uniqueness of within-derivatives forces the two one-sided tangents to agree.
    calc
      (((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (-Real.pi + θ) * Complex.I))
          = derivWithin γ (Set.Icc (1 / 8 : ℝ) (1 / 4 : ℝ)) (1 / 4 : ℝ) := by
              symm
              exact hinnerγ.derivWithin hinnerUD
      _ = d := hinnerMain.derivWithin hinnerUD
      _ = derivWithin γ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 4 : ℝ) := by
            symm
            exact hlowerMain.derivWithin hlowerUD
      _ = ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) :=
            hlowerγ.derivWithin hlowerUD
  have hr : 0 < r := lt_trans hε hεr
  have hθ_pos : 0 < θ := by
    simpa [θ] using Real.arctan_pos.mpr (div_pos hε hr)
  have hinner_im_pos :
      0 <
        ((((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
            (circleMap 0 ε (-Real.pi + θ) * Complex.I)) : ℂ).im := by
    have hθ_bounds := exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
    have hpi_sub_pos : 0 < Real.pi - θ := by
      have hθ_lt_pi : θ < Real.pi := by
        linarith [hθ_bounds.2, Real.pi_pos]
      linarith
    have hfactor_neg : 8 * ((-Real.pi + θ) - (Real.pi - θ)) < 0 := by
      have hfactor_eq : 8 * ((-Real.pi + θ) - (Real.pi - θ)) = -16 * (Real.pi - θ) := by
        ring
      rw [hfactor_eq]
      nlinarith
    have hre_neg : (circleMap 0 ε (-Real.pi + θ)).re < 0 := by
      simpa [θ] using
        (exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := ε) hε)
    rw [show
      ((((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (-Real.pi + θ) * Complex.I)) : ℂ).im =
        (8 * ((-Real.pi + θ) - (Real.pi - θ))) *
          (circleMap 0 ε (-Real.pi + θ)).re by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    exact mul_pos_of_neg_of_neg hfactor_neg hre_neg
  have hlower_im_neg :
      ((((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) : ℂ)).im < 0 := by
    have hsin_pos : 0 < Real.sin θ := by
      simpa [θ] using (Real.sin_arctan_pos.mpr (div_pos hε hr))
    have hsin_neg : -Real.sin θ < 0 := by
      linarith
    have hcore : (r - ε) * (-Real.sin θ) < 0 := by
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hεr) hsin_neg
    rw [show
      ((((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) : ℂ)).im =
        4 * ((r - ε) * (-Real.sin θ)) by
          simp [circleMap_zero_im, sub_eq_add_neg]
          have hsin :
              Real.sin (-Real.pi + θ) = -Real.sin θ := by
            rw [show -Real.pi + θ = θ - Real.pi by ring]
            simp [Real.sin_sub]
          rw [hsin]
          ring]
    exact mul_neg_of_pos_of_neg (by norm_num) hcore
  have him_eq :
      ((((8 * ((-Real.pi + θ) - (Real.pi - θ))) : ℝ) •
          (circleMap 0 ε (-Real.pi + θ) * Complex.I)) : ℂ).im =
        ((((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) : ℂ)).im := by
    simpa using congrArg Complex.im hcompare
  linarith

lemma exercise21Delta_not_differentiable_at_one_half
    {r ε : ℝ} (hε : 0 < ε) (hεr : ε < r) :
    ¬ DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
  -- Compare the lower-lip and outer-arc tangents at the third corner of the keyhole contour.
  intro hdiff
  let θ : ℝ := Real.arctan (ε / r)
  let γ : ℝ → ℂ := (exercise21Delta r ε).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ)
  let lower : ℝ → ℂ := fun t ↦
    AffineMap.lineMap
      (circleMap 0 ε (-Real.pi + θ))
      (circleMap 0 r (-Real.pi + θ))
      (4 * t - 1)
  let outer : ℝ → ℂ := fun t ↦
    circleMap 0 r
      (AffineMap.lineMap (-Real.pi + θ) (Real.pi - θ) (2 * t - 1))
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
        ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
        (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    -- Differentiate the affine lower-lip model and transfer it back to the explicit contour.
    have hmodel :
        HasDerivAt lower
          ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
          (1 / 2 : ℝ) := by
      have hmodel' :
          HasDerivAt
            (fun t : ℝ ↦
              AffineMap.lineMap
                (circleMap 0 ε (-Real.pi + θ))
                (circleMap 0 r (-Real.pi + θ))
                (t * 4 - 1))
            ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
            (1 / 2 : ℝ) := by
        simpa [smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul,
          two_mul, mul_assoc, mul_left_comm, mul_comm] using
          (AffineMap.hasDerivAt_lineMap
            (a := circleMap 0 ε (-Real.pi + θ))
            (b := circleMap 0 r (-Real.pi + θ))
            (x := (1 / 2 : ℝ) * 4 - 1)).scomp
            (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).mul_const 4).sub_const 1)
      simpa [lower, mul_comm] using hmodel'
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, lower] using exercise21Delta_eq_on_lower_lip r ε ht)
      (by constructor <;> norm_num)
  have houterγ :
      HasDerivWithinAt γ
        (((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
          (circleMap 0 r (-Real.pi + θ) * Complex.I))
        (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
    -- Differentiate the outer circular arc through its affine angle parameter.
    have hparam :
        HasDerivAt
          (fun t : ℝ ↦ AffineMap.lineMap (-Real.pi + θ) (Real.pi - θ) (2 * t - 1))
          (2 * ((Real.pi - θ) - (-Real.pi + θ))) (1 / 2 : ℝ) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul, two_mul,
        mul_assoc, mul_left_comm, mul_comm] using
        (AffineMap.hasDerivAt_lineMap
          (a := -Real.pi + θ) (b := Real.pi - θ) (x := (2 : ℝ) * (1 / 2 : ℝ) - 1)).comp
          (1 / 2 : ℝ) (((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).sub_const 1)
    have hmodel :
        HasDerivAt outer
          (((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
            (circleMap 0 r (-Real.pi + θ) * Complex.I))
          (1 / 2 : ℝ) := by
      simpa [outer, smul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add,
        add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using
        (hasDerivAt_circleMap 0 r
          (AffineMap.lineMap (-Real.pi + θ) (Real.pi - θ) ((2 : ℝ) * (1 / 2 : ℝ) - 1))).scomp
          (1 / 2 : ℝ) hparam
    exact hmodel.hasDerivWithinAt.congr_of_mem
      (fun t ht ↦ by simpa [γ, outer] using exercise21Delta_eq_on_outer_arc r ε ht)
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
      ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) =
        (((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
          (circleMap 0 r (-Real.pi + θ) * Complex.I)) := by
    -- Uniqueness of within-derivatives forces the two one-sided tangents to agree.
    calc
      ((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ)))
          = derivWithin γ (Set.Icc (1 / 4 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
              symm
              exact hlowerγ.derivWithin hlowerUD
      _ = d := hlowerMain.derivWithin hlowerUD
      _ = derivWithin γ (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
            symm
            exact houterMain.derivWithin houterUD
      _ =
          (((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
            (circleMap 0 r (-Real.pi + θ) * Complex.I)) :=
            houterγ.derivWithin houterUD
  have hr : 0 < r := lt_trans hε hεr
  have hθ_pos : 0 < θ := by
    simpa [θ] using Real.arctan_pos.mpr (div_pos hε hr)
  have hlower_re_neg :
      ((((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) : ℂ)).re < 0 := by
    have hcos_pos : 0 < Real.cos θ := by
      simpa [θ] using Real.cos_arctan_pos (ε / r)
    have hcos_neg : -Real.cos θ < 0 := by
      linarith
    have hcore : (r - ε) * (-Real.cos θ) < 0 := by
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hεr) hcos_neg
    rw [show
      ((((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) : ℂ)).re =
        4 * ((r - ε) * (-Real.cos θ)) by
          simp [circleMap_zero_re, sub_eq_add_neg]
          have hcos :
              Real.cos (-Real.pi + θ) = -Real.cos θ := by
            rw [show -Real.pi + θ = θ - Real.pi by ring]
            simp [Real.cos_sub]
          rw [hcos]
          ring]
    exact mul_neg_of_pos_of_neg (by norm_num) hcore
  have houter_re_pos :
      0 <
        ((((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
            (circleMap 0 r (-Real.pi + θ) * Complex.I)) : ℂ).re := by
    have hθ_bounds := exercise21_keyhole_angle_bounds (r := r) (ε := ε) hε hεr
    have hpi_sub_pos : 0 < Real.pi - θ := by
      have hθ_lt_pi : θ < Real.pi := by
        linarith [hθ_bounds.2, Real.pi_pos]
      linarith
    have hfactor_pos : 0 < 2 * ((Real.pi - θ) - (-Real.pi + θ)) := by
      have hfactor_eq : 2 * ((Real.pi - θ) - (-Real.pi + θ)) = 4 * (Real.pi - θ) := by
        ring
      rw [hfactor_eq]
      nlinarith
    have hre_neg : (circleMap 0 r (-Real.pi + θ)).re < 0 := by
      simpa [θ] using
        (exercise21Delta_lower_lip_re_neg (r := r) (ε := ε) (ρ := r) hr)
    have him_neg : (circleMap 0 r (-Real.pi + θ)).im < 0 := by
      have hline :
          (circleMap 0 r (-Real.pi + θ)).im =
            (ε / r) * (circleMap 0 r (-Real.pi + θ)).re := by
        simpa [θ] using exercise21Delta_lower_lip_line r ε r
      rw [hline]
      exact mul_neg_of_pos_of_neg (div_pos hε hr) hre_neg
    rw [show
      ((((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
          (circleMap 0 r (-Real.pi + θ) * Complex.I)) : ℂ).re =
        (2 * ((Real.pi - θ) - (-Real.pi + θ))) *
          (-(circleMap 0 r (-Real.pi + θ)).im) by
          simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_left_comm, mul_comm]]
    exact mul_pos hfactor_pos (by linarith)
  have hre_eq :
      ((((4 : ℝ) • (circleMap 0 r (-Real.pi + θ) - circleMap 0 ε (-Real.pi + θ))) : ℂ)).re =
        ((((2 * ((Real.pi - θ) - (-Real.pi + θ))) : ℝ) •
            (circleMap 0 r (-Real.pi + θ) * Complex.I)) : ℂ).re := by
    simpa using congrArg Complex.re hcompare
  linarith

lemma exercise21Delta_regular_parameter_mem_open_branch
    (r ε : ℝ) (hε : 0 < ε) (hεr : ε < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((exercise21Delta r ε).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀) :
    t₀ ∈ Set.Ioo (0 : ℝ) (1 / 8) ∨
      t₀ ∈ Set.Ioo (1 / 8 : ℝ) (1 / 4) ∨
      t₀ ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2) ∨
      t₀ ∈ Set.Ioo (1 / 2 : ℝ) (1 : ℝ) := by
  let t : I := ⟨t₀, ⟨ht₀.1.le, ht₀.2.le⟩⟩
  -- The interval dispatcher leaves only the four open branches and the three genuine corners.
  rcases exercise21Delta_parameter_cases t with
    ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
  · exfalso
    have ht0' : t₀ = 0 := by
      simpa [t] using ht0
    linarith [ht₀.1, ht0']
  · exact Or.inl htupper
  · exfalso
    have ht18' : t₀ = 1 / 8 := by
      simpa [t] using ht18
    exact
      (exercise21Delta_not_differentiable_at_one_eighth hε hεr)
        (by simpa [ht18'] using hdiff)
  · exact Or.inr <| Or.inl htinner
  · exfalso
    have ht14' : t₀ = 1 / 4 := by
      simpa [t] using ht14
    exact
      (exercise21Delta_not_differentiable_at_one_quarter hε hεr)
        (by simpa [ht14'] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inl htlower
  · exfalso
    have ht12' : t₀ = 1 / 2 := by
      simpa [t] using ht12
    exact
      (exercise21Delta_not_differentiable_at_one_half hε hεr)
        (by simpa [ht12'] using hdiff)
  · exact Or.inr <| Or.inr <| Or.inr htouter
  · exfalso
    have ht1' : t₀ = 1 := by
      simpa [t] using ht1
    linarith [ht₀.2, ht1']

