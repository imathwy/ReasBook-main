module

public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Definition_61_3.SimpleClosedCurve
public import Topology_Munkres_2000.Book.Definition_53_4.Torus
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Real.Pi.Bounds

public section

namespace Torus

/-- A small coordinate circle in the standard torus. -/
def smallCircle : Set Torus :=
  Set.range fun z : Circle ↦
    (Circle.exp ((z : ℂ).re / 8), Circle.exp ((z : ℂ).im / 8))

/-- A meridian in the standard torus. -/
def meridian : Set Torus :=
  Set.range fun z : Circle ↦ (z, 1)

/-- Helper for Exercise 61.1: the parametrization of the small coordinate circle. -/
private noncomputable def smallCircleParam : Circle → Torus :=
  fun z ↦ (Circle.exp ((z : ℂ).re / 8), Circle.exp ((z : ℂ).im / 8))

/-- Helper for Exercise 61.1: the small coordinate-circle parametrization is an embedding. -/
private lemma smallCircleParam_isEmbedding :
    Topology.IsEmbedding smallCircleParam := by
  -- Continuity follows coordinatewise from the real and imaginary projections.
  have hcontinuous : Continuous smallCircleParam := by
    unfold smallCircleParam
    fun_prop
  -- Both angular coordinates lie in a fundamental interval for `Circle.exp`.
  have hinjective : Function.Injective smallCircleParam := by
    intro z w hzw
    have hre : (z : ℂ).re / 8 = (w : ℂ).re / 8 := by
      apply Circle.exp_injOn_Icc (a := -(1 / 8 : ℝ)) (b := 1 / 8)
      · linarith [Real.pi_gt_three]
      · constructor
        · have hz := Complex.abs_re_le_norm (z : ℂ)
          rw [Circle.norm_coe] at hz
          rw [abs_le] at hz
          linarith
        · have hz := Complex.abs_re_le_norm (z : ℂ)
          rw [Circle.norm_coe] at hz
          rw [abs_le] at hz
          linarith
      · constructor
        · have hw := Complex.abs_re_le_norm (w : ℂ)
          rw [Circle.norm_coe] at hw
          rw [abs_le] at hw
          linarith
        · have hw := Complex.abs_re_le_norm (w : ℂ)
          rw [Circle.norm_coe] at hw
          rw [abs_le] at hw
          linarith
      · exact congrArg Prod.fst hzw
    have him : (z : ℂ).im / 8 = (w : ℂ).im / 8 := by
      apply Circle.exp_injOn_Icc (a := -(1 / 8 : ℝ)) (b := 1 / 8)
      · linarith [Real.pi_gt_three]
      · constructor
        · have hz := Complex.abs_im_le_norm (z : ℂ)
          rw [Circle.norm_coe] at hz
          rw [abs_le] at hz
          linarith
        · have hz := Complex.abs_im_le_norm (z : ℂ)
          rw [Circle.norm_coe] at hz
          rw [abs_le] at hz
          linarith
      · constructor
        · have hw := Complex.abs_im_le_norm (w : ℂ)
          rw [Circle.norm_coe] at hw
          rw [abs_le] at hw
          linarith
        · have hw := Complex.abs_im_le_norm (w : ℂ)
          rw [Circle.norm_coe] at hw
          rw [abs_le] at hw
          linarith
      · exact congrArg Prod.snd hzw
    apply Circle.ext
    apply Complex.ext
    · linarith
    · linarith
  exact (hcontinuous.isClosedEmbedding hinjective).isEmbedding

/-- The subtype of the small coordinate-circle is a simple closed curve. -/
instance instIsSimpleClosedCurveSmallCircle :
    Topology.IsSimpleClosedCurve smallCircle := by
  -- The embedding identifies the circle with exactly the declared range.
  refine ⟨⟨?_⟩⟩
  exact (smallCircleParam_isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by rfl))).symm

/-- The subtype of the meridian is a simple closed curve. -/
instance instIsSimpleClosedCurveMeridian :
    Topology.IsSimpleClosedCurve meridian := by
  -- The standard product embedding identifies the circle with the meridian range.
  refine ⟨⟨?_⟩⟩
  exact ((isEmbedding_prodMkLeft (1 : Circle)).toHomeomorph.trans
    (Homeomorph.setCongr (by rfl))).symm

/-- Helper for Exercise 61.1: membership in the meridian is determined by the second coordinate. -/
private lemma mem_meridian_iff (p : Torus) : p ∈ meridian ↔ p.2 = 1 := by
  -- Unpack the range description and compare product coordinates.
  constructor
  · rintro ⟨z, rfl⟩
    rfl
  · intro hp
    exact ⟨p.1, Prod.ext rfl hp.symm⟩

/-- Helper for Exercise 61.1: the circle exponential is not one inside one open period. -/
private lemma circleExp_ne_one_of_mem_Ioo_zero_twoPi (t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) : Circle.exp t ≠ 1 := by
  -- Injectivity on the half-open fundamental interval distinguishes `t` from zero.
  intro hexp
  have hinjective := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
  have ht0 : t = 0 := hinjective ⟨ht.1.le, ht.2⟩
    ⟨le_rfl, Real.two_pi_pos⟩ (by simpa using hexp)
  exact (ne_of_gt ht.1) ht0

/-- Helper for Exercise 61.1: wrap a principal argument into the open interval `(0, 2 * π)`. -/
private noncomputable def wrappedCircleArg (z : Circle) : ℝ :=
  if 0 < Complex.arg z then Complex.arg z else Complex.arg z + 2 * Real.pi

/-- Helper for Exercise 61.1: a nonunit point's wrapped argument lies in one open period. -/
private lemma wrappedCircleArg_mem_Ioo (z : Circle) (hz : z ≠ 1) :
    wrappedCircleArg z ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
  -- Split according to whether the principal argument is already positive.
  by_cases harg : 0 < Complex.arg z
  · rw [wrappedCircleArg, if_pos harg]
    constructor
    · exact harg
    · linarith [Complex.arg_le_pi z, Real.pi_pos]
  · rw [wrappedCircleArg, if_neg harg]
    constructor
    · have harg_ne : Complex.arg z ≠ 0 := by
        simpa [Circle.arg_eq_zero] using hz
      have harg_neg : Complex.arg z < 0 := lt_of_le_of_ne (le_of_not_gt harg) harg_ne
      linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
    · have harg_ne : Complex.arg z ≠ 0 := by
        simpa [Circle.arg_eq_zero] using hz
      have harg_neg : Complex.arg z < 0 := lt_of_le_of_ne (le_of_not_gt harg) harg_ne
      linarith

/-- Helper for Exercise 61.1: exponentiating the wrapped argument recovers the circle point. -/
private lemma exp_wrappedCircleArg (z : Circle) :
    Circle.exp (wrappedCircleArg z) = z := by
  -- Adding one full period does not change the exponential.
  by_cases harg : 0 < Complex.arg z
  · rw [wrappedCircleArg, if_pos harg, Circle.exp_arg]
  · rw [wrappedCircleArg, if_neg harg, Circle.exp_add_two_pi, Circle.exp_arg]

/-- Helper for Exercise 61.1: an open-period angle gives a point outside the meridian. -/
private lemma meridianComplementValue_mem
    (x : Circle × Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    (x.1, Circle.exp x.2) ∈ meridianᶜ := by
  -- Complement membership is exactly nonunit second coordinate.
  rw [Set.mem_compl_iff, mem_meridian_iff]
  exact circleExp_ne_one_of_mem_Ioo_zero_twoPi x.2 x.2.property

/-- Helper for Exercise 61.1: a continuous parametrization of the meridian complement. -/
private noncomputable def meridianComplementParam :
    Circle × Set.Ioo (0 : ℝ) (2 * Real.pi) → (meridianᶜ : Set Torus) :=
  fun x ↦ ⟨(x.1, Circle.exp x.2), meridianComplementValue_mem x⟩

/-- Helper for Exercise 61.1: the meridian-complement parametrization is continuous. -/
private lemma meridianComplementParam_continuous :
    Continuous meridianComplementParam := by
  -- Continuity is inherited coordinatewise through the subtype topology.
  unfold meridianComplementParam
  fun_prop

/-- Helper for Exercise 61.1: the open-period parametrization covers the meridian complement. -/
private lemma meridianComplementParam_surjective :
    Function.Surjective meridianComplementParam := by
  -- Use the wrapped principal argument for the second coordinate.
  intro p
  have hp : p.1.2 ≠ 1 := by
    intro hpone
    exact p.2 ((mem_meridian_iff p.1).2 hpone)
  let t : Set.Ioo (0 : ℝ) (2 * Real.pi) :=
    ⟨wrappedCircleArg p.1.2, wrappedCircleArg_mem_Ioo p.1.2 hp⟩
  refine ⟨(p.1.1, t), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact exp_wrappedCircleArg p.1.2

/-- Helper for Exercise 61.1: the squared angular radius on the torus. -/
private noncomputable def angularRadiusSquared (p : Torus) : ℝ :=
  ‖(AddCircle.homeomorphCircle').symm p.1‖ ^ 2 +
    ‖(AddCircle.homeomorphCircle').symm p.2‖ ^ 2

/-- Helper for Exercise 61.1: the squared angular radius is continuous. -/
private lemma angularRadiusSquared_continuous :
    Continuous angularRadiusSquared := by
  -- The invariant is assembled from the inverse circle homeomorphism and the norm.
  unfold angularRadiusSquared
  fun_prop

/-- Helper for Exercise 61.1: angular norm agrees with absolute value on the principal interval. -/
private lemma angleNorm_exp_eq_abs (t : ℝ) (ht : |t| ≤ Real.pi) :
    ‖(AddCircle.homeomorphCircle').symm (Circle.exp t)‖ = |t| := by
  -- Rewrite the exponential as the homeomorphism applied to the angle class.
  have hangle :
      (AddCircle.homeomorphCircle').symm (Circle.exp t) = (t : Real.Angle) := by
    rw [← AddCircle.homeomorphCircle'_apply_mk]
    exact (AddCircle.homeomorphCircle').symm_apply_apply (t : Real.Angle)
  rw [hangle]
  exact (@AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) t (by positivity)).2
    (by simpa [abs_of_pos Real.pi_pos] using ht)

/-- Helper for Exercise 61.1: every point of the small circle has the threshold angular radius. -/
private lemma angularRadiusSquared_eq_of_mem_smallCircle {p : Torus}
    (hp : p ∈ smallCircle) : angularRadiusSquared p = (1 / 8 : ℝ) ^ 2 := by
  -- Normalize both angular coordinates of the defining parametrization.
  obtain ⟨z, rfl⟩ := hp
  have hre : |(z : ℂ).re / 8| ≤ Real.pi := by
    have hz := Complex.abs_re_le_norm (z : ℂ)
    rw [Circle.norm_coe] at hz
    norm_num [abs_div]
    nlinarith [Real.pi_gt_three]
  have him : |(z : ℂ).im / 8| ≤ Real.pi := by
    have hz := Complex.abs_im_le_norm (z : ℂ)
    rw [Circle.norm_coe] at hz
    norm_num [abs_div]
    nlinarith [Real.pi_gt_three]
  rw [angularRadiusSquared, angleNorm_exp_eq_abs _ hre, angleNorm_exp_eq_abs _ him]
  rw [sq_abs, sq_abs]
  have hnormSq : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    simpa only [pow_two, Complex.normSq_apply] using Circle.normSq_coe z
  nlinarith

/-- Helper for Exercise 61.1: the threshold angular-radius level is exactly the small circle. -/
private lemma mem_smallCircle_of_angularRadiusSquared_eq {p : Torus}
    (hp : angularRadiusSquared p = (1 / 8 : ℝ) ^ 2) : p ∈ smallCircle := by
  -- Scale the canonical angle representatives to form a unit complex parameter.
  let a : ℝ := Real.Angle.toReal ((AddCircle.homeomorphCircle').symm p.1)
  let b : ℝ := Real.Angle.toReal ((AddCircle.homeomorphCircle').symm p.2)
  have haNorm : ‖(AddCircle.homeomorphCircle').symm p.1‖ = |a| := by
    have haBound := Real.Angle.abs_toReal_le_pi
      ((AddCircle.homeomorphCircle').symm p.1)
    have hangle :
        (AddCircle.homeomorphCircle').symm p.1 = (a : Real.Angle) := by
      exact (Real.Angle.coe_toReal ((AddCircle.homeomorphCircle').symm p.1)).symm
    rw [hangle]
    exact (@AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) a (by positivity)).2
      (by norm_num [a, abs_of_pos Real.pi_pos]; exact haBound)
  have hbNorm : ‖(AddCircle.homeomorphCircle').symm p.2‖ = |b| := by
    have hbBound := Real.Angle.abs_toReal_le_pi
      ((AddCircle.homeomorphCircle').symm p.2)
    have hangle :
        (AddCircle.homeomorphCircle').symm p.2 = (b : Real.Angle) := by
      exact (Real.Angle.coe_toReal ((AddCircle.homeomorphCircle').symm p.2)).symm
    rw [hangle]
    exact (@AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) b (by positivity)).2
      (by norm_num [b, abs_of_pos Real.pi_pos]; exact hbBound)
  have hab : a ^ 2 + b ^ 2 = (1 / 8 : ℝ) ^ 2 := by
    rw [angularRadiusSquared, haNorm, hbNorm, sq_abs, sq_abs] at hp
    exact hp
  have hzNormSq : Complex.normSq (8 * a + (8 * b) * Complex.I) = 1 := by
    rw [Complex.normSq_apply]
    norm_num
    nlinarith
  have hzNorm : ‖(8 * a + (8 * b) * Complex.I : ℂ)‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow 2,
      pow_two, Complex.norm_mul_self_eq_normSq]
    exact hzNormSq
  let z : Circle :=
    ⟨8 * a + (8 * b) * Complex.I, mem_sphere_zero_iff_norm.2 hzNorm⟩
  refine ⟨z, ?_⟩
  apply Prod.ext
  · have hfirst : Circle.exp a = p.1 := by
      calc
        Circle.exp a = AddCircle.homeomorphCircle' (a : Real.Angle) :=
          (AddCircle.homeomorphCircle'_apply_mk a).symm
        _ = AddCircle.homeomorphCircle' ((AddCircle.homeomorphCircle').symm p.1) := by
          rw [Real.Angle.coe_toReal]
        _ = p.1 := AddCircle.homeomorphCircle'.apply_symm_apply p.1
    simpa [z, a] using hfirst
  · have hsecond : Circle.exp b = p.2 := by
      calc
        Circle.exp b = AddCircle.homeomorphCircle' (b : Real.Angle) :=
          (AddCircle.homeomorphCircle'_apply_mk b).symm
        _ = AddCircle.homeomorphCircle' ((AddCircle.homeomorphCircle').symm p.2) := by
          rw [Real.Angle.coe_toReal]
        _ = p.2 := AddCircle.homeomorphCircle'.apply_symm_apply p.2
    simpa [z, b] using hsecond

/-- Helper for Exercise 61.1: the torus identity has zero squared angular radius. -/
private lemma angularRadiusSquared_one_one :
    angularRadiusSquared ((1 : Circle), (1 : Circle)) = 0 := by
  -- Both unit coordinates correspond to the zero angle.
  rw [← Circle.exp_zero]
  rw [angularRadiusSquared, angleNorm_exp_eq_abs 0 (by simp [Real.pi_pos.le])]
  norm_num

/-- Helper for Exercise 61.1: a quarter-angle point lies above the small-circle radius. -/
private lemma angularRadiusSquared_quarter_one :
    angularRadiusSquared (Circle.exp (1 / 4 : ℝ), (1 : Circle)) = (1 / 4 : ℝ) ^ 2 := by
  -- Normalize the quarter-angle coordinate and the zero-angle coordinate.
  rw [← Circle.exp_zero]
  have hquarter : |(1 / 4 : ℝ)| ≤ Real.pi := by
    norm_num
    linarith [Real.pi_gt_three]
  rw [angularRadiusSquared, angleNorm_exp_eq_abs _ hquarter,
    angleNorm_exp_eq_abs 0 (by simp [Real.pi_pos.le])]
  norm_num

/-- Helper for Exercise 61.1: the small-circle complement is not preconnected. -/
private lemma smallCircle_complement_not_preconnected :
    ¬ PreconnectedSpace (smallCircleᶜ : Set Torus) := by
  -- A preconnected complement would lie wholly on one side of the radius threshold.
  intro hpreconnected
  let threshold : ℝ := (1 / 8 : ℝ) ^ 2
  have havoid : ∀ p ∈ smallCircleᶜ, angularRadiusSquared p ≠ threshold := by
    intro p hp hpeq
    exact hp (mem_smallCircle_of_angularRadiusSquared_eq hpeq)
  have hcontinuous : Continuous fun p : (smallCircleᶜ : Set Torus) ↦
      angularRadiusSquared p :=
    angularRadiusSquared_continuous.comp continuous_subtype_val
  have hsides := (isPreconnected_univ : IsPreconnected
      (Set.univ : Set (smallCircleᶜ : Set Torus))).mapsTo_Ioi_or_Iio
    hcontinuous.continuousOn
    (fun p _ ↦ havoid p p.property)
  have hbelow_mem : ((1 : Circle), (1 : Circle)) ∈ smallCircleᶜ := by
    intro hone
    have hradius := angularRadiusSquared_eq_of_mem_smallCircle hone
    rw [angularRadiusSquared_one_one] at hradius
    norm_num at hradius
  have habove_mem : (Circle.exp (1 / 4 : ℝ), (1 : Circle)) ∈ smallCircleᶜ := by
    intro hquarter
    have hradius := angularRadiusSquared_eq_of_mem_smallCircle hquarter
    rw [angularRadiusSquared_quarter_one] at hradius
    norm_num at hradius
  rcases hsides with habove | hbelow
  · have hpositive := habove (x := ⟨((1 : Circle), (1 : Circle)), hbelow_mem⟩)
      (by trivial)
    change threshold < angularRadiusSquared ((1 : Circle), (1 : Circle)) at hpositive
    rw [angularRadiusSquared_one_one] at hpositive
    norm_num [threshold] at hpositive
  · have hsmall := hbelow
      (x := ⟨(Circle.exp (1 / 4 : ℝ), (1 : Circle)), habove_mem⟩) (by trivial)
    change angularRadiusSquared (Circle.exp (1 / 4 : ℝ), (1 : Circle)) < threshold at hsmall
    rw [angularRadiusSquared_quarter_one] at hsmall
    norm_num [threshold] at hsmall

/-- Helper for Exercise 61.1: the small coordinate-circle separates the torus. -/
theorem smallCircle_separates : smallCircle.Separates := by
  -- Separation is exactly failure of preconnectedness of the complement.
  exact Set.separates_iff.mpr smallCircle_complement_not_preconnected

/-- Helper for Exercise 61.1: the meridian does not separate the torus. -/
theorem meridian_not_separates : ¬ meridian.Separates := by
  -- A continuous surjection from a path-connected product makes the complement path connected.
  letI : PathConnectedSpace (Set.Ioo (0 : ℝ) (2 * Real.pi)) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ioo (0 : ℝ) (2 * Real.pi)).isPathConnected
        ⟨Real.pi, Real.pi_pos, by linarith [Real.pi_pos]⟩)
  have hpath : PathConnectedSpace (meridianᶜ : Set Torus) :=
    meridianComplementParam_surjective.pathConnectedSpace
      meridianComplementParam_continuous
  exact fun hseparates ↦ (Set.separates_iff.mp hseparates) inferInstance

/-- Exercise 61.1: A simple closed curve in the torus may separate it or fail to separate it. -/
theorem simpleClosedCurve_separation_examples :
    smallCircle.Separates ∧ ¬ meridian.Separates := by
  -- The two explicit simple closed curves exhibit the contrasting behaviors.
  exact ⟨smallCircle_separates, meridian_not_separates⟩

end Torus
