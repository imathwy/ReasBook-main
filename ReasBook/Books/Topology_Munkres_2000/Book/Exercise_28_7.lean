module

public import Topology_Munkres_2000.Book.Definition_28_6.ShrinkingMap
public import Topology_Munkres_2000.Book.Definition_28_7.Contraction
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Order.Compact

public section

universe u

open scoped NNReal

/-- Technical companion for Exercise 28.7, part (a): a contraction on a nonempty compact
metric space has a unique fixed point. -/
theorem ContractingWith.existsUnique_fixedPoint_of_compact {X : Type u} [MetricSpace X]
    [CompactSpace X] [Nonempty X] {K : ℝ≥0} {f : X → X} (hf : ContractingWith K f) :
    ∃! x, Function.IsFixedPt f x := by
  -- Compact metric spaces are complete, so the Banach fixed-point API supplies the point.
  refine ⟨hf.fixedPoint f, hf.fixedPoint_isFixedPt, ?_⟩
  -- Its library uniqueness theorem closes the existential uniqueness field.
  intro x hx
  exact hf.fixedPoint_unique hx

/-- The source-facing conclusion of Exercise 28.7, part (a), in existential form. -/
theorem IsContraction.existsUnique_fixedPoint_of_compact {X : Type u} [MetricSpace X]
    [CompactSpace X] [Nonempty X] {f : X → X} (hf : IsContraction f) :
    ∃! x, Function.IsFixedPt f x := by
  obtain ⟨K, hK⟩ := hf.exists_contractingWith
  exact hK.existsUnique_fixedPoint_of_compact

/-- Helper for Exercise 28.7: a shrinking map has at most one fixed point. -/
theorem IsShrinkingMap.fixedPoint_unique {X : Type u} [MetricSpace X] {f : X → X}
    (hf : IsShrinkingMap f) {x y : X} (hx : Function.IsFixedPt f x)
    (hy : Function.IsFixedPt f y) : x = y := by
  -- Distinct fixed points would have to be strictly closer than themselves.
  by_contra hxy
  have hlt := hf.dist_lt x y hxy
  rw [hx, hy] at hlt
  exact (lt_irrefl _ hlt)

/-- The conclusion of Exercise 28.7, part (b): a shrinking map on a nonempty compact metric
space has a unique fixed point. -/
theorem IsShrinkingMap.existsUnique_fixedPoint_of_compact {X : Type u} [MetricSpace X]
    [CompactSpace X] [Nonempty X] {f : X → X} (hf : IsShrinkingMap f) :
    ∃! x, Function.IsFixedPt f x := by
  -- Minimize the displacement of the map on the compact whole space.
  have hcontinuous : Continuous (fun x ↦ dist (f x) x) :=
    hf.continuous.dist continuous_id
  obtain ⟨x, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hcontinuous.continuousOn
  have hfixed : Function.IsFixedPt f x := by
    -- A nonfixed minimizer would have strictly smaller displacement at its image.
    rw [Function.IsFixedPt]
    by_contra hfixed
    have hne : x ≠ f x := Ne.symm hfixed
    have hshrink := hf.dist_lt x (f x) hne
    have himage_min := isMinOn_iff.mp hmin (f x) (Set.mem_univ (f x))
    rw [dist_comm (f x) x, dist_comm (f (f x)) (f x)] at himage_min
    exact (not_lt_of_ge himage_min hshrink)
  refine ⟨x, hfixed, ?_⟩
  -- Strict shrinking gives uniqueness independently of compactness.
  intro y hy
  exact hf.fixedPoint_unique hy hfixed

/-- The real function `x ↦ x - x ^ 2 / 2` used for the interval example. -/
noncomputable def intervalQuadratic (x : ℝ) : ℝ :=
  x - x ^ 2 / 2

/-- Part (c1) of Exercise 28.7: `intervalQuadratic` maps `Set.Icc 0 1` into itself. -/
theorem intervalQuadratic_mapsTo :
    Set.MapsTo intervalQuadratic (Set.Icc (0 : ℝ) 1) (Set.Icc 0 1) := by
  intro x hx
  constructor
  · -- On the unit interval, `x * (1 - x)` witnesses the lower bound.
    have hproduct : 0 ≤ x * (1 - x) :=
      mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
    unfold intervalQuadratic
    nlinarith
  · -- Subtracting a nonnegative square preserves the upper endpoint bound.
    unfold intervalQuadratic
    nlinarith [sq_nonneg x]

/-- The restriction of `intervalQuadratic` to a self-map of `Set.Icc 0 1`. -/
noncomputable def intervalQuadraticMap : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 :=
  intervalQuadratic_mapsTo.restrict intervalQuadratic (Set.Icc (0 : ℝ) 1) (Set.Icc 0 1)

/-- The underlying real value of `intervalQuadraticMap x` is `intervalQuadratic x`. -/
@[simp]
theorem intervalQuadraticMap_val (x : Set.Icc (0 : ℝ) 1) :
    (intervalQuadraticMap x : ℝ) = intervalQuadratic x :=
  intervalQuadratic_mapsTo.val_restrict_apply x

/-- Helper for Exercise 28.7: between ordered points of `Set.Icc 0 1`, the increment of
`intervalQuadratic` is positive and strictly smaller than the original increment. -/
lemma intervalQuadratic_sub_lt {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (hxy : x < y) :
    0 < intervalQuadratic y - intervalQuadratic x ∧
      intervalQuadratic y - intervalQuadratic x < y - x := by
  -- Factor the increment; its second factor lies strictly between zero and one.
  have hsum_pos : 0 < x + y := by linarith [hx.1]
  have hsum_lt : x + y < 2 := by linarith [hy.2]
  have hfactor_pos : 0 < 1 - (x + y) / 2 := by linarith
  have hfactor_lt : 1 - (x + y) / 2 < 1 := by linarith
  have hincrement :
      intervalQuadratic y - intervalQuadratic x =
        (y - x) * (1 - (x + y) / 2) := by
    unfold intervalQuadratic
    ring
  rw [hincrement]
  constructor
  · exact mul_pos (sub_pos.mpr hxy) hfactor_pos
  · simpa only [mul_one] using
      mul_lt_mul_of_pos_left hfactor_lt (sub_pos.mpr hxy)

/-- Helper for Exercise 28.7: `intervalQuadratic` strictly decreases real distances on
`Set.Icc 0 1`. -/
lemma intervalQuadratic_dist_lt {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (hxy : x ≠ y) :
    dist (intervalQuadratic x) (intervalQuadratic y) < dist x y := by
  -- Orient the two points, then use the corresponding positive increment estimate.
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · obtain ⟨hpositive, hshort⟩ := intervalQuadratic_sub_lt hx hy hlt
    have hvalue_lt : intervalQuadratic x < intervalQuadratic y := sub_pos.mp hpositive
    rw [Real.dist_eq, Real.dist_eq, abs_of_neg (sub_neg.mpr hvalue_lt),
      abs_of_neg (sub_neg.mpr hlt)]
    simpa only [neg_sub] using hshort
  · obtain ⟨hpositive, hshort⟩ := intervalQuadratic_sub_lt hy hx hgt
    rw [Real.dist_eq, Real.dist_eq, abs_of_pos hpositive,
      abs_of_pos (sub_pos.mpr hgt)]
    exact hshort

/-- Part (c2) of Exercise 28.7: the interval self-map `intervalQuadraticMap` is shrinking. -/
theorem intervalQuadraticMap_isShrinking : IsShrinkingMap intervalQuadraticMap := by
  rw [isShrinkingMap_iff]
  intro x y hxy
  -- Push the subtype distance comparison down to the real-valued helper.
  simpa only [Subtype.dist_eq, intervalQuadraticMap_val] using
    intervalQuadratic_dist_lt x.property y.property (Subtype.coe_injective.ne hxy)

/-- Helper for Exercise 28.7: zero belongs to the real unit interval. -/
lemma zero_mem_real_Icc : (0 : ℝ) ∈ Set.Icc 0 1 := by
  -- Both endpoint inequalities are immediate.
  exact ⟨le_rfl, zero_le_one⟩

/-- Helper for Exercise 28.7: if `K < 1`, then `1 - (K : ℝ)` belongs to the unit interval. -/
lemma one_sub_coe_mem_Icc (K : ℝ≥0) (hK : K < 1) :
    1 - (K : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  -- Coercion preserves nonnegativity and the strict upper bound on `K`.
  constructor
  · exact sub_nonneg.mpr (NNReal.coe_le_one.mpr hK.le)
  · linarith [K.coe_nonneg]

/-- Part (c3) of Exercise 28.7: the interval self-map `intervalQuadraticMap` is
not a contraction. -/
theorem intervalQuadraticMap_not_contracting :
    ¬ IsContraction intervalQuadraticMap := by
  intro hcontraction
  obtain ⟨K, hK⟩ := hcontraction.exists_contractingWith
  -- Test the Lipschitz inequality at `0` and `1 - K`.
  let x : Set.Icc (0 : ℝ) 1 := ⟨0, zero_mem_real_Icc⟩
  let y : Set.Icc (0 : ℝ) 1 := ⟨1 - (K : ℝ), one_sub_coe_mem_Icc K hK.1⟩
  have hbound := hK.dist_le_mul x y
  have hK_real : (K : ℝ) < 1 := NNReal.coe_lt_one.mpr hK.1
  have hy_pos : 0 < 1 - (K : ℝ) := sub_pos.mpr hK_real
  have hzero : intervalQuadratic 0 = 0 := by
    norm_num [intervalQuadratic]
  have himage_nonneg : 0 ≤ intervalQuadratic (1 - (K : ℝ)) :=
    (intervalQuadratic_mapsTo (one_sub_coe_mem_Icc K hK.1)).1
  simp only [Subtype.dist_eq, intervalQuadraticMap_val, Real.dist_eq, x, y,
    hzero, zero_sub, abs_neg] at hbound
  rw [abs_of_nonneg himage_nonneg, abs_of_nonneg hy_pos.le] at hbound
  -- The displayed inequality would force the positive square `(1 - K) ^ 2` to vanish.
  unfold intervalQuadratic at hbound
  nlinarith [sq_pos_of_pos hy_pos]

/-- The real function `x ↦ (x + Real.sqrt (x ^ 2 + 1)) / 2`. -/
noncomputable def sqrtAverage (x : ℝ) : ℝ :=
  (x + Real.sqrt (x ^ 2 + 1)) / 2

/-- Helper for Exercise 28.7: the derivative of `sqrtAverage` has its expected closed form. -/
lemma sqrtAverage_hasDerivAt (x : ℝ) :
    HasDerivAt sqrtAverage ((1 + x / Real.sqrt (x ^ 2 + 1)) / 2) x := by
  unfold sqrtAverage
  -- Differentiate the positive radicand before applying the square-root rule.
  have hinner : HasDerivAt (fun y : ℝ ↦ y ^ 2 + 1) (2 * x) x := by
    have hpower := (hasDerivAt_pow 2 x).add_const 1
    have hpower_coefficient : (2 : ℝ) * x ^ (2 - 1) = 2 * x := by
      norm_num
    exact hpower.congr_deriv hpower_coefficient
  have hradicand_pos : 0 < x ^ 2 + 1 := by positivity
  have hsqrt_ne : Real.sqrt (x ^ 2 + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hradicand_pos)
  have hroot := hinner.sqrt hradicand_pos.ne'
  have hcoefficient :
      (1 + (2 * x) / (2 * Real.sqrt (x ^ 2 + 1))) / 2 =
        (1 + x / Real.sqrt (x ^ 2 + 1)) / 2 := by
    field_simp
  -- Normalize the coefficient once, keeping the named function opaque afterwards.
  rw [← hcoefficient]
  simpa only [Pi.add_apply] using
    ((hasDerivAt_id' (x := x)).add hroot).div_const 2

/-- Helper for Exercise 28.7: the derivative of `sqrtAverage` is strictly between zero and one. -/
lemma sqrtAverage_deriv_mem_Ioo (x : ℝ) :
    deriv sqrtAverage x ∈ Set.Ioo (0 : ℝ) 1 := by
  -- The strict inequality `x ^ 2 < x ^ 2 + 1` bounds the square root on both sides.
  have hsqrt_pos : 0 < Real.sqrt (x ^ 2 + 1) := by positivity
  have hx_square_lt : x ^ 2 < x ^ 2 + 1 := by nlinarith
  have hx_lt : x < Real.sqrt (x ^ 2 + 1) :=
    Real.lt_sqrt_of_sq_lt hx_square_lt
  have hneg_square_lt : (-x) ^ 2 < x ^ 2 + 1 := by nlinarith
  have hneg_lt : -Real.sqrt (x ^ 2 + 1) < x := by
    have h := Real.lt_sqrt_of_sq_lt hneg_square_lt
    linarith
  have hratio_upper : x / Real.sqrt (x ^ 2 + 1) < 1 :=
    (div_lt_one hsqrt_pos).mpr hx_lt
  have hratio_lower : -1 < x / Real.sqrt (x ^ 2 + 1) := by
    rw [lt_div_iff₀ hsqrt_pos]
    linarith
  rw [(sqrtAverage_hasDerivAt x).deriv]
  constructor
  · linarith
  · linarith

/-- Helper for Exercise 28.7: ordered inputs have a positive `sqrtAverage` increment smaller
than their original increment. -/
lemma sqrtAverage_sub_lt {x y : ℝ} (hxy : x < y) :
    0 < sqrtAverage y - sqrtAverage x ∧
      sqrtAverage y - sqrtAverage x < y - x := by
  -- Apply the two strict mean-value inequalities to the derivative bounds.
  have hdifferentiable : Differentiable ℝ sqrtAverage :=
    fun z ↦ (sqrtAverage_hasDerivAt z).differentiableAt
  have hlower := mul_sub_lt_image_sub_of_lt_deriv hdifferentiable
    (fun z ↦ (sqrtAverage_deriv_mem_Ioo z).1) hxy
  have hupper := image_sub_lt_mul_sub_of_deriv_lt hdifferentiable
    (fun z ↦ (sqrtAverage_deriv_mem_Ioo z).2) hxy
  constructor
  · simpa only [zero_mul] using hlower
  · simpa only [one_mul] using hupper

/-- Part (d1) of Exercise 28.7: the real self-map `sqrtAverage` is shrinking. -/
theorem sqrtAverage_isShrinking : IsShrinkingMap sqrtAverage := by
  rw [isShrinkingMap_iff]
  intro x y hxy
  -- Orient the inputs and translate the corresponding increment estimate into distances.
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · obtain ⟨hpositive, hshort⟩ := sqrtAverage_sub_lt hlt
    have hvalue_lt : sqrtAverage x < sqrtAverage y := sub_pos.mp hpositive
    rw [Real.dist_eq, Real.dist_eq, abs_of_neg (sub_neg.mpr hvalue_lt),
      abs_of_neg (sub_neg.mpr hlt)]
    simpa only [neg_sub] using hshort
  · obtain ⟨hpositive, hshort⟩ := sqrtAverage_sub_lt hgt
    rw [Real.dist_eq, Real.dist_eq, abs_of_pos hpositive,
      abs_of_pos (sub_pos.mpr hgt)]
    exact hshort

/-- Helper for Exercise 28.7: `sqrtAverage` has no pointwise fixed point. -/
lemma sqrtAverage_ne_self (x : ℝ) : sqrtAverage x ≠ x := by
  intro hfixed
  -- A fixed point would identify the square root with `x`.
  have hsqrt_eq : Real.sqrt (x ^ 2 + 1) = x := by
    unfold sqrtAverage at hfixed
    linarith
  have hsquare_eq := congrArg (fun z : ℝ ↦ z ^ 2) hsqrt_eq
  have hradicand_nonneg : 0 ≤ x ^ 2 + 1 := by positivity
  have hsqrt_square : Real.sqrt (x ^ 2 + 1) ^ 2 = x ^ 2 + 1 :=
    Real.sq_sqrt hradicand_nonneg
  -- Squaring then gives the contradiction `x ^ 2 + 1 = x ^ 2`.
  nlinarith

/-- Part (d2) of Exercise 28.7: the real self-map `sqrtAverage` is not a contraction. -/
theorem sqrtAverage_not_contracting :
    ¬ IsContraction sqrtAverage := by
  intro hcontraction
  obtain ⟨K, hK⟩ := hcontraction.exists_contractingWith
  -- Banach's theorem would supply a fixed point, contradicting the pointwise obstruction.
  exact sqrtAverage_ne_self (hK.fixedPoint sqrtAverage) hK.fixedPoint_isFixedPt

/-- Part (d3) of Exercise 28.7: the real self-map `sqrtAverage` has no fixed point. -/
theorem sqrtAverage_no_fixedPoint :
    ¬ ∃ x : ℝ, Function.IsFixedPt sqrtAverage x := by
  -- Eliminate the asserted witness with the pointwise no-fixed-point lemma.
  rintro ⟨x, hx⟩
  exact sqrtAverage_ne_self x hx

/-- Exercise 28.7: the theorem family comprising the fixed-point results and the two
source examples. -/
theorem Exercise_28_7 :
    (∀ {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {f : X → X},
      IsContraction f → ∃! x, Function.IsFixedPt f x) ∧
      (∀ {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {f : X → X},
        IsShrinkingMap f → ∃! x, Function.IsFixedPt f x) ∧
      Set.MapsTo intervalQuadratic (Set.Icc (0 : ℝ) 1) (Set.Icc 0 1) ∧
      IsShrinkingMap intervalQuadraticMap ∧
      ¬ IsContraction intervalQuadraticMap ∧
      IsShrinkingMap sqrtAverage ∧
      ¬ IsContraction sqrtAverage ∧
      ¬ ∃ x : ℝ, Function.IsFixedPt sqrtAverage x := by
  -- Assemble the source conclusions from the component theorems proved above.
  exact ⟨IsContraction.existsUnique_fixedPoint_of_compact,
    IsShrinkingMap.existsUnique_fixedPoint_of_compact, intervalQuadratic_mapsTo,
    intervalQuadraticMap_isShrinking, intervalQuadraticMap_not_contracting,
    sqrtAverage_isShrinking, sqrtAverage_not_contracting, sqrtAverage_no_fixedPoint⟩
