import BauschkeLean.Chap29.Definition_29_40

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction SetValuedOperator

-- This file stays on the scalar subgradient spine from Definition 29.40:
-- direct subdifferential inequalities, then the canonical Chapter 29 projector owner for the
-- explicit branch formula.

/-- The scalar convex function used in Example 29.47. -/
def example_29_47_function : ℝ → ℝ :=
  fun x ↦ max (x + 1) (2 * x + 1)

private theorem example_29_47_function_continuous :
    Continuous example_29_47_function := by
  simpa [example_29_47_function] using
    (continuous_id.add continuous_const).max
      ((continuous_const.mul continuous_id).add continuous_const)

private theorem example_29_47_function_convexOn :
    _root_.ConvexOn ℝ Set.univ example_29_47_function := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  rw [example_29_47_function]
  apply max_le_iff.mpr
  constructor
  · calc
      a * (x + 1) + b * (y + 1)
          = (a * x + b * y) + 1 := by ring
      _ ≤ a * example_29_47_function x + b * example_29_47_function y := by
            gcongr <;> exact le_max_left _ _
  · calc
      a * (2 * x + 1) + b * (2 * y + 1)
          = 2 * (a * x + b * y) + 1 := by ring
      _ ≤ a * example_29_47_function x + b * example_29_47_function y := by
            gcongr <;> exact le_max_right _ _

private theorem one_mem_example_29_47_subdifferential_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    (1 : ℝ) ∈ (∂ example_29_47_function.toEReal) x := by
  rw [ERealFunction.mem_subdifferential_iff]
  intro y
  have hx_eq : example_29_47_function x = x + 1 := by
    rw [example_29_47_function, max_eq_left]
    linarith
  have hreal : inner ℝ (y - x) 1 + example_29_47_function x ≤ example_29_47_function y := by
    have hinner : inner ℝ (y - x) 1 = y - x := by
      calc
        inner ℝ (y - x) 1 = (starRingEnd ℝ) (y - x) * 1 := RCLike.inner_apply' _ _
        _ = y - x := by simp
    calc
      inner ℝ (y - x) 1 + example_29_47_function x = y + 1 := by
        rw [hinner, hx_eq]
        ring
      _ ≤ max (y + 1) (2 * y + 1) := le_max_left (y + 1) (2 * y + 1)
      _ = example_29_47_function y := by rw [example_29_47_function]
  have hcast :
      (((inner ℝ (y - x) 1 + example_29_47_function x : ℝ)) : EReal) ≤
        CoeTC.coe (Function.toEReal example_29_47_function y) := by
    simpa [Function.toEReal_apply] using
      (show (((inner ℝ (y - x) 1 + example_29_47_function x : ℝ)) : EReal) ≤
          ((example_29_47_function y : ℝ) : EReal) from by
            exact_mod_cast hreal)
  calc
    ↑(inner ℝ (y - x) 1) + CoeTC.coe (Function.toEReal example_29_47_function x) =
        ↑(inner ℝ (y - x) 1) + ↑(example_29_47_function x) := by
          rfl
    _ = (((inner ℝ (y - x) 1 + example_29_47_function x : ℝ)) : EReal) := by
          simp [EReal.coe_add]
    _ ≤ CoeTC.coe (Function.toEReal example_29_47_function y) := hcast

private theorem two_mem_example_29_47_subdifferential_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (2 : ℝ) ∈ (∂ example_29_47_function.toEReal) x := by
  rw [ERealFunction.mem_subdifferential_iff]
  intro y
  have hx_eq : example_29_47_function x = 2 * x + 1 := by
    rw [example_29_47_function, max_eq_right]
    linarith
  have hreal : inner ℝ (y - x) 2 + example_29_47_function x ≤ example_29_47_function y := by
    have hinner : inner ℝ (y - x) 2 = 2 * (y - x) := by
      calc
        inner ℝ (y - x) 2 = (starRingEnd ℝ) (y - x) * 2 := RCLike.inner_apply' _ _
        _ = (y - x) * 2 := by simp
        _ = 2 * (y - x) := by ring
    calc
      inner ℝ (y - x) 2 + example_29_47_function x = 2 * y + 1 := by
        rw [hinner, hx_eq]
        ring
      _ ≤ max (y + 1) (2 * y + 1) := le_max_right (y + 1) (2 * y + 1)
      _ = example_29_47_function y := by rw [example_29_47_function]
  have hcast :
      (((inner ℝ (y - x) 2 + example_29_47_function x : ℝ)) : EReal) ≤
        CoeTC.coe (Function.toEReal example_29_47_function y) := by
    simpa [Function.toEReal_apply] using
      (show (((inner ℝ (y - x) 2 + example_29_47_function x : ℝ)) : EReal) ≤
          ((example_29_47_function y : ℝ) : EReal) from by
            exact_mod_cast hreal)
  calc
    ↑(inner ℝ (y - x) 2) + CoeTC.coe (Function.toEReal example_29_47_function x) =
        ↑(inner ℝ (y - x) 2) + ↑(example_29_47_function x) := by
          rfl
    _ = (((inner ℝ (y - x) 2 + example_29_47_function x : ℝ)) : EReal) := by
          simp [EReal.coe_add]
    _ ≤ CoeTC.coe (Function.toEReal example_29_47_function y) := hcast

/-- The Example 29.47 function is subdifferentiable at every real point. -/
theorem example_29_47_mem_subdifferential_dom (x : ℝ) :
    x ∈ SetValuedOperator.dom (∂ example_29_47_function.toEReal) := by
  rw [SetValuedOperator.mem_dom_iff]
  by_cases hx : x ≤ 0
  · exact ⟨1, one_mem_example_29_47_subdifferential_of_nonpos hx⟩
  · exact ⟨2, two_mem_example_29_47_subdifferential_of_nonneg (le_of_not_ge hx)⟩

/-- Example 29.47 (1): for `f(x) = max{x + 1, 2x + 1}`, the scalar subdifferential at `0`
is the interval `[1,2]`. -/
theorem example_29_47_subdifferential_zero_eq_Icc :
    (∂ example_29_47_function.toEReal) (0 : ℝ) = Set.Icc (1 : ℝ) 2 := by
  ext u
  constructor
  · intro hu
    rw [ERealFunction.mem_subdifferential_iff] at hu
    constructor
    · -- Testing the subgradient inequality at `y = -1` forces the lower slope bound `u ≥ 1`.
      have hneg :
          (((inner ℝ ((-1 : ℝ) - 0) u + example_29_47_function 0 : ℝ)) : EReal) ≤
            ((example_29_47_function (-1) : ℝ) : EReal) := by
        simpa [Function.toEReal_apply] using hu (-1)
      have hreal : inner ℝ ((-1 : ℝ) - 0) u + example_29_47_function 0 ≤
          example_29_47_function (-1) := by
        exact_mod_cast hneg
      norm_num [example_29_47_function] at hreal
      have hinner : inner ℝ (1 : ℝ) u = u := by
        calc
          inner ℝ (1 : ℝ) u = (starRingEnd ℝ) (1 : ℝ) * u := RCLike.inner_apply' _ _
          _ = u := by simp
      rw [hinner] at hreal
      linarith
    · -- Testing instead at `y = 1` forces the upper slope bound `u ≤ 2`.
      have hpos :
          (((inner ℝ ((1 : ℝ) - 0) u + example_29_47_function 0 : ℝ)) : EReal) ≤
            ((example_29_47_function 1 : ℝ) : EReal) := by
        simpa [Function.toEReal_apply] using hu 1
      have hreal : inner ℝ ((1 : ℝ) - 0) u + example_29_47_function 0 ≤
          example_29_47_function 1 := by
        exact_mod_cast hpos
      norm_num [example_29_47_function] at hreal
      have hinner : inner ℝ (1 : ℝ) u = u := by
        calc
          inner ℝ (1 : ℝ) u = (starRingEnd ℝ) (1 : ℝ) * u := RCLike.inner_apply' _ _
          _ = u := by simp
      rw [hinner] at hreal
      linarith
  · intro hu
    rw [ERealFunction.mem_subdifferential_iff]
    intro y
    have hinner : inner ℝ (y - 0) u = y * u := by
      calc
        inner ℝ (y - 0) u = (starRingEnd ℝ) (y - 0) * u := RCLike.inner_apply' _ _
        _ = y * u := by simp
    have hreal : inner ℝ (y - 0) u + example_29_47_function 0 ≤ example_29_47_function y := by
      by_cases hy : 0 ≤ y
      · -- On the right half-line, the active affine branch has slope `2`.
        calc
          inner ℝ (y - 0) u + example_29_47_function 0 = y * u + 1 := by
            rw [hinner]
            norm_num [example_29_47_function]
          _ ≤ 2 * y + 1 := by
            nlinarith [hu.2, hy]
          _ ≤ max (y + 1) (2 * y + 1) := le_max_right _ _
          _ = example_29_47_function y := by
            rw [example_29_47_function]
      · have hy' : y ≤ 0 := le_of_not_ge hy
        -- On the left half-line, the active affine branch has slope `1`.
        calc
          inner ℝ (y - 0) u + example_29_47_function 0 = y * u + 1 := by
            rw [hinner]
            norm_num [example_29_47_function]
          _ ≤ y + 1 := by
            nlinarith [hu.1, hy']
          _ ≤ max (y + 1) (2 * y + 1) := le_max_left _ _
          _ = example_29_47_function y := by
            rw [example_29_47_function]
    have hcast :
        (((inner ℝ (y - 0) u + example_29_47_function 0 : ℝ)) : EReal) ≤
          CoeTC.coe (Function.toEReal example_29_47_function y) := by
      simpa [Function.toEReal_apply] using
        (show (((inner ℝ (y - 0) u + example_29_47_function 0 : ℝ)) : EReal) ≤
            ((example_29_47_function y : ℝ) : EReal) from by
              exact_mod_cast hreal)
    calc
      ↑(inner ℝ (y - 0) u) + CoeTC.coe (Function.toEReal example_29_47_function 0) =
          ↑(inner ℝ (y - 0) u) + ↑(example_29_47_function 0) := by
            rfl
      _ = (((inner ℝ (y - 0) u + example_29_47_function 0 : ℝ)) : EReal) := by
            simp [EReal.coe_add]
      _ ≤ CoeTC.coe (Function.toEReal example_29_47_function y) := hcast

/-- Helper for Example 29.47: the zero-sublevel set of `x ↦ max (x + 1) (2x + 1)` is
`(-∞, -1]`. -/
private theorem example_29_47_function_le_zero_iff {x : ℝ} :
    example_29_47_function x ≤ 0 ↔ x ≤ -1 := by
  constructor
  · intro hx
    have hx' : x + 1 ≤ 0 := by
      exact le_trans (le_max_left (x + 1) (2 * x + 1)) hx
    linarith
  · intro hx
    -- Both affine branches are nonpositive once `x ≤ -1`.
    rw [example_29_47_function]
    apply max_le_iff.mpr
    constructor <;> linarith

/-- Helper for Example 29.47: on the negative branch, the scalar subdifferential collapses to the
singleton `{1}`. -/
private theorem example_29_47_subdifferential_eq_singleton_one_of_neg {x : ℝ} (hx : x < 0) :
    (∂ example_29_47_function.toEReal) x = ({1} : Set ℝ) := by
  ext u
  constructor
  · intro hu
    rw [Set.mem_singleton_iff]
    rw [ERealFunction.mem_subdifferential_iff] at hu
    have hx_half : x / 2 < 0 := by linarith
    have hthree_half : (3 * x) / 2 < 0 := by linarith
    have hx_eq : example_29_47_function x = x + 1 := by
      rw [example_29_47_function, max_eq_left]
      linarith
    have hx_half_eq : example_29_47_function (x / 2) = x / 2 + 1 := by
      rw [example_29_47_function, max_eq_left]
      linarith
    have hthree_half_eq : example_29_47_function ((3 * x) / 2) = (3 * x) / 2 + 1 := by
      rw [example_29_47_function, max_eq_left]
      linarith
    have hupper :
        (((inner ℝ (x / 2 - x) u + example_29_47_function x : ℝ)) : EReal) ≤
          ((example_29_47_function (x / 2) : ℝ) : EReal) := by
      simpa [Function.toEReal_apply] using hu (x / 2)
    have hlower :
        (((inner ℝ ((3 * x) / 2 - x) u + example_29_47_function x : ℝ)) : EReal) ≤
          ((example_29_47_function ((3 * x) / 2) : ℝ) : EReal) := by
      simpa [Function.toEReal_apply] using hu ((3 * x) / 2)
    have hupper_real :
        inner ℝ (x / 2 - x) u + example_29_47_function x ≤
          example_29_47_function (x / 2) := by
      exact_mod_cast hupper
    have hlower_real :
        inner ℝ ((3 * x) / 2 - x) u + example_29_47_function x ≤
          example_29_47_function ((3 * x) / 2) := by
      exact_mod_cast hlower
    have hinner_upper : inner ℝ (x / 2 - x) u = (-(x / 2)) * u := by
      calc
        inner ℝ (x / 2 - x) u = (starRingEnd ℝ) (x / 2 - x) * u := by
          simpa using (RCLike.inner_apply' (x / 2 - x) u)
        _ = (x / 2 - x) * u := by simp
        _ = (-(x / 2)) * u := by ring
    have hinner_lower : inner ℝ ((3 * x) / 2 - x) u = (x / 2) * u := by
      calc
        inner ℝ ((3 * x) / 2 - x) u = (starRingEnd ℝ) ((3 * x) / 2 - x) * u := by
          simpa using (RCLike.inner_apply' ((3 * x) / 2 - x) u)
        _ = ((3 * x) / 2 - x) * u := by simp
        _ = (x / 2) * u := by ring
    rw [hinner_upper, hx_eq, hx_half_eq] at hupper_real
    rw [hinner_lower, hx_eq, hthree_half_eq] at hlower_real
    have hu_le : u ≤ 1 := by
      nlinarith [hx, hupper_real]
    have hu_ge : 1 ≤ u := by
      nlinarith [hx, hlower_real]
    linarith
  · intro hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact one_mem_example_29_47_subdifferential_of_nonpos hx.le

/-- Helper for Example 29.47: on the positive branch, the scalar subdifferential collapses to the
singleton `{2}`. -/
private theorem example_29_47_subdifferential_eq_singleton_two_of_pos {x : ℝ} (hx : 0 < x) :
    (∂ example_29_47_function.toEReal) x = ({2} : Set ℝ) := by
  ext u
  constructor
  · intro hu
    rw [Set.mem_singleton_iff]
    rw [ERealFunction.mem_subdifferential_iff] at hu
    have hx_half : 0 < x / 2 := by linarith
    have hthree_half : 0 < (3 * x) / 2 := by linarith
    have hx_eq : example_29_47_function x = 2 * x + 1 := by
      rw [example_29_47_function, max_eq_right]
      linarith
    have hx_half_eq : example_29_47_function (x / 2) = x + 1 := by
      rw [example_29_47_function, max_eq_right]
      · ring
      · linarith
    have hthree_half_eq : example_29_47_function ((3 * x) / 2) = 3 * x + 1 := by
      rw [example_29_47_function, max_eq_right]
      · ring
      · linarith
    have hlower :
        (((inner ℝ (x / 2 - x) u + example_29_47_function x : ℝ)) : EReal) ≤
          ((example_29_47_function (x / 2) : ℝ) : EReal) := by
      simpa [Function.toEReal_apply] using hu (x / 2)
    have hupper :
        (((inner ℝ ((3 * x) / 2 - x) u + example_29_47_function x : ℝ)) : EReal) ≤
          ((example_29_47_function ((3 * x) / 2) : ℝ) : EReal) := by
      simpa [Function.toEReal_apply] using hu ((3 * x) / 2)
    have hlower_real :
        inner ℝ (x / 2 - x) u + example_29_47_function x ≤
          example_29_47_function (x / 2) := by
      exact_mod_cast hlower
    have hupper_real :
        inner ℝ ((3 * x) / 2 - x) u + example_29_47_function x ≤
          example_29_47_function ((3 * x) / 2) := by
      exact_mod_cast hupper
    have hinner_lower : inner ℝ (x / 2 - x) u = (-(x / 2)) * u := by
      calc
        inner ℝ (x / 2 - x) u = (starRingEnd ℝ) (x / 2 - x) * u := by
          simpa using (RCLike.inner_apply' (x / 2 - x) u)
        _ = (x / 2 - x) * u := by simp
        _ = (-(x / 2)) * u := by ring
    have hinner_upper : inner ℝ ((3 * x) / 2 - x) u = (x / 2) * u := by
      calc
        inner ℝ ((3 * x) / 2 - x) u = (starRingEnd ℝ) ((3 * x) / 2 - x) * u := by
          simpa using (RCLike.inner_apply' ((3 * x) / 2 - x) u)
        _ = ((3 * x) / 2 - x) * u := by simp
        _ = (x / 2) * u := by ring
    rw [hinner_lower, hx_eq, hx_half_eq] at hlower_real
    rw [hinner_upper, hx_eq, hthree_half_eq] at hupper_real
    have hu_ge : 2 ≤ u := by
      nlinarith [hx, hlower_real]
    have hu_le : u ≤ 2 := by
      nlinarith [hx, hupper_real]
    linarith
  · intro hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact two_mem_example_29_47_subdifferential_of_nonneg hx.le

/-- Helper for Example 29.47: the selected subgradient equals `1` on the negative branch. -/
private theorem example_29_47_selectedSubgradient_eq_one_of_neg
    (s : Selection (∂ example_29_47_function.toEReal)) {x : ℝ} (hx : x < 0) :
    (s ⟨x, example_29_47_mem_subdifferential_dom x⟩ : ℝ) = 1 := by
  -- The singleton fiber forces the selected value.
  have hmem :=
    selection_apply_mem s ⟨x, example_29_47_mem_subdifferential_dom x⟩
  simpa [example_29_47_subdifferential_eq_singleton_one_of_neg hx, Set.mem_singleton_iff] using hmem

/-- Helper for Example 29.47: the selected subgradient equals `2` on the positive branch. -/
private theorem example_29_47_selectedSubgradient_eq_two_of_pos
    (s : Selection (∂ example_29_47_function.toEReal)) {x : ℝ} (hx : 0 < x) :
    (s ⟨x, example_29_47_mem_subdifferential_dom x⟩ : ℝ) = 2 := by
  -- The singleton fiber forces the selected value.
  have hmem :=
    selection_apply_mem s ⟨x, example_29_47_mem_subdifferential_dom x⟩
  simpa [example_29_47_subdifferential_eq_singleton_two_of_pos hx, Set.mem_singleton_iff] using hmem

/-- Helper for Example 29.47: every reciprocal slope coming from `[1,2]` lands in
`[-1, -1 / 2]` after multiplying by `-1`. -/
private theorem neg_one_div_mem_Icc_of_mem_Icc_one_two {u : ℝ}
    (hu : u ∈ Set.Icc (1 : ℝ) 2) :
    -(1 : ℝ) / u ∈ Set.Icc (-1 : ℝ) (-(1 / 2 : ℝ)) := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu.1
  constructor
  · -- The lower endpoint uses `u ≥ 1`.
    refine (le_div_iff₀ hu_pos).2 ?_
    nlinarith [hu.1]
  · -- The upper endpoint uses `u ≤ 2`.
    refine (div_le_iff₀ hu_pos).2 ?_
    nlinarith [hu.2]

/-- The point `0` belongs to the domain of the subdifferential of `example_29_47_function`. -/
theorem example_29_47_zero_mem_subdifferential_dom :
    (0 : ℝ) ∈ SetValuedOperator.dom (∂ example_29_47_function.toEReal) := by
  simpa using example_29_47_mem_subdifferential_dom 0

/-- The value selected by a subgradient selection of `example_29_47_function` at `0`. -/
noncomputable def example_29_47_selection_value_zero
    (s : Selection (∂ example_29_47_function.toEReal)) : ℝ :=
  s ⟨0, example_29_47_mem_subdifferential_dom 0⟩

/-- The selected subgradient at `0` lies in the interval `[1,2]`. -/
theorem example_29_47_selection_value_zero_mem_Icc
    (s : Selection (∂ example_29_47_function.toEReal)) :
    example_29_47_selection_value_zero s ∈ Set.Icc (1 : ℝ) 2 := by
  -- The selected value belongs to the zero fiber, and that fiber is `[1,2]`.
  have hmem :=
    selection_apply_mem s ⟨0, example_29_47_mem_subdifferential_dom 0⟩
  simpa [example_29_47_selection_value_zero, example_29_47_subdifferential_zero_eq_Icc] using hmem

private theorem example_29_47_lowerLevelSet_zero_nonempty :
    (lowerLevelSet example_29_47_function.toEReal.asEReal 0).Nonempty := by
  refine ⟨-1, ?_⟩
  rw [ERealFunction.mem_lowerLevelSet_iff]
  norm_num [example_29_47_function, Function.toEReal_apply]

private theorem example_29_47_selectedSubgradient_eq
    (s : Selection (∂ example_29_47_function.toEReal)) (x : ℝ) :
    continuousConvexSelectedSubgradient
        example_29_47_function
        example_29_47_function_continuous
        example_29_47_function_convexOn
        s x =
      s ⟨x, example_29_47_mem_subdifferential_dom x⟩ := by
  have harg :
      (⟨x,
          subgradientProjector_mem_dom
            example_29_47_function
            example_29_47_function_continuous
            example_29_47_function_convexOn
            x⟩ :
        {y // y ∈ SetValuedOperator.dom (∂ example_29_47_function.toEReal)}) =
        ⟨x, example_29_47_mem_subdifferential_dom x⟩ := by
    exact Subtype.ext (by rfl)
  simpa [continuousConvexSelectedSubgradient] using congrArg s harg

/-- Example 29.47 (2): if `s` is a selection of `∂ f` for
`f(x) = max{x + 1, 2x + 1}`, then the associated subgradient projector onto
`C = ]-∞, -1 / 2]` is the source-facing specialization of
`ERealFunction.continuousConvexSubgradientProjector`. -/
noncomputable def example_29_47_subgradient_projector
    (s : Selection (∂ example_29_47_function.toEReal)) : ℝ → ℝ :=
  ERealFunction.continuousConvexSubgradientProjector
    example_29_47_function
    0
    example_29_47_function_continuous
    example_29_47_function_convexOn
    example_29_47_lowerLevelSet_zero_nonempty
    s

/-- Evaluating the Example 29.47 projector recovers the displayed piecewise formula. -/
theorem example_29_47_subgradient_projector_apply
    (s : Selection (∂ example_29_47_function.toEReal)) (x : ℝ) :
    example_29_47_subgradient_projector s x =
      if x ≤ -1 then
        x
      else if x < 0 then
        -1
      else if x = 0 then
        -(1 : ℝ) / example_29_47_selection_value_zero s
      else
        -(1 / 2 : ℝ) := by
  by_cases hx_le : x ≤ -1
  · -- On the lower-level set, the projector fixes `x`.
    have hx_mem :
        x ∈ ERealFunction.lowerLevelSet example_29_47_function.toEReal.asEReal 0 := by
      rw [ERealFunction.mem_lowerLevelSet_iff]
      simpa [Function.toEReal_apply, example_29_47_function_le_zero_iff] using hx_le
    rw [example_29_47_subgradient_projector]
    rw [ERealFunction.continuousConvexSubgradientProjector_apply_of_mem_lowerLevelSet
      example_29_47_function 0
      example_29_47_function_continuous
      example_29_47_function_convexOn
      example_29_47_lowerLevelSet_zero_nonempty
      s
      hx_mem]
    simp [hx_le]
  · by_cases hx_neg : x < 0
    · have hx_active : 0 < example_29_47_function x := by
        -- Outside `(-∞, -1]`, the function value is strictly positive.
        have hnot_mem : ¬ example_29_47_function x ≤ 0 := by
          rw [example_29_47_function_le_zero_iff]
          exact hx_le
        exact lt_of_not_ge hnot_mem
      have hslope :
          (s ⟨x, example_29_47_mem_subdifferential_dom x⟩ : ℝ) = 1 :=
        example_29_47_selectedSubgradient_eq_one_of_neg s hx_neg
      have hbranch : example_29_47_function x = x + 1 := by
        rw [example_29_47_function, max_eq_left]
        linarith
      have hvalue : example_29_47_subgradient_projector s x = -1 := by
        calc
          example_29_47_subgradient_projector s x
              = x + (((0 - example_29_47_function x) / (‖(1 : ℝ)‖ ^ 2)) • (1 : ℝ)) := by
                  simpa [example_29_47_subgradient_projector, hslope,
                    example_29_47_selectedSubgradient_eq] using
                    (ERealFunction.continuousConvexSubgradientProjector_apply_of_lt
                      example_29_47_function 0
                      example_29_47_function_continuous
                      example_29_47_function_convexOn
                      example_29_47_lowerLevelSet_zero_nonempty
                      s
                      hx_active)
          _ = x - example_29_47_function x := by
                change x + (((0 - example_29_47_function x) / (‖(1 : ℝ)‖ ^ 2)) * (1 : ℝ)) =
                  x - example_29_47_function x
                norm_num [sub_eq_add_neg]
          _ = -1 := by
                rw [hbranch]
                ring
      simpa [hx_le, hx_neg] using hvalue
    · by_cases hx_zero : x = 0
      · have hx_active : 0 < example_29_47_function x := by
          subst hx_zero
          norm_num [example_29_47_function]
        have hu_mem := example_29_47_selection_value_zero_mem_Icc s
        have hu_pos : 0 < example_29_47_selection_value_zero s := by
          linarith [hu_mem.1]
        -- At the kink, the active formula keeps the selected slope explicit.
        subst hx_zero
        have hnorm :
            ‖example_29_47_selection_value_zero s‖ = example_29_47_selection_value_zero s := by
          rw [Real.norm_eq_abs, abs_of_pos hu_pos]
        have hvalue : example_29_47_subgradient_projector s 0 =
            -(1 : ℝ) / example_29_47_selection_value_zero s := by
          calc
            example_29_47_subgradient_projector s 0
                = 0 + (((0 - example_29_47_function 0) /
                    (‖example_29_47_selection_value_zero s‖ ^ 2)) •
                    example_29_47_selection_value_zero s) := by
                      simpa
                        [example_29_47_subgradient_projector, example_29_47_selection_value_zero,
                          example_29_47_selectedSubgradient_eq]
                        using
                        (ERealFunction.continuousConvexSubgradientProjector_apply_of_lt
                          example_29_47_function 0
                          example_29_47_function_continuous
                          example_29_47_function_convexOn
                          example_29_47_lowerLevelSet_zero_nonempty
                          s
                          hx_active)
            _ = -(1 : ℝ) / example_29_47_selection_value_zero s := by
                  have hu_ne : example_29_47_selection_value_zero s ≠ 0 := by
                    linarith
                  calc
                    0 + (((0 - example_29_47_function 0) /
                        (‖example_29_47_selection_value_zero s‖ ^ 2)) •
                        example_29_47_selection_value_zero s)
                        = ((-1 : ℝ) / (example_29_47_selection_value_zero s ^ 2)) *
                            example_29_47_selection_value_zero s := by
                              rw [show example_29_47_function 0 = 1 by
                                norm_num [example_29_47_function], hnorm]
                              simp
                    _ = -(1 : ℝ) / example_29_47_selection_value_zero s := by
                          field_simp [hu_ne]
        have hnot : ¬ ((1 : ℝ) ≤ 0) := by
          norm_num
        simpa [hx_le, hx_neg, hnot] using hvalue
      · have hx_pos : 0 < x := by
          have hx_nonneg : 0 ≤ x := le_of_not_gt hx_neg
          have hx_ne_zero : 0 ≠ x := by
            simpa [eq_comm] using hx_zero
          exact lt_of_le_of_ne hx_nonneg hx_ne_zero
        have hx_active : 0 < example_29_47_function x := by
          -- On the positive side, the branch `2x + 1` is strictly positive.
          rw [example_29_47_function, max_eq_right]
          · linarith
          · linarith
        have hslope :
            (s ⟨x, example_29_47_mem_subdifferential_dom x⟩ : ℝ) = 2 :=
          example_29_47_selectedSubgradient_eq_two_of_pos s hx_pos
        have hbranch : example_29_47_function x = 2 * x + 1 := by
          rw [example_29_47_function, max_eq_right]
          linarith
        have hvalue : example_29_47_subgradient_projector s x = -(1 / 2 : ℝ) := by
          calc
            example_29_47_subgradient_projector s x
                = x + (((0 - example_29_47_function x) / (‖(2 : ℝ)‖ ^ 2)) • (2 : ℝ)) := by
                    simpa [example_29_47_subgradient_projector, hslope,
                      example_29_47_selectedSubgradient_eq] using
                      (ERealFunction.continuousConvexSubgradientProjector_apply_of_lt
                        example_29_47_function 0
                        example_29_47_function_continuous
                        example_29_47_function_convexOn
                        example_29_47_lowerLevelSet_zero_nonempty
                        s
                        hx_active)
            _ = x - example_29_47_function x / 2 := by
                  change x + (((0 - example_29_47_function x) / (‖(2 : ℝ)‖ ^ 2)) * (2 : ℝ)) =
                    x - example_29_47_function x / 2
                  norm_num [sub_eq_add_neg]
                  ring
            _ = -(1 / 2 : ℝ) := by
                  rw [hbranch]
                  ring
        simpa [hx_le, hx_neg, hx_zero, hx_pos.ne'] using hvalue

/-- At `0`, the Example 29.47 projector lands in the interval `[-1, -1 / 2]`. -/
theorem example_29_47_subgradient_projector_zero_mem_Icc
    (s : Selection (∂ example_29_47_function.toEReal)) :
    example_29_47_subgradient_projector s 0 ∈ Set.Icc (-1 : ℝ) (-(1 / 2 : ℝ)) := by
  -- Rewrite the projector at `0` and finish with the reciprocal interval lemma.
  have hzero :
      example_29_47_subgradient_projector s 0 =
        -(1 : ℝ) / example_29_47_selection_value_zero s := by
    have hnot : ¬ ((1 : ℝ) ≤ 0) := by
      norm_num
    simpa [hnot] using example_29_47_subgradient_projector_apply s 0
  rw [hzero]
  exact neg_one_div_mem_Icc_of_mem_Icc_one_two
    (example_29_47_selection_value_zero_mem_Icc s)

/-- Example 29.47 (3): the subgradient projector attached to a selection of `∂ f` is
discontinuous. -/
  theorem example_29_47_subgradient_projector_not_continuous
    (s : Selection (∂ example_29_47_function.toEReal)) :
    ¬ Continuous (example_29_47_subgradient_projector s) := by
  intro hcont
  let xSeq : ℕ → ℝ := fun n ↦ -(1 / ((n : ℝ) + 1))
  let ySeq : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hxSeq_tendsto : Filter.Tendsto xSeq Filter.atTop (nhds (0 : ℝ)) := by
    -- The negative reciprocal sequence converges to `0`.
    simpa [xSeq] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (nhds 0)).sub
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hySeq_tendsto : Filter.Tendsto ySeq Filter.atTop (nhds (0 : ℝ)) := by
    -- The positive reciprocal sequence converges to `0`.
    simpa [ySeq] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1) : ℝ)) Filter.atTop (nhds (0 : ℝ)))
  have hxProj_tendsto :
      Filter.Tendsto (fun n ↦ example_29_47_subgradient_projector s (xSeq n))
        Filter.atTop (nhds (example_29_47_subgradient_projector s 0)) := by
    exact (hcont.continuousAt.tendsto).comp hxSeq_tendsto
  have hyProj_tendsto :
      Filter.Tendsto (fun n ↦ example_29_47_subgradient_projector s (ySeq n))
        Filter.atTop (nhds (example_29_47_subgradient_projector s 0)) := by
    exact (hcont.continuousAt.tendsto).comp hySeq_tendsto
  have hxProj_value :
      ∀ n, example_29_47_subgradient_projector s (xSeq n) = -1 := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [xSeq, example_29_47_subgradient_projector_apply]
    · have hn_pos : 0 < (n : ℝ) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr hn
      have hx_neg : xSeq n < 0 := by
        dsimp [xSeq]
        have hdenom_pos : 0 < (n : ℝ) + 1 := by positivity
        have hrecip_pos : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hdenom_pos
        nlinarith
      have hx_not_le : ¬ xSeq n ≤ -1 := by
        dsimp [xSeq]
        have hdenom_pos : 0 < (n : ℝ) + 1 := by positivity
        intro hle
        have htmp : (1 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
          linarith
        have hdenom_le : (n : ℝ) + 1 ≤ 1 := by
          have htmp' : (1 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
            simpa [one_div] using htmp
          rw [le_div_iff₀ hdenom_pos] at htmp'
          simpa using htmp'
        linarith
      simpa [hx_not_le, hx_neg] using
        example_29_47_subgradient_projector_apply s (xSeq n)
  have hyProj_value :
      ∀ n, example_29_47_subgradient_projector s (ySeq n) = -(1 / 2 : ℝ) := by
    intro n
    have hy_pos : 0 < ySeq n := by
      dsimp [ySeq]
      have hdenom_pos : 0 < (n : ℝ) + 1 := by positivity
      simpa using one_div_pos.mpr hdenom_pos
    have hy_not_zero : ySeq n ≠ 0 := by
      linarith
    have hy_not_le : ¬ ySeq n ≤ -1 := by
      linarith
    have hy_not_neg : ¬ ySeq n < 0 := by
      linarith
    simpa [hy_not_le, hy_not_neg, hy_not_zero] using
      example_29_47_subgradient_projector_apply s (ySeq n)
  have hxConst :
      Filter.Tendsto (fun n ↦ example_29_47_subgradient_projector s (xSeq n))
        Filter.atTop (nhds (-1 : ℝ)) := by
    have hEq :
        (fun n ↦ example_29_47_subgradient_projector s (xSeq n)) = fun _ : ℕ ↦ (-1 : ℝ) := by
      funext n
      exact hxProj_value n
    rw [hEq]
    exact tendsto_const_nhds
  have hyConst :
      Filter.Tendsto (fun n ↦ example_29_47_subgradient_projector s (ySeq n))
        Filter.atTop (nhds (-(1 / 2 : ℝ))) := by
    have hEq :
        (fun n ↦ example_29_47_subgradient_projector s (ySeq n)) =
          fun _ : ℕ ↦ (-(1 / 2 : ℝ)) := by
      funext n
      exact hyProj_value n
    rw [hEq]
    exact tendsto_const_nhds
  have hzero_eq_neg_one :
      example_29_47_subgradient_projector s 0 = -1 := by
    exact tendsto_nhds_unique hxProj_tendsto hxConst
  have hzero_eq_neg_half :
      example_29_47_subgradient_projector s 0 = -(1 / 2 : ℝ) := by
    exact tendsto_nhds_unique hyProj_tendsto hyConst
  linarith
