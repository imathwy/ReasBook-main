import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap17.Definition_17_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped EuclideanSpace InnerProductSpace

namespace ERealFunction

noncomputable section

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The counterexample function `(ξ₁, ξ₂) ↦ |ξ₁| + 2 |ξ₂|`. -/
def example17_23Function (x : ℝ²) : ℝ :=
  |x 0| + 2 * |x 1|

local notation "f" => example17_23Function.toEReal

/-- The base point `(1,0)` used in the counterexample. -/
def example17_23Point : ℝ² :=
  !₂[(1 : ℝ), 0]

/-- The vector `(1, εδ)` used as a subgradient candidate in the counterexample. -/
def example17_23Subgradient (ε δ : ℝ) : ℝ² :=
  !₂[(1 : ℝ), ε * δ]

/-- Helper for Example 17 23: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

/-- Helper for Example 17 23: a vector in `ℝ²` is determined by its two coordinates. -/
private theorem euclideanSpace_fin2_eq (x : ℝ²) : x = !₂[x 0, x 1] := by
  ext i
  fin_cases i <;> simp

/-- Helper for Example 17 23: the base point has value `1` under the counterexample function. -/
@[simp] theorem example17_23Function_point :
    example17_23Function example17_23Point = 1 := by
  -- Evaluate the two coordinates of the base point directly.
  simp [example17_23Function, example17_23Point]

/-- Helper for Example 17 23: the affine minorant expression at `(1,0)` reduces to the scalar
coordinate formula `y₀ + (εδ) y₁`. -/
private theorem example17_23_affine_minorant_left (y : ℝ²) (ε δ : ℝ) :
    ⟪y - example17_23Point, example17_23Subgradient ε δ⟫_ℝ +
        example17_23Function example17_23Point =
      y 0 + (ε * δ) * y 1 := by
  -- Rewrite the vector in coordinates and expand the `Fin 2` inner product.
  rw [euclideanSpace_fin2_eq y]
  simp [PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_mul, example17_23Point,
    example17_23Subgradient, example17_23Function]
  ring

/-- Helper for Example 17 23: subtracting a scaled candidate subgradient from `(1,0)` gives the
explicit coordinate formula `(1 - α, -(αεδ))`. -/
theorem example17_23_point_sub_smul_subgradient_eq (α ε δ : ℝ) :
    example17_23Point - α • example17_23Subgradient ε δ = !₂[(1 - α : ℝ), -(α * ε * δ)] := by
  -- Check the two coordinates separately.
  ext i
  fin_cases i <;> simp [example17_23Point, example17_23Subgradient, mul_assoc]

/-- Helper for Example 17 23: the value after stepping along the negative candidate subgradient
has the explicit scalar form `|1 - α| + 2 |αεδ|`. -/
private theorem example17_23Function_sub_step (α ε δ : ℝ) :
    example17_23Function (example17_23Point - α • example17_23Subgradient ε δ) =
      |1 - α| + 2 * |α * ε * δ| := by
  -- Rewrite the stepped point in coordinates and evaluate the function entrywise.
  rw [example17_23_point_sub_smul_subgradient_eq]
  simp [example17_23Function]

/-- Helper for Example 17 23: viewing a real-valued convex function through `toEReal` preserves
convexity on the effective domain. -/
private theorem convexOn_toEReal_of_convexOn_univ
    (g : ℝ² → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ g) :
    ConvexOn g.toEReal (effectiveDomain g.toEReal) := by
  refine ⟨?_, ?_, ?_⟩
  · -- A real-valued function stays finite after the `toEReal` coercion.
    simp [Function.effectiveDomain_toEReal]
  · -- Effective-domain membership is therefore automatic.
    simp [Function.effectiveDomain_toEReal]
  · intro x _hx y _hy a ha0 ha1
    -- Rewrite the convexity inequality back to the original real-valued statement.
    have hreal :
        g (a • x + (1 - a) • y) ≤ a * g x + (1 - a) * g y := by
      simpa [smul_eq_mul] using
        hconv.2 (by simp : x ∈ (Set.univ : Set ℝ²)) (by simp : y ∈ (Set.univ : Set ℝ²))
          ha0.le (sub_nonneg.mpr ha1.le) (by ring)
    change ((g (a • x + (1 - a) • y) : ℝ) : EReal) ≤
      ((a * g x + (1 - a) * g y : ℝ) : EReal)
    exact_mod_cast hreal

/-- Helper for Example 17 23: the real-valued map `(ξ₁, ξ₂) ↦ |ξ₁| + 2 |ξ₂|` is convex on
all of `ℝ²`. -/
private theorem example17_23Function_real_convexOn_univ :
    _root_.ConvexOn ℝ Set.univ example17_23Function := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b ha hb _hab
  have hcoord0 :
      |(a • x + b • y) 0| ≤ a * |x 0| + b * |y 0| := by
    -- The first coordinate satisfies the triangle inequality with nonnegative weights.
    calc
      |(a • x + b • y) 0| = |a * x 0 + b * y 0| := by simp
      _ ≤ |a * x 0| + |b * y 0| := abs_add_le _ _
      _ = a * |x 0| + b * |y 0| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hcoord1 :
      |(a • x + b • y) 1| ≤ a * |x 1| + b * |y 1| := by
    -- The same estimate holds for the second coordinate.
    calc
      |(a • x + b • y) 1| = |a * x 1 + b * y 1| := by simp
      _ ≤ |a * x 1| + |b * y 1| := abs_add_le _ _
      _ = a * |x 1| + b * |y 1| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  -- Combine the coordinatewise convexity estimates.
  calc
    example17_23Function (a • x + b • y)
        = |(a • x + b • y) 0| + 2 * |(a • x + b • y) 1| := by
            simp [example17_23Function]
    _ ≤ (a * |x 0| + b * |y 0|) + 2 * (a * |x 1| + b * |y 1|) := by
          exact add_le_add hcoord0 (mul_le_mul_of_nonneg_left hcoord1 (by positivity))
    _ = a • example17_23Function x + b • example17_23Function y := by
          simp [smul_eq_mul, example17_23Function]
          ring

-- Proof sketch: `f` is finite everywhere, so it never takes the value
-- `-∞`, and its effective domain is all of the canonical Euclidean model of `ℝ²`, hence in
-- particular nonempty.
/-- The counterexample function, viewed through the canonical `toEReal` owner, is proper. -/
theorem example17_23Function_isProper :
    IsProper (f : ℝ² → EReal) := by
  refine ⟨?_, ?_⟩
  · -- Every `toEReal` value is finite below, so `f` never takes the value `-∞`.
    intro x
    simp [Function.toEReal_apply]
  · -- The base point witnesses that the domain is nonempty.
    refine ⟨example17_23Point, ?_⟩
    simpa [dom, Function.toEReal_apply, example17_23Function_point] using
      (EReal.coe_lt_top (1 : ℝ))

-- Proof sketch: the coordinate maps `x ↦ |x 0|` and `x ↦ 2 |x 1|` are convex on `ℝ²`, so their
-- sum is convex on the effective domain of `f`.
/-- The counterexample function is convex on its effective domain. -/
theorem example17_23Function_convexOn :
    ConvexOn f (effectiveDomain f) := by
  simpa using
    convexOn_toEReal_of_convexOn_univ example17_23Function
      example17_23Function_real_convexOn_univ

-- Proof sketch: expand the subdifferential inequality for
-- `f(ξ₁, ξ₂) = |ξ₁| + 2 |ξ₂|` at `(1,0)`, use that the first coordinate has slope `1` there, and
-- use `|εδ| ≤ 3 / 2` to control the second coordinate term.
/-- If the second coordinate `εδ` is bounded by `3 / 2` in absolute value, then the vector
`(1, εδ)` belongs to the subdifferential of the counterexample function at `(1,0)`. In
particular, this applies to the textbook family `δ ∈ [1/2, 3/2]` with `ε = ±1`. -/
theorem example17_23Subgradient_mem_subdifferential {δ ε : ℝ}
    (hδ : |ε * δ| ≤ 3 / 2) :
    example17_23Subgradient ε δ ∈ (∂ f) example17_23Point := by
  rw [mem_subdifferential_iff]
  intro y
  have hmul :
      (ε * δ) * y 1 ≤ 2 * |y 1| := by
    have habs_mul :
        |(ε * δ) * y 1| ≤ (3 / 2) * |y 1| := by
      calc
        |(ε * δ) * y 1| = |ε * δ| * |y 1| := by rw [abs_mul]
        _ ≤ (3 / 2) * |y 1| := by
          exact mul_le_mul_of_nonneg_right hδ (abs_nonneg (y 1))
    -- Bound the second-coordinate contribution by the textbook `3/2` estimate.
    calc
      (ε * δ) * y 1 ≤ |(ε * δ) * y 1| := le_abs_self ((ε * δ) * y 1)
      _ ≤ (3 / 2) * |y 1| := habs_mul
      _ ≤ 2 * |y 1| := by
        have hthree_halves_le_two : (3 / 2 : ℝ) ≤ 2 := by norm_num
        exact mul_le_mul_of_nonneg_right hthree_halves_le_two (abs_nonneg (y 1))
  have hreal :
      ⟪y - example17_23Point, example17_23Subgradient ε δ⟫_ℝ +
          example17_23Function example17_23Point ≤
        example17_23Function y := by
    -- Reduce the affine minorant inequality to the scalar coordinate estimate.
    have hy0 : y 0 ≤ |y 0| := le_abs_self (y 0)
    calc
      ⟪y - example17_23Point, example17_23Subgradient ε δ⟫_ℝ +
          example17_23Function example17_23Point = y 0 + (ε * δ) * y 1 := by
            rw [example17_23_affine_minorant_left]
      _ ≤ |y 0| + 2 * |y 1| := by linarith
      _ = example17_23Function y := by simp [example17_23Function]
  have hcast :
      ((⟪y - example17_23Point, example17_23Subgradient ε δ⟫_ℝ +
          example17_23Function example17_23Point : ℝ) : EReal) ≤
        (example17_23Function y : EReal) := by
    exact_mod_cast hreal
  have hleft :
      ((⟪y - example17_23Point, example17_23Subgradient ε δ⟫_ℝ +
          example17_23Function example17_23Point : ℝ) : EReal) =
        (⟪y - example17_23Point, example17_23Subgradient ε δ⟫_ℝ : EReal) +
          (f example17_23Point : EReal) := by
    -- Expand the owner coercion and split the casted real sum.
    rw [example17_23Function_point, EReal.coe_add]
    simp [Function.toEReal_apply]
  -- Repackage the real inequality as the `EReal` subgradient inequality.
  calc
    (⟪y - example17_23Point, example17_23Subgradient ε δ⟫_ℝ : EReal) +
        (f example17_23Point : EReal)
        = ((⟪y - example17_23Point, example17_23Subgradient ε δ⟫_ℝ +
            example17_23Function example17_23Point : ℝ) : EReal) := by
              symm
              exact hleft
    _ ≤ (example17_23Function y : EReal) := hcast
    _ = (f y : EReal) := by
          simp [Function.toEReal_apply]

-- Proof sketch: write
-- `example17_23Point - α • example17_23Subgradient ε δ = (1 - α, -α ε δ)`, then compute
-- `|1 - α| + 2 |α ε δ|` and use `|ε| = 1` together with `δ ≥ 1 / 2` to show this is at least
-- `1 = example17_23Function example17_23Point` for every `α > 0`.
/-- Every positive step along the negative of the chosen subgradient keeps the counterexample
function above its value at `(1,0)` once `δ ≥ 1 / 2`. In particular, this applies to the
textbook interval `δ ∈ [1/2, 3/2]`. -/
theorem example17_23_nondecrease_along_neg_subgradient {δ ε : ℝ}
    (hδ : (1 / 2 : ℝ) ≤ δ) (hε : ε = 1 ∨ ε = -1)
    (α : ℝ) (hα : α ∈ Set.Ioi (0 : ℝ)) :
    (f (example17_23Point - α • example17_23Subgradient ε δ) : EReal) ≥
      (f example17_23Point : EReal) := by
  have hα_nonneg : 0 ≤ α := le_of_lt hα
  have hδ_nonneg : 0 ≤ δ := by
    linarith
  have hεabs : |ε| = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  have hstep_abs : |α * ε * δ| = α * δ := by
    -- Positivity of `α` and `δ` plus `|ε| = 1` collapses the absolute value.
    calc
      |α * ε * δ| = |α * ε| * |δ| := by rw [abs_mul]
      _ = |α| * |ε| * |δ| := by rw [abs_mul]
      _ = α * 1 * δ := by
            rw [abs_of_nonneg hα_nonneg, hεabs, abs_of_nonneg hδ_nonneg]
      _ = α * δ := by ring
  have hreal :
      example17_23Function (example17_23Point - α • example17_23Subgradient ε δ) ≥
        example17_23Function example17_23Point := by
    -- The explicit step formula is bounded below by `(1 - α) + α = 1`.
    rw [example17_23Function_sub_step, example17_23Function_point, hstep_abs]
    have hfirst : 1 - α ≤ |1 - α| := le_abs_self (1 - α)
    have htwo_delta_ge_one : 1 ≤ 2 * δ := by
      linarith
    have hsecond : α ≤ 2 * (α * δ) := by
      calc
        α = α * 1 := by ring
        _ ≤ α * (2 * δ) := by
          exact mul_le_mul_of_nonneg_left htwo_delta_ge_one hα_nonneg
        _ = 2 * (α * δ) := by ring
    linarith
  have hcast :
      (((example17_23Function example17_23Point : ℝ) : EReal)) ≤
        (example17_23Function (example17_23Point - α • example17_23Subgradient ε δ) : EReal) := by
    exact_mod_cast hreal
  -- Convert the real inequality back to the `toEReal` owner.
  simpa [Function.toEReal_apply] using hcast

-- Proof sketch: combine `example17_23Subgradient_mem_subdifferential` with the textbook upper
-- bound `δ ≤ 3 / 2`, using `|ε| = 1` for `ε = ±1`, and use the lower bound `δ ≥ 1 / 2` together
-- with `example17_23_nondecrease_along_neg_subgradient` to rule out strict decrease along
-- `-example17_23Subgradient ε δ`.
/-- Example 17 23: for `f(ξ₁, ξ₂) = |ξ₁| + 2 |ξ₂|`, `x = (1,0)`, and `u = (1, ±δ)` with
`δ ∈ [1/2, 3/2]`, the vector `u` belongs to `∂ f(x)` while `-u` is not a descent direction at
`x`. -/
theorem example17_23_subgradient_and_neg_not_descentDirection {δ ε : ℝ}
    (hδ : δ ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) (hε : ε = 1 ∨ ε = -1) :
    example17_23Subgradient ε δ ∈ (∂ f) example17_23Point ∧
      ¬ IsDescentDirectionAt f example17_23Point (-example17_23Subgradient ε δ) := by
  have hδ_nonneg : 0 ≤ δ := by
    linarith [hδ.1]
  have hεabs : |ε| = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  have habs_eq : |ε * δ| = δ := by
    -- On the textbook interval, the second parameter is nonnegative, so `|εδ| = δ`.
    calc
      |ε * δ| = |ε| * |δ| := by rw [abs_mul]
      _ = 1 * δ := by rw [hεabs, abs_of_nonneg hδ_nonneg]
      _ = δ := by ring
  constructor
  · -- The textbook upper bound `δ ≤ 3/2` gives the needed subgradient estimate.
    have hεδ : |ε * δ| ≤ 3 / 2 := by
      rw [habs_eq]
      exact hδ.2
    exact example17_23Subgradient_mem_subdifferential hεδ
  · intro hdescent
    rcases hdescent with ⟨_hxdom, ε₀, hε₀pos, hdecrease⟩
    let α : ℝ := ε₀ / 2
    have hα_mem : α ∈ Set.Ioc (0 : ℝ) ε₀ := by
      -- Choose the midpoint of the descent interval.
      dsimp [α]
      constructor
      · nlinarith
      · linarith
    have hstrict := hdecrease hα_mem
    have hstrict' :
        (f (example17_23Point - α • example17_23Subgradient ε δ) : EReal) <
          (f example17_23Point : EReal) := by
      -- Route correction: rewrite the descent step `x + α • (-u)` as `x - α • u`.
      simpa [Function.asEReal_apply, α, sub_eq_add_neg, smul_neg] using hstrict
    have hnondec :=
      example17_23_nondecrease_along_neg_subgradient hδ.1 hε α hα_mem.1
    exact not_lt_of_ge hnondec hstrict'

end

end ERealFunction
