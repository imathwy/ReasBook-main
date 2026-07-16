import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace

noncomputable section

/- Proposition 4.9 is `source-facing`: it computes the conjugate of the hinge loss on `ℝ`.
The `core/canonical` owner abstractions already live upstream as `extendedIndicator` in
Chapter 2 and `conjugate_function` in Definition 4.1. This file therefore keeps only the
hinge-loss integrand and the scalar specialization of that owner conjugate via `toDualMap ℝ ℝ`.
The primitive data here is just the hinge-loss function; the conjugacy formula is derived API. -/

/-- The hinge-loss example `x ↦ max (1 - x, 0)`, viewed as an `EReal`-valued function. -/
def hinge_loss : ℝ → EReal :=
  fun x ↦ (max (1 - x) 0 : EReal)

/-- Evaluating `hinge_loss` at `x` returns `max (1 - x, 0)` as an extended real number. -/
@[simp] theorem hinge_loss_apply (x : ℝ) :
    hinge_loss x = (max (1 - x) 0 : EReal) :=
  rfl

-- Proof sketch: analyze the supremum in
-- `conjugate_function hinge_loss (InnerProductSpace.toDualMap ℝ ℝ y)` piecewise in `x`.
-- The affine branch on `(-∞, 1]` has slope `1 + y`, the branch on `[1, ∞)` has slope `y`, so a
-- finite maximizer exists exactly for `y ∈ [-1, 0]`, where the value at `x = 1` is `y`.
/-- Proposition 4.9: the convex conjugate of the hinge loss `x ↦ max (1 - x, 0)`, expressed via
the Chapter 4 owner `conjugate_function` on `ℝ` using `toDualMap ℝ ℝ`, is the affine function
`y` plus the extended-real-valued indicator of the interval `[-1, 0]`. -/
theorem hinge_loss_conjugate_eq (y : ℝ) :
    conjugate_function hinge_loss (toDualMap ℝ ℝ y) =
      (y : EReal) + extendedIndicator (Set.Icc (-1 : ℝ) 0) y := sorry
