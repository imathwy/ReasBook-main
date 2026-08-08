import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Proposition_2_13
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_23
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

noncomputable section

/- Proposition 4.4 is `source-facing`. Its owner abstractions already exist upstream in the
project: `extendedIndicator` from Chapter 2, `support_function` from Chapter 2,
`conjugate_function` from Definition 4.1, and the coordinatewise max function
`coordinatewiseMax` from Chapter 3. This file keeps only the simplex-support bridge for that max
function and the resulting conjugate statement. -/

-- Proof sketch: `support_function_unit_simplex_eq_coordinate_max` already identifies the support
-- function of the standard simplex with the coordinate supremum. Rewrite that supremum using the
-- project owner `coordinatewiseMax`.
/-- The coordinatewise maximum is the support function of the standard simplex. -/
theorem coordinatewiseMax_eq_support_function_stdSimplex {n : ℕ} [Nonempty (Fin n)]
    (x : Fin n → ℝ) :
    (coordinatewiseMax x : EReal) =
      support_function (stdSimplex ℝ (Fin n)) (dotProductEquiv ℝ (Fin n) x) := sorry

-- Proof sketch: rewrite `fun x ↦ (coordinatewiseMax x : EReal)` as the support function of the
-- standard simplex using `coordinatewiseMax_eq_support_function_stdSimplex`. Then identify the
-- conjugate of that support function with the indicator of the simplex; because the standard
-- simplex is closed and convex, the general support-function conjugacy formula specializes to
-- `extendedIndicator (stdSimplex ℝ (Fin n))`.
/-- Proposition 4.4: for the function `f(x) = max {x_1, x_2, ..., x_n}` on `R^n`, the Fenchel
conjugate, expressed on `R^n` through the Euclidean pairing `dotProductEquiv`, is the indicator
function of the standard simplex `Δ_n`. -/
theorem conjugate_coordinatewiseMax_eq_extendedIndicator_stdSimplex {n : ℕ}
    [Nonempty (Fin n)] :
    (fun y : Fin n → ℝ ↦
      conjugate_function (fun x : Fin n → ℝ ↦ (coordinatewiseMax x : EReal))
        (dotProductEquiv ℝ (Fin n) y)) =
      extendedIndicator (stdSimplex ℝ (Fin n)) := sorry
