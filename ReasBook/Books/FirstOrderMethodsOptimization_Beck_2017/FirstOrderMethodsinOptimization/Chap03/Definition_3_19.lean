import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_17
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Proposition_3_17

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace (toDual)
open WithLp (toLp)
open scoped BigOperators Gradient Pointwise

noncomputable section

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "l1Norm" => (fun y : E ↦ ‖toLp 1 fun i ↦ y i‖)
local notation "l1Regularizer" => (fun lam : ℝ ↦ fun y : E ↦ ((lam * l1Norm y : ℝ) : EReal))

/- Definition 3.19 is `source-facing`: it defines the stationary-point predicate for the
`ℓ₁`-regularized problem. The owner abstractions in this domain are the chapter/project
`is_differentiable_at`, `subdifferentialAt`, and the composite stationary predicate
`is_stationary_point`, so this file keeps only the specialized `ℓ₁` extendedRealSubdifferential term on top
of the chapter differentiability owner. -/

recall is_stationary_point
recall is_differentiable_at
recall subdifferentialAt

/-- Definition 3.19: a point `x` is stationary for the `ℓ₁`-regularized problem
`min_y f y + λ l1n[y]` when `f` is differentiable at `x` in the sense of Definition 3.10 and the
negative gradient belongs to `λ ∂ l1n[·] (x)`. -/
def is_l1_regularized_stationary_point (f : E → EReal) (lam : ℝ) (x : E) : Prop :=
  is_differentiable_at f x ∧
    -toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) ∈
      lam • subdifferentialAt l1Norm x

/-- Unfolding `is_l1_regularized_stationary_point` gives the chapter differentiability condition
and the scaled `ℓ₁`-extendedRealSubdifferential condition. -/
@[simp] theorem is_l1_regularized_stationary_point_iff
    {f : E → EReal} {lam : ℝ} {x : E} :
    is_l1_regularized_stationary_point f lam x ↔
      is_differentiable_at f x ∧
        -toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) ∈
          lam • subdifferentialAt l1Norm x :=
  Iff.rfl

-- Proof sketch: under `0 ≤ λ`, Definition 3.19 is the same stationary condition as in
-- Definition 3.17 for the composite objective with nonsmooth term `y ↦ λ * l1n[y]`. The
-- identification of the extendedRealSubdifferential of `y ↦ λ * l1n[y]` with `λ ∂ l1n[·]` is the standard scalar
-- chain rule from Theorem 3.21.
/-- Under the standard nonnegativity hypothesis on the regularization parameter, Definition 3.19 is
exactly the owner stationary predicate from Definition 3.17 for the composite objective
`f + λ l1n[·]`. -/
theorem is_l1_regularized_stationary_point_iff_is_stationary_point
    {f : E → EReal} {lam : ℝ} {x : E}
    (hlam : 0 ≤ lam) :
    is_l1_regularized_stationary_point f lam x ↔
      is_stationary_point f (l1Regularizer lam) x := sorry

-- Proof sketch: rewrite stationarity with `is_l1_regularized_stationary_point_iff`, then apply the
-- coordinatewise description of `∂ l1n[·](x)` from Proposition 3.17 and scale each coordinate by
-- `λ`. The three cases `x i > 0`, `x i < 0`, and `x i = 0` yield the displayed piecewise gradient
-- conditions.
/-- The stationarity condition for `f + λ l1n[·]` is equivalent to the coordinatewise relations
`∂ᵢ f(x) = -λ` on positive coordinates, `∂ᵢ f(x) = λ` on negative coordinates, and
`∂ᵢ f(x)` lying between `-λ` and `λ` on zero coordinates. -/
theorem is_l1_regularized_stationary_point_iff_coordinatewise
    (f : E → EReal) (lam : ℝ) (x : E) :
    is_l1_regularized_stationary_point f lam x ↔
      is_differentiable_at f x ∧
        ∀ i : Fin n,
          (0 < x i → (∇ (fun y ↦ (f y).toReal) x) i = -lam) ∧
            (x i < 0 → (∇ (fun y ↦ (f y).toReal) x) i = lam) ∧
              (x i = 0 → (∇ (fun y ↦ (f y).toReal) x) i ∈ Set.uIcc (-lam) lam) := sorry

end
