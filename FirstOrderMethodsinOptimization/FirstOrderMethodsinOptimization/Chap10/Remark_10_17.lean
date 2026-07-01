import Mathlib
import FirstOrderMethodsinOptimization.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Remark 10.17 is `source-facing`: the genuinely new item-level content is the first-order
residual `ℓ_f(x, y) = f(x) - f(y) - ⟪∇ f(y), x - y⟫`.

Domain sampling in the existing Chapter 10 API identifies:
- `proximal_gradient_curvature_model` from Algorithm 10.66 as the source-facing Euclidean
  quadratic model at the base point `y`;
- `proximal_gradient_backtracking_B2_accepts` from Algorithm 10.3 as the chapter owner of the
  upper-model comparison at the prox-gradient point;
- `fundamental_prox_grad_inequality` from Theorem 10.16 as the owner of the prox-gradient gap
  estimate written using the residual introduced here.

Primitive data:
- the totalized `EReal` residual `ℓ_f(x, y)`, which depends only on the Hilbert-space gradient
  data already present in the chapter, together with the completion needed by the gradient owner.

Derived API:
- the Euclidean curvature-model gap estimate is owned downstream by Theorem 10.16, which combines
  the residual introduced here with the chapter owner `proximal_gradient_backtracking_B2_accepts`
  for the required upper-model comparison. -/

/-- The first-order linearization defect
`ℓ_f(x, y) = f(x) - f(y) - ⟪∇ f(y), x - y⟫` of the smooth term `f` at the base point `y`,
viewed as a totalized `EReal` expression on `E × interior (effective_domain f)`. -/
def prox_gradient_linearization_defect (f : E → EReal) (x : E)
    (y : interior (effective_domain f)) : EReal :=
  f x - f (y : E) -
    (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) : EReal)

/- Textbook bracket notation for the first-order residual `ℓ_f(x, y)`. -/
notation "ℓ[" f ", " x ", " y "]" => prox_gradient_linearization_defect f x y

-- Proof sketch: unfold `prox_gradient_linearization_defect`; the right-hand side is exactly the
-- defining first-order residual at the base point `y`.
/-- Evaluating `ℓ[f, x, y]` expands to `f(x) - f(y) - ⟪∇ f(y), x - y⟫`. -/
@[simp] theorem prox_gradient_linearization_defect_eq
    (f : E → EReal) (x : E) (y : interior (effective_domain f)) :
    ℓ[f, x, y] =
      f x - f (y : E) -
        (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) : EReal) :=
  rfl

end

end
