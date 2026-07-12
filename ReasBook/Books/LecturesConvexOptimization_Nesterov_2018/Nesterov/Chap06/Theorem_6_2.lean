import LecturesConvexOptimization_Nesterov_2018.Chap06.Algorithm_6_1
import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_31

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped ConstrainedArgmin
open scoped WithTopConvexAnalysis

universe u

/- Theorem 6.2 lies in the chapter's composite-acceleration / similar-triangles domain.

Sampled owner-style declarations:
- `CompositeLipschitzGradientModel` in `Definition_6_8`, the chapter owner for a composite
  problem together with its chosen gradient field, Lipschitz constant, prox-function, and
  tractable prox subproblems;
- `constrainedArgmin` with notation `argmin[Q] f` in `Chap01/Definition_1_3_3`, the project
  owner for constrained minimizers on a feasible set;
- `IsProxCenter` in `Definition_6_31`, the canonical normalized prox-center owner for the initial
  point of the prox term;
- `SimilarTrianglesMethod`, `similarTrianglesEstimatingWeight`, and
  `SimilarTrianglesMethod.interpolationPoint` in `Algorithm_6_1`, the canonical owner layer for
  method `(6.1.19)`;
- `similarTrianglesEstimatingUpdate` in `Algorithm_6_1`, the owner recursion for the estimating
  functions `φ_k`.

Best owner abstraction:
- source-facing: Theorem 6.2's explicit estimating-function lower bound and the resulting
  suboptimality estimate;
- core/canonical: `SimilarTrianglesMethod` over `CompositeLipschitzGradientModel`, together with
  the normalized prox-center owner `IsProxCenter model.feasibleSet model.proxFunction x0` and
  the constrained minimizer owner
  `argmin[model.feasibleSet] (fun x ↦ model.smoothPart x + withTopRealPart model.nonsmoothPart x)`;
- bridge/view: the closed-form estimating function on the feasible-set owner `model.feasibleSet`,
  using the canonical Chapter 3 finite real part `withTopRealPart model.nonsmoothPart` rather
  than a parallel global real-valued regularizer witness.

Primitive data:
- a similar-triangles method over the canonical composite Lipschitz-gradient owner;
- a normalized prox-center `x0` for the prox-function `d`;
- the closed convex regularizer `model.nonsmoothPart : E → WithTop ℝ`, already owned by the
  Chapter 3 composite problem structure;
- the explicit affine-model closed form of `φ_k` on the feasible-set subtype, where the
  regularizer is canonically read through `withTopRealPart`.

Derived API:
- the closed-form estimating function `estimatingFunction`;
- the bridge theorem comparing `method.φ` with the closed-form `φ_k`;
- the lower-bound and suboptimality statements of Theorem 6.2, with constrained optimality
  consumed through the Chapter 1 argmin owner rather than a parallel raw `IsMinOn` hypothesis.

Source/core/bridge triage:
- source-facing: the two theorem statements below;
- core/canonical: `SimilarTrianglesMethod`, `IsProxCenter`, and `argmin[Q] f`;
- bridge/view: `estimatingFunction` and `phi_eq_estimatingFunction`. -/

namespace SimilarTrianglesMethod

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {model : CompositeLipschitzGradientModel E} {x0 : model.feasibleSet}

/-- The closed-form estimating function `φ_k` from Theorem 6.2, written on the canonical
similar-triangles owner surface over the feasible-set subtype and using the chapter owner
`withTopRealPart model.nonsmoothPart` for the regularizer term. -/
def estimatingFunction
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) : model.feasibleSet → ℝ :=
  fun x ↦
    (model.L : ℝ) * model.proxFunction x +
      Finset.sum (Finset.range k) (fun i ↦
        similarTrianglesEstimatingWeight i *
          (model.smoothPart (method.interpolationPoint i) +
            model.smoothGradient (method.interpolationPoint i)
              (x - method.interpolationPoint i))) +
      (((k : ℝ) * (k + 1)) / 4) * withTopRealPart model.nonsmoothPart x

/-- Evaluating the explicit estimating function recovers the prox term, the accumulated affine
models of `model.smoothPart` at the interpolation points `y_i`, and the penalty term
`((k (k + 1)) / 4) withTopRealPart model.nonsmoothPart x` on the feasible set. -/
-- Proof sketch: unfold `estimatingFunction`.
@[simp] theorem estimatingFunction_apply
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) (x : model.feasibleSet) :
    method.estimatingFunction k x =
      (model.L : ℝ) * model.proxFunction x +
        Finset.sum (Finset.range k) (fun i ↦
          similarTrianglesEstimatingWeight i *
            (model.smoothPart (method.interpolationPoint i) +
              model.smoothGradient (method.interpolationPoint i)
                (x - method.interpolationPoint i))) +
        (((k : ℝ) * (k + 1)) / 4) * withTopRealPart model.nonsmoothPart x := sorry

-- Proof sketch: prove by induction on `k`, using `phi_zero`, `phi_succ`,
-- `similarTrianglesEstimatingUpdate_apply`, and the identity
-- `∑_{i=0}^{k-1} ((i + 1) / 2) = (k (k + 1)) / 4`, with the nonsmooth term rewritten on the
-- feasible set via `withTopRealPart`.
/-- On the feasible set `Q`, the recursive estimating-function owner `method.φ k` is the
extended-real coercion of the closed-form `φ_k` from Theorem 6.2. -/
theorem phi_eq_estimatingFunction
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) (x : model.feasibleSet) :
    method.φ k x = (method.estimatingFunction k x : WithTop ℝ) := sorry

-- Proof sketch: combine the quadratic-growth bound from the prox-center hypothesis at `k = 0`
-- with the standard estimating-sequence induction on feasible points using
-- `phi_eq_estimatingFunction`, the minimizing property `v_succ_isMin`, convexity of `f`, and
-- the update rules of `SimilarTrianglesMethod`.
/-- Theorem 6.2 [Chapter6_2.json:20]: equation `(6.1.20)` states that if `x_k`, `y_k`, and
`v_k` are generated by method `(6.1.19)`, then for every `k ≥ 0` and every feasible point
`x ∈ Q`,
`((k (k + 1)) / 4) \tilde f(x_k) + (L / 2) ‖v_k - x‖² ≤ φ_k(x)`, where
`\tilde f(x_k) = f(x_k) + Ψ(x_k)` is read through the canonical finite-real-part bridge on
`Q`. -/
theorem objective_le_estimatingFunction
    (method : SimilarTrianglesMethod model x0)
    (hx0 : IsProxCenter model.feasibleSet model.proxFunction (x0 : E))
    (k : ℕ) (x : model.feasibleSet) :
    (((k : ℝ) * (k + 1)) / 4) *
          (model.smoothPart (method k) + withTopRealPart model.nonsmoothPart (method k)) +
        ((model.L : ℝ) / 2) * ‖(method.v k : E) - x‖ ^ (2 : ℕ) ≤
      method.estimatingFunction k x := sorry

-- Proof sketch: apply `objective_le_estimatingFunction` with `x = xStar`, unpack the canonical
-- argmin owner hypothesis through `mem_constrainedArgmin_iff` to recover feasibility and the
-- minimizing property of `xStar` for the composite objective, and divide by
-- `((k (k + 1)) / 4)` for `k ≥ 1`.
/-- The suboptimality estimate `(6.1.21)` obtained from the estimating-function lower bound:
if `xStar` is an optimal solution of problem `(6.1.18)`, then for every `k ≥ 1` the iterate
suboptimality and the squared distance to `v_k` satisfy the displayed accelerated rate
estimate. -/
theorem suboptimality_bound
    (method : SimilarTrianglesMethod model x0)
    (hx0 : IsProxCenter model.feasibleSet model.proxFunction (x0 : E))
    (xStar : E)
    (hxStar : xStar ∈
      argmin[model.feasibleSet]
        (fun x ↦ model.smoothPart x + withTopRealPart model.nonsmoothPart x))
    {k : ℕ} (hk : 1 ≤ k) :
    (model.smoothPart (method k) + withTopRealPart model.nonsmoothPart (method k)) -
        (model.smoothPart xStar + withTopRealPart model.nonsmoothPart xStar) +
        (2 * (model.L : ℝ) / ((k : ℝ) * (k + 1))) * ‖(method.v k : E) - xStar‖ ^ (2 : ℕ) ≤
      (4 * (model.L : ℝ) * model.proxFunction xStar) / ((k : ℝ) * (k + 1)) := sorry

end SimilarTrianglesMethod

end
