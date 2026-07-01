import Mathlib
import Nesterov.Chap06.Definition_6_44
import Nesterov.Chap07.Definition_7_20
import Nesterov.Chap07.Definition_7_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RealSymmetricMatrixSpace
open scoped PositiveDefMatrixNorm

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

section Proposition725

/- Proposition 7.25 lies in Chapter 7's weighted-matrix-norm / matrix-smoothing domain.

Sampled owner-style declarations:
- `squaredLpMatrixNormSmoothing` in `Chap06/Definition_6_44`, the Chapter 6 source-facing owner
  for `F_p(X) = (1 / 2) ‖λ(X)‖_(2p)^2`;
- the inherited norm `‖·‖` on `𝕊^n`, recalled in `Definition_7_20` as the Frobenius norm on real
  symmetric matrices;
- `positiveDefMatrixNorm` and the notation `‖·‖[G]` in `Definition_7_23`, the chapter owner for
  the primal norm induced by a positive-definite matrix;
- `IsMinOn` in mathlib, the canonical minimizer owner for the objective and norm-minimizing
  hypotheses;
- `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem` in `Chap02/Definition_2_14`, the
  nearby owner theorem for quadratic lower bounds at minimizers, used here only as a style sample
  for keeping minimizer consequences as derived API rather than primitive data.

Best owner abstraction:
- source-facing: Proposition 7.25's quadratic lower bound and distance estimate for an objective
  factoring through the Chapter 6 smoothing owner;
- core/canonical: the chapter owners `squaredLpMatrixNormSmoothing`, `‖·‖` on `𝕊^n`, and
  `positiveDefMatrixNorm`, with the positive-definite matrix carried as the canonical subtype
  `{G // G.PosDef}`;
- bridge/view: the representation `f y = squaredLpMatrixNormSmoothing p (X y)`, the rank-bounded
  lower comparison between the Frobenius norm and `F_p`, and the identification
  `‖y‖[G] = ‖X y‖`.

Primitive data:
- `r p : ℕ+`;
- a positive-definite matrix `G : {G : Matrix (Fin m) (Fin m) ℝ // G.PosDef}`;
- the matrix map `X : E → 𝕊^n` and objective `f : E → ℝ`;
- the pointwise comparison hypotheses `h_smoothing_lower`, `hXrank`, `hf`, and `hGnorm`.

Derived API:
- the pointwise quadratic lower bound;
- its specialization at an objective minimizer;
- the distance bound to a weighted-norm minimizer on a convex feasible set.

Source/core/bridge triage:
- source-facing: the three proposition statements below;
- core/canonical: `squaredLpMatrixNormSmoothing`, `‖·‖` on `𝕊^n`, and `‖·‖[G]`;
- bridge/view: the rank-bounded Frobenius-to-smoothing comparison and the norm-identification
  hypothesis.

This refinement removes the generic placeholder `schattenEvenNorm` and states the proposition at
the actual Chapter 6 owner `squaredLpMatrixNormSmoothing`. It also drops the redundant
rank-independent upper-comparison binder and keeps only the rank-dependent bridge that the
proposition uses. The weighted norm remains on the canonical Chapter 7 notation `‖·‖[G]`.
-/

variable (r p : ℕ+)
variable (G : {G : Matrix (Fin m) (Fin m) ℝ // G.PosDef})
variable (X : E → 𝕊^n) (f : E → ℝ)

variable
  (h_smoothing_lower : ∀ M : 𝕊^n,
      Matrix.rank (M : Matrix (Fin n) (Fin n) ℝ) ≤ (r : ℕ) →
        (1 / (2 * (r : ℝ))) * ‖M‖ ^ (2 : ℕ) ≤
          squaredLpMatrixNormSmoothing p M)
  (hXrank : ∀ y : E, Matrix.rank (X y : Matrix (Fin n) (Fin n) ℝ) ≤ (r : ℕ))
  (hf : ∀ y : E, f y = squaredLpMatrixNormSmoothing p (X y))
  (hGnorm : ∀ y : E, ‖y‖[G] = ‖X y‖)

-- Proof sketch: apply the rank-bounded Frobenius-to-smoothing estimate to `X y`, use
-- `Matrix.rank (X y) ≤ r`, rewrite `f y` via `hf`, and substitute
-- `‖y‖[G] = ‖X y‖` via `hGnorm`.
/-- Proposition 7.25: [Quadratic lower bound and distance bound] if the objective factors as
`f(y) = F_p(X(y))` through the Chapter 6 smoothing owner
`F_p = squaredLpMatrixNormSmoothing p`, the matrix family `X(y)` has rank at most `r`, and the
weighted norm agrees with the Frobenius norm of `X(y)`, then
`(1 / (2r)) ‖y‖_G^2 ≤ f(y)` for every `y`. -/
theorem quadratic_lower_bound_of_rank_bounded_schatten_model
    (y : E) :
    (1 / (2 * (r : ℝ))) * ‖y‖[G] ^ (2 : ℕ) ≤ f y := sorry

-- Proof sketch: specialize `quadratic_lower_bound_of_rank_bounded_schatten_model` at the chosen
-- minimizer `yStar`, then identify `f yStar` with the minimum value `sInf (f '' Q)` using the
-- `IsMinOn` hypothesis.
/-- Any minimizer of the objective on a feasible set satisfies the same quadratic lower bound with
the minimum value `f_p* = min_{y ∈ Q} f(y)` on the right-hand side. -/
theorem quadratic_lower_bound_at_objective_minimizer
    {Q : Set E} {yStar : E} (hyStar : IsMinOn f Q yStar) :
    (1 / (2 * (r : ℝ))) * ‖yStar‖[G] ^ (2 : ℕ) ≤
      sInf (f '' Q) := sorry

-- Proof sketch: use the projection inequality for the `G`-norm on the convex set `Q` at the
-- norm minimizer `x0` to bound `‖yStar - x0‖_G^2` by `‖yStar‖_G^2`, then combine this with
-- `quadratic_lower_bound_at_objective_minimizer`.
/-- If `Q` is convex and `x0` minimizes the `G`-norm on `Q`, then every objective minimizer
`yStar` lies within `G`-distance squared at most `2 r f_p*` from `x0`; equivalently,
`(1 / 2) ‖yStar - x0‖_G^2 ≤ r f_p*` with `f_p* = min_{y ∈ Q} f(y)`. -/
theorem distance_bound_to_weighted_norm_minimizer
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {yStar x0 : E} (hyStar : IsMinOn f Q yStar)
    (hx0 : IsMinOn (fun y : E ↦ ‖y‖[G]) Q x0) :
    (1 / 2 : ℝ) * ‖yStar - x0‖[G] ^ (2 : ℕ) ≤
      (r : ℝ) * sInf (f '' Q) := sorry

end Proposition725
