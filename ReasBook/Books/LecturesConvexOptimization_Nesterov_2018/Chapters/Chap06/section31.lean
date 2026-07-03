import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_31 (from Chap06) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Seminorm ℝ E} [Seminorm.IsNorm p]
variable {Q : Set E} {d : E → ℝ}

/- Domain sampling for the prox-function / prox-center item.

Sampled owner declarations:
- mathlib `ContinuousOn`, the canonical owner for continuity on a feasible set;
- project `StrongConvexOnWith`, the source-faithful owner for strong convexity with respect to a
  chosen seminorm;
- mathlib `IsMinOn`, the canonical owner for minimizers on a feasible set;
- project `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem`, the canonical lower-bound
  theorem attached to strong convexity at a feasible minimizer.

Source/core/bridge triage:
- source-facing: the prox-center of `d` on `Q` and its normalized quadratic lower bound;
- core/canonical: `ContinuousOn`, `StrongConvexOnWith`, `IsMinOn`, and the quadratic-growth
  theorem at a feasible minimizer;
- bridge/view: the chapter owners `IsProxFunction` and `IsProxCenter`, which package the
  prox-function hypothesis and the normalized minimizing point used in the lower bound.

Primitive data:
- the norm-like seminorm `p`, feasible set `Q`, prox-function candidate `d`, and candidate
  center `x₀`;
- for `IsProxFunction`, continuity and unit strong convexity on `Q` with respect to `p`;
- for `IsProxCenter`, feasibility, minimization on `Q`, and the normalization `d x₀ = 0`;
- for the quadratic lower bound, a feasible comparison point `x ∈ Q`.

Derived API:
- `IsProxFunction.continuousOn` and `IsProxFunction.strongConvexOnWith`;
- `IsProxCenter.mem`, `IsProxCenter.isMinOn`, and `IsProxCenter.value_eq_zero`.
-/

/-- A prox-function on `Q` with respect to the norm `p` is continuous on `Q` and
`1`-strongly convex on `Q` with respect to `p`. -/
class IsProxFunction (p : Seminorm ℝ E) [Seminorm.IsNorm p] (Q : Set E) (d : E → ℝ) : Prop where
  /-- A prox-function is continuous on the feasible set. -/
  continuousOn : ContinuousOn d Q
  /-- A prox-function is `1`-strongly convex on the feasible set with respect to the chosen norm.
  -/
  strongConvexOnWith : StrongConvexOnWith p 1 Q d

/-- A prox-function hypothesis canonically supplies unit strong convexity on the feasible set
with respect to the chosen norm. -/
instance [hd : IsProxFunction p Q d] : Fact (StrongConvexOnWith p 1 Q d) where
  out := hd.strongConvexOnWith

/-- Definition 6.31 [Chapter6_1.json:68]: a prox-center of `d` on `Q` is a feasible minimizer
`x₀`, together with the standard normalization `d x₀ = 0`. -/
structure IsProxCenter (Q : Set E) (d : E → ℝ) (x₀ : E) : Prop where
  /-- A prox-center belongs to the feasible set. -/
  mem : x₀ ∈ Q
  /-- A prox-center minimizes `d` on the feasible set. -/
  isMinOn : IsMinOn d Q x₀
  /-- The prox-function is normalized to vanish at the prox-center. -/
  value_eq_zero : d x₀ = 0

/-- A prox-center canonically supplies its minimizing property on the feasible set as a `Fact`. -/
instance {Q : Set E} {d : E → ℝ} {x₀ : E} (hx₀ : IsProxCenter Q d x₀) :
    Fact (IsMinOn d Q x₀) where
  out := hx₀.isMinOn

end

/-! ### Proposition_6_31 (from Chap06) -/
noncomputable section

open scoped ConstrainedArgmin

/- Proposition 6.31 lies in the Euclidean linear-algebra / unconstrained argmin domain.

Sampled owner-style declarations:
* `constrainedArgmin` with notation `argmin[Q]` in `Chap01/Definition_1_3_3`, the project owner
  for global minimizers on a set;
* `IsMinOn`, the canonical minimizer predicate underlying `argmin[Q]`;
* `Matrix.toEuclideanLin`, the canonical linear-map owner attached to a real matrix acting on
  Euclidean spaces;
* `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, the mathlib bridge identifying transpose with
  the adjoint on Euclidean spaces.

Best owner abstraction:
* source-facing: the affine-quadratic minimand
  `x ↦ ⟪A x, uHat⟫ + (1 / 2) ‖x‖²` on `ℝⁿ`;
* core/canonical: `Matrix.toEuclideanLin A` together with the project argmin owner
  `argmin[Set.univ]`;
* bridge/view: the Euclidean transpose formula `-Aᵀ uHat` for a chosen minimizer.

Primitive data:
* the matrix `A : ℝ^{m × n}`;
* the dual vector `uHat : ℝ^m`.

Derived API:
* the minimand `euclideanLinearQuadraticMinimand A uHat`;
* the pointwise formula for that minimand;
* the canonical argmin identity `x0 = -Aᵀ uHat` for any chosen minimizer;
* the resulting uniqueness of global minimizers.

No parallel wrapper around matrices, transpose maps, or argmin witnesses is introduced here; the
file stays on the canonical matrix and argmin owners already present in mathlib and the project.
-/

variable {m n : ℕ}

local notation "E₁" => EuclideanSpace ℝ (Fin n)
local notation "E₂" => EuclideanSpace ℝ (Fin m)

/-- The affine-quadratic minimand `x ↦ ⟪A x, uHat⟫ + (1 / 2) ‖x‖²` from Proposition 6.31. -/
def euclideanLinearQuadraticMinimand
    (A : Matrix (Fin m) (Fin n) ℝ) (uHat : E₂) : E₁ → ℝ :=
  fun x ↦ inner ℝ (A.toEuclideanLin x) uHat + (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)

-- Proof sketch: unfold `euclideanLinearQuadraticMinimand`.
/-- Evaluating `euclideanLinearQuadraticMinimand` recovers the defining expression
`⟪A x, uHat⟫ + (1 / 2) ‖x‖²`. -/
@[simp] theorem euclideanLinearQuadraticMinimand_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (uHat : E₂) (x : E₁) :
    euclideanLinearQuadraticMinimand A uHat x =
      inner ℝ (A.toEuclideanLin x) uHat + (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) := sorry

-- Proof sketch: rewrite the affine term using the Euclidean adjoint of
-- `A.toEuclideanLin`, identify that adjoint with `(Aᵀ).toEuclideanLin`, and apply the
-- first-order condition for a global minimizer of the strongly convex function
-- `x ↦ ⟪A x, uHat⟫ + (1 / 2) ‖x‖²`.
/-- Proposition 6.31 [Chapter6_1.json:100]: if `x0(uHat)` is chosen in
`argmin_x {⟪A x, uHat⟫ + (1 / 2) ‖x‖²}`, then `x0(uHat) = -Aᵀ uHat`. -/
theorem euclideanLinearQuadraticMinimizer_eq_neg_transpose_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (uHat : E₂) {x0 : E₁}
    (hx0 : x0 ∈ argmin[Set.univ] (euclideanLinearQuadraticMinimand A uHat)) :
    x0 = -(A.transpose.toEuclideanLin uHat) := sorry

-- Proof sketch: apply
-- `euclideanLinearQuadraticMinimizer_eq_neg_transpose_apply` to both minimizers and compare
-- their common value `-Aᵀ uHat`.
/-- Any two global minimizers of `euclideanLinearQuadraticMinimand A uHat` are equal. -/
theorem euclideanLinearQuadraticMinimizer_unique
    (A : Matrix (Fin m) (Fin n) ℝ) (uHat : E₂) {x y : E₁}
    (hx : x ∈ argmin[Set.univ] (euclideanLinearQuadraticMinimand A uHat))
    (hy : y ∈ argmin[Set.univ] (euclideanLinearQuadraticMinimand A uHat)) :
    x = y := sorry
