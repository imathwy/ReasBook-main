import Mathlib
import Nesterov.Chap07.Definition_7_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.37 lies in Chapter 7's positive-definite matrix / weighted dual-norm /
rank-one-update domain.

Relevant owner-style declarations sampled before refinement:
- `positiveDefMatrixNorm` and the notation `‖g‖[G,*]` in `Definition_7_23`, the chapter owner for
  the dual norm attached to a positive-definite matrix;
- `positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv` in `Definition_7_23`, the canonical bridge
  from that owner to the inverse-matrix quadratic form `√⟪g, G⁻¹ g⟫`;
- `rankOneUpdatedMatrix` in `Lemma_7_4`, the chapter owner for the basic interpolation
  `(1 - α) G + α ggᵀ`;
- mathlib `Matrix.add_mul_mul_inv_eq_sub`, the Woodbury/binomial inverse owner for inverse
  formulas of rank-one perturbations.

Best owner abstraction:
- source-facing: Proposition 7.37's quasi-Newton Hessian update with coefficient
  `(δ / (1 - δ)) / ‖g‖[G,*]^2`;
- core/canonical: the Chapter 7 dual norm owner `‖g‖[G,*]`;
- bridge/view: the update-expansion and inverse-expansion theorems below.

Primitive data:
- a positive-definite Hessian matrix `G`;
- a vector `g`;
- the accuracy parameter `δ`.

Derived API:
- the squared dual norm appears as `‖g‖[G,*] ^ 2`, derived from the existing owner rather than as
  a second local definition;
- the rank-one update formula and its inverse identity.

The duplicate wheel in the previous version was the local scalar owner
`quasiNewtonDualNormSq`. This refinement deletes that duplicate and rewrites the source-facing
update directly in terms of the chapter owner `‖g‖[G,*]`.
-/

/-- The rank-one Hessian update
`G + (δ / (1 - δ)) * (ggᵀ / ‖g‖_{G}^{*2})` from the relative-accuracy quasi-Newton scheme,
written using the canonical Chapter 7 dual norm owner. -/
def quasiNewtonUpdatedHessian
    (δ : ℝ) (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (g : E) :
    Matrix (Fin n) (Fin n) ℝ :=
  G.1 + ((δ / (1 - δ)) / (‖g‖[G,*] ^ (2 : ℕ))) • Matrix.vecMulVec g g

/-- Expanding `quasiNewtonUpdatedHessian δ G g` gives the displayed rank-one update formula for
the next Hessian matrix. -/
-- Proof sketch: unfold `quasiNewtonUpdatedHessian`.
theorem quasiNewtonUpdatedHessian_def
    (δ : ℝ) (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (g : E) :
    quasiNewtonUpdatedHessian δ G g =
      G.1 + ((δ / (1 - δ)) / (‖g‖[G,*] ^ (2 : ℕ))) • Matrix.vecMulVec g g := rfl

/-- The rank-one update preserves positive definiteness when `δ ∈ (0, 1)`. -/
-- Proof sketch: the update coefficient is nonnegative for `δ ∈ (0, 1)`, and
-- `Matrix.vecMulVec g g` is positive semidefinite. A positive-definite matrix plus a
-- nonnegative multiple of this rank-one form remains positive definite.
theorem quasiNewtonUpdatedHessian_posDef
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (g : E) :
    (quasiNewtonUpdatedHessian δ G g).PosDef := sorry

-- Proof sketch: the first identity is the definition of `quasiNewtonUpdatedHessian`. For the
-- second, apply the Sherman-Morrison formula to `G + u uᵀ` with
-- `u = √((δ / (1 - δ)) / ‖g‖[G,*]^2) • g`, then simplify the scalar factor using
-- `1 + (δ / (1 - δ)) = (1 - δ)⁻¹`.
/-- Proposition 7.37: if `ψ_k` is a quadratic estimating function with positive-definite Hessian
`G_k`, then the next Hessian is obtained by the rank-one update
`G_{k+1} = G_k + (δ / (1 - δ)) * g_k g_kᵀ / ‖g_k‖_{G_k}^{*2}`, and its inverse satisfies the
Sherman-Morrison identity
`G_{k+1}^{-1} = G_k^{-1} - δ * G_k^{-1} g_k g_kᵀ G_k^{-1} / ‖g_k‖_{G_k}^{*2}`. -/
theorem quasiNewtonRankOneHessianUpdate_and_inverse
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (Gk : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (gk : E) :
    quasiNewtonUpdatedHessian δ Gk gk =
      Gk.1 + ((δ / (1 - δ)) / (‖gk‖[Gk,*] ^ (2 : ℕ))) • Matrix.vecMulVec gk gk ∧
    (quasiNewtonUpdatedHessian δ Gk gk)⁻¹ =
      Gk.1⁻¹ - (δ / (‖gk‖[Gk,*] ^ (2 : ℕ))) •
        (Gk.1⁻¹ * Matrix.vecMulVec gk gk * Gk.1⁻¹) := sorry

end
