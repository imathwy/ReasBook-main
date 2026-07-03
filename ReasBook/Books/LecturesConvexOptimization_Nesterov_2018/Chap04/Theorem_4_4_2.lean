import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap04.Algorithm_4_4_1
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_1_1
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SmoothNonlinearEquationProblem
open scoped InnerProduct LevelSetNotation Manifold MinimalSingularValue

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
variable [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
variable [CompleteSpace E₂]

/- Theorem 4.4.2 lies in the local modified Gauss--Newton / nondegenerate-solution domain.

Sampled owner-style declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate dynamics
  and accepted trial points;
* `jacobian_lipschitz_taylor_remainder_le` in `Proposition_4_4_5`, the chapter owner for the
  quadratic first-order Taylor remainder on a convex set;
* `SmoothNonlinearEquationProblem.solutionSet` in `Definition_4_4_8`, the chapter owner for the
  exact-solution locus `problem x = 0`;
* mathlib `LipschitzOnWith L (fun x ↦ fderiv ℝ problem x) 𝓕`, the canonical on-set
  Jacobian-Lipschitz owner;
* `minimalSingularValue` / `σ_min(_)` in `Definition_4_4_5`, the chapter owner for the dual
  nondegeneracy quantity;
* the complete-inner-product-space ambient layer already used by `Assumption_4_4_3`,
  `Theorem_4_4_3`, `Theorem_4_4_4`, and `Theorem_4_4_5`.

Best owner abstraction:
* source-facing: the local quadratic contraction of the modified Gauss--Newton iteration near a
  nondegenerate exact solution;
* core/canonical: a convex neighborhood `𝓕` carrying the on-set Jacobian-Lipschitz bound,
  together with the exact-solution owner `xStar ∈ solutionSet problem` and the dual
  nondegeneracy owner at `xStar`;
* bridge/view: containment of the initial sublevel set `𝓛[f]((f x0))` in `𝓕`, which places the
  iterate orbit and the exact solution inside the convex Lipschitz domain needed by the Taylor
  bound.

Primitive data:
* the method `method`;
* the exact solution point `xStar ∈ solutionSet problem`;
* the convex set `𝓕` containing `𝓛[f]((f x0))`;
* the Jacobian-Lipschitz owner on `𝓕`.

Derived API:
* the one-step sublevel-set invariance and quadratic contraction estimate.

The earlier statement put the Jacobian-Lipschitz hypothesis only on the initial sublevel set
`𝓛[f]((f x0))`. That is too weak for the chapter Taylor-remainder owner, whose segment argument
needs a convex set containing the whole segment between the relevant points. This refinement keeps
the source-facing contraction theorem but upgrades its smoothness hypothesis to the correct convex
ambient domain and uses sublevel containment only as the bridge back to the iterate orbit.
The exact-solution input is also refined to the chapter owner `solutionSet problem` instead of the
raw equation `problem xStar = 0`, matching the nearby Chapter 4 theorem surfaces.
A finite-dimensional ambient hypothesis is not part of the theorem's mathematical content: the
public surface only uses the smooth-map owner, on-set Jacobian Lipschitz control, and the adjoint
minimal-singular-value nondegeneracy condition, so the file lives on the same complete
inner-product-space layer as the neighboring Chapter 4 owners.
-/

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

section

variable {problem : SmoothMap}
variable {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
variable {L0 : ℝ} {L : NNReal} {γφ : ℝ} {x0 xStar : E₁}

local notation "f" => meritFunctionReformulation problem φ
local notation "𝓛0" => (𝓛[f]((f x0)) : Set E₁)

-- Proof sketch: `mem_solutionSet_iff.mp hxStar` and the merit-function axioms imply
-- `f xStar = 0 ≤ f x0`, so
-- `xStar ∈ 𝓛0 ⊆ 𝓕`. Proposition 4.4.7 gives `f (method (k + 1)) ≤ f (method k) ≤ f x0`, so the
-- current and next iterates stay in `𝓛0 ⊆ 𝓕` without a separate feasibility hypothesis. Since
-- `𝓕` is convex, the segment joining `method k` to `xStar` lies in the Lipschitz domain, so
-- Proposition 4.4.5 controls the first-order Taylor remainder there. Combine that remainder bound
-- with the sharp lower bound with constant `γφ` and the dual nondegeneracy owner
-- `0 < σ_min((F'(x*))†)` to solve for `‖x_{k+1} - x*‖`.
/-- Theorem 4.4.2: if `x* ∈ solutionSet problem`, if the Jacobian at `x*` is nondegenerate in the
dual sense `0 < σ_min((F'(x*))†)`, if `γφ` is the sharpness constant from Definition 4.4.9, and
if the Jacobian is `L`-Lipschitz on a convex set `𝓕` containing the initial sublevel set
`𝓛[f]((f x₀))`, then every sufficiently close modified Gauss--Newton iterate satisfies the local
quadratic error estimate from `(4.4.20)` and the next iterate `x_{k+1}` remains in
`𝓛[f]((f x₀))`. -/
theorem local_contraction_near_nondegenerate_solution
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    {𝓕 : Set E₁} {k : ℕ}
    (h𝓕 : Convex ℝ 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hxStar : xStar ∈ solutionSet problem)
    (hσ_pos : 0 < σ_min((fderiv ℝ problem xStar)†))
    (hγφ_mem : γφ ∈ Set.Ioc (0 : ℝ) 1)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (hclose :
      ‖method k - xStar‖ ≤
        (2 / (L : ℝ)) * (σ_min((fderiv ℝ problem xStar)†) * γφ / (3 + 5 * γφ))) :
    (method (k + 1) ∈ 𝓛0 ∧
      ‖method (k + 1) - xStar‖ ≤
        (3 * (1 + γφ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ)) /
          (2 * γφ *
            (σ_min((fderiv ℝ problem xStar)†) -
              (L : ℝ) * ‖method k - xStar‖))) := by
  sorry

-- Proof sketch: starting from the smallness assumption on `‖x_k - x*‖`, rearrange the scalar
-- inequality exactly as in the textbook estimate to show that the fraction appearing in
-- `(4.4.20)` is bounded above by `‖x_k - x*‖`.
/-- If `γφ ∈ (0, 1]` and the current error satisfies the smallness condition from
Theorem 4.4.2, then the explicit quadratic error bound from `(4.4.20)` is itself at most the
current error `‖x_k - x*‖`. -/
theorem local_contraction_bound_le_current_error
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    {k : ℕ}
    (hγφ_mem : γφ ∈ Set.Ioc (0 : ℝ) 1)
    (hclose :
      ‖method k - xStar‖ ≤
        (2 / (L : ℝ)) * (σ_min((fderiv ℝ problem xStar)†) * γφ / (3 + 5 * γφ))) :
    ((3 * (1 + γφ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ)) /
        (2 * γφ *
          (σ_min((fderiv ℝ problem xStar)†) -
            (L : ℝ) * ‖method k - xStar‖)) ≤
      ‖method k - xStar‖) := by
  sorry

end
