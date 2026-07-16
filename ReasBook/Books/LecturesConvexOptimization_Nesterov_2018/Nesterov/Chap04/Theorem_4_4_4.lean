import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Assumption_4_4_3
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_4_8
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_4_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SmoothNonlinearEquationProblem
open scoped Manifold

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/- Theorem 4.4.4 lies in the whole-space modified Gauss--Newton / exact-solvability domain.

Sampled owner-style declarations:
* `SmoothNonlinearEquationProblem.solutionSet` in `Definition_4_4_8`, the chapter owner for the
  exact-solution locus `problem x = 0`;
* mathlib `LipschitzOnWith L (fun x ↦ fderiv ℝ problem x) Set.univ`, the canonical whole-space
  Jacobian-Lipschitz owner for the residual map;
* `HasUniformDualNondegeneracyOnInitialSublevelSet` in `Assumption_4_4_3`, the source-facing
  nondegeneracy owner on the norm-merit initial sublevel set;
* `IsMinOn` in mathlib, the canonical owner for global minimizers on `Set.univ`;
* `exact_solution_isMinOn_meritFunctionReformulation` in `Proposition_4_4_4`, the thin bridge
  from an exact solution back to the minimizer reformulation.

Best owner abstraction:
* source-facing: existence of an exact solution `xStar ∈ solutionSet problem` together with the
  displayed distance bound from the initial point;
* core/canonical: the residual map `problem` together with the whole-space Jacobian-Lipschitz
  owner `LipschitzOnWith L (fderiv ℝ problem) Set.univ`;
* bridge/view: the norm-merit reformulation `meritFunctionReformulation problem norm` on whose
  initial sublevel set Assumption 4.4.3 is imposed.

Primitive data:
* the bundled smooth residual map `problem`;
* the initial point `x0`;
* the nondegeneracy constant `σ`;
* the whole-space Jacobian-Lipschitz hypothesis on `problem`;
* the norm-merit nondegeneracy assumption
  `HasUniformDualNondegeneracyOnInitialSublevelSet`.

Derived API:
* the exact-solution owner `xStar ∈ solutionSet problem`;
* the initial-residual distance bound.

This refinement keeps the labeled theorem at the source-facing exact-solution layer. The
minimizer reformulation is left to the upstream bridge from `Proposition_4_4_4`
`exact_solution_isMinOn_meritFunctionReformulation` instead of being repackaged locally. It also
removes the nonfaithful global `C¹` hypothesis on the raw norm merit `x ↦ ‖problem x‖`, whose
nondifferentiability at nondegenerate zeros conflicts with Assumption 4.4.3, and instead places
the smoothness input on the canonical owner layer already used by the chapter Taylor-remainder
bridge: the whole-space Jacobian-Lipschitz control of `problem`.
-/

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯

section

variable {problem : SmoothMap}
variable {x0 : E} {σ : ℝ}

-- Proof sketch: apply the global modified Gauss--Newton method to the norm-merit reformulation
-- `x ↦ ‖problem x‖` with constant regularization `M_k = L`. The whole-space Jacobian-Lipschitz
-- hypothesis supplies the smooth residual-map owner needed for the chapter Taylor-remainder and
-- one-step decrease estimates, while Assumption 4.4.3 controls the same norm-merit sublevel set.
-- The first phase gives uniform merit decrease until the threshold `σ^2 / L`, and the second
-- phase gives geometric decay of the merit values together with summable step lengths via the
-- residual bound from Lemma 4.4.7. The iterate sequence therefore converges to a point
-- `xStar ∈ solutionSet problem`, and summing the two phases yields
-- `‖xStar - x0‖ ≤ (2 / σ) * ‖problem x0‖`.
/-- Theorem 4.4.4: if the residual map `problem` has `L`-Lipschitz Jacobian on `Set.univ` and
Assumption 4.4.3 holds on the initial sublevel set of the norm-merit reformulation
`x ↦ ‖problem x‖`, then there exists an exact solution `x* ∈ solutionSet problem` whose distance
from the initial point is bounded by `(2 / σ) * ‖problem x₀‖`. -/
theorem exists_exact_solution_dist_le_two_div_sigma_mul_initialResidual
    (L : NNReal)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) Set.univ)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem norm x0 σ) :
    ∃ xStar : E,
      xStar ∈ solutionSet problem ∧
        ‖xStar - x0‖ ≤ (2 / σ) * ‖problem x0‖ := sorry

end
