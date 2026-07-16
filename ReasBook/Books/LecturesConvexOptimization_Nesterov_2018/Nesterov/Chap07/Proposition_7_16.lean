import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Algorithm_7_8
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.16 lies in Chapter 7's weighted smooth convex minimization / accelerated
projected-gradient domain.

Sampled owner-style declarations:
- `AcceleratedConvexMinimizationScheme` in `Algorithm_7_8`, the chapter owner of an accelerated
  feasible-set run with chosen gradient field, weighted proximal matrix, and positive smoothness
  constant;
- `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner of
  a constrained minimizer together with the canonical feasibility-plus-`IsMinOn` membership
  bridge;
- `acceleratedSchemeSearchPoint` and `acceleratedSchemeProximalMinimand` in `Algorithm_7_8`, the
  derived chapter API for the extrapolated point and proximal objective;
- `positiveDefMatrixNorm` and the notations `‖·‖[G]`, `‖·‖[G,*]` in `Definition_7_23`, the
  chapter owners of the weighted norm and its dual norm for a positive-definite matrix;
- `CompositeSmoothConvexMinimizationProblem` in `Definition_7_39`, the nearby problem owner that
  uses the same positive `NNRealˣ` smoothness parameter and positive-definite matrix owner.

Best owner abstraction:
- source-facing: Proposition 7.16's rate estimate for an accelerated run on a closed convex set;
- core/canonical: `AcceleratedConvexMinimizationScheme n N`;
- bridge/view: the weighted dual-gradient Lipschitz hypothesis, stated pointwise on the feasible
  set and consumed by the accelerated-scheme owner, together with the constrained-minimizer
  membership `xStar ∈ argmin[Q] φ` unpacked via `mem_constrainedArgmin_iff` when needed.

Primitive data:
- the constrained problem, chosen gradient field, positive smoothness constant, positive-definite
  matrix owner, initial point, and iterate/prox-center sequences, all owned by
  `AcceleratedConvexMinimizationScheme`;
- the minimizing point `xStar`, packaged canonically as a member of
  `argmin[scheme.problem.feasibleSet] scheme.problem`.

Derived API:
- the extrapolated point `yₖ`, through `acceleratedSchemeSearchPoint`;
- the proximal argmin step, through `scheme.v_succ_mem_argmin`;
- feasibility and `IsMinOn` for `xStar`, through `mem_constrainedArgmin_iff`;
- the weighted and dual weighted norms, through `positiveDefMatrixNorm`.

The previous version duplicated the chapter owner by introducing a second public scheme structure
with the same mathematical content and a weaker raw-`L` parameter surface. This refinement
deletes that duplicate layer and states the proposition directly over the existing Chapter 7 owner.
-/

-- Proof sketch: derive the weighted smoothness inequality from the assumed dual-gradient Lipschitz
-- bound, then run the standard estimate-sequence argument for the chapter owner
-- `scheme : AcceleratedConvexMinimizationScheme n N`. Evaluating the resulting potential estimate
-- at the minimizer `xStar` gives the final bound for the output iterate `x_N`.
namespace AcceleratedConvexMinimizationScheme

/-- Proposition 7.16: if `scheme` is the accelerated projected-gradient run
`S(φ, L, Q, G, x₀, N)` with positive horizon `N ≥ 1`, and the chosen gradient field is
`L`-Lipschitz with respect to the weighted norm `‖·‖[G]` and dual norm `‖·‖[G,*]` on the
feasible set, then the output point `scheme.outputPoint = x_N` satisfies
`φ(x_N) - φ(xStar) ≤ 2 L ‖x₀ - xStar‖[G]^2 / (N (N + 1))` for every minimizer `xStar` of `φ` on
`Q`. -/
theorem outputPoint_suboptimality_le
    {N : ℕ} (scheme : AcceleratedConvexMinimizationScheme n N)
    (hN : 1 ≤ N)
    (hgradient_lipschitz :
      ∀ ⦃x y : E⦄,
        x ∈ scheme.problem.feasibleSet →
        y ∈ scheme.problem.feasibleSet →
          ‖scheme.gradient x - scheme.gradient y‖[scheme.metricMatrix,*] ≤
            (scheme.smoothness : ℝ) * ‖x - y‖[scheme.metricMatrix])
    {xStar : E} (hxStar : xStar ∈ argmin[scheme.problem.feasibleSet] scheme.problem) :
    scheme.problem scheme.outputPoint - scheme.problem xStar ≤
      (2 * (scheme.smoothness : ℝ) * ‖scheme.initialPoint - xStar‖[scheme.metricMatrix] ^ (2 : ℕ)) /
        ((N : ℝ) * ((N : ℝ) + 1)) := sorry

end AcceleratedConvexMinimizationScheme

end
