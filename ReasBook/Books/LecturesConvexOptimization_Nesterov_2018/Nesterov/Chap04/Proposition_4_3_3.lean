import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_3_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open scoped Gradient CubicNewtonStepNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Proposition 4.3.3 lies in the symmetric bilinear-form-induced cubic-Newton first-order
optimality domain.

Sampled owner declarations:
* `LinearMap.BilinForm.primalSeminorm` in `Definition_4_3_4`, the chapter owner for the
  `B`-induced norm `‖·‖[B]`;
* `LinearMap.BilinForm.IsSymm` in `Definition_4_2_5`, the canonical symmetry owner needed to
  expose the cubic derivative as the explicit covector `B (T_M(x) - x)`;
* `LinearMap.BilinForm.PrimalSpace` in `Definition_4_2_9`, the intrinsic owner for the
  `B`-geometry carried by Chapter 4.3;
* `cubicNewtonModel` in `Definition_4_3_6`, the source cubic model minimized by `T_M(x)`;
* `CubicNewtonStep.firstOrderOptimalityCondition` in `Definition_4_3_6`, the core owner-level
  stationarity theorem `fderiv ℝ (cubicNewtonModel B f M x) (T_M x) = 0`;
* `hessian_isSelfAdjoint_of_contDiffAt` in `Text_4_2_3`, the chapter bridge turning a `C²`
  hypothesis into the self-adjointness needed to rewrite the Hessian derivative term.

Best owner abstraction:
* source-facing: the explicit first-order optimality equation `(4.3.12)` for `T_M(x)`;
* core/canonical: `CubicNewtonStep B f M` together with
  `CubicNewtonStep.firstOrderOptimalityCondition`;
* bridge/view: the dual-valued expansion of that derivative-zero statement, where the quadratic
  term is written with `hessian f x` only after a self-adjointness bridge, and the cubic term is
  written as `((M / 2) * r_M(x)) • B (T_M(x) - x)` only after a symmetry bridge for `B`.

Primitive data:
* the bilinear form `B`;
* the objective `f`;
* the regularization parameter `M`;
* the chosen cubic Newton step `step : CubicNewtonStep B f M`;
* the symmetry hypothesis `B.IsSymm`;
* the self-adjointness hypothesis `IsSelfAdjoint (hessian f x)`.

Derived API:
* the residual `r[step](x) = ‖step x - x‖[B]`;
* the owner derivative-zero statement for the cubic Newton model;
* the source-facing optimality equation below, obtained by expanding that owner theorem;
* the `C²` companion theorem obtained by the canonical bridge
  `hessian_isSelfAdjoint_of_contDiffAt`.

This proposition is therefore a source-facing bridge theorem on the existing Chapter 4.3 owner
`CubicNewtonStep`; it must not be collapsed to the ambient-norm Chapter 4.2 owner
`CubicRegularizationMapping`. -/

namespace CubicNewtonStep

variable {B : BilinForm ℝ E} [Fact B.toQuadraticMap.PosDef] {f : E → ℝ} {M : ℝ}

/-- Proposition 4.3.3 in primitive bridge form: if `B` is symmetric and `hessian f x` is
self-adjoint, then the cubic Newton point `T_M(x)` satisfies the source first-order optimality
condition `(4.3.12)`, written as an equality of linear functionals so the explicit Chapter 4.3
covector `B (T_M(x) - x)` remains visible. -/
theorem firstOrderOptimalityCondition_toDual_of_isSelfAdjoint
    (step : CubicNewtonStep B f M) (x : E)
    (hSymm : B.IsSymm) (hH : IsSelfAdjoint (hessian f x)) :
    InnerProductSpace.toDual ℝ E (∇ f x + hessian f x (step x - x)) +
        ((M / 2 : ℝ) * r[step](x)) • B (step x - x) = 0 := by
  sorry

/-- Proposition 4.3.3: if `f` is `C²` at `x` and `B` is symmetric, then the cubic Newton point
`T_M(x)` satisfies the source first-order optimality condition `(4.3.12)`. This is the Chapter
4.3 `C²` bridge obtained from
`firstOrderOptimalityCondition_toDual_of_isSelfAdjoint` via
`hessian_isSelfAdjoint_of_contDiffAt`. -/
theorem firstOrderOptimalityCondition_toDual
    (step : CubicNewtonStep B f M) (x : E)
    (hSymm : B.IsSymm) (hf : ContDiffAt ℝ 2 f x) :
    InnerProductSpace.toDual ℝ E (∇ f x + hessian f x (step x - x)) +
        ((M / 2 : ℝ) * r[step](x)) • B (step x - x) = 0 := by
  exact step.firstOrderOptimalityCondition_toDual_of_isSelfAdjoint x hSymm
    (hessian_isSelfAdjoint_of_contDiffAt f x hf)

end CubicNewtonStep
