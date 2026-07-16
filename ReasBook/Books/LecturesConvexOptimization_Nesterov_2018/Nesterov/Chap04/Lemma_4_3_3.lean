import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_3_5
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_3_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BInducedNorm CubicNewtonStepNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 4.3.3 lies in the bilinear-form-induced cubic-Newton / Hessian-Lipschitz remainder
domain.

Sampled owner-style declarations:
* `HasLipschitzContinuousHessian` in `Definition_4_3_5`, written on theorem surfaces as
  `f ∈ C22[Mf]` on `PrimalSpace B`;
* `HasLipschitzContinuousHessian.gradient_deviation_le` in `Chap01/Lemma_1_5_11`, read on the
  intrinsic carrier `PrimalSpace B`;
* `CubicNewtonStep` in `Definition_4_3_6`, the source-facing owner of the chosen cubic Newton map;
* `CubicNewtonStep.firstOrderOptimalityCondition` in `Definition_4_3_6`, the owner-level
  first-order optimality theorem for the chosen cubic Newton point.

Best owner abstraction:
* source-facing: the cubic Newton step `step : CubicNewtonStep B f M`;
* core/canonical: the owners `((f : PrimalSpace B → ℝ) ∈ C22[Mf])` and
  `CubicNewtonStep B f M`;
* bridge/view: the gradient remainder estimate along `step x - x` and the scalar optimality
  identity obtained from the minimizing property of `step`.

Primitive data:
* the bilinear form `B`;
* the positive-definite quadratic data of `B`;
* the canonical Hessian-Lipschitz owner instance on `PrimalSpace B`;
* the chosen cubic Newton step `step`.

Derived API:
* the owner gradient Taylor remainder bound `HasLipschitzContinuousHessian.gradient_deviation_le`
  between arbitrary points `x` and `y`;
* the scalar pairing of the owner-level first-order optimality condition with the displacement
  `step x - x`;
* the lower bounds of Lemma 4.3.3 built from those owner theorems.

The previous file stored the remainder estimate and scalar optimality relation as separate local
`Prop` wrappers, and then specialized the remainder theorem directly to `y = step x`. Those were
not new mathematical owners; they were derived API that should sit on the existing owners
`HasLipschitzContinuousHessian` and `CubicNewtonStep`. This refinement deletes the duplicate
wrapper layer and uses the Chapter 1 remainder theorem together with the owner-level first-order
optimality theorem on `CubicNewtonStep` directly.
-/

section

variable {B : BilinForm ℝ E} {Mf : NNReal} {f : E → ℝ}
variable [Fact B.toQuadraticMap.PosDef]
variable (hf : (f : PrimalSpace B → ℝ) ∈ C22[Mf])

-- Proof sketch: apply the owner gradient remainder estimate at `(x, step x)`, combine it with
-- the scalar identity obtained by pairing
-- `step.firstOrderOptimalityCondition x`,
-- with `step x - x`,
-- expand `r[step](x) = ‖step x - x‖[B]`, and rearrange the resulting quadratic inequality in
-- the remainder term.
/-- Lemma 4.3.3 (1): for positive regularization `M`, the pairing of the gradient at the cubic
Newton point with the displacement `x - T_M(x)` is bounded below by the reciprocal-residual
dual-gradient term plus the cubic correction `((M² - M_f²) / (4M)) r_M(x)^3`. -/
lemma cubicNewtonStep_dualPairing_lower_bound
    {M : ℝ} (step : CubicNewtonStep B f M)
    (hM : 0 < M)
    (x : E) :
    let g := fderiv ℝ f (step x)
    g (x - step x) ≥
      (1 / (M * r[step](x))) *
          ‖g‖[B,*] ^ (2 : ℕ) +
        ((M ^ (2 : ℕ) - (Mf : ℝ) ^ (2 : ℕ)) / (4 * M)) *
          (r[step](x)) ^ (3 : ℕ) := sorry

-- Proof sketch: start from `cubicNewtonStep_dualPairing_lower_bound`, use the hypothesis
-- `M ≥ M_f / σ` in the equivalent form `M_f ≤ σ M`, and simplify the cubic coefficient
-- `((M² - M_f²) / (4M))` to `((1 - σ²) / 4) M`.
/-- Lemma 4.3.3 (2): if `σ ∈ (0, 1]` and `M ≥ M_f / σ`, then the cubic correction in the lower
bound can be replaced by `((1 - σ²) / 4) M r_M(x)^3`; the positive-regime hypothesis `0 < M`
keeps the reciprocal-residual term in its textbook form. -/
lemma cubicNewtonStep_dualPairing_lower_bound_of_sigma
    {M : ℝ} (step : CubicNewtonStep B f M)
    {σ : ℝ}
    (hσ : σ ∈ Set.Ioc (0 : ℝ) 1)
    (hMσ : M ≥ (1 / σ) * (Mf : ℝ))
    (hM : 0 < M)
    (x : E) :
    let g := fderiv ℝ f (step x)
    g (x - step x) ≥
      (1 / (M * r[step](x))) *
          ‖g‖[B,*] ^ (2 : ℕ) +
        ((1 - σ ^ (2 : ℕ)) / 4 : ℝ) * M * (r[step](x)) ^ (3 : ℕ) := sorry

end
