

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_2_47_1 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

namespace SmoothFunctionalConstraintsMinimizationProblem

/- Remark 2.47.1 lies in the constrained smooth minimax local-model domain.

Domain-style sampling for this refinement:
* `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` in
  `Definition_2_47.lean`, the bridge from the constrained problem to the fixed-`t`
  `SmoothMinimaxProblem` owner;
* `SmoothFunctionalConstraintsMinimizationProblem`
  `.existsUnique_isMinOn_regularizedAffineApproximation` in `Text_2_4.lean`, the constrained
  owner well-definedness theorem for the fixed-`t` quadratically regularized affine model;
* `SmoothFunctionalConstraintsMinimizationProblem.constrainedGradientMapping` and
  `SmoothFunctionalConstraintsMinimizationProblem.constrainedReducedGradient` in
  `Definition_2_47.lean`, the source-facing constrained exact-step abbreviations already built on
  that bridge owner;
* `SmoothMinimaxProblem.lowerRegularizedModelValue_le_optimalValue` and
  `SmoothMinimaxProblem.optimalValue_le_upperRegularizedModelValue` in `Text_2_4.lean`, the owner
  optimal-value comparison theorems for the regularized affine models.

Best owner abstraction:
* the fixed-`t` bridge `problem.toParametricSmoothMinimaxProblem t`.

Primitive data:
* the constrained problem `problem`;
* the scalar parameter `t`;
* the linearization point `xBar`;
* the regularization parameter `γ`.

Derived API:
* the constrained exact step and reduced gradient, obtained by specializing the max-type owner to
  the fixed-`t` bridge problem;
* the regularized model-value comparisons at parameters `μ` and `L`;
* the constrained optimal value
  `sInf ((problem.toParametricSmoothMinimaxProblem t) ''
    (problem.toParametricSmoothMinimaxProblem t).feasibleSet)`.

Source/core/bridge triage:
* source-facing: the constrained gradient mapping, constrained reduced gradient, and the two
  constrained optimal-value inequalities in the remark;
* core/canonical: the fixed-`t` owner `problem.toParametricSmoothMinimaxProblem t`, together with
  the max-type exact-step owners and the `SmoothMinimaxProblem` model-value comparisons;
* bridge/view: the constrained step and reduced-gradient abbreviations already provided by
  `Definition_2_47.lean`.

Accordingly this file reuses the constrained step and reduced-gradient owners already introduced in
`Definition_2_47.lean`, and adds only the genuinely new remark-level well-definedness and
optimal-value comparison statements. It keeps no parallel package or surrogate local-model API. -/

section ExactStep

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
variable (t : ℝ)

/-- Remark 2.47.1 (1): for every `t`, the constrained gradient mapping is well defined as the
unique feasible minimizer of the regularized affine model of the fixed-`t` bridge problem. -/
-- Proof sketch: apply the existing constrained owner theorem from `Text_2_4` at the positive
-- regularization parameter `γ`.
theorem existsUnique_constrainedGradientMapping
    (xBar : E) (γ : NNRealˣ) :
    ∃! xPlus : E,
      xPlus ∈ problem.ambientSet ∧
        IsMinOn
          (quadraticallyRegularizedObjective
            ((problem.toParametricSmoothMinimaxProblem t).affineApproximation xBar)
            γ
            xBar)
          problem.ambientSet
          xPlus :=
    problem.existsUnique_isMinOn_regularizedAffineApproximation t xBar γ

end ExactStep

section ModelValueComparison

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
variable (t : ℝ) (xBar : E)

/-- Remark 2.47.1 (2): the constrained regularized model value with curvature `μ` is bounded above
by the constrained optimal value of the fixed-`t` bridge problem. -/
-- Proof sketch: apply
-- `SmoothMinimaxProblem.lowerRegularizedModelValue_le_optimalValue` to
-- `problem.toParametricSmoothMinimaxProblem t` at base point `xBar`, then rewrite its feasible
-- set as `problem.ambientSet`.
theorem lowerRegularizedModelValue_le_parametricProblemOptimalValue :
    problem.regularizedModelValue t xBar μ ≤
      sInf ((problem.toParametricSmoothMinimaxProblem t) '' problem.ambientSet) := by
  simpa [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue] using
    (problem.toParametricSmoothMinimaxProblem t).lowerRegularizedModelValue_le_optimalValue xBar

/-- Remark 2.47.1 (3): the constrained optimal value of the fixed-`t` bridge problem is bounded
above by the constrained regularized model value with curvature `L`. -/
-- Proof sketch: apply
-- `SmoothMinimaxProblem.optimalValue_le_upperRegularizedModelValue` to
-- `problem.toParametricSmoothMinimaxProblem t` at base point `xBar`, then rewrite its feasible
-- set as `problem.ambientSet`.
theorem parametricProblemOptimalValue_le_upperRegularizedModelValue :
    sInf ((problem.toParametricSmoothMinimaxProblem t) '' problem.ambientSet) ≤
      problem.regularizedModelValue t xBar L := by
  simpa [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue] using
    (problem.toParametricSmoothMinimaxProblem t).optimalValue_le_upperRegularizedModelValue xBar

end ModelValueComparison

end SmoothFunctionalConstraintsMinimizationProblem

/-! ### Definition_2_47 (from Chap02) -/
open scoped Gradient MaxTypeStep

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

namespace SmoothFunctionalConstraintsMinimizationProblem

/-
Definition 2.47 sits at the bridge/view layer between smooth functional-constraint problems and
the chapter's canonical smooth minimax owner for a fixed parameter `t`.

Sampled owner-style declarations:
* `SmoothFunctionalConstraintsMinimizationProblem` in `Definition_2_44`, which owns the ambient
  set `Q`, the objective `f₀`, and the constraint family `fᵢ`;
* `SmoothMinimaxProblem` in `Definition_2_38`, the owner abstraction for fixed-feasible-set
  max-type problems together with the derived affine model `affineApproximation`;
* `SmoothFunctionalConstraintsMinimizationProblem.toLagrangianProblem` in `Definition_2_44`
  together with `LagrangianProblem.constrainedAuxiliaryComponents` in `Lemma_2_21`, which give
  the owner fixed-`t` max-type component family;
* `maxTypeAffineApproximation` in `Lemma_2_18`, which gives the explicit max-type formula for
  the fixed-`t` affine model;
* `quadraticallyRegularizedObjective` in `Definition_1_4_17.lean`, the owner quadratic
  regularization used by the exact-step predicate `IsMinOn`.

Best owner abstraction:
* the bridge problem `problem.toParametricSmoothMinimaxProblem t`;
* the exact-step predicate
  `IsMinOn
      (quadraticallyRegularizedObjective
        ((problem.toParametricSmoothMinimaxProblem t).affineApproximation (xBar : E))
        γ
        (xBar : E))
      (problem.toParametricSmoothMinimaxProblem t).feasibleSet
      xPlus`.

Primitive data:
* the constrained problem `problem`;
* the scalar parameter `t`;
* the feasible base point `xBar : problem.ambientSet`;
* the regularization parameter `γ`;
* the exact-step point `xPlus`, through the owner `IsMinOn` predicate.

Derived API:
* the fixed-`t` bridge `toParametricSmoothMinimaxProblem`;
* the residual expression `γ • ((xBar : E) - xPlus)`.

Source/core/bridge triage:
* source-facing: the textbook constrained step notation `x_f(t; xBar; γ)` and reduced-gradient
  residual once an exact step `xPlus` is fixed;
* core/canonical: `SmoothMinimaxProblem` together with the owner `IsMinOn` exact-step predicate;
* bridge/view: `toParametricSmoothMinimaxProblem` and the explicit
  `problem.toLagrangianProblem.constrainedAuxiliaryComponents` presentation of its affine model.

Accordingly this file does not introduce a second public chosen-point API via
`Classical.choose`; downstream files should use the owner exact-step predicate directly and only
bridge back to the explicit functional-constraint model when that view is mathematically needed.
-/

/-- Shifting the objective by the scalar parameter `t` preserves the owner
`𝓢^{1,1}_{μ,L}(E)` class. -/
private theorem objective_sub_const_mem
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (t : ℝ) :
    IsStrongConvexSmoothObjective μ L (fun x : E ↦ problem.objective x - t) := by
  rcases problem.objective_mem with ⟨hμ, hcont, hstrong, hlip⟩
  refine ⟨hμ, ?_, ?_, ?_⟩
  · simpa using hcont.sub contDiff_const
  · rw [strongConvexOn_iff_convex] at hstrong ⊢
    simpa [sub_eq_add_neg, sub_add_eq_add_sub, add_assoc, add_left_comm, add_comm] using
      hstrong.add_const (-t)
  · intro x y
    simpa [gradient, fderiv_sub_const] using hlip x y

/-- The fixed-`t` functional-constraint problem, viewed through the canonical smooth minimax owner
of Chapter 2. -/
def toParametricSmoothMinimaxProblem
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (t : ℝ) :
    SmoothMinimaxProblem E (Fin (m + 1)) μ L where
  feasibleSet := problem.ambientSet
  feasible_nonempty := problem.ambient_nonempty
  feasible_closed := problem.ambient_closed
  feasible_convex := problem.ambient_convex
  components := problem.constrainedAuxiliaryComponents t
  components_mem := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using problem.objective_sub_const_mem t
    · intro j
      simpa using problem.constraints_mem j

@[simp] theorem toParametricSmoothMinimaxProblem_feasibleSet
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (t : ℝ) :
    (problem.toParametricSmoothMinimaxProblem t).feasibleSet = problem.ambientSet :=
  rfl

/-- The constrained regularized model value of the fixed-`t` bridge problem at base point `xBar`
and regularization parameter `γ`. This is the infimum of the owner quadratically regularized
affine model over the owner feasible set. -/
def regularizedModelValue
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (t : ℝ) (xBar : E) (γ : ℝ) : ℝ :=
  let parametricProblem := problem.toParametricSmoothMinimaxProblem t
  sInf
    ((quadraticallyRegularizedObjective
        (parametricProblem.affineApproximation xBar)
        γ xBar) '' parametricProblem.feasibleSet)

section ExactStep

variable [ProperSpace E]
variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (t : ℝ)

local instance : Fact problem.ambientSet.Nonempty :=
  ⟨problem.ambient_nonempty⟩

local instance : Fact (IsClosed problem.ambientSet) :=
  ⟨problem.ambient_closed⟩

local instance : Fact (Convex ℝ problem.ambientSet) :=
  ⟨problem.ambient_convex⟩

/-- Definition 2.47: the constrained gradient mapping `x_f(t; xBar; γ)` is the chosen exact step
of the quadratically regularized affine model for the fixed-`t` bridge problem on the ambient
constraint set `Q`. -/
abbrev constrainedGradientMapping
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (t : ℝ) (xBar : E) (γ : NNRealˣ) : E :=
  x_f[problem.ambientSet | (problem.toParametricSmoothMinimaxProblem t).components; γ](xBar)

namespace ConstrainedStep

scoped notation:max
    "x_f[" problem ";" t ";" γ "]" "(" xBar ")" =>
  SmoothFunctionalConstraintsMinimizationProblem.constrainedGradientMapping problem t xBar γ

end ConstrainedStep

open scoped ConstrainedStep

-- Proof sketch: unfold `constrainedGradientMapping`; the result is exactly the feasible-point
-- theorem `maxTypeGradientMapping_mem` for the fixed-`t` bridge problem.
/-- The constrained gradient mapping belongs to the ambient feasible set `Q`. -/
theorem constrainedGradientMapping_mem
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (t : ℝ) (xBar : E) (γ : NNRealˣ) :
    x_f[problem; t; γ](xBar) ∈ problem.ambientSet := by
  simpa [constrainedGradientMapping] using
    (maxTypeGradientMapping_mem_and_isMinOn_ofFact
      problem.ambientSet
      (problem.toParametricSmoothMinimaxProblem t).components
      xBar
      γ).1

-- Proof sketch: unfold `constrainedGradientMapping`; this is the exact-step theorem
-- `maxTypeGradientMapping_isMinOn` for the fixed-`t` bridge problem.
/-- The constrained gradient mapping minimizes the fixed-`t` quadratically regularized affine
model on `Q`. -/
theorem constrainedGradientMapping_isMinOn
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (t : ℝ) (xBar : E) (γ : NNRealˣ) :
    IsMinOn
      (quadraticallyRegularizedObjective
        ((problem.toParametricSmoothMinimaxProblem t).affineApproximation xBar)
        γ
        xBar)
      problem.ambientSet
      x_f[problem; t; γ](xBar) := by
  simpa [constrainedGradientMapping] using
    (maxTypeGradientMapping_mem_and_isMinOn_ofFact
      problem.ambientSet
      (problem.toParametricSmoothMinimaxProblem t).components
      xBar
      γ).2

/-- The constrained reduced gradient `g_f(t; xBar; γ)` is the reduced-gradient residual attached
to the constrained gradient mapping. -/
abbrev constrainedReducedGradient
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (t : ℝ) (xBar : E) (γ : NNRealˣ) : E :=
  g_f[problem.ambientSet | (problem.toParametricSmoothMinimaxProblem t).components; γ](xBar)

namespace ConstrainedStep

scoped notation:max
    "g_f[" problem ";" t ";" γ "]" "(" xBar ")" =>
  SmoothFunctionalConstraintsMinimizationProblem.constrainedReducedGradient problem t xBar γ

end ConstrainedStep

-- Proof sketch: unfold `constrainedReducedGradient` and `constrainedGradientMapping`; the
-- statement is the specialized defining identity of `maxTypeReducedGradient`.
/-- The constrained reduced gradient is the scaled residual from `xBar` to the constrained
gradient mapping. -/
theorem constrainedReducedGradient_eq_smul_sub
    (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
    (t : ℝ) (xBar : E) (γ : NNRealˣ) :
    g_f[problem; t; γ](xBar) =
      (γ : ℝ) • (xBar - x_f[problem; t; γ](xBar)) := by
  simpa [constrainedReducedGradient, constrainedGradientMapping] using
    maxTypeReducedGradient_eq_smul_sub_ofFact
      problem.ambientSet
      (problem.toParametricSmoothMinimaxProblem t).components
      xBar
      γ

end ExactStep

end SmoothFunctionalConstraintsMinimizationProblem
