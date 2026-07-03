import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_40 (from Chap02) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- Definition 2.40 is a recall-only item in the finite max-type quadratic-regularization domain on
a real Hilbert space.

Sampled owner-style declarations:
* `maxTypeAffineApproximation` in `Definition_2_39`, the owner affine max-type model at `xBar`;
* `maxTypeAffineApproximation_apply`, the pointwise bridge for that affine model;
* `quadraticallyRegularizedObjective` in `Definition_1_4_17.lean`, the owner quadratic
  regularization of an objective;
* `quadraticallyRegularizedObjective_apply`, the pointwise bridge for the regularized objective.

Best owner abstraction:
* source-facing/core:
  `quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar`;
* bridge/view: the pointwise expansion obtained by composing the two owner `..._apply` lemmas.

Primitive data:
* a nonempty finite component family `fi : ι → E → ℝ`;
* a base point `xBar : E`;
* a regularization parameter `γ : ℝ`.

Derived API:
* the affine max-type model `maxTypeAffineApproximation fi xBar`;
* the expanded value formula for the regularized max-type model.

Source/core/bridge triage:
* source-facing/core:
  `quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar`;
* bridge/view: its pointwise expansion.

This file therefore recalls the composed owner expression directly and introduces no parallel local
alias such as `regularizedMaxTypeModel` or `proximalMaxLinearization`. -/

recall maxTypeAffineApproximation
recall maxTypeAffineApproximation_apply
recall quadraticallyRegularizedObjective
recall quadraticallyRegularizedObjective_apply

section

variable (fi : ι → E → ℝ) (γ : ℝ) (xBar : E)

set_option linter.hashCommand false in
#check quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar

example (x : E) :
    quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar x =
      Finset.univ.sup' Finset.univ_nonempty
          (fun i : ι ↦ fi i xBar + inner ℝ (∇ (fi i) xBar) (x - xBar)) +
        (γ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
  rw [quadraticallyRegularizedObjective_apply, maxTypeAffineApproximation_apply]

end

/-! ### Theorem_2_40 (from Chap02) -/
/- Primary domain: constrained strong convexity and quadratic growth on complete real
inner-product spaces.

Sampled owner-style declarations:
* `StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt` in `Definition_2_14`
* `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Theorem_2_29`
* `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem` in `Definition_2_14`
* `StrongConvexOn.quadratic_growth_of_isMinOn_of_mem` in `Theorem_2_30`

Best owner abstraction:
* source-facing/core: `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem`
* bridge/view: the ambient-norm specialization `StrongConvexOn.quadratic_growth_of_isMinOn_of_mem`

Primitive data:
* the seminorm `p`
* the feasible set `Q`
* the objective `f`
* the strong-convexity hypothesis `hf : StrongConvexOnWith p μ Q f`
* the feasible minimizer data `hxStar_mem : xStar ∈ Q` and `hxStar : IsMinOn f Q xStar`

Derived API:
* the constrained owner quadratic-growth theorem on a feasible set
* the whole-space ambient-norm specialization from `Theorem_2_30`

This file therefore introduces no second proof surface: Theorem 2.40 is recalled directly from
the weaker owner theorem in `Definition_2_14`, without keeping a redundant differentiable
specialization. -/

/- Theorem 2.40 is the direct owner recall of constrained quadratic growth at a feasible
minimizer. -/
recall StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem
