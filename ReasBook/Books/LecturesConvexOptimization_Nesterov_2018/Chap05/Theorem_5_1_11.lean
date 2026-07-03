import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_3_3
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_18
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin ConvexAnalysis Gradient

noncomputable section

universe u₁ u₂

variable {E₁ : Type u₁} {E₂ : Type u₂}

variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
variable [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

local notation "Z" => WithLp 2 (E₁ × E₂)

/- Theorem 5.1.11 lies in the chapter's partial-minimization / self-concordance calculus.

Sampled owner-style declarations in this domain:
- `IsSelfConcordantOnWith` from `Definition_5_1_1`, the Chapter 5 owner for quantitative
  self-concordance on an ambient Hilbert space;
- `partialInfProjection` from Chapter 3 and `extendedRealRealPart` from `Definition_5_0_18`, the
  canonical owners for the partial-minimization objective;
- `argmin[Q] f` and `mem_constrainedArgmin_iff` from `Chap01/Definition_1_3_3`, the project
  owner for chosen constrained minimizers;
- mathlib `WithLp 2 (E₁ × E₂)` together with the canonical bridge `z ↦ z.ofLp`, the intrinsic
  `L²` product owner determined by `E₁` and `E₂`;
- mathlib/project `hessian`, applied to the frozen `y`-slice `Φ ∘ Prod.mk x`, the canonical
  Chapter 5 owner for the `yy` second-derivative data.

Best owner abstraction:
- source-facing: the self-concordance of `Φ : E₁ × E₂ → ℝ` on `interior Q`;
- core/canonical:
  `IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) Mf
    (Φ ∘ WithLp.ofLp)`,
  `partialInfProjection Q (Real.toEReal ∘ Φ)`, its real surface, and the frozen-slice Hessian
  `hessian (Φ ∘ Prod.mk x) (y x)`;
- bridge/view: the chosen minimizer branch `y`, used to evaluate the slice Hessian at the
  minimizing point.

Primitive data:
- the feasible set `Q : Set (E₁ × E₂)`;
- the objective `Φ : E₁ × E₂ → ℝ`;
- the selected minimizing branch `y : E₁ → E₂`, recorded by membership in the canonical fiberwise
  owner `argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)`.

Derived API:
- the partial-minimization objective
  `extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))`;
- the frozen-slice Hessian `hessian (Φ ∘ Prod.mk x) (y x)`.

This refinement keeps the main theorem on the intrinsic product-space owner
`IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) Mf
  (Φ ∘ WithLp.ofLp)`; the `WithLp` realization is now the canonical ambient owner rather than
extra raw-product instance data, while the fiberwise data is expressed through the canonical map
`Prod.mk x : E₂ → E₁ × E₂` instead of coordinate-level set comprehensions and lambdas. -/

-- Proof sketch: combine the global lower Taylor inequality for the self-concordant function `Φ`
-- on `interior Q` with the envelope identities at the canonical fiber minimizer
-- `y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)`. The minimizing property removes the
-- `y`-gradient term, and the positive-definite frozen-slice `yy` Hessian identifies the Hessian
-- of the value
-- function with the Schur complement of the ambient Hessian, yielding the same self-concordance
-- constant for the partial minimization objective.
/-- Theorem 5.1.11: if `Φ` is self-concordant with constant `M_Φ` on `interior Q` for a chosen
intrinsic `L²` product lift of `E₁ × E₂`, and each fiberwise infimum is attained at an interior
point `y(x)` where the frozen `y`-slice Hessian `∇² (Φ ∘ Prod.mk x) (y x)` is positive
definite, then the canonical real surface of the partial infimal projection is self-concordant on
its natural domain with the same constant. -/
theorem partialMinimizationObjective_isSelfConcordantOnWith
    {Q : Set (E₁ × E₂)} {Mf : NNReal} {Φ : E₁ × E₂ → ℝ} {y : E₁ → E₂}
    (hself :
      IsSelfConcordantOnWith ((WithLp.ofLp : Z → E₁ × E₂) ⁻¹' interior Q) Mf
        (Φ ∘ WithLp.ofLp))
    (hy_mem_interior :
      ∀ ⦃x : E₁⦄, x ∈ dom (partialInfProjection Q (Real.toEReal ∘ Φ)) → (x, y x) ∈ interior Q)
    (hy_argmin :
      ∀ ⦃x : E₁⦄, x ∈ dom (partialInfProjection Q (Real.toEReal ∘ Φ)) →
        y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x))
    (hyy_pos :
      ∀ ⦃x : E₁⦄, x ∈ dom (partialInfProjection Q (Real.toEReal ∘ Φ)) → ∀ v : E₂, v ≠ 0 →
        0 < inner ℝ v ((hessian (Φ ∘ Prod.mk x) (y x)) v)) :
    IsSelfConcordantOnWith (dom (partialInfProjection Q (Real.toEReal ∘ Φ))) Mf
      (extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))) := sorry

end
