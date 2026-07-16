import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Example_5_1_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Example 5.1.4 lies in the Chapter 5 self-concordance / logarithmic-sublevel-barrier domain.

Sampled owner-style declarations:
* `quadraticAffineObjective` from `Example_5_1_2`, the chapter source-facing owner for affine-
  quadratic objectives on a real Hilbert space;
* `sublevelLogBarrier` from `Theorem_5_1_4`, the chapter owner for barriers `x ↦ -log (β - f x)`;
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the core self-concordance owner for
  constant `1`;
* `ContinuousLinearMap.IsPositive`, the canonical positivity owner for self-adjoint positive
  semidefinite operators.

Source/core/bridge triage:
* source-facing: the logarithmic barrier of the concave affine-quadratic potential
  `φ(x) = α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫`;
* core/canonical: `sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0` on
  `{x : E | x ∈ (Set.univ : Set E) ∧ quadraticAffineObjective (-α) (-a) A x < 0}`;
* bridge/view: the sign rewrite
  `0 - quadraticAffineObjective (-α) (-a) A x = α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫`.

Primitive data:
* `α`, `a`, and `A`.

Derived API:
* the generic strict sublevel set expression as a proof bridge for the textbook positivity set;
* the generic Chapter 5 sublevel barrier as a proof bridge for the textbook `-log φ`.

This example remains source-facing at the theorem surface: the public statement keeps the textbook
positivity domain and logarithmic barrier, while the Chapter 5 sublevel-barrier owners remain the
canonical internal bridge. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- The canonical strict-sublevel domain
`{x | quadraticAffineObjective (-α) (-a) A x < 0}` is exactly the textbook positivity domain
`{x | 0 < α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫}`. -/
theorem quadraticAffineObjective_neg_strictSublevel_eq
    (α : ℝ) (a : E) (A : E →L[ℝ] E) :
    {x : E | quadraticAffineObjective (-α) (-a) A x < 0} =
      {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x} := by
  ext x
  change quadraticAffineObjective (-α) (-a) A x < 0 ↔
    0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x
  rw [quadraticAffineObjective_apply]
  simp only [inner_neg_left]
  constructor <;> intro hx <;> linarith

/- The canonical sublevel-log-barrier owner
`sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0` evaluates to the textbook
logarithmic barrier of the concave affine-quadratic potential. -/
theorem sublevelLogBarrier_quadraticAffineObjective_neg_eq
    (α : ℝ) (a : E) (A : E →L[ℝ] E) :
    sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0 =
      fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x) := by
  funext x
  rw [sublevelLogBarrier_apply, quadraticAffineObjective_apply]
  simp only [inner_neg_left]
  congr 1
  ring_nf

variable [CompleteSpace E]

/-- Example 5.1.4: if `A` is positive, then the logarithmic barrier attached to the affine-
quadratic potential `φ(x) = α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫` is standard self-concordant on its
positivity domain `{x | 0 < φ(x)}`. The generic Chapter 5 sublevel-barrier owners are only a
proof bridge behind this source-facing formulation. -/
theorem logAffineQuadraticBarrier_isStandardSelfConcordantOn
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : A.IsPositive) :
    IsStandardSelfConcordantOn
      {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x}
      (fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x)) := sorry

end
