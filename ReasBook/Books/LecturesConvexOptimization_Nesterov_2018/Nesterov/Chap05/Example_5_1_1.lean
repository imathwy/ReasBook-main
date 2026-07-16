import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Example_5_1_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (α : ℝ) (a : E)

/- Example 5.1.1 lies in the Chapter 5 self-concordance domain.

Sampled owner-style declarations:
* `IsSelfConcordantOnWith`
* `quadraticAffineObjective`
* `quadraticAffineObjective_zero_operator`
* `quadraticAffineObjective_isSelfConcordantOnWith_zero`

Best owner abstraction:
* source-facing: the affine objective `x ↦ α + ⟪a, x⟫`
* core/canonical: `quadraticAffineObjective α a A`
* bridge/view: the specialization `A = 0`

Primitive data:
* the offset `α`
* the linear term `a`

Derived API:
* the affine self-concordance statement, obtained by specializing the chapter owner theorem to the
  zero quadratic part

This item adds no new mathematics beyond the chapter owner theorem
`quadraticAffineObjective_isSelfConcordantOnWith_zero`, so the file keeps only the specialization
check and does not introduce a parallel wrapper theorem. -/

/- Example 5.1.1 is the zero-quadratic specialization of
`quadraticAffineObjective_isSelfConcordantOnWith_zero`. -/
#check
  (show IsSelfConcordantOnWith (Set.univ : Set E) 0 (fun x ↦ α + inner ℝ a x) from by
    simpa using
      quadraticAffineObjective_isSelfConcordantOnWith_zero
        α a (0 : E →L[ℝ] E) ContinuousLinearMap.isPositive_zero)
