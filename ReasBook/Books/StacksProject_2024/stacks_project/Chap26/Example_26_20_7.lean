import Mathlib.AlgebraicGeometry.ValuativeCriterion
import StacksProject_2024.stacks_project.Chap26.Example_26_14_4_Projective_line
import StacksProject_2024.stacks_project.Chap26.Proposition_26_20_6_Valuative_criterion_of_universal_closedness
import StacksProject_2024.stacks_project.Chap29.ProjectiveSpaceBasic

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: Chapter 29 already fixes the standard projective-space structure morphism as
-- `projectiveSpaceToSpec`, and Chapter 26 already records the canonical equivalence
-- `universallyClosed_iff_valuativeCriterionExistence`. This file therefore keeps only the
-- source-facing `P^1_k` specialization and the two source-facing example consequences.

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

section ProjectiveLine

variable (k : Type u) [Field k]

/-- The canonical structure morphism `P^1_k ⟶ Spec(k)` on the standard `Proj` model of the
projective line, as the `n = 1` case of the Chapter 29 projective-space structure morphism. -/
abbrev projectiveLineToSpec :
    projectiveLine k ⟶ Spec (.of k) :=
  projectiveSpaceToSpec k 1

/-- The projective-line structure morphism is the `n = 1` specialization of the canonical
projective-space structure morphism. -/
theorem projectiveLineToSpec_def :
    projectiveLineToSpec k = projectiveSpaceToSpec k 1 :=
  rfl

/-- Example 26.20.7 (1): for the standard `Proj` model of `P^1_k`, the canonical structure morphism
`projectiveLineToSpec k` satisfies the existence part of the valuative criterion. -/
@[stacks 01KG]
theorem projectiveLine_valuativeCriterionExistence :
    ValuativeCriterion.Existence (projectiveLineToSpec k) := by
  exact (universallyClosed_iff_valuativeCriterionExistence (projectiveLineToSpec k)).mp
    inferInstance

/-- Example 26.20.7 (2): for the standard `Proj` model of `P^1_k`, the canonical structure morphism
`projectiveLineToSpec k` is universally closed. This is the
projective-spectrum formalization
of the textbook statement that `\mathbf{P}^1_k \to \operatorname{Spec}(k)` is universally closed. -/
@[stacks 01KG]
theorem projectiveLine_universallyClosed :
    UniversallyClosed (projectiveLineToSpec k) := by
  change UniversallyClosed (projectiveSpaceToSpec k 1)
  infer_instance

end ProjectiveLine

end AlgebraicGeometry
