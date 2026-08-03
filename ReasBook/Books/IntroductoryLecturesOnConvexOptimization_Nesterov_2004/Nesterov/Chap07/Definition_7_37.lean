import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Nesterov.Chap03.Definition_3_1_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Nesterov.Chap07.Proposition_7_7

noncomputable section

open scoped RealInnerProductSpace

universe u

/- Primary domain: finite max-type / affine-slice constrained minimization.

Sampled owner-style declarations:
- `maxTypeObjective` in `Chap02/Lemma_2_18`, the project owner for finite maxima of nonempty
  families;
- `hyperplane` and `mem_hyperplane_iff` in `Chap03/Definition_3_1_4_1`, the canonical affine
  level-set owner for constraints of the form `⟪d, x⟫ = 1`;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `supportAbsMinProblem` in `Chap07/Proposition_7_7`, the exact earlier chapter owner of the
  problem `min {max_i |⟪a_i, x⟫| | ⟪d, x⟫ = 1}`.

Best owner abstraction:
- source-facing: `supportAbsMinProblem a d`;
- core/canonical: `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`, `hyperplane d 1`, and
  `SetConstrainedMinimizationProblem`;
- bridge/view: the objective and feasible-set identification lemmas below.

Primitive data:
- a finite family `a : ι → E`;
- a normal vector `d : E`.

Derived API:
- the canonical problem owner `supportAbsMinProblem a d`;
- its objective `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`;
- its feasible slice `hyperplane d 1`.

Source/core/bridge triage:
- source-facing: the conic reformulation problem `min {max_i |⟪a_i, x⟫| | ⟪d, x⟫ = 1}`;
- core/canonical: `supportAbsMinProblem`;
- bridge/view: the two identification lemmas below.

-/

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section

variable (a : ι → E) (d x : E)

recall maxTypeObjective
recall hyperplane
recall mem_hyperplane_iff

/- Definition 7.37: the conic reformulation
`min {max_i |⟪a_i, x⟫| | ⟪d, x⟫ = 1}` is the canonical constrained minimization problem
`supportAbsMinProblem a d`. -/
recall supportAbsMinProblem

/- The objective of the conic reformulation is `x ↦ max_i |⟪a_i, x⟫|`. -/
recall supportAbsMinProblem_apply

/- The feasible set of the conic reformulation is the affine hyperplane `hyperplane d 1`. -/
recall supportAbsMinProblem_feasibleSet

/- Membership in the feasible set is exactly the affine constraint `⟪d, x⟫ = 1`. -/
recall mem_supportAbsMinProblem_feasibleSet_iff

end

end
