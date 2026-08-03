import Mathlib
import BauschkeLean.Chap06.Definition_6_38
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap20.Definition_20_1
import BauschkeLean.Chap26.Text_26_0_1
import BauschkeLean.Chap26.Problem_26_28

open scoped InnerProductSpace Pointwise Set SetValuedOperator

universe u v

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

noncomputable section

namespace SetValuedOperator

-- Semantic recall/local precedent: `lean_leansearch` surfaced only generic graph/orthogonal
-- results, so this item uses the verified Chapter 26 inclusion owners
-- `primal_inclusion_solution_set`, `dual_inclusion_solution_set`,
-- `composite_primal_inclusion_solution_set`, and `composite_dual_inclusion_solution_set`,
-- together with the canonical graph owner `L.toLinearMap.graph`,
-- the codomain-translation owner `addConst`, the domain-translation owner `translate`,
-- and the product owner `SetValuedOperator.prod`.

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Proposition 26.37 (1): a product-space primal solution for the normal-cone/graph reduction is
exactly a graph point `(x, L x)` whose first coordinate solves the primal inclusion from Problem
26.28. -/
theorem mem_primal_inclusion_solution_set_normalCone_graph_iff
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (x : H) (y : K) :
    (x, y) ∈
        primal_inclusion_solution_set
          (N[L.toLinearMap.graph])
          (A.addConst (-z) × B.translate r) ↔
      y = L x ∧ x ∈ composite_primal_inclusion_solution_set z A r B L := sorry

/-- Proposition 26.37 (2): a product-space dual solution for the normal-cone/graph reduction is
exactly a point `(-L† v, v)` whose second coordinate solves the dual inclusion from Problem
26.28. -/
theorem mem_dual_inclusion_solution_set_normalCone_graph_iff
    (z : H) (A : SetValuedOperator H H) (r : K) (B : SetValuedOperator K K)
    (L : H →L[ℝ] K) (u : H) (v : K) :
    (u, v) ∈
        dual_inclusion_solution_set
          (N[L.toLinearMap.graph])
          (A.addConst (-z) × B.translate r) ↔
      u = -L.adjoint v ∧ v ∈ composite_dual_inclusion_solution_set z A r B L := sorry

end SetValuedOperator
