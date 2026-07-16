import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_13
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_16
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_17
import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_27_4

noncomputable section

universe u v w z

namespace Bifunction

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.8 says that, when the generalized convex program attached to `F`
  is consistent, the ambient set of optimal solutions is exactly the minimum set of `F₀`, and
  this set is a possibly empty convex subset of the feasible set.
- `core/canonical`: the existing owners are `Bifunction.objective`, the Chapter 6 consistency
  owner `Bifunction.IsConsistent`, the Chapter 6 feasible-set owner `Bifunction.feasibleSet`, and
  the Chapter 6 minimum-set owner `minimumSet`.
- `bridge/view`: the source set of optimal solutions is owned here as `optimalSolutionSet F`,
  then related to the canonical owner `minimumSet (F)₀`.

Domain-style sampling used here:
- `Bifunction.objective`;
- `Bifunction.IsConsistent` and `isConsistent_iff_feasibleSet_nonempty`;
- `Bifunction.feasibleSet`;
- `dom(·)` through the feasible-set owner;
- `minimumSet`, `minimumSet_subset_dom_of_nonempty_dom`, and `minimumSet_isConvex`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β`;
- source-facing optimal-solution owner: `optimalSolutionSet F`, expressed intrinsically as
  feasible minimizers of `(F)₀`;
- canonical comparison owner: `minimumSet (F)₀`;
- primitive feasibility hypothesis: `IsConsistent F`, equivalently `(feasibleSet F).Nonempty`;
- derived geometry: convexity of that minimum set and its containment in the feasible set.

Layer target:
- clause `(1)` is `source-facing`, stated as the set equality between `optimalSolutionSet F` and
  the canonical minimum set;
- clauses `(2)` and `(3)` stay on the source-facing owner `optimalSolutionSet F`, proved through
  the canonical bridge to `minimumSet (F)₀`.
-/

section OptimalSolutions

variable {U : Type u} {X : Type v} {β : Type w}
variable [Preorder β] [Top β] [Zero U]

/-- The ambient set of optimal solutions of the generalized convex program attached to `F`. -/
def optimalSolutionSet (F : U → X → β) : Set X :=
  feasibleSet F ∩ minimumSet (F)₀

/-- Membership in `optimalSolutionSet F` is feasible-membership together with minimizer
membership for `F₀`. -/
@[simp] theorem mem_optimalSolutionSet {F : U → X → β} {x : X} :
    x ∈ optimalSolutionSet F ↔ x ∈ feasibleSet F ∧ x ∈ minimumSet (F)₀ :=
  Iff.rfl

/-- If the generalized convex program attached to `F` is inconsistent, then it has no optimal
solutions. -/
theorem optimalSolutionSet_eq_empty_of_not_consistent
    {F : U → X → β}
    (hF_inconsistent : ¬ IsConsistent F) :
    optimalSolutionSet F = ∅ := by
  ext x
  constructor
  · intro hx
    exfalso
    exact hF_inconsistent <| (isConsistent_iff_feasibleSet_nonempty F).2 ⟨x, hx.1⟩
  · intro hx
    cases hx

end OptimalSolutions

section OptimalSolutionsConsistent

variable {U : Type u} {X : Type v} {β : Type w}
variable [Preorder β] [Top β] [Zero U]

-- Proof sketch: by definition `optimalSolutionSet F = feasibleSet F ∩ minimumSet (F)₀`.
-- Under consistency, `feasibleSet F = dom((F)₀)` is nonempty, so every minimizer of `(F)₀` is
-- finite via `minimumSet_subset_dom_of_nonempty_dom`, hence feasible.
/-- Lemma 6.29.8 (1): when the generalized convex program attached to `F` is consistent, the
ambient set of optimal solutions is exactly the minimum set of `F₀`. -/
theorem optimalSolutionSet_eq_minimumSet_of_consistent
    {F : U → X → β}
    (hF_consistent : IsConsistent F) :
    optimalSolutionSet F = minimumSet (F)₀ := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hfeasible_nonempty : (feasibleSet F).Nonempty :=
      (isConsistent_iff_feasibleSet_nonempty F).1 hF_consistent
    have hobjective_dom_nonempty : dom((F)₀).Nonempty := by
      simpa [feasibleSet] using hfeasible_nonempty
    have hx_feasible_dom : x ∈ dom((F)₀) :=
      (minimumSet_subset_dom_of_nonempty_dom (f := (F)₀) hobjective_dom_nonempty) hx
    have hx_feasible : x ∈ feasibleSet F := by
      simpa [feasibleSet] using hx_feasible_dom
    exact ⟨hx_feasible, hx⟩

end OptimalSolutionsConsistent

section Convexity

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMulZeroClass 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [ConditionallyCompleteLattice α]
variable [AddCommMonoid α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

-- Proof sketch: apply the owner method `Function.IsConvex.convex_minimumSet` to the objective
-- function `objective F`. Its convexity is supplied by the existing slice theorem
-- `Function.IsConvex.objective`, which specializes convexity of `Function.uncurry F` to the zero
-- slice `F₀`. If `F` is inconsistent, then `optimalSolutionSet F = ∅`.
/-- Lemma 6.29.8 (2): if the graph function of `F` is convex, then the optimal-solution set is
convex. -/
theorem optimalSolutionSet_isConvex_of_uncurry_isConvex
    {F : U → X → WithBotTop α}
    (hF_convex : (Function.uncurry F).IsConvex 𝕜) :
    Convex 𝕜 (optimalSolutionSet F) := by
  by_cases hF_consistent : IsConsistent F
  · rw [optimalSolutionSet_eq_minimumSet_of_consistent hF_consistent]
    exact hF_convex.objective.convex_minimumSet
  · rw [optimalSolutionSet_eq_empty_of_not_consistent hF_consistent]
    simpa using (convex_empty : Convex 𝕜 (∅ : Set X))

end Convexity

section Feasibility

variable {U : Type u} {X : Type v} {β : Type w}
variable [Preorder β] [Top β] [Zero U]

-- Proof sketch: membership in the source-facing owner `optimalSolutionSet F` already includes
-- feasibility as one of its two defining clauses.
/-- Lemma 6.29.8 (3): every optimal solution is feasible. -/
theorem optimalSolutionSet_subset_feasibleSet
    {F : U → X → β} :
    optimalSolutionSet F ⊆ feasibleSet F := by
  intro x hx
  exact hx.1

end Feasibility

end Bifunction
