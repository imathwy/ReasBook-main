module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch2.Assumption_A1.ClosedConvex

public section

universe u

variable {H₁ : Type u} [TopologicalSpace H₁] [AddCommMonoid H₁] [Module ℝ H₁]

/- Assumption A1 (1). The closed-subset clause of the feasible-set assumption is formalized in
Lean by the canonical predicate `IsClosed C` for `C : Set H₁`. -/
#check IsClosed

/- Assumption A1 (2). The convex-subset clause of the feasible-set assumption is formalized in
Lean by the canonical predicate `Convex ℝ C` for `C : Set H₁`. -/
#check Convex

/- Assumption A1. The combined feasible-set hypothesis used later in the chapter is packaged by
the source-facing companion predicate `Set.ClosedConvex C`. -/
#check Set.ClosedConvex
