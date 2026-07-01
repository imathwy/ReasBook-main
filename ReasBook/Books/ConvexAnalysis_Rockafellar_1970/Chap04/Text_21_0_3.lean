import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_21_0_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {E : Type u} [TopologicalSpace E]
variable {I : Sort v}

/-!
Source/core/bridge triage:

- `source-facing`: Text 21.0.3 records the closedness of the feasible set for a system consisting
  only of weak convex inequalities whose left-hand sides are lower semicontinuous.
- `core/canonical`: the primitive all-weak owner is `LinearConstraintRelation.leFeasible`
  (equivalently `LinearConstraintRelation.feasibleSet (fun _ ↦ .le)`, under the evaluation pairing
  owner from Chapter 1).
- `bridge/view`: the Chapter 21 owner
  `convexInequalitySolutionSet (fun _ ↦ ConvexInequalityRelation.le) f μ` is a direct view of that
  all-weak core owner.

Domain-style sampling used here:
- `convexInequalitySolutionSet` from `Text_21_0_1`;
- `LinearConstraintRelation.leFeasible` from `Chap01.Corollary_2_1_1`;
- `ConvexInequalityRelation.le.solutionSet` from `Text_21_0_1`;
- `LowerSemicontinuous.isClosed_preimage`;
- `isClosed_iInter`.

Primitive data vs derived API:
- primitive data: the index family `f`, the bounds `μ`, and lower semicontinuity of each `f i`;
- derived API: the closedness of the owner feasible set for the all-weak system.

Codomain layer refinement:
- this item only needs lower-semicontinuity sublevel closedness, so the owner statement is placed
  on an arbitrary linear-ordered codomain `β`, rather than the stronger chapter specialization
  `WithBotTop α`.

Layer target: `core/canonical`.
-/

-- Proof sketch: `LinearConstraintRelation.leFeasible f μ` is the intersection of weak sublevel
-- sets `Set.preimage (f i) (Set.Iic (μ i))`. For each `i`, lower semicontinuity of `f i` gives
-- closedness by `LowerSemicontinuous.isClosed_preimage`, and `isClosed_iInter` closes the
-- intersection.
/-- Core owner theorem: lower semicontinuity of every left-hand side makes the all-weak
feasible-set owner `LinearConstraintRelation.leFeasible` closed. -/
theorem isClosed_leFeasible_of_lowerSemicontinuous
    {β : Type w} [LinearOrder β]
    (f : I → E → β) (μ : I → β)
    (hclosed : ∀ i, LowerSemicontinuous (f i)) :
    IsClosed ((LinearConstraintRelation.leFeasible f μ : Set E)) := by
  simpa [LinearConstraintRelation.leFeasible, closedHalfSpaceLE_eq_preimage] using
    isClosed_iInter fun i ↦ (hclosed i).isClosed_preimage (μ i)

/-- Text 21.0.3: if every left-hand side in an all-weak convex inequality system is lower
semicontinuous, then its solution set is closed. -/
theorem isClosed_convexInequalitySolutionSet_of_lowerSemicontinuous
    {β : Type w} [LinearOrder β]
    (f : I → E → β) (μ : I → β)
    (hclosed : ∀ i, LowerSemicontinuous (f i)) :
    IsClosed (convexInequalitySolutionSet
      (fun _ : I ↦ ConvexInequalityRelation.le) f μ) := by
  simpa [convexInequalitySolutionSet, LinearConstraintRelation.leFeasible,
    LinearConstraintRelation.feasibleSet, LinearConstraintRelation.solutionSet] using
    isClosed_leFeasible_of_lowerSemicontinuous (f := f) (μ := μ) hclosed

end
