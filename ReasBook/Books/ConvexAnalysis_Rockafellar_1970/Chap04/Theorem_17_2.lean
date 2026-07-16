import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E]

/-!
Source/core/bridge triage:

`source-facing`: this file keeps the Theorem 17.2 bridge shape through
`closedConvexHull 𝕜 S = convexHull 𝕜 (closure S)` and
`closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S)`, but it makes the key
closedness witness explicit: `IsClosed (convexHull 𝕜 (closure S))`.
- `core/canonical`: the owner abstraction is `closedConvexHull 𝕜 S`, together with set closure
  `closure` and convex hull `convexHull 𝕜`, at the primitive topological-module layer.
- `bridge/view`: the owner-side identity is obtained directly from the minimality owners
  `closedConvexHull_min` and `convexHull_min`, together with
  `closedConvexHull_closure_eq_closedConvexHull`.
- Domain-style sampling used here: `closedConvexHull`, `closedConvexHull_eq_closure_convexHull`,
  `closedConvexHull_closure_eq_closedConvexHull`, `isClosed_closedConvexHull`.
- Primitive data vs derived API: the primitive owner-side bridge input in this file is exactly the
  closedness of `convexHull 𝕜 (closure S)`, rather than a stronger compactness or boundedness
  hypothesis. `closedConvexHull 𝕜 S` is generated owner data, and the displayed equalities are
  derived bridge API.
- Layer target: `bridge/view`; source-facing corollaries are stated directly on the same primitive
  closedness witness, with no non-primitive wrapper assumptions.
-/

/-- The primitive owner-side bridge: if `convexHull 𝕜 (closure S)` is closed, then the closed
convex hull of `S` is the convex hull of `closure S`. -/
-- Proof sketch: rewrite `closedConvexHull 𝕜 S` as `closedConvexHull 𝕜 (closure S)`, then use
-- the minimality rules for `closedConvexHull` and `convexHull`.
theorem closedConvexHull_eq_convexHull_closure_of_isClosed_convexHull_closure (S : Set E)
    (hS_convexHullClosure_closed : IsClosed (convexHull 𝕜 (closure S))) :
    closedConvexHull 𝕜 S = convexHull 𝕜 (closure S) := by
  calc
    closedConvexHull 𝕜 S = closedConvexHull 𝕜 (closure S) := by
      symm
      exact closedConvexHull_closure_eq_closedConvexHull
    _ = convexHull 𝕜 (closure S) := by
      refine subset_antisymm ?_ ?_
      · exact
          closedConvexHull_min (subset_convexHull 𝕜 (closure S))
            (convex_convexHull 𝕜 (closure S)) hS_convexHullClosure_closed
      · exact
          convexHull_min (subset_closedConvexHull (𝕜 := 𝕜) (s := closure S))
            (convex_closedConvexHull (𝕜 := 𝕜) (s := closure S))

/-- Owner-side recognition bridge: `closedConvexHull 𝕜 S` is exactly `convexHull 𝕜 (closure S)`
precisely when `convexHull 𝕜 (closure S)` is closed. -/
theorem closedConvexHull_eq_convexHull_closure_iff_isClosed_convexHull_closure (S : Set E) :
    closedConvexHull 𝕜 S = convexHull 𝕜 (closure S) ↔
      IsClosed (convexHull 𝕜 (closure S)) := by
  constructor
  · intro hEq
    simpa [← hEq] using (isClosed_closedConvexHull (𝕜 := 𝕜) (s := S))
  · intro hS_convexHullClosure_closed
    exact
      closedConvexHull_eq_convexHull_closure_of_isClosed_convexHull_closure
        S hS_convexHullClosure_closed

end

section

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [TopologicalSpace E]

/-- Primitive source-facing closure bridge: if `convexHull 𝕜 (closure S)` is closed and
`closure (convexHull 𝕜 S)` is convex, then
`closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S)`. -/
-- Proof sketch: prove each inclusion by minimality at the primitive set level.
theorem
    closure_convexHull_eq_convexHull_closure_of_isClosed_of_convex_closure
    (S : Set E) (hS_convexHullClosure_closed : IsClosed (convexHull 𝕜 (closure S)))
    (hS_closureConvexHull_convex : Convex 𝕜 (closure (convexHull 𝕜 S))) :
    closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S) := by
  refine subset_antisymm ?_ ?_
  · exact
      closure_minimal
        (convexHull_mono (subset_closure : S ⊆ closure S))
        hS_convexHullClosure_closed
  · exact
      convexHull_min
        (closure_minimal
          (subset_trans (subset_convexHull 𝕜 S) subset_closure)
          isClosed_closure)
        hS_closureConvexHull_convex

/-- Primitive source-facing recognition bridge: under the primitive convexity input
`Convex 𝕜 (closure (convexHull 𝕜 S))`, the identity
`closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S)` is equivalent to closedness of
`convexHull 𝕜 (closure S)`. -/
theorem
    closure_convexHull_eq_convexHull_closure_iff_isClosed_convexHull_closure_of_convex_closure
    (S : Set E) (hS_closureConvexHull_convex : Convex 𝕜 (closure (convexHull 𝕜 S))) :
    closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S) ↔
      IsClosed (convexHull 𝕜 (closure S)) := by
  constructor
  · intro hEq
    simpa [hEq] using (isClosed_closure : IsClosed (closure (convexHull 𝕜 S)))
  · intro hS_convexHullClosure_closed
    exact
      closure_convexHull_eq_convexHull_closure_of_isClosed_of_convex_closure
        S hS_convexHullClosure_closed hS_closureConvexHull_convex

end

section

variable {𝕜 E : Type*}
variable [Field 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

/-- Source-facing recognition bridge: `closure (convexHull 𝕜 S)` is exactly
`convexHull 𝕜 (closure S)` precisely when `convexHull 𝕜 (closure S)` is closed. -/
theorem closure_convexHull_eq_convexHull_closure_iff_isClosed_convexHull_closure
    (S : Set E) :
    closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S) ↔
      IsClosed (convexHull 𝕜 (closure S)) := by
  have hS_closureConvexHull_convex : Convex 𝕜 (closure (convexHull 𝕜 S)) := by
    simpa [closedConvexHull_eq_closure_convexHull (𝕜 := 𝕜) (s := S)] using
      (convex_closedConvexHull (𝕜 := 𝕜) (s := S))
  exact
    closure_convexHull_eq_convexHull_closure_iff_isClosed_convexHull_closure_of_convex_closure
      (𝕜 := 𝕜) S hS_closureConvexHull_convex

/-- Source-facing closure bridge: if `convexHull 𝕜 (closure S)` is closed, then
`closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S)`. -/
theorem closure_convexHull_eq_convexHull_closure_of_isClosed_convexHull_closure (S : Set E)
    (hS_convexHullClosure_closed : IsClosed (convexHull 𝕜 (closure S))) :
    closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S) := by
  exact
    (closure_convexHull_eq_convexHull_closure_iff_isClosed_convexHull_closure
      (𝕜 := 𝕜) S).2 hS_convexHullClosure_closed

end

section

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [TopologicalSpace E]

/-- Closed-set bridge at the source-facing surface: for closed `S`,
`convexHull 𝕜 S` is closed precisely when `convexHull 𝕜 (closure S)` is closed. -/
theorem isClosed_convexHull_iff_isClosed_convexHull_closure_of_isClosed
    (S : Set E) (hS_closed : IsClosed S) :
    IsClosed (convexHull 𝕜 S) ↔ IsClosed (convexHull 𝕜 (closure S)) := by
  simp

/-- Closed-set corollary under the same bridge witness: if `S` is closed and
`convexHull 𝕜 (closure S)` is closed, then `convexHull 𝕜 S` is closed. -/
theorem isClosed_convexHull_of_isClosed_of_isClosed_convexHull_closure
    (S : Set E) (hS_closed : IsClosed S)
    (hS_convexHullClosure_closed : IsClosed (convexHull 𝕜 (closure S))) :
    IsClosed (convexHull 𝕜 S) := by
  exact
    (isClosed_convexHull_iff_isClosed_convexHull_closure_of_isClosed
      (𝕜 := 𝕜) S hS_closed).2 hS_convexHullClosure_closed

end
