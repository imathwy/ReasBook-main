import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_20
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_39_0_1

open scoped Rockafellar SetRel

universe u v w

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Definition 39.0.5 introduces the closure `cl A` of a convex process and says
  that a process is closed when `cl A = A`.
- `core/canonical`: the owner of a process graph is the existing relation type `SetRel U X`, and
  graph closure is the ambient topological closure `_root_.closure` on subsets of `U × X`.
- `bridge/view`: the process owner from Definition 39.0.1 is the predicate `A.IsConvexProcess R`
  on a relation `A : SetRel U X`, so the theorem that closure preserves convex processes should be
  stated directly on that owner.

Primary mathematical domain:
- convex processes as graph relations in topological modules.

Domain-style sampling used here:
- `SetRel` from `Mathlib.Data.Rel` as the canonical graph owner;
- `_root_.closure` and `_root_.IsClosed` for graph closure and graph closedness;
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`;
- `Set.IsConvexCone.closure` from `Chap02.Text_6_20` as the owner-level graph-closure theorem.

Primitive data vs derived API:
- primitive source-facing data: the relation graph `A : SetRel U X`;
- primitive owner introduced here: `SetRel.closure A`;
- derived API: graph-closure formula, closedness-as-fixed-point, and the theorem that closure
  preserves the convex-process owner.

Notation decision:
- the chapter closure notation `cl(·)` is extended to relation graphs in the same
  `Rockafellar` notation scope used elsewhere in the project, so source-facing Chapter 39
  statements can use `cl(A)` directly while the canonical owner remains `SetRel.closure`.

Layer target: `source-facing`, stated directly on the canonical relation owner.
-/

section Closure

variable {U : Type u} {X : Type v}
variable [TopologicalSpace (U × X)]

/-- Definition 39.0.5: the closure of a convex process `A` is the relation whose graph is the
ambient topological closure of the graph of `A`. -/
abbrev closure (A : SetRel U X) : SetRel U X :=
  _root_.closure A

scoped[Rockafellar] notation (name := setRelTermCl) "cl(" A ")" => SetRel.closure A

@[simp] theorem coe_closure (A : SetRel U X) :
    (cl(A) : Set (U × X)) = _root_.closure A := rfl

-- Proof sketch: this is the standard set-theoretic inclusion `subset_closure` applied to the
-- graph set `(A : Set (U × X))`.
/-- Every relation is contained in its graph closure. -/
theorem subset_closure (A : SetRel U X) :
    A ⊆ cl(A) := by
  intro p hp
  exact _root_.subset_closure hp

-- Proof sketch: relation membership is pair membership in the graph, and `SetRel.closure` is
-- definitionally the ambient closure of `(A : Set (U × X))`.
/-- A pair `(u, x)` belongs to `SetRel.closure A` exactly when it lies in the ambient closure of
the graph of `A`. -/
@[simp] theorem mem_closure_iff {A : SetRel U X} {u : U} {x : X} :
    u ~[cl(A)] x ↔ (u, x) ∈ _root_.closure A := Iff.rfl

/-- A relation, and in particular a convex process, is closed when its graph is topologically
closed in `U × X`. This is the primitive canonical owner layer for graph closedness. -/
abbrev IsClosed (A : SetRel U X) : Prop :=
  _root_.IsClosed A

@[simp] theorem isClosed_closure (A : SetRel U X) :
    (cl(A)).IsClosed := by
  exact (_root_.isClosed_closure : _root_.IsClosed (_root_.closure A))

-- Proof sketch: this is exactly `closure_eq_iff_isClosed` on the graph set `(A : Set (U × X))`
-- with the owner-level abbreviation `SetRel.IsClosed` unfolded.
/-- Canonical closedness owner for relation graphs: closure fixed points are exactly closed
relations. -/
theorem closure_eq_iff_isClosed (A : SetRel U X) :
    cl(A) = A ↔ A.IsClosed := by
  simpa [SetRel.IsClosed, SetRel.closure] using
    (_root_.closure_eq_iff_isClosed : _root_.closure A = A ↔ _root_.IsClosed A)

@[simp] theorem closure_closure (A : SetRel U X) :
    cl(cl(A)) = cl(A) :=
  (SetRel.closure_eq_iff_isClosed (cl(A))).2 (SetRel.isClosed_closure A)

/-- Definition 39.0.5 textbook fixed-point phrasing: a relation is closed exactly when its graph
closure equals itself. -/
theorem isClosed_iff_closure_eq (A : SetRel U X) :
    A.IsClosed ↔ cl(A) = A := (SetRel.closure_eq_iff_isClosed A).symm

end Closure

namespace IsConvexProcess

section Closure

variable {R : Type w} [Semiring R] [PartialOrder R]
variable {U : Type u} [AddCommMonoid U] [SMul R U]
variable {X : Type v} [AddCommMonoid X] [SMul R X]
variable [TopologicalSpace (U × X)] [ContinuousAdd (U × X)] [ContinuousConstSMul R (U × X)]
variable {A : SetRel U X}

-- Proof sketch: `Set.IsConvexCone.closure` supplies the graph-side closure step on the canonical
-- set owner; the process proof only adds preservation of the origin.
/-- The closure of a convex process is again a convex process.
This is stated at the intrinsic graph level: the ambient topological `R`-module structure required
for closure is only on `U × X`. -/
theorem closure (hA : A.IsConvexProcess R) :
    (cl(A)).IsConvexProcess R := by
  exact ⟨hA.isConvexCone.closure, SetRel.subset_closure A hA.zero_mem⟩

end Closure

end IsConvexProcess

end SetRel
