module

public import Mathlib.Topology.MetricSpace.Closeds

public section

open Set

universe u

namespace TopologicalSpace

/-- The type of nonempty bounded closed subsets of a topological bornological space. -/
abbrev NonemptyClosedBounded (X : Type u) [TopologicalSpace X] [Bornology X] :=
  { A : Closeds X // (A : Set X).Nonempty ∧ Bornology.IsBounded (A : Set X) }

namespace NonemptyClosedBounded

variable {X : Type u} [TopologicalSpace X] [Bornology X]

/-- The underlying set of a bundled nonempty closed bounded set is nonempty. -/
protected theorem nonempty (A : NonemptyClosedBounded X) : (A : Set X).Nonempty :=
  A.property.1

/-- The underlying set of a bundled nonempty closed bounded set is closed. -/
protected theorem isClosed (A : NonemptyClosedBounded X) : IsClosed (A : Set X) :=
  A.val.isClosed

/-- The underlying set of a bundled nonempty closed bounded set is bounded. -/
protected theorem isBounded (A : NonemptyClosedBounded X) :
    Bornology.IsBounded (A : Set X) :=
  A.property.2

/-- A bundled nonempty closed bounded set satisfies its three defining conditions. -/
theorem spec (A : NonemptyClosedBounded X) :
    (A : Set X).Nonempty ∧ IsClosed (A : Set X) ∧ Bornology.IsBounded (A : Set X) :=
  ⟨A.nonempty, A.isClosed, A.isBounded⟩

/-- Bundled nonempty closed bounded sets are equal when their underlying sets are equal. -/
@[ext]
theorem ext {A B : NonemptyClosedBounded X} (h : (A : Set X) = (B : Set X)) : A = B := by
  apply Subtype.ext
  exact Closeds.ext h

variable [T1Space X]

/-- The singleton containing `x` as a nonempty closed bounded set. -/
def singleton (x : X) : NonemptyClosedBounded X where
  val := ⟨{x}, isClosed_singleton⟩
  property := ⟨Set.singleton_nonempty x, Bornology.isBounded_singleton⟩


end NonemptyClosedBounded

end TopologicalSpace
