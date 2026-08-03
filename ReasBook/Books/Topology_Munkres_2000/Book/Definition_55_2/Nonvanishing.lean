module

public import Mathlib.Topology.ContinuousMap.Basic

public section

namespace ContinuousMap

/-- A continuous map is nonvanishing when none of its values is zero. -/
@[expose]
def IsNonvanishing {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Zero Y]
    (f : C(X, Y)) : Prop :=
  ∀ x, f x ≠ 0

/-- Nonvanishing means that every value of the continuous map is nonzero. -/
theorem isNonvanishing_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Zero Y]
    (f : C(X, Y)) : f.IsNonvanishing ↔ ∀ x, f x ≠ 0 :=
  Iff.rfl

/-- A nonvanishing continuous map, regarded as a map into the nonzero subtype. -/
@[expose]
def toNonzero {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Zero Y]
    (f : C(X, Y)) (hf : f.IsNonvanishing) : C(X, {y : Y // y ≠ 0}) :=
  ⟨fun x ↦ ⟨f x, hf x⟩, f.continuous.subtype_mk _⟩

/-- Restricting a nonvanishing continuous map to the nonzero subtype preserves its values. -/
theorem toNonzero_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Zero Y]
    (f : C(X, Y)) (hf : f.IsNonvanishing) (x : X) : (f.toNonzero hf x : Y) = f x :=
  rfl

end ContinuousMap
