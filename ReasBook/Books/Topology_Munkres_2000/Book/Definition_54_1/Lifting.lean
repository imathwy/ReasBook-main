module

public import Mathlib.Topology.ContinuousMap.Basic

public section

universe u v w z

namespace ContinuousMap

variable {X : Type u} {E : Type v} {B : Type w} {Y : Type z}
variable [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Y]

/-- A continuous map `lift : C(X, E)` lifts `f : C(X, B)` through `p : E → B` when
`p ∘ lift = f`. -/
def IsLift (p : E → B) (f : C(X, B)) (lift : C(X, E)) : Prop :=
  p ∘ lift = f

/-- The defining equation for a lifting through a map. -/
theorem isLift_iff {p : E → B} {f : C(X, B)} {lift : C(X, E)} :
    IsLift p f lift ↔ p ∘ lift = f := Iff.rfl

/-- A lifting equation holds pointwise. -/
theorem IsLift.apply {p : E → B} {f : C(X, B)} {lift : C(X, E)}
    (h : IsLift p f lift) (x : X) : p (lift x) = f x := congrFun h x

/-- Precomposing a lifting with a continuous map gives another lifting. -/
theorem IsLift.comp {p : E → B} {f : C(X, B)} {lift : C(X, E)}
    (h : IsLift p f lift) (g : C(Y, X)) : IsLift p (f.comp g) (lift.comp g) := by
  ext y
  exact h.apply (g y)

end ContinuousMap
