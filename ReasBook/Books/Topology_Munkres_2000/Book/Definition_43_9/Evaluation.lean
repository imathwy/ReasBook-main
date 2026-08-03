module

public import Mathlib.Topology.ContinuousMap.Basic

public section

universe u v

namespace ContinuousMap

variable (X : Type u) (Y : Type v)
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- The evaluation function on a point and a continuous map. -/
@[expose]
def evaluation : X × C(X, Y) → Y :=
  fun p ↦ p.2 p.1

/-- Evaluation at a pair `(x, f)` is application of `f` to `x`. -/
@[simp]
theorem evaluation_apply (x : X) (f : C(X, Y)) : evaluation X Y (x, f) = f x := rfl

/-- Point-first evaluation is mathlib's usual function-first evaluation after swapping inputs. -/
theorem evaluation_eq_comp_swap :
    evaluation X Y = (fun p : C(X, Y) × X ↦ p.1 p.2) ∘ Prod.swap := rfl

end ContinuousMap
