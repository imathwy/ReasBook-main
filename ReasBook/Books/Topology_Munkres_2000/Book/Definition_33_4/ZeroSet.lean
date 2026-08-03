module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

public section

open Set

universe u

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X]

/-- A continuous map to the closed unit interval vanishes precisely on `A` when its
zero set is exactly `A`. -/
def VanishesPreciselyOn (f : C(X, Icc (0 : ℝ) 1)) (A : Set X) : Prop :=
  ∀ x, (f x : ℝ) = 0 ↔ x ∈ A

/-- A continuous map vanishes precisely on `A` exactly when its value is zero precisely
at the points of `A`. -/
theorem vanishesPreciselyOn_iff (f : C(X, Icc (0 : ℝ) 1)) (A : Set X) :
    f.VanishesPreciselyOn A ↔ ∀ x, (f x : ℝ) = 0 ↔ x ∈ A := by
  rfl

namespace VanishesPreciselyOn

/-- The zero set of a continuous map that vanishes precisely on `A` is `A`. -/
theorem zeroSet_eq {f : C(X, Icc (0 : ℝ) 1)} {A : Set X}
    (h : f.VanishesPreciselyOn A) : {x | (f x : ℝ) = 0} = A := by
  ext x
  exact h x

/-- Away from `A`, a continuous map that vanishes precisely on `A` is strictly positive. -/
theorem positive_iff_notMem {f : C(X, Icc (0 : ℝ) 1)} {A : Set X}
    (h : f.VanishesPreciselyOn A) (x : X) : 0 < (f x : ℝ) ↔ x ∉ A := by
  constructor
  · intro hx hmem
    exact (ne_of_gt hx) ((h x).2 hmem)
  · intro hnotMem
    have hne : (f x : ℝ) ≠ 0 := fun hx ↦ hnotMem ((h x).1 hx)
    exact lt_of_le_of_ne (f x).property.1 hne.symm

end VanishesPreciselyOn

end ContinuousMap
