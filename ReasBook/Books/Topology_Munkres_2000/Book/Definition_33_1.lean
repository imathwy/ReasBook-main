module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

public section

open Set

universe u

/-- Definition 33.1. Two subsets are functionally separated when a continuous map to the closed
unit interval is zero on the first set and one on the second. -/
def FunctionallySeparated {X : Type u} [TopologicalSpace X] (A B : Set X) : Prop :=
  ∃ f : C(X, Icc (0 : ℝ) 1),
    EqOn f (fun _ ↦ (⟨0, le_rfl, zero_le_one⟩ : Icc (0 : ℝ) 1)) A ∧
      EqOn f (fun _ ↦ (⟨1, zero_le_one, le_rfl⟩ : Icc (0 : ℝ) 1)) B

end
