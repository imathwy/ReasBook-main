module

public import Topology_Munkres_2000.Book.Definition_54_1.Lifting
public import Mathlib.Topology.Homotopy.Path

public section

universe u v

namespace ContinuousMap.IsLift

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Concatenating lifts of composable paths gives a lift of their concatenation. -/
theorem transPath {p : E → B} {e₀ e₁ e₂ : E} {b₀ b₁ b₂ : B}
    {α : Path b₀ b₁} {β : Path b₁ b₂} {liftα : Path e₀ e₁} {liftβ : Path e₁ e₂}
    (hα : ContinuousMap.IsLift p α.toContinuousMap liftα.toContinuousMap)
    (hβ : ContinuousMap.IsLift p β.toContinuousMap liftβ.toContinuousMap) :
    ContinuousMap.IsLift p (α.trans β).toContinuousMap
      (liftα.trans liftβ).toContinuousMap := by
  rw [ContinuousMap.isLift_iff] at hα hβ ⊢
  funext t
  change p ((liftα.trans liftβ) t) = (α.trans β) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact congrFun hα _
  · exact congrFun hβ _

end ContinuousMap.IsLift
