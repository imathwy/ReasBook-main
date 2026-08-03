module

public import Mathlib.Topology.MetricSpace.Lipschitz

public section

universe u

/-- A self-map of a metric space is shrinking if it strictly decreases the distance between
every pair of distinct points. -/
def IsShrinkingMap {X : Type u} [MetricSpace X] (f : X → X) : Prop :=
  ∀ x y, x ≠ y → dist (f x) (f y) < dist x y

namespace IsShrinkingMap

/-- A shrinking map strictly decreases the distance between distinct points. -/
theorem dist_lt {X : Type u} [MetricSpace X] {f : X → X} (hf : IsShrinkingMap f)
    (x y : X) (hxy : x ≠ y) : dist (f x) (f y) < dist x y :=
  hf x y hxy

/-- A shrinking map does not increase distances. -/
theorem dist_le {X : Type u} [MetricSpace X] {f : X → X} (hf : IsShrinkingMap f)
    (x y : X) : dist (f x) (f y) ≤ dist x y := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  · exact (hf.dist_lt x y hxy).le

/-- A shrinking map is Lipschitz with constant one. -/
theorem lipschitzWith_one {X : Type u} [MetricSpace X] {f : X → X} (hf : IsShrinkingMap f) :
    LipschitzWith 1 f :=
  lipschitzWith_iff_dist_le_mul.2 fun x y ↦ by simpa using hf.dist_le x y

/-- A shrinking map is continuous. -/
theorem continuous {X : Type u} [MetricSpace X] {f : X → X} (hf : IsShrinkingMap f) :
    Continuous f :=
  hf.lipschitzWith_one.continuous

end IsShrinkingMap

/-- A map is shrinking exactly when it strictly decreases distances between distinct points. -/
theorem isShrinkingMap_iff {X : Type u} [MetricSpace X] (f : X → X) :
    IsShrinkingMap f ↔ ∀ x y, x ≠ y → dist (f x) (f y) < dist x y :=
  Iff.rfl
