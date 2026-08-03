module

public import Mathlib.Geometry.Manifold.Instances.Real

public section

universe u

namespace Surface

/-- A finite family of pairwise disjoint disk charts chosen in a topological space. -/
structure HoleCharts (X : Type u) [TopologicalSpace X] (k : ℕ) where
  charts : Fin k → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) X
  source_eq : ∀ i, (charts i).source = Metric.ball 0 1
  pairwiseDisjoint_target :
    Set.univ.PairwiseDisjoint (fun i ↦ (charts i).target)

/-- A family of hole charts acts as its underlying indexed family of charts. -/
instance instCoeFunHoleCharts {X : Type u} [TopologicalSpace X] {k : ℕ} :
    CoeFun (HoleCharts X k)
      (fun _ ↦ Fin k → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) X) where
  coe charts := charts.charts

/-- The union of the concentric radius-`1 / 2` disks deleted from the chart targets. -/
def removedDisks {X : Type u} [TopologicalSpace X] {k : ℕ}
    (charts : HoleCharts X k) : Set X :=
  ⋃ i, charts i '' Metric.ball 0 (1 / 2 : ℝ)

/-- Membership in the deleted subset is membership in one chosen radius-`1 / 2` disk image. -/
theorem mem_removedDisks {X : Type u} [TopologicalSpace X] {k : ℕ}
    (charts : HoleCharts X k) (x : X) :
    x ∈ removedDisks charts ↔
      ∃ i : Fin k, x ∈ charts i '' Metric.ball 0 (1 / 2 : ℝ) := by
  simp [removedDisks]

/-- The subspace remaining after deleting the chosen concentric radius-`1 / 2` disks. -/
abbrev withHoles {X : Type u} [TopologicalSpace X] {k : ℕ}
    (charts : HoleCharts X k) : Type u :=
  {x : X // x ∉ removedDisks charts}

/-- A point avoids the deleted subset exactly when it avoids every chosen disk image. -/
theorem mem_compl_removedDisks {X : Type u} [TopologicalSpace X] {k : ℕ}
    (charts : HoleCharts X k) (x : X) :
    x ∈ (removedDisks charts)ᶜ ↔
      ∀ i : Fin k, x ∉ charts i '' Metric.ball 0 (1 / 2 : ℝ) := by
  simp [mem_removedDisks]

end Surface
