module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import Topology_Munkres_2000.Book.Exercise_57_6

public section

open MeasureTheory

namespace Set

/-- A planar polygonal region is a regular filled region admitting a finite
triangulation by straight triangles. -/
def IsPolygonalRegion (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ triangles : Finset (Fin 3 → EuclideanSpace ℝ (Fin 2)),
    A = ⋃ triangle ∈ triangles, convexHull ℝ (range triangle) ∧
      IsConnected (interior A) ∧ closure (interior A) = A ∧ IsConnected Aᶜ

/-- The defining finite triangulation and regularity conditions for a polygonal region. -/
theorem isPolygonalRegion_iff (A : Set (EuclideanSpace ℝ (Fin 2))) :
    A.IsPolygonalRegion ↔
      ∃ triangles : Finset (Fin 3 → EuclideanSpace ℝ (Fin 2)),
        A = ⋃ triangle ∈ triangles, convexHull ℝ (range triangle) ∧
          IsConnected (interior A) ∧ closure (interior A) = A ∧ IsConnected Aᶜ :=
  Iff.rfl

/-- A polygonal region exposes its finite triangulation and regularity conditions. -/
theorem IsPolygonalRegion.spec {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : A.IsPolygonalRegion) :
    ∃ triangles : Finset (Fin 3 → EuclideanSpace ℝ (Fin 2)),
      A = ⋃ triangle ∈ triangles, convexHull ℝ (range triangle) ∧
        IsConnected (interior A) ∧ closure (interior A) = A ∧ IsConnected Aᶜ :=
  hA

/-- A planar polygonal region is Lebesgue measurable. -/
theorem IsPolygonalRegion.measurableSet {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : A.IsPolygonalRegion) : MeasurableSet A := by
  obtain ⟨triangles, rfl, _⟩ := hA
  exact triangles.measurableSet_biUnion fun triangle _ ↦
    (finite_range triangle).isCompact_convexHull ℝ |>.measurableSet

/-- A planar polygonal region is bounded. -/
theorem IsPolygonalRegion.isBounded {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : A.IsPolygonalRegion) : Bornology.IsBounded A := by
  obtain ⟨triangles, rfl, _⟩ := hA
  rw [Bornology.isBounded_biUnion_finset]
  exact fun triangle _ ↦ isBounded_convexHull.2 (finite_range triangle).isBounded

end Set

/-- Theorem 57.4 (The bisection theorem). Given two bounded polygonal regions in
`EuclideanSpace ℝ (Fin 2)`, there is a line that bisects the area of each region.
The witnesses `v` and `c` describe the line `{x | inner ℝ v x = c}`. -/
theorem existsLineBisectsPolygonalRegions
    (A₁ A₂ : Set (EuclideanSpace ℝ (Fin 2)))
    (hA₁ : A₁.IsPolygonalRegion) (hA₂ : A₂.IsPolygonalRegion) :
    ∃ (v : EuclideanSpace ℝ (Fin 2)) (c : ℝ),
      ‖v‖ = 1 ∧
        volume (A₁ ∩ {x | inner ℝ v x ≤ c}) = volume A₁ / 2 ∧
        volume (A₂ ∩ {x | inner ℝ v x ≤ c}) = volume A₂ / 2 :=
  existsLineBisectsBoth A₁ A₂ hA₁.measurableSet hA₂.measurableSet hA₁.isBounded hA₂.isBounded
