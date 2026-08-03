module

public import Topology_Munkres_2000.Book.Theorem_57_5.JordanMeasurable

import Topology_Munkres_2000.Book.Exercise_57_6

public section

open MeasureTheory

/-- Helper for Theorem 57.5: intersecting with any set preserves measure when a
set is replaced by its interior and its frontier has measure zero. -/
private lemma measure_inter_interior_of_null_frontier
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : Measure α} {s t : Set α} (h : μ (frontier s) = 0) :
    μ (s ∩ t) = μ (interior s ∩ t) := by
  -- Intersect the a.e. equality between the set and its interior with `t`.
  exact measure_congr
    (ae_eq_set_inter (interior_ae_eq_of_null_frontier h).symm (ae_eq_refl t))

/-- Theorem 57.5. Any two Jordan-measurable subsets of the Euclidean plane
admit a single affine line that bisects the area of both sets. -/
theorem existsLineBisectsJordanMeasurable
    (A₁ A₂ : Set (EuclideanSpace ℝ (Fin 2)))
    (hA₁ : A₁.IsJordanMeasurable) (hA₂ : A₂.IsJordanMeasurable) :
    ∃ (v : EuclideanSpace ℝ (Fin 2)) (c : ℝ),
      ‖v‖ = 1 ∧
        volume (A₁ ∩ {x | inner ℝ v x ≤ c}) = volume A₁ / 2 ∧
        volume (A₂ ∩ {x | inner ℝ v x ≤ c}) = volume A₂ / 2 := by
  -- The interiors are canonical measurable representatives of the Jordan sets.
  have hA₁_measurable : MeasurableSet (interior A₁) := isOpen_interior.measurableSet
  have hA₂_measurable : MeasurableSet (interior A₂) := isOpen_interior.measurableSet
  have hA₁_bounded : Bornology.IsBounded (interior A₁) :=
    hA₁.isBounded.subset interior_subset
  have hA₂_bounded : Bornology.IsBounded (interior A₂) :=
    hA₂.isBounded.subset interior_subset
  -- Apply the measurable-set bisection theorem without unfolding its construction.
  obtain ⟨v, c, hv, hbisect₁, hbisect₂⟩ :=
    existsLineBisectsBoth (interior A₁) (interior A₂)
      hA₁_measurable hA₂_measurable hA₁_bounded hA₂_bounded
  use v, c
  constructor
  · exact hv
  constructor
  · -- Transfer both the cut and total volumes from the interior back to `A₁`.
    calc
      volume (A₁ ∩ {x | inner ℝ v x ≤ c}) =
          volume (interior A₁ ∩ {x | inner ℝ v x ≤ c}) :=
        measure_inter_interior_of_null_frontier hA₁.null_frontier
      _ = volume (interior A₁) / 2 := hbisect₁
      _ = volume A₁ / 2 :=
        congrArg (fun m : ENNReal ↦ m / 2)
          (measure_interior_of_null_frontier hA₁.null_frontier)
  · -- The same null-frontier transfer returns the bisection equality for `A₂`.
    calc
      volume (A₂ ∩ {x | inner ℝ v x ≤ c}) =
          volume (interior A₂ ∩ {x | inner ℝ v x ≤ c}) :=
        measure_inter_interior_of_null_frontier hA₂.null_frontier
      _ = volume (interior A₂) / 2 := hbisect₂
      _ = volume A₂ / 2 :=
        congrArg (fun m : ENNReal ↦ m / 2)
          (measure_interior_of_null_frontier hA₂.null_frontier)
