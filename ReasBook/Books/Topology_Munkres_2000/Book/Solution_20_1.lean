module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public section

namespace Metric

/-- A ball whose radius is the minimum of two radii lies in the intersection
whenever the two original balls lie in the respective sets. -/
theorem ball_min_subset_inter {X : Type u} [PseudoMetricSpace X]
    {B₁ B₂ : Set X} {y : X} {δ₁ δ₂ : ℝ}
    (h₁ : ball y δ₁ ⊆ B₁) (h₂ : ball y δ₂ ⊆ B₂) :
    ball y (min δ₁ δ₂) ⊆ B₁ ∩ B₂ := by
  intro z hz
  exact ⟨h₁ (ball_subset_ball (min_le_left δ₁ δ₂) hz),
    h₂ (ball_subset_ball (min_le_right δ₁ δ₂) hz)⟩

/-- Solution 20.1: If `y` belongs to two metric balls, then a positive-radius
ball centered at `y` is contained in their intersection. -/
theorem exists_ball_subset_inter {X : Type u} [PseudoMetricSpace X]
    {x₁ x₂ y : X} {ε₁ ε₂ : ℝ}
    (hy : y ∈ ball x₁ ε₁ ∩ ball x₂ ε₂) :
    ∃ δ > 0, ball y δ ⊆ ball x₁ ε₁ ∩ ball x₂ ε₂ := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_ball_subset_ball hy.1
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_ball_subset_ball hy.2
  exact ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ball_min_subset_inter h₁ h₂⟩

end Metric
