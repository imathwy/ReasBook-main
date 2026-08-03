module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Defs

universe u

public section

/-- Helper for Definition 20.3: all positive-radius balls containing `a` form a basis
of `nhds a`. -/
lemma Metric.nhds_basis_all_balls {X : Type u} [MetricSpace X] (a : X) :
    (nhds a).HasBasis
      (fun U : Set X ↦ (∃ x : X, ∃ ε > 0, U = Metric.ball x ε) ∧ a ∈ U) id := by
  -- Reindex the canonical basis of balls centered at `a` by all balls containing `a`.
  refine Metric.nhds_basis_ball.to_hasBasis ?_ ?_
  · intro ε hε
    refine ⟨Metric.ball a ε, ?_, fun _ hz ↦ hz⟩
    exact ⟨⟨a, ε, hε, rfl⟩, Metric.mem_ball_self hε⟩
  · intro U hU
    rcases hU with ⟨⟨x, ε, hε, rfl⟩, ha⟩
    -- A ball containing `a` contains a smaller positive-radius ball centered at `a`.
    rcases Metric.exists_ball_subset_ball ha with ⟨δ, hδ, hsubset⟩
    exact ⟨δ, hδ, hsubset⟩

/-- Definition 20.3: The positive-radius balls of a metric space form a basis for its
induced topology. -/
theorem Metric.isTopologicalBasis_ball {X : Type u} [MetricSpace X] :
    TopologicalSpace.IsTopologicalBasis
      {U : Set X | ∃ x : X, ∃ ε > 0, U = Metric.ball x ε} := by
  -- Assemble the global basis from the pointwise neighborhood bases above.
  exact TopologicalSpace.IsTopologicalBasis.of_hasBasis_nhds Metric.nhds_basis_all_balls

/- Equivalently, positive-radius balls centered at `x` form a basis of `nhds x`. -/
#check fun {X : Type u} [MetricSpace X] (x : X) ↦
  (Metric.nhds_basis_ball : (nhds x).HasBasis (fun ε : ℝ ↦ 0 < ε) (Metric.ball x))
