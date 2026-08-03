module

public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Thickening

public section

universe u

namespace IsClosed

/-- Example 40.2: A closed subset of a pseudometric space is the intersection of its open
metric thickenings of radii `1 / (n + 1)` for `n : ℕ`. -/
theorem eq_iInter_thickening_inv_nat {X : Type u} [PseudoMetricSpace X] {A : Set X}
    (hA : IsClosed A) : A = ⋂ n : ℕ, Metric.thickening ((n + 1 : ℝ)⁻¹) A := by
  -- The inverse-successor radii are all strictly positive.
  have hRadiiPositive :
      Set.range (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹)) ⊆ Set.Ioi 0 := by
    rintro δ ⟨n, rfl⟩
    simp only [Set.mem_Ioi]
    positivity
  -- The same radii occur arbitrarily close to zero.
  have hRadiiAccumulate : ∀ ε : ℝ, 0 < ε →
      (Set.range (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹)) ∩ Set.Ioc 0 ε).Nonempty := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨((n + 1 : ℝ)⁻¹), ⟨⟨n, rfl⟩, ?_⟩⟩
    exact ⟨hRadiiPositive ⟨n, rfl⟩, by simpa only [one_div] using hn.le⟩
  -- Closedness identifies `A` with its closure, to which the thickening formula applies.
  calc
    A = closure A := hA.closure_eq.symm
    _ = ⋂ δ ∈ Set.range (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹)), Metric.thickening δ A :=
      Metric.closure_eq_iInter_thickening' A _ hRadiiPositive hRadiiAccumulate
    _ = ⋂ n : ℕ, Metric.thickening ((n + 1 : ℝ)⁻¹) A := Set.biInter_range

end IsClosed
