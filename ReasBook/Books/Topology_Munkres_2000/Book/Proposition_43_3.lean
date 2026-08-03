module

public import Topology_Munkres_2000.Book.Proposition_43_3.UniformMetric

public section

universe u v

namespace BoundedFunction

/-- Proposition 43.3. On bounded functions, the uniform distance associated to the standard
bounded metric on `Y` is the standard bounded distance associated to the sup metric. -/
theorem uniformMetric_dist_eq_min_dist {X : Type u} {Y : Type v} [MetricSpace Y]
    (f g : BoundedFunction X Y) :
    (uniformMetric X Y).dist f g = min (dist f g) 1 := by
  -- Express both function-space distances as suprema of their pointwise distances.
  rw [uniformMetric_dist, dist_eq_iSup]
  rcases isEmpty_or_nonempty X with hX | hX
  · letI : IsEmpty X := hX
    -- On an empty domain, both indexed suprema are zero.
    simp only [Real.iSup_of_isEmpty, min_eq_left zero_le_one]
  · letI : Nonempty X := hX
    -- Truncation at one is monotone and continuous, so it commutes with the bounded supremum.
    exact (Monotone.map_ciSup_of_continuousAt
      (f := fun r : ℝ ↦ min r 1) (g := fun x ↦ dist (f x) (g x))
      (continuous_id.min continuous_const).continuousAt
      (monotone_id.min monotone_const)
      (distRange_bddAbove f g)).symm

end BoundedFunction
