module

public import Topology_Munkres_2000.Book.Definition_43_4.BoundedFunction

public section

/- Definition 43.4: The bounded functions `X → Y` into a metric space carry the sup metric,
whose distance is the supremum of the pointwise distances. -/
namespace BoundedFunction

universe u v

variable {X : Type u}

/-- Definition 43.4: Bounded functions into a metric space form a metric space under the sup
metric. -/
noncomputable instance instMetricSpace {Y : Type v} [MetricSpace Y] :
    MetricSpace (BoundedFunction X Y) := MetricSpace.mk fun {f g} hfg ↦ by
    -- Zero sup distance forces the functions to agree at every point.
    apply ext
    intro x
    apply eq_of_dist_eq_zero
    apply le_antisymm
    · calc
        dist (f x) (g x) ≤ sSup (Set.range (fun x ↦ dist (f x) (g x))) :=
          le_csSup (distRange_bddAbove f g) (Set.mem_range_self x)
        _ = dist f g := (dist_eq_sSup f g).symm
        _ = 0 := hfg
    · exact dist_nonneg


end BoundedFunction
