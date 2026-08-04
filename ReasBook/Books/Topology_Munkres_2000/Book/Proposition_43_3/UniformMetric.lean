module

public import Topology_Munkres_2000.Book.Definition_20_9
public import Topology_Munkres_2000.Book.Definition_43_4.BoundedFunction

public section

universe u v

namespace BoundedFunction

/-- The uniform metric on bounded functions, obtained by restricting
`MetricSpace.uniformFun` along the coercion to the underlying function. -/
@[implicit_reducible]
noncomputable def uniformMetric (X : Type u) (Y : Type v) [m : MetricSpace Y] :
    MetricSpace (BoundedFunction X Y) :=
  MetricSpace.induced (fun f ↦ ⇑f) DFunLike.coe_injective (m.uniformFun X)

variable {X : Type u} {Y : Type v} [MetricSpace Y]

/-- Uniform distance between bounded functions is the supremum of their pointwise standard
bounded distances. -/
theorem uniformMetric_dist (f g : BoundedFunction X Y) :
    (uniformMetric X Y).dist f g = ⨆ x, min (dist (f x) (g x)) 1 := by
  -- The induced distance is the uniform distance of the underlying functions.
  exact MetricSpace.uniformFun_dist (inferInstance : MetricSpace Y) X f g


end BoundedFunction
