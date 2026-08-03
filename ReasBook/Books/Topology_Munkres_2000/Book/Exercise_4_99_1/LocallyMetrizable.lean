module

public import Topology_Munkres_2000.Book.Exercise_4_99_2.LocallyMetrizable
public import Topology_Munkres_2000.Book.Exercise_10_6
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Order.T5

public section

namespace OpenOmegaOne

/-- The open first-uncountable ordinal is locally metrizable. -/
instance instLocallyMetrizableSpace : LocallyMetrizableSpace OpenOmegaOne := by
  constructor
  intro x
  -- The initial segment ending just after `x` is an open neighborhood of `x`.
  refine ⟨Set.Iio (Order.succ x), Iio_mem_nhds (Order.lt_succ x), ?_⟩
  -- This initial segment is a countable order-topological space, hence metrizable.
  infer_instance

end OpenOmegaOne
