module

public import Topology_Munkres_2000.Book.Example_24_7.SineCurve

public section

namespace TopologistsSineCurve

/-- The oscillating graph `curve` is connected. -/
theorem curve_isConnected : IsConnected curve := by
  -- The graph is the continuous image of the connected interval `(0, 1]`.
  rw [curve]
  apply (isConnected_Ioc zero_lt_one).image
  intro x hx
  have hx_ne : x ≠ 0 := ne_of_gt hx.1
  have hrecip : ContinuousAt (fun y : ℝ ↦ 1 / y) x :=
    continuousAt_const.div continuousAt_id hx_ne
  have hsin : ContinuousAt (fun y : ℝ ↦ Real.sin (1 / y)) x :=
    Real.continuous_sin.continuousAt.comp hrecip
  exact (continuousAt_id.prodMk hsin).continuousWithinAt

/-- The closure `carrier` of the oscillating graph is connected. -/
theorem carrier_isConnected : IsConnected carrier := curve_isConnected.closure

/-- The topologist's sine curve is connected as a topological space. -/
instance instConnectedSpace : ConnectedSpace Space :=
  Subtype.connectedSpace carrier_isConnected

end TopologistsSineCurve
