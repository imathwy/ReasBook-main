module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/- Example 17.2: The nonnegative quadrant in `ℝ × ℝ` is closed. -/
#check (isClosed_Ici.prod isClosed_Ici : IsClosed (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)))
