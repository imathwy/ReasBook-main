module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Order.IntermediateValue

public section

/- Corollary 24.2: The real line ℝ is connected, as are its standard bounded intervals
and one-sided rays, subject to the usual nonemptiness conditions. -/
#check (inferInstance : ConnectedSpace ℝ)
#check (fun {a b : ℝ} (h : a ≤ b) ↦ isConnected_Icc h)
#check (fun {a b : ℝ} (h : a < b) ↦ isConnected_Ioc h)
#check (fun {a b : ℝ} (h : a < b) ↦ isConnected_Ico h)
#check (fun {a b : ℝ} (h : a < b) ↦ isConnected_Ioo h)
#check (fun (a : ℝ) ↦ (isConnected_Ici : IsConnected (Set.Ici a)))
#check (fun (a : ℝ) ↦ (isConnected_Iic : IsConnected (Set.Iic a)))
#check (fun (a : ℝ) ↦ (isConnected_Ioi : IsConnected (Set.Ioi a)))
#check (fun (a : ℝ) ↦ (isConnected_Iio : IsConnected (Set.Iio a)))
