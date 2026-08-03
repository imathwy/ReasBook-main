module

public import Mathlib.Topology.Algebra.Module.LocallyConvex

public section

/-- Exercise 24.10: Every open connected subset of the real plane `ℝ × ℝ` is path connected. -/
theorem openConnectedRealPlane_isPathConnected {U : Set (ℝ × ℝ)}
    (hU_open : IsOpen U) (hU_connected : IsConnected U) : IsPathConnected U :=
  (hU_open.isConnected_iff_isPathConnected).mp hU_connected
