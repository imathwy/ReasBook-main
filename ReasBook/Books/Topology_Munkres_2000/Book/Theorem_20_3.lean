module

import Mathlib.Analysis.Normed.Lp.PiLp

public section

/- Theorem 20.3: The topologies on `ℝⁿ` induced by the Euclidean metric and the square
metric are both the finite product topology. -/
#check fun n : ℕ ↦
  (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ), PiLp.homeomorph ⊤ (fun _ : Fin n ↦ ℝ))
