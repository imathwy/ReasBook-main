module

import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Instances.Real.Lemmas

open Set

/- Example 18.9 (parametrized curves). A plane-valued map on a closed interval is
continuous if and only if both coordinate functions are continuous. -/
#check (continuous_prodMk :
  ∀ {a b : ℝ} {x y : Icc a b → ℝ},
    Continuous (fun t ↦ (x t, y t)) ↔ Continuous x ∧ Continuous y)

/- Example 18.9 (plane vector fields). A plane vector field is continuous if and only if
both of its scalar component functions are continuous. -/
#check (continuous_prodMk :
  ∀ {P Q : ℝ × ℝ → ℝ},
    Continuous (fun p ↦ (P p, Q p)) ↔ Continuous P ∧ Continuous Q)
