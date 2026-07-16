import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap21.Theorem_21_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

noncomputable section

local instance : MeasurableSpace BrownianPathSpace := borel _

local instance : BorelSpace BrownianPathSpace := ⟨rfl⟩

/-- The supremum of a continuous real path on `[0,1]`. -/
noncomputable def brownianPathSupOnUnitInterval (ω : BrownianPathSpace) : ℝ :=
  sSup (Set.range (ω.restrict (Set.Icc (0 : NNReal) 1)))

-- Proof sketch: the time `0` belongs to `[0,1]`, so a path started at `0` contributes the value
-- `0` to the set over which the supremum is taken.
/-- If a path starts at `0`, then its supremum on `[0,1]` is nonnegative. -/
theorem brownianPathSupOnUnitInterval_nonneg {ω : BrownianPathSpace} (hω : ω 0 = 0) :
    0 ≤ brownianPathSupOnUnitInterval ω := sorry

/-- The unit-interval supremum is the supremum of the path values on `[0,1]`. -/
theorem brownianPathSupOnUnitInterval_spec (ω : BrownianPathSpace) :
    brownianPathSupOnUnitInterval ω =
      sSup (Set.range fun t : Set.Icc (0 : NNReal) 1 ↦ ω t) :=
  rfl

-- Proof sketch: if two continuous paths are uniformly close on `[0,1]`, then their suprema on
-- `[0,1]` differ by at most the same uniform error. This yields continuity for the path functional.
/-- The unit-interval supremum is continuous on the continuous path space. -/
theorem continuous_brownianPathSupOnUnitInterval :
    Continuous brownianPathSupOnUnitInterval := sorry

-- Proof sketch: apply `Continuous.measurable` to the continuity statement for the supremum map.
/-- Corollary 21.32: the map sending a continuous path, hence in particular a Brownian path, to
its supremum on `[0,1]` is Borel measurable. -/
theorem measurable_brownianPathSupOnUnitInterval :
    Measurable brownianPathSupOnUnitInterval := sorry
