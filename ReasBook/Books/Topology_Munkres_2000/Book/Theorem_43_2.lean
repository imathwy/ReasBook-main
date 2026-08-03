module

import Mathlib.Analysis.InnerProductSpace.PiL2

/- Theorem 43.2 (1): `EuclideanSpace ℝ (Fin k)` is complete for the Euclidean
metric `d`. -/
#check fun k : ℕ ↦ (inferInstance : CompleteSpace (EuclideanSpace ℝ (Fin k)))

/- Theorem 43.2 (2): `Fin k → ℝ` is complete for the square metric `ρ`, modeled
by the canonical finite Pi-space metric. -/
#check fun k : ℕ ↦ (inferInstance : CompleteSpace (Fin k → ℝ))
