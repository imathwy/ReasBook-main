import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open scoped ENNReal PowerSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

namespace PowerSeries

/-- Definition I.2-extra-3: the radius of convergence of a scalar formal power series, viewed
through the canonical scalar formal multilinear series attached to its coefficients. -/
noncomputable abbrev radius (S : 𝕜⟦X⟧) : ℝ≥0∞ :=
  (ofScalars 𝕜 fun n ↦ coeff n S).radius

/-- Definition I.2-extra-3: the analytic sum attached to a scalar formal power series, viewed
through the canonical scalar formal multilinear series attached to its coefficients. -/
noncomputable abbrev sum (S : 𝕜⟦X⟧) : 𝕜 → 𝕜 :=
  ofScalarsSum fun n ↦ coeff n S

end PowerSeries
