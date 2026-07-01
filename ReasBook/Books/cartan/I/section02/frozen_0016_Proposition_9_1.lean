import Mathlib
import cartan.I.section02.«frozen_0004_Definition_I_2_extra_3»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PowerSeries
open PowerSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

-- Proof sketch: recover the centered inverse data for `S` from `hT0` and `hST`, identify `T`
-- with the canonical substitution inverse using the section 1 uniqueness theorem, and then apply
-- the analytic inverse-radius theorem to that canonical inverse.
/-- Proposition 9.1: if a scalar power series `S` has nonzero radius of convergence and `T` is a
compositional right inverse with `T(0) = 0`, then `T` also has nonzero radius of convergence. -/
theorem scalar_series_inverse_radius_ne_zero
    (S T : 𝕜⟦X⟧)
    (hT0 : T.constantCoeff = 0)
    (hST : S.subst T = X)
    (hS : S.radius ≠ 0) :
    T.radius ≠ 0 := by
  sorry
