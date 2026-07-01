import cartan.IV.section13.«0007_Proposition_3_I»
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` is unavailable in this session; this item is matched
-- against the project owner `MvPowerSeries.coeffXY` and the canonical owner `PowerSeries`.

universe u

namespace MvPowerSeries

open scoped MvPowerSeries PowerSeries

/-- Definition VII.1-extra-1 (1): a majorant series of a two-variable formal power series is a
two-variable formal power series with nonnegative real coefficients whose coefficient of `X^p Y^q`
dominates the norm of the corresponding coefficient of the given series for every `p, q ≥ 0`. -/
class IsMajorantSeries {𝕜 : Type u} [Norm 𝕜] (f : 𝕜⟦X,Y⟧) (F : NNReal⟦X,Y⟧) : Prop where
  coeff_le (p q : ℕ) : ‖coeffXY f p q‖ ≤ ((coeffXY F p q : NNReal) : ℝ)

end MvPowerSeries

namespace PowerSeries

/-- Definition VII.1-extra-1 (2): a majorant series of a one-variable formal series
`∑_{n ≥ 1} aₙ Xⁿ` is a one-variable formal power series with nonnegative real coefficients,
vanishing constant term, whose positive-degree coefficients dominate the norms of the
corresponding coefficients of the given series; the source series itself also has vanishing
constant term. -/
class IsMajorantSeries {𝕜 : Type u} [Semiring 𝕜] [Norm 𝕜] (φ : 𝕜⟦X⟧) (Φ : NNReal⟦X⟧) : Prop where
  source_constantCoeff_eq_zero : constantCoeff φ = 0
  constantCoeff_eq_zero : constantCoeff Φ = 0
  coeff_le (n : ℕ) : ‖coeff (n + 1) φ‖ ≤ ((coeff (n + 1) Φ : NNReal) : ℝ)

@[simp] theorem IsMajorantSeries.source_coeff_zero {𝕜 : Type u} [Semiring 𝕜] [Norm 𝕜]
    {φ : 𝕜⟦X⟧} {Φ : NNReal⟦X⟧} (h : IsMajorantSeries φ Φ) : coeff 0 φ = 0 := by
  simpa [coeff_zero_eq_constantCoeff_apply] using h.source_constantCoeff_eq_zero

@[simp] theorem IsMajorantSeries.coeff_zero {𝕜 : Type u} [Semiring 𝕜] [Norm 𝕜]
    {φ : 𝕜⟦X⟧} {Φ : NNReal⟦X⟧} (h : IsMajorantSeries φ Φ) : coeff 0 Φ = 0 := by
  simpa [coeff_zero_eq_constantCoeff_apply] using h.constantCoeff_eq_zero

end PowerSeries
