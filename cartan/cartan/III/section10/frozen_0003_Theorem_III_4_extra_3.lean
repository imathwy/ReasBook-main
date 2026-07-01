import Mathlib
import cartan.III.section10.«0002_Definition_III_4_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: choose intermediate circles inside the annulus, define the coefficients by
-- Cauchy integrals on those circles, expand the Cauchy kernels into positive and negative power
-- series on each closed subannulus, and use normal convergence to identify the resulting Laurent
-- series with `f`.
/-- Owner form: a function analytic on the annulus `ρ₂ < |z| < ρ₁` has a Laurent expansion there. -/
theorem AnalyticOnNhd.hasLaurentExpansionOnAnnulus
    {ρ₂ ρ₁ : ENNReal} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexOpenAnnulus ρ₂ ρ₁)) :
    HasLaurentExpansionOnAnnulus f ρ₂ ρ₁ := sorry

/- Theorem III.4-extra-3: every holomorphic function on the annulus `ρ₂ < |z| < ρ₁` admits a
Laurent expansion whose sum agrees with the function on that annulus. This is exactly the owner
theorem `AnalyticOnNhd.hasLaurentExpansionOnAnnulus`. -/
recall AnalyticOnNhd.hasLaurentExpansionOnAnnulus
