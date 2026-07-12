import Mathlib
import DifferentialForms_Cartan_1970.III.section10.«0001_Definition_III_4_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition III.4-extra-2: a function `f` has a Laurent expansion in the annulus
`ρ₂ < |z| < ρ₁` if there are Laurent coefficients whose Laurent series converges in that annulus
and sums to `f` at every point of the annulus. -/
def HasLaurentExpansionOnAnnulus (f : ℂ → ℂ) (ρ₂ ρ₁ : ENNReal) : Prop :=
  ∃ a : ℤ → ℂ,
    IsLaurentSeriesOnAnnulus a ρ₂ ρ₁ ∧
      Set.EqOn f (fun z ↦ ∑' n : ℤ, a n * z ^ n) (complexOpenAnnulus ρ₂ ρ₁)
