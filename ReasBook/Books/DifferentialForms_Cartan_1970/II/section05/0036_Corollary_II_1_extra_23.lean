import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

-- Proof sketch: pass to the real and imaginary components using `IsClosedOn.comp`, identify each
-- component with a planar differential form, and apply the oriented-boundary Green-Riemann theorem
-- together with the closedness criterion for planar forms.
/-- Corollary II.1-extra-23: if a complex-valued differential form is closed on `D`, then its
integral over the oriented boundary of any compact subset of `D` is zero. -/
theorem orientedBoundary_integral_eq_zero_of_isClosedOn
    {ι : Type u} [Fintype ι] {D K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hω : IsClosedOn ω D) :
    (∑ i, ∫ᶜ z in (Γ i).toPath, ω z) = 0 := sorry
