import Mathlib
import cartan.II.section05.«0010_Proposition_4_1»
import cartan.II.section05.«0033_Definition_II_1_extra_20»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

-- Proof sketch: reduce the compact region to finitely many local boundary charts coming from
-- `IsOrientedBoundaryOf`, cut the region into rectangles, apply the rectangle Green-Riemann
-- formula on each piece, and then cancel the contributions of the interior cuts.
/-- Theorem II.1-extra-22: if `Γ` is the oriented boundary of a compact set `K`, and the real
coefficient functions `P` and `Q` are continuously differentiable on an open neighborhood `D` of
`K`, then the boundary integral of `P dx + Q dy` along `Γ` equals the
area integral of
`∂Q/∂x - ∂P/∂y` over `K`. -/
theorem orientedBoundary_green_riemann_formula
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P D) (hQ_cont : ContinuousOn Q D)
    (hdPdy_cont : ContinuousOn dPdy D) (hdQdx_cont : ContinuousOn dQdx D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re) :
    (∑ i, ∫ᶜ z in (Γ i).toPath, (P dx + Q dy) z) =
      ∫ z in K, (dQdx z - dPdy z) := sorry
