import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»

-- `lean_leansearch` is unavailable in this environment; the statement surface was matched against
-- the local `IsClosedOn` / `HasPrimitiveOn` API, Proposition 3.1, and the existing rectangle
-- boundary path precedent.

noncomputable section

/-- The boundary path of the axis-parallel rectangle with opposite corners `z` and `w`,
traversing the four sides
`z → (w.re, z.im) → w → (z.re, w.im) → z`. -/
def axisParallelRectangleBoundaryPath (z w : ℂ) : Path z z :=
  let zw := Complex.mk w.re z.im
  let wz := Complex.mk z.re w.im
  (Path.segment z zw).trans
    ((Path.segment zw w).trans
      ((Path.segment w wz).trans
        (Path.segment wz z)))

/-- Proposition 4.1 (1): a continuous complex-valued differential form on `D` is closed if and
only if, around every point of `D`, every sufficiently small axis-parallel rectangle contained in
`D` has vanishing boundary integral. -/
theorem isClosedOn_iff_zero_rectangle_boundary_integral_locally
    {D : Set ℂ} {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : ContinuousOn ω D) :
    IsClosedOn ω D ↔
      ∀ z ∈ D, ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ D ∧
        ∀ w₀ w₁ : ℂ,
          Complex.Rectangle w₀ w₁ ⊆ Metric.ball z r →
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath w₀ w₁, ω ζ = 0 := sorry

/-- Proposition 4.1 (2): if `ω = P dx + Q dy` has continuous coefficients on the open set `D` and
`∂P/∂y` is continuous on `D`, then the condition `∂P/∂y = ∂Q/∂x` is necessary and sufficient for
`ω` to be closed. -/
theorem isClosedOn_planarDifferentialForm_iff_partialDeriv_eq
    {D : Set ℂ} (hD : IsOpen D) {P Q dPdy dQdx : ℂ → ℂ}
    (hP : ContinuousOn P D) (hQ : ContinuousOn Q D)
    (hdPdy : ContinuousOn dPdy D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re) :
    IsClosedOn (P dx + Q dy) D ↔
      ∀ z ∈ D, dPdy z = dQdx z := sorry
