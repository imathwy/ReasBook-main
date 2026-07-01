import Mathlib
import cartan.II.section05.«0004_Definition_II_1_extra_4»

noncomputable section

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: if `ω` has a primitive, then every axis-parallel rectangle contained in `D` has
-- zero boundary integral by the fundamental theorem for line integrals; Green's formula identifies
-- that boundary integral with the double integral of `∂Q/∂x - ∂P/∂y`, and continuity of one mixed
-- partial then forces the difference to vanish pointwise.
/-- Proposition 3.1 (1): on an open set, the existence of a primitive for
`Complex.planarDifferentialForm P Q` implies that the cross partials satisfy
`∂P/∂y = ∂Q/∂x`. -/
theorem hasPrimitiveOn_imp_partialDeriv_eq
    {D : Set ℂ} (hD : IsOpen D) {P Q dPdy dQdx : ℂ → ℂ}
    (hdPdy_cont : ContinuousOn dPdy D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    (hprimitive : HasPrimitiveOn D (Complex.planarDifferentialForm P Q)) :
    ∀ z ∈ D, dPdy z = dQdx z := sorry

-- Proof sketch: Green's formula turns the identity `∂P/∂y = ∂Q/∂x` into vanishing of the
-- boundary integral over every axis-parallel rectangle inside the disc, and one continuous mixed
-- second partial suffices because the equality identifies the other one with it on the disc.
/-- Proposition 3.1 (2): on an open disc in `ℂ`, the identity `∂P/∂y = ∂Q/∂x` is sufficient for
the form `Complex.planarDifferentialForm P Q` to admit a primitive. -/
theorem partialDeriv_eq_imp_hasPrimitiveOn_ball
    (c : ℂ) (r : ℝ) {P Q dPdy dQdx : ℂ → ℂ}
    (hP_cont : ContinuousOn P (Metric.ball c r)) (hQ_cont : ContinuousOn Q (Metric.ball c r))
    (hdPdy_cont : ContinuousOn dPdy (Metric.ball c r))
    (hP_dy : ∀ z ∈ Metric.ball c r, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ Metric.ball c r, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re)
    (hpartial : ∀ z ∈ Metric.ball c r, dPdy z = dQdx z) :
    HasPrimitiveOn (Metric.ball c r) (Complex.planarDifferentialForm P Q) := sorry
