import Mathlib
import cartan.II.section05.«0001_Definition_II_1_extra_1»
import cartan.II.section05.«0019_Theorem_2»
import cartan.II.section06.«0005_Corollary_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

namespace Path

-- Proof sketch: use Corollary 1 to get a local primitive of `f` near each point of `D`, hence a
-- closed real-linear form underlying `f(z) dz` on `D`; then apply the closed-path homotopy
-- invariance theorem from Section II.1 to compare the integral along `γ` with the integral along
-- the constant loop supplied by the null-homotopy, which is zero.
/-- Corollary 2: if `f` is holomorphic on an open set `D`, then the integral of `f(z) dz` along
any piecewise differentiable closed path in `D` that is homotopic in `D` to a point is zero. -/
theorem curveIntegral_eq_zero_of_differentiableOn_of_null_homotopic
    {D : Set ℂ} (hD : IsOpen D) {z₀ : ℂ} {γ : Path z₀ z₀}
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγ_null : IsNullHomotopicClosedPathIn D γ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) :
    ∫ᶜ z in γ, (f dz) z = 0 := by
  have hω_closed :
      IsClosedOn (Complex.realScalarOneForm f) D := by
    intro w hw
    rcases holomorphic_has_local_primitive hD hf hw with ⟨r, hr, hball, hExact⟩
    refine ⟨Metric.ball w r, Metric.isOpen_ball, Metric.mem_ball_self hr, hball, ?_⟩
    simpa [Complex.realScalarOneForm] using hExact.hasPrimitiveOn
  rcases hγ_null with ⟨x, _, hγx⟩
  have hEq :
      ∫ᶜ z in γ, ((f dz) z).restrictScalars ℝ =
        ∫ᶜ z in Path.refl x, ((f dz) z).restrictScalars ℝ := by
    simpa [Complex.realScalarOneForm] using
      (curveIntegral_eq_of_homotopic_closed_paths_of_closed_form hγx hγ_piecewise
        (isPiecewiseDifferentiable_refl x) hω_closed :
        ∫ᶜ z in γ, Complex.realScalarOneForm f z =
          ∫ᶜ z in Path.refl x, Complex.realScalarOneForm f z)
  rw [curveIntegral_restrictScalars, curveIntegral_restrictScalars] at hEq
  simpa using hEq

end Path
