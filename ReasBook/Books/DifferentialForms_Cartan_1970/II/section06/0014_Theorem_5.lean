import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0026_Definition_II_1_extra_16»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.II.section05.«0036_Corollary_II_1_extra_23»
import DifferentialForms_Cartan_1970.II.section06.«0005_Corollary_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

section

variable {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ)
variable (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D) (f : ℂ → ℂ)
variable (hf : DifferentiableOn ℂ f D)

/-- Helper for Theorem 5: an interior point of `K` is the center of some closed ball still
contained in `interior K`. -/
private lemma exists_closed_ball_subset_interior {a : ℂ} (ha : a ∈ interior K) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ interior K := by
  -- Choose an open ball inside `interior K`, then shrink it so its closed ball still fits.
  rcases Metric.isOpen_iff.mp isOpen_interior a ha with ⟨R, hR, hRsub⟩
  refine ⟨R / 2, half_pos hR, ?_⟩
  exact (Metric.closedBall_subset_ball (half_lt_self hR)).trans hRsub

-- Proof sketch: decompose the oriented boundary into its finitely many closed piecewise
-- differentiable components, apply the holomorphic rectangle-integral theorem inside the compact
-- region bounded by them, and cancel the contributions of the auxiliary interior cuts.
/-- Theorem 5 (1): if `Γ` is the oriented boundary of a compact subset `K` of an open set `D` and
`f` is holomorphic on `D`, then the sum of the integrals of `f(z) dz` over the boundary components
of `Γ` is zero. -/
theorem orientedBoundary_sum_curveIntegral_eq_zero
    : ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z = 0 := by
  -- Each point of `D` has a primitive neighborhood for `f(z) dz`, so the underlying real form is
  -- closed on `D`.
  have hω :
      IsClosedOn (Complex.realScalarOneForm f) D := by
    intro z hz
    rcases holomorphic_has_local_primitive hD hf hz with ⟨r, hr, hball, hExact⟩
    refine ⟨Metric.ball z r, Metric.isOpen_ball, Metric.mem_ball_self hr, hball, ?_⟩
    simpa [Complex.realScalarOneForm] using hExact.hasPrimitiveOn
  -- The oriented-boundary corollary evaluates the total integral of this closed form to zero.
  simpa [Complex.realScalarOneForm, curveIntegral_restrictScalars] using
    (orientedBoundary_integral_eq_zero_of_local_primitives (Γ := Γ) hΓ hKD hω)

/-- Helper for Theorem 5: the positively oriented small circle centered at `a` evaluates the
Cauchy kernel integral to `2π i f(a)` once the closed disc lies in `D`. -/
private theorem small_circle_integral_div_sub_eq_two_pi_I_mul {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hclosed : Metric.closedBall a r ⊆ D) :
    (∮ z in C(a, r), f z / (z - a)) = (2 * Real.pi * Complex.I : ℂ) * f a := by
  -- Restrict holomorphicity to the closed disc and invoke the circle Cauchy formula there.
  have hfd : DifferentiableOn ℂ f (Metric.closedBall a r) := hf.mono hclosed
  have ha_ball : a ∈ Metric.ball a r := by
    simpa using Metric.mem_ball_self hr
  simpa [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    hfd.circleIntegral_sub_inv_smul ha_ball

-- Proof sketch: remove a small positively oriented circle around the interior point `a`, apply the
-- first part to `z ↦ f z / (z - a)` on the punctured compact region, then evaluate the circle term
-- by the Cauchy integral formula.
/-- Theorem 5 (2): if `Γ` is the oriented boundary of a compact subset `K` of an open set `D`,
`f` is holomorphic on `D`, and `a` lies in the interior of `K`, then the sum of the integrals of
`f(z) dz / (z - a)` over the boundary components of `Γ` is `2πif(a)`. -/
theorem orientedBoundary_sum_curveIntegral_div_sub_eq_two_pi_I_mul
    {a : ℂ} (ha : a ∈ interior K) :
    ∑ i, ∫ᶜ z in (Γ i).toPath, f z • indexForm a z =
      2 * π * Complex.I * f a := by
  -- Follow the source proof: excise a small disc around `a` that stays inside `interior K`.
  obtain ⟨r, hr, hclosedInterior⟩ := exists_closed_ball_subset_interior (K := K) ha
  have hclosedD : Metric.closedBall a r ⊆ D := by
    exact ((hclosedInterior.trans interior_subset).trans hKD)
  have hcircle :
      (∮ z in C(a, r), f z / (z - a)) = (2 * π * Complex.I : ℂ) * f a :=
    small_circle_integral_div_sub_eq_two_pi_I_mul (D := D) (f := f) hf hr hclosedD
  have hcompare :
      ∑ i, ∫ᶜ z in (Γ i).toPath, f z • indexForm a z =
        ∮ z in C(a, r), f z / (z - a) := by
    -- TODO: prove the excision comparison by showing that the oriented boundary of
    -- `K \ Metric.ball a r` is given by the original family `Γ` together with the reversed small
    -- circle, then apply part (1) to `z ↦ f z / (z - a)` on `D \ {a}` and rewrite the reversed
    -- circle term via `curveIntegral_symm`.
    sorry
  -- Once the excision identity is available, the inner circle evaluation closes the formula.
  calc
    ∑ i, ∫ᶜ z in (Γ i).toPath, f z • indexForm a z = ∮ z in C(a, r), f z / (z - a) := hcompare
    _ = (2 * π * Complex.I : ℂ) * f a := hcircle
    _ = 2 * π * Complex.I * f a := by ring

end
