import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.VI.section26.«0001_Definition_VI_5_extra_1»

open MeasureTheory
open scoped Manifold Real

noncomputable section

-- Domain sampling: the primary domain here is integration of scalar differentials on analytic-
-- continuation surfaces over `ℂ`. The relevant owner declarations inspected before this refinement
-- were:
-- * the section-26 source-facing surface owners `RiemannSurfaceOver` and
--   `ConnectedHausdorffUnramifiedSurfaceOver.toRiemannSurfaceOver` in the section-26 owner files;
-- * `Complex.scalarOneForm` with its source-facing notation `f dz` in
--   `II/section05/0001_Definition_II_1_extra_1.lean`;
-- * mathlib's canonical base-plane owner `curveIntegral`, together with the segment specialization
--   `curveIntegral_segment`.
-- Primitive data for the example is the surface over `ℂ`, a path on that surface, and the scalar
-- coefficient of the pulled-back differential along that path. The segment integral and the
-- Beta/Gamma evaluation are derived bridge API from that owner-level surface statement.

namespace RiemannSurfaceOver

/-- The integral of the scalar differential `f dπ` along a path `γ` on a Riemann surface `X`
spread over `ℂ`, where `π = X.projection`. This is the source-facing path/form interface used in
Example VI.5-extra-7 before descending to the base segment computation. -/
def scalarIntegral (X : RiemannSurfaceOver 𝓘(ℂ) ℂ) {x y : X} (γ : Path x y) (f : X → ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    derivWithin (fun s : ℝ ↦ X.projection (γ.extend s)) (Set.Icc (0 : ℝ) 1) t *
      f (γ.extend t)

end RiemannSurfaceOver

/-- The real integrand appearing in Example VI.5-extra-7. -/
def exampleVI5Extra7Integrand (x : ℝ) : ℝ :=
  ((1 - x ^ 3) ^ (1 / 3 : ℝ))⁻¹

/-- On the real segment `[0,1]`, the scalar `1`-form used in Example VI.5-extra-7 reduces to the
real integral `∫_0^1 dx / (1 - x^3)^(1 / 3)`. -/
theorem exampleVI5Extra7_segment_curveIntegral_eq_intervalIntegral :
    ∫ᶜ z in Path.segment (0 : ℂ) 1,
      (((fun w : ℂ ↦ (exampleVI5Extra7Integrand w.re : ℂ)) dz) z) =
      (∫ x in (0 : ℝ)..1, exampleVI5Extra7Integrand x : ℝ) := by
  rw [curveIntegral_segment]
  let f : ℝ → ℝ := exampleVI5Extra7Integrand
  have h_ofReal :
      (∫ x in (0 : ℝ)..1, (f x : ℂ)) = ↑(∫ x in (0 : ℝ)..1, f x) :=
    intervalIntegral.integral_ofReal
  simpa [f, AffineMap.lineMap_apply] using h_ofReal

/-- Bridge from the surface-path integral in Example VI.5-extra-7 to the base segment integral:
if the projection of a path on a Riemann surface over `ℂ` is the segment `0 → 1`, and the scalar
coefficient along that path is the distinguished cubic-root branch, then the surface integral
reduces to the segment integral on the base. -/
theorem exampleVI5Extra7_scalarIntegral_eq_segment_curveIntegral
    (X : RiemannSurfaceOver 𝓘(ℂ) ℂ) {x y : X} (γ : Path x y) (f : X → ℂ)
    (hproj : Set.EqOn
      (fun t : ℝ ↦ X.projection (γ.extend t))
      (fun t ↦ (t : ℂ))
      (Set.Icc (0 : ℝ) 1))
    (hf : Set.EqOn
      (fun t : ℝ ↦ f (γ.extend t))
      (fun t ↦ (exampleVI5Extra7Integrand t : ℂ))
      (Set.Icc (0 : ℝ) 1)) :
    X.scalarIntegral γ f =
      ∫ᶜ z in Path.segment (0 : ℂ) 1, (((fun w : ℂ ↦ (exampleVI5Extra7Integrand w.re : ℂ)) dz) z) :=
  by
  rw [exampleVI5Extra7_segment_curveIntegral_eq_intervalIntegral]
  unfold RiemannSurfaceOver.scalarIntegral
  have h_eq :
      (∫ t in (0 : ℝ)..1,
        derivWithin (fun s : ℝ ↦ X.projection (γ.extend s)) (Set.Icc (0 : ℝ) 1) t *
          f (γ.extend t)) =
        ∫ t in (0 : ℝ)..1, (exampleVI5Extra7Integrand t : ℂ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro t ht
    have h0t : (0 : ℝ) ≤ t := by
      simpa [min_eq_left zero_le_one] using ht.1.le
    have ht1 : t ≤ (1 : ℝ) := by
      simpa [max_eq_right zero_le_one] using ht.2
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨h0t, ht1⟩
    have hderiv :
        derivWithin (fun s : ℝ ↦ X.projection (γ.extend s)) (Set.Icc (0 : ℝ) 1) t = 1 := by
      rw [derivWithin_congr hproj (hproj htI)]
      simpa using
        (((hasDerivAt_id t).ofReal_comp).hasDerivWithinAt.derivWithin
          ((uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt htI) :
          derivWithin (fun s : ℝ ↦ (s : ℂ)) (Set.Icc (0 : ℝ) 1) t = 1)
    simp [hderiv, hf htI]
  calc
    ∫ t in (0 : ℝ)..1,
        derivWithin (fun s : ℝ ↦ X.projection (γ.extend s)) (Set.Icc (0 : ℝ) 1) t *
          f (γ.extend t) =
        ∫ t in (0 : ℝ)..1, (exampleVI5Extra7Integrand t : ℂ) := h_eq
    _ = ↑(∫ t in (0 : ℝ)..1, exampleVI5Extra7Integrand t) := intervalIntegral.integral_ofReal

-- The derived real interval is canonically a Beta value after the cubic substitution `u = x^3`.
-- Owner abstraction: `ProbabilityTheory.beta`.
-- Derived API used below: Euler's reflection formula `Real.Gamma_mul_Gamma_one_sub`.

/-- Helper for Example VI.5-extra-7: after the cubic substitution `u = x^3`, the source integral is
the Beta value `β(1 / 3, 2 / 3)` scaled by `1 / 3`. -/
private theorem exampleVI5Extra7_intervalIntegral_eq_one_third_beta :
    ∫ x in (0 : ℝ)..1, exampleVI5Extra7Integrand x =
      (1 / 3 : ℝ) * ProbabilityTheory.beta (1 / 3 : ℝ) (2 / 3 : ℝ) := by
  let s : Set ℝ := Set.Ioo (0 : ℝ) 1
  have hbeta :
      ∫ u in Set.Ioo (0 : ℝ) 1,
        u ^ ((1 / 3 : ℝ) - 1) * (1 - u) ^ ((2 / 3 : ℝ) - 1) ∂volume =
          ProbabilityTheory.beta (1 / 3 : ℝ) (2 / 3 : ℝ) := by
    -- Identify the real kernel on `(0, 1)` with the standard complex Beta integral.
    calc
      ∫ u in Set.Ioo (0 : ℝ) 1,
          u ^ ((1 / 3 : ℝ) - 1) * (1 - u) ^ ((2 / 3 : ℝ) - 1) ∂volume
          = (Complex.betaIntegral (1 / 3 : ℝ) (2 / 3 : ℝ)).re := by
              rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
                ← integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re]
              · refine setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ ?_
                norm_cast
                rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
                  Complex.re_mul_ofReal, Complex.ofReal_re]
                all_goals
                  nlinarith [hx.1, hx.2]
              · convert! Complex.betaIntegral_convergent
                  (u := (1 / 3 : ℝ)) (v := (2 / 3 : ℝ)) (by norm_num) (by norm_num) using 1
                rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]
      _ = ProbabilityTheory.beta (1 / 3 : ℝ) (2 / 3 : ℝ) := by
            simpa using
              (ProbabilityTheory.beta_eq_betaIntegralReal (1 / 3 : ℝ) (2 / 3 : ℝ)
                (by norm_num) (by norm_num)).symm
  have hcubeImage : (fun x : ℝ ↦ x ^ 3) '' s = s := by
    -- The cubic map is a bijection from `(0, 1)` to itself.
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor
      · exact pow_pos hx.1 3
      · exact pow_lt_one₀ hx.1.le hx.2 (by norm_num)
    · intro hu
      refine ⟨u ^ (1 / 3 : ℝ), ?_, ?_⟩
      · constructor
        · exact Real.rpow_pos_of_pos hu.1 _
        · exact Real.rpow_lt_one hu.1.le hu.2 (by norm_num)
      · have hcubic : (u ^ (1 / 3 : ℝ)) ^ (3 : ℝ) = u := by
          simpa [one_div] using
            (Real.rpow_inv_rpow hu.1.le (show (3 : ℝ) ≠ 0 by norm_num))
        simpa [Real.rpow_natCast] using hcubic
  have hderiv :
      ∀ x ∈ s, HasDerivWithinAt (fun y : ℝ ↦ y ^ 3) (3 * x ^ 2) s x := by
    -- The substitution `u = x^3` has derivative `3x^2` on the open interval.
    intro x hx
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_pow 3 x).hasDerivWithinAt :
        HasDerivWithinAt (fun y : ℝ ↦ y ^ 3) (3 * x ^ (3 - 1)) s x)
  have hinj : Set.InjOn (fun x : ℝ ↦ x ^ 3) s := by
    -- Cubing is injective, so the image-change formula applies on `(0, 1)`.
    intro x hx y hy hxy
    have hmono : StrictMono (fun t : ℝ ↦ t ^ 3) := by
      simpa using (show Odd 3 by decide).strictMono_pow (R := ℝ)
    exact hmono.injective hxy
  have hchange :
      ∫ u in Set.Ioo (0 : ℝ) 1,
        u ^ ((1 / 3 : ℝ) - 1) * (1 - u) ^ ((2 / 3 : ℝ) - 1) ∂volume
        =
          ∫ x in s,
            |3 * x ^ 2| •
              ((x ^ 3) ^ ((1 / 3 : ℝ) - 1) * (1 - x ^ 3) ^ ((2 / 3 : ℝ) - 1)) ∂volume := by
    -- Execute the cubic substitution on the open interval, away from the singular endpoints.
    have hchange_image :
        ∫ u in (fun x : ℝ ↦ x ^ 3) '' s,
          u ^ ((1 / 3 : ℝ) - 1) * (1 - u) ^ ((2 / 3 : ℝ) - 1) ∂volume
          =
            ∫ x in s,
              |3 * x ^ 2| •
                ((x ^ 3) ^ ((1 / 3 : ℝ) - 1) * (1 - x ^ 3) ^ ((2 / 3 : ℝ) - 1)) ∂volume := by
      rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
    simpa [hcubeImage] using hchange_image
  have hpoint :
      ∀ x ∈ s,
        |3 * x ^ 2| •
            ((x ^ 3) ^ ((1 / 3 : ℝ) - 1) * (1 - x ^ 3) ^ ((2 / 3 : ℝ) - 1))
          =
            (3 : ℝ) * exampleVI5Extra7Integrand x := by
    -- On `(0, 1)`, positivity lets us simplify the Jacobian and both `rpow` factors exactly.
    intro x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    have hx2_ne : x ^ 2 ≠ 0 := by positivity
    have hx3_lt : x ^ 3 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
    have h_one_sub_pos : 0 < 1 - x ^ 3 := sub_pos.mpr hx3_lt
    have hpow_mul :
        x ^ (3 * (((1 / 3 : ℝ) - 1))) = (x ^ 3) ^ ((1 / 3 : ℝ) - 1) := by
      simpa using (Real.rpow_natCast_mul hx0.le 3 (((1 / 3 : ℝ) - 1)))
    have hpow_x :
        (x ^ 3) ^ ((1 / 3 : ℝ) - 1) = (x ^ 2)⁻¹ := by
      calc
        (x ^ 3) ^ ((1 / 3 : ℝ) - 1) = x ^ (3 * (((1 / 3 : ℝ) - 1))) := hpow_mul.symm
        _ = x ^ (-2 : ℝ) := by congr 1; norm_num
        _ = (x⁻¹) ^ (2 : ℝ) := by
              rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg_eq_inv_rpow]
        _ = (x⁻¹) ^ (2 : ℕ) := by
              simp
        _ = (x ^ 2)⁻¹ := by simp
    have hpow_one_sub :
        (1 - x ^ 3) ^ ((2 / 3 : ℝ) - 1) = ((1 - x ^ 3) ^ (1 / 3 : ℝ))⁻¹ := by
      rw [show ((2 / 3 : ℝ) - 1) = -(1 / 3 : ℝ) by norm_num, Real.rpow_neg_eq_inv_rpow,
        Real.inv_rpow h_one_sub_pos.le]
    calc
      |3 * x ^ 2| •
          ((x ^ 3) ^ ((1 / 3 : ℝ) - 1) * (1 - x ^ 3) ^ ((2 / 3 : ℝ) - 1))
          = (3 * x ^ 2) * ((x ^ 2)⁻¹ * ((1 - x ^ 3) ^ (1 / 3 : ℝ))⁻¹) := by
              rw [smul_eq_mul, abs_of_pos (by positivity), hpow_x, hpow_one_sub]
      _ = ((3 * x ^ 2) * (x ^ 2)⁻¹) * ((1 - x ^ 3) ^ (1 / 3 : ℝ))⁻¹ := by
            simp [mul_assoc]
      _ = 3 * (x ^ 2 * (x ^ 2)⁻¹) * ((1 - x ^ 3) ^ (1 / 3 : ℝ))⁻¹ := by
            ac_rfl
      _ = (3 : ℝ) * ((1 - x ^ 3) ^ (1 / 3 : ℝ))⁻¹ := by
            simp [hx2_ne]
      _ = (3 : ℝ) * exampleVI5Extra7Integrand x := by rfl
  have hscaled :
      ∫ u in Set.Ioo (0 : ℝ) 1,
        u ^ ((1 / 3 : ℝ) - 1) * (1 - u) ^ ((2 / 3 : ℝ) - 1) ∂volume
        =
          (3 : ℝ) * ∫ x in Set.Ioo (0 : ℝ) 1, exampleVI5Extra7Integrand x ∂volume := by
    -- After pointwise normalization, the substitution contributes exactly the scalar `3`.
    calc
      ∫ u in Set.Ioo (0 : ℝ) 1,
          u ^ ((1 / 3 : ℝ) - 1) * (1 - u) ^ ((2 / 3 : ℝ) - 1) ∂volume
          =
            ∫ x in s,
              |3 * x ^ 2| •
                ((x ^ 3) ^ ((1 / 3 : ℝ) - 1) * (1 - x ^ 3) ^ ((2 / 3 : ℝ) - 1)) ∂volume :=
        hchange
      _ = ∫ x in s, (3 : ℝ) * exampleVI5Extra7Integrand x ∂volume := by
            refine setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_
            exact hpoint x hx
      _ = (3 : ℝ) * ∫ x in s, exampleVI5Extra7Integrand x ∂volume := by
            rw [integral_const_mul]
  -- Convert the original interval integral to the open interval, then insert the Beta identity.
  calc
    ∫ x in (0 : ℝ)..1, exampleVI5Extra7Integrand x
        = ∫ x in Set.Ioo (0 : ℝ) 1, exampleVI5Extra7Integrand x ∂volume := by
            rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    _ =
        (1 / 3 : ℝ) *
          ∫ u in Set.Ioo (0 : ℝ) 1,
            u ^ ((1 / 3 : ℝ) - 1) * (1 - u) ^ ((2 / 3 : ℝ) - 1) ∂volume := by
              calc
                ∫ x in Set.Ioo (0 : ℝ) 1, exampleVI5Extra7Integrand x ∂volume
                    =
                      (1 / 3 : ℝ) *
                        ((3 : ℝ) *
                          ∫ x in Set.Ioo (0 : ℝ) 1, exampleVI5Extra7Integrand x ∂volume) := by
                            ring
                _ =
                    (1 / 3 : ℝ) *
                      ∫ u in Set.Ioo (0 : ℝ) 1,
                        u ^ ((1 / 3 : ℝ) - 1) * (1 - u) ^ ((2 / 3 : ℝ) - 1) ∂volume := by
                          rw [hscaled]
    _ = (1 / 3 : ℝ) * ProbabilityTheory.beta (1 / 3 : ℝ) (2 / 3 : ℝ) := by
          rw [hbeta]

/-- Derived Beta/Gamma evaluation of the real integral appearing in Example VI.5-extra-7. -/
theorem exampleVI5Extra7_intervalIntegral_eq :
    ∫ x in (0 : ℝ)..1, exampleVI5Extra7Integrand x =
      2 * Real.pi / (3 * Real.sqrt 3) := by
  have hsqrt3 : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  calc
    ∫ x in (0 : ℝ)..1, exampleVI5Extra7Integrand x =
        (1 / 3 : ℝ) * ProbabilityTheory.beta (1 / 3 : ℝ) (2 / 3 : ℝ) :=
      exampleVI5Extra7_intervalIntegral_eq_one_third_beta
    _ = (1 / 3 : ℝ) * (Real.pi / Real.sin (Real.pi * (1 / 3 : ℝ))) := by
      rw [ProbabilityTheory.beta,
        show (1 / 3 : ℝ) + (2 / 3 : ℝ) = 1 by norm_num,
        Real.Gamma_one, div_one]
      have hthird : (1 - (1 / 3 : ℝ)) = (2 / 3 : ℝ) := by norm_num
      rw [← hthird, Real.Gamma_mul_Gamma_one_sub (1 / 3 : ℝ)]
    _ = 2 * Real.pi / (3 * Real.sqrt 3) := by
      have hsin : Real.sin (Real.pi * (1 / 3 : ℝ)) = Real.sqrt 3 / 2 := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using Real.sin_pi_div_three
      rw [hsin]
      field_simp [hsqrt3]

/-- Example VI.5-extra-7, at the base-segment level formalized in this file: the corresponding
curve integral on `Path.segment 0 1` equals `2π / (3 * √3)`. -/
theorem exampleVI5Extra7_segment_curveIntegral_eq :
    ∫ᶜ z in Path.segment (0 : ℂ) 1,
      (((fun w : ℂ ↦ (exampleVI5Extra7Integrand w.re : ℂ)) dz) z) =
      (2 * Real.pi / (3 * Real.sqrt 3) : ℂ) := by
  rw [exampleVI5Extra7_segment_curveIntegral_eq_intervalIntegral]
  simpa using congrArg (fun r : ℝ ↦ (r : ℂ)) exampleVI5Extra7_intervalIntegral_eq

/-- Example VI.5-extra-7 on its source-facing surface owner: a path on a Riemann surface over
`ℂ` carrying the cubic-root differential and projecting to the segment `0 → 1` has integral
`2π / (3 * √3)`. The real segment computation appears only as a bridge. -/
theorem exampleVI5Extra7_scalarIntegral_eq
    (X : RiemannSurfaceOver 𝓘(ℂ) ℂ) {x y : X} (γ : Path x y) (f : X → ℂ)
    (hproj : Set.EqOn
      (fun t : ℝ ↦ X.projection (γ.extend t))
      (fun t ↦ (t : ℂ))
      (Set.Icc (0 : ℝ) 1))
    (hf : Set.EqOn
      (fun t : ℝ ↦ f (γ.extend t))
      (fun t ↦ (exampleVI5Extra7Integrand t : ℂ))
      (Set.Icc (0 : ℝ) 1)) :
    X.scalarIntegral γ f = (2 * Real.pi / (3 * Real.sqrt 3) : ℂ) := by
  rw [exampleVI5Extra7_scalarIntegral_eq_segment_curveIntegral X γ f hproj hf]
  simpa using exampleVI5Extra7_segment_curveIntegral_eq
