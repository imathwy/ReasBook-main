import DifferentialForms_Cartan_1970.IV.section16.«0002_Theorem_IV_4_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

open Complex InnerProductSpace Metric Real Set

-- Semantic search tool `lean_leansearch` is unavailable in this session; the statement shape was
-- chosen by inspection of the local section-IV.4 harmonic-disc precedent and mathlib's
-- `HarmonicContOnCl` API.

/-- Problem IV.4-extra-1. For a continuous `2π`-periodic real-valued boundary datum on the circle
`|z| = r`, there exists a real-valued function on the complex plane that is continuous on the
closed disc, harmonic on the open disc, and agrees with the boundary datum on the circle. -/
theorem exists_harmonic_extension_of_continuous_periodic_boundary_datum {f : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (hf_cont : Continuous f) (hf_periodic : Function.Periodic f (2 * Real.pi)) :
    ∃ F : ℂ → ℝ,
      HarmonicContOnCl F (ball (0 : ℂ) r) ∧
        ∀ θ : ℝ, F (circleMap 0 r θ) = f θ := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let g : Real.Angle → ℝ := AddCircle.liftIoc (2 * Real.pi) (-Real.pi) f
  let φ : ℂ → ℝ := fun z ↦ g (z.arg : Real.Angle)
  have hφ_cont : ContinuousOn φ (sphere (0 : ℂ) r) := by
    -- First descend the periodic datum to `Real.Angle` using the endpoint compatibility at `±π`.
    have h_endpoint : f (-Real.pi) = f (-Real.pi + 2 * Real.pi) := (hf_periodic (-Real.pi)).symm
    have hg_cont : Continuous g := by
      dsimp [g]
      refine AddCircle.liftIoc_continuous ?_ (hf_cont.continuousOn)
      simpa [two_mul] using h_endpoint
    -- Next, `arg : ℂ → Real.Angle` is continuous away from `0`, and the positive-radius sphere
    -- never meets `0`.
    have harg_cont : ContinuousOn (fun z : ℂ ↦ (z.arg : Real.Angle)) (sphere (0 : ℂ) r) := by
      intro z hz
      have hz_ne_zero : z ≠ 0 := by
        apply norm_ne_zero_iff.mp
        rw [mem_sphere_zero_iff_norm.mp hz]
        exact hr.ne'
      simpa only [Function.comp_apply] using
        (Complex.continuousAt_arg_coe_angle (x := z) hz_ne_zero).continuousWithinAt
    -- Compose the continuous lift with the continuous angle-valued argument on the boundary.
    simpa [φ] using hg_cont.comp_continuousOn harg_cont
  have hφ_circle : ∀ θ : ℝ, φ (circleMap 0 r θ) = f θ := by
    intro θ
    -- On the boundary, `circleMap` has angle class `θ`.
    have harg_circle : ((circleMap 0 r θ).arg : Real.Angle) = θ := by
      rw [Complex.arg_coe_angle_eq_iff_eq_toReal]
      calc
        Complex.arg (circleMap 0 r θ)
            = Complex.arg (Complex.exp (θ * Complex.I)) := by
                rw [circleMap_zero, Complex.arg_real_mul _ hr]
        _ = toIocMod Real.two_pi_pos (-Real.pi) θ := Complex.arg_exp_mul_I θ
        _ = (θ : Real.Angle).toReal := rfl
    -- Evaluating the descended lift at the angle class of `θ` recovers the original periodic datum.
    have hperiodic_lift : g (θ : Real.Angle) = f θ := by
      have hθmem : ((θ : Real.Angle).toReal) ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
        simpa [two_mul] using Real.Angle.toReal_mem_Ioc (θ : Real.Angle)
      have htoReal :
          (θ : Real.Angle).toReal = toIocMod Real.two_pi_pos (-Real.pi) θ := rfl
      have hdecomp :
          (θ : Real.Angle).toReal
            + toIocDiv Real.two_pi_pos (-Real.pi) θ * (2 * Real.pi) = θ := by
        rw [htoReal]
        exact toIocMod_add_toIocDiv_mul Real.two_pi_pos (-Real.pi) θ
      have hcanonical :
          AddCircle.liftIoc (2 * Real.pi) (-Real.pi) f (((θ : Real.Angle).toReal : ℝ) : Real.Angle)
            = f ((θ : Real.Angle).toReal) :=
        AddCircle.liftIoc_coe_apply (f := f) hθmem
      have htoReal_eval : f ((θ : Real.Angle).toReal) = f θ := by
        have hshift :=
          (hf_periodic.int_mul (toIocDiv Real.two_pi_pos (-Real.pi) θ))
            ((θ : Real.Angle).toReal)
        rw [hdecomp] at hshift
        exact hshift.symm
      -- Rewrite through the canonical `Ioc` representative of the angle class.
      dsimp [g]
      rw [← Real.Angle.coe_toReal (θ : Real.Angle)]
      exact hcanonical.trans htoReal_eval
    -- Rewriting by the boundary angle identity reduces the boundary value to the periodic lift.
    simpa [φ, harg_circle] using hperiodic_lift
  have h_dirichlet :
      ∃ F : ℂ → ℝ, HarmonicContOnCl F (ball (0 : ℂ) r) ∧ EqOn F φ (sphere (0 : ℂ) r) :=
    dirichlet_problem_disc_exists hφ_cont
  obtain ⟨F, hF_harmonic, hF_boundary⟩ := h_dirichlet
  refine ⟨F, hF_harmonic, ?_⟩
  intro θ
  have hmem : circleMap 0 r θ ∈ sphere (0 : ℂ) r := by
    exact circleMap_mem_sphere (0 : ℂ) hr.le θ
  rw [hF_boundary hmem, hφ_circle θ]
