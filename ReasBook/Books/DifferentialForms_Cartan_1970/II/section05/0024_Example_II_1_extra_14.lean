import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Example II.1-extra-14 (1): a subset of the complex plane that is starred with respect to one
of its points is simply connected. -/
-- Proof sketch: use `StarConvex.contractibleSpace` on the subtype `D`, then deduce simple
-- connectedness from `SimplyConnectedSpace.ofContractible`.
theorem isSimplyConnected_of_starConvex {D : Set ℂ} {a : ℂ} (ha : a ∈ D)
    (hD : StarConvex ℝ a D) : IsSimplyConnected D := by
  letI : ContractibleSpace D := hD.contractibleSpace ⟨a, ha⟩
  exact (inferInstance : SimplyConnectedSpace D)

/-- Example II.1-extra-14 (2): a convex subset of the complex plane is simply connected as soon
as one chooses a point of it; in particular every nonempty convex open set is simply connected. -/
-- Proof sketch: apply the starred case to `Convex.starConvex`.
theorem isSimplyConnected_of_convex {D : Set ℂ} {a : ℂ} (hD : Convex ℝ D) (ha : a ∈ D) :
    IsSimplyConnected D := by
  exact isSimplyConnected_of_starConvex ha (hD.starConvex ha)

/-- Example II.1-extra-14 (3): the punctured complex plane is not simply connected. -/
-- Proof sketch: use the unit circle as a loop in `({0}ᶜ : Set ℂ)` and show it cannot be
-- null-homotopic because the integral of `z ↦ z⁻¹` around it is nonzero.
theorem punctured_complex_plane_not_isSimplyConnected :
    ¬ IsSimplyConnected ({0}ᶜ : Set ℂ) := by
  intro hsc
  have hopen : IsOpen ({0}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  have hnonzero : (0 : ℂ) ∉ (fun z : ℂ ↦ z) '' ({0}ᶜ : Set ℂ) := by
    simp
  rcases Complex.exists_continuousOn_eqOn_exp_comp hsc hopen continuousOn_id hnonzero with
    ⟨f, hf_cont, hf_exp⟩
  let γ : Set.Icc (0 : ℝ) (2 * Real.pi) → ℂ := fun t ↦
    f (circleMap 0 1 t) - ((t : ℝ) : ℂ) * Complex.I
  have hγ_cont : Continuous γ := by
    have hcircle_cont :
        Continuous (fun t : Set.Icc (0 : ℝ) (2 * Real.pi) ↦ circleMap 0 1 (t : ℝ)) := by
      simpa using (continuous_circleMap 0 1).comp continuous_subtype_val
    have hcircle_mapsTo :
        ∀ t : Set.Icc (0 : ℝ) (2 * Real.pi), circleMap 0 1 (t : ℝ) ∈ ({0}ᶜ : Set ℂ) := by
      intro t
      simp [circleMap_eq_center_iff]
    have hcoe_cont : Continuous (fun t : Set.Icc (0 : ℝ) (2 * Real.pi) ↦ ((t : ℝ) : ℂ)) := by
      simpa using Complex.continuous_ofReal.comp continuous_subtype_val
    exact (hf_cont.comp_continuous hcircle_cont hcircle_mapsTo).sub (hcoe_cont.mul_const Complex.I)
  have hγ_exp : ∀ t, Complex.exp (γ t) = 1 := by
    intro t
    have ht : circleMap 0 1 t ∈ ({0}ᶜ : Set ℂ) := by
      simp [circleMap_eq_center_iff]
    calc
      Complex.exp (γ t)
          = Complex.exp (f (circleMap 0 1 t)) / Complex.exp (((t : ℝ) : ℂ) * Complex.I) := by
              simp [γ, Complex.exp_sub]
      _ = circleMap 0 1 t / Complex.exp (((t : ℝ) : ℂ) * Complex.I) := by
            simpa [Function.comp] using hf_exp ht
      _ = 1 := by simp [circleMap]
  have hγ_loc : IsLocallyConstant γ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro t
    refine ⟨γ ⁻¹' Metric.ball (γ t) 1, hγ_cont.isOpen_preimage _ Metric.isOpen_ball, ?_, ?_⟩
    · simp [Metric.mem_ball, zero_lt_one]
    · intro t' ht'
      have hEqExp : Complex.exp (γ t') = Complex.exp (γ t) := by rw [hγ_exp t', hγ_exp t]
      rcases Complex.exp_eq_exp_iff_exists_int.mp hEqExp with ⟨n, hn⟩
      by_cases hn0 : n = 0
      · simpa [hn0] using hn
      · have hdist_lt : ‖γ t' - γ t‖ < 1 := by
          simpa [Metric.mem_ball, dist_eq_norm] using ht'
        have hnorm_n : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
          have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
          simpa [Complex.norm_intCast] using this
        have hnorm_ge : 2 * Real.pi ≤ ‖γ t' - γ t‖ := by
          calc
            2 * Real.pi = 1 * ‖(2 * Real.pi : ℂ) * Complex.I‖ := by
              simp [mul_comm, abs_of_nonneg Real.pi_pos.le]
            _ ≤ ‖(n : ℂ)‖ * ‖(2 * Real.pi : ℂ) * Complex.I‖ := by gcongr
            _ = ‖(n : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)‖ := by simp
            _ = ‖γ t' - γ t‖ := by
              simp [hn, sub_eq_add_neg, add_comm, add_assoc]
        have hlt : (1 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
        linarith
  haveI : PreconnectedSpace (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    Subtype.preconnectedSpace
      ((show Set.OrdConnected (Set.Icc (0 : ℝ) (2 * Real.pi)) from inferInstance).isPreconnected)
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    constructor
    · rfl
    · positivity
  have h2pi_mem : (2 * Real.pi : ℝ) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    constructor
    · positivity
    · rfl
  have hconst :
      γ ⟨0, h0_mem⟩ =
        γ ⟨2 * Real.pi, h2pi_mem⟩ :=
    hγ_loc.apply_eq_of_preconnectedSpace _ _
  have hEq : f 1 = f 1 - 2 * Real.pi * Complex.I := by
    simpa [γ, circleMap] using hconst
  have hzero : (2 * Real.pi * Complex.I : ℂ) = 0 := by
    have := congrArg (fun z : ℂ ↦ z - f 1) hEq
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm
  have htwo_pi_ne : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
  exact (mul_ne_zero htwo_pi_ne Complex.I_ne_zero) hzero
