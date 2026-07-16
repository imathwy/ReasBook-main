import DifferentialForms_Cartan_1970.cartan.III.section12.«0038_Exercise_25».RationalContourDecay

noncomputable section

open Filter Bornology
open scoped Topology unitInterval

/-- Helper for Cartan section12 0038_Exercise_25: at each simple noninteger pole, the source
circle-integral residue datum agrees with the meromorphic trailing coefficient of `P / Q`. -/
lemma exercise25_rational_trailingCoeff_eq_residue
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hsimple : ∀ z ∈ s, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z = -1)
    (residue : ℂ → ℂ) (hresidue : exercise25RationalResidueData P Q s residue)
    {z : ℂ} (hz : z ∈ s) :
    meromorphicTrailingCoeffAt (fun w ↦ P.eval w / Q.eval w) z = residue z := by
  -- Route correction: the plain quotient `P.eval / Q.eval` can have removable singularities at
  -- common roots of `P` and `Q`, so the bridge runs through the meromorphic normal form, which is
  -- holomorphic away from the actual pole finset `s`.
  let f : ℂ → ℂ := fun w ↦ P.eval w / Q.eval w
  let gNF : ℂ → ℂ := toMeromorphicNFOn f Set.univ
  have hmeromorphic : MeromorphicOn f Set.univ := by
    simpa [f] using exercise25_rationalEval_meromorphicOn_univ P Q
  have hEqNF : gNF =ᶠ[𝓝[≠] z] f := by
    simpa [gNF, f] using hmeromorphic.toMeromorphicNFOn_eq_self_on_nhdsNE (by simp : z ∈ Set.univ)
  have hholNF : DifferentiableOn ℂ gNF (↑s : Set ℂ)ᶜ := by
    simpa [gNF, f] using
      exercise25_rationalNormalForm_differentiableOn_compl_poleFinset P Q s hpoles
  have horderNF : meromorphicOrderAt gNF z = (-1 : WithTop ℤ) := by
    rw [meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := Set.univ) hmeromorphic (by simp)]
    simpa [f] using hsimple z hz
  have hmerNF : MeromorphicAt gNF z := by
    apply meromorphicAt_of_meromorphicOrderAt_ne_zero
    simpa [horderNF]
  -- Write the normal form in the canonical simple-pole shape `G(w) / (w - z)`.
  obtain ⟨G, hG_an, hG_ne, hG_eq⟩ := (meromorphicOrderAt_eq_int_iff hmerNF).1 horderNF
  have hcoeffNF : meromorphicTrailingCoeffAt gNF z = G z := by
    exact
      hG_an.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
        (f := gNF) (x := z) (n := (-1 : ℤ)) hG_ne hG_eq
  obtain ⟨ρG, hρG_pos, hG_ball⟩ := hG_an.exists_ball_analyticOnNhd
  have hEqNF' : ∀ᶠ w in 𝓝[≠] z, gNF w = f w := by
    simpa [Filter.EventuallyEq] using hEqNF
  have hG_eq' : ∀ᶠ w in 𝓝[≠] z, gNF w = (w - z) ^ (-1 : ℤ) • G w := by
    simpa [Filter.EventuallyEq] using hG_eq
  rw [eventually_nhdsWithin_iff] at hEqNF' hG_eq'
  rcases Metric.mem_nhds_iff.1 hEqNF' with ⟨δNF, hδNF_pos, hδNF⟩
  rcases Metric.mem_nhds_iff.1 hG_eq' with ⟨δG, hδG_pos, hδG⟩
  rcases hresidue z hz with ⟨R, hR, hRK, hRD, hsep, hdiffR, hcircleR⟩
  let r : ℝ := min (R / 2) (min (ρG / 2) (min (δNF / 2) (δG / 2)))
  have hr : 0 < r := by
    dsimp [r]
    refine lt_min (half_pos hR) ?_
    refine lt_min (half_pos hρG_pos) ?_
    exact lt_min (half_pos hδNF_pos) (half_pos hδG_pos)
  have hr_le_R : r ≤ R := by
    dsimp [r]
    calc
      r ≤ R / 2 := min_le_left _ _
      _ ≤ R := by linarith
  have hr_lt_ρG : r < ρG := by
    dsimp [r]
    calc
      r ≤ ρG / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
      _ < ρG := by linarith
  have hr_lt_δNF : r < δNF := by
    dsimp [r]
    calc
      r ≤ δNF / 2 := le_trans (min_le_right _ _) <| le_trans (min_le_right _ _) (min_le_left _ _)
      _ < δNF := by linarith
  have hr_lt_δG : r < δG := by
    dsimp [r]
    calc
      r ≤ δG / 2 := le_trans (min_le_right _ _) <| le_trans (min_le_right _ _) (min_le_right _ _)
      _ < δG := by linarith
  have hG_diff : DifferentiableOn ℂ G (Metric.closedBall z r) := by
    -- The analytic numerator `G` is holomorphic on a small ball around `z`, so it remains
    -- differentiable on the closed ball supporting the comparison circle.
    refine hG_ball.differentiableOn.mono ?_
    intro w hw
    exact Metric.mem_ball.2 (lt_of_le_of_lt hw hr_lt_ρG)
  have hcircleR_nf :
      ∮ w in C(z, R), gNF w = (2 * Real.pi * Complex.I : ℂ) * residue z := by
    have hEqCircle :
        (fun w ↦ gNF w) =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)] f := by
      exact
        (toMeromorphicNFOn_eqOn_codiscrete (U := Set.univ) hmeromorphic).symm.filter_mono
          (Filter.codiscreteWithin_mono (by
            intro w hw
            simp))
    -- The source residue circle transfers unchanged to the meromorphic normal form on the same
    -- boundary because the two functions differ only on a codiscrete subset of that sphere.
    calc
      ∮ w in C(z, R), gNF w = ∮ w in C(z, R), f w := by
        exact circleIntegral.circleIntegral_congr_codiscreteWithin hEqCircle hR.ne'
      _ = (2 * Real.pi * Complex.I : ℂ) * residue z := hcircleR
  have hClosedAnnulusSubset :
      Metric.closedBall z R \ Metric.ball z r ⊆ (↑s : Set ℂ)ᶜ := by
    intro w hw hwS
    by_cases hwz : w = z
    · subst hwz
      exact hw.2 (Metric.mem_ball_self hr)
    · exact hsep w (by simpa using hwS) hwz hw.1
  have hOpenAnnulusSubset :
      Metric.ball z R \ Metric.closedBall z r ⊆ (↑s : Set ℂ)ᶜ := by
    intro w hw hwS
    by_cases hwz : w = z
    · subst hwz
      exact hw.2 (Metric.mem_closedBall_self hr.le)
    · exact hsep w (by simpa using hwS) hwz (Metric.ball_subset_closedBall hw.1)
  have hcontAnnulus :
      ContinuousOn gNF (Metric.closedBall z R \ Metric.ball z r) :=
    hholNF.continuousOn.mono hClosedAnnulusSubset
  have hdiffAnnulus :
      DifferentiableOn ℂ gNF (Metric.ball z R \ Metric.closedBall z r) :=
    hholNF.mono hOpenAnnulusSubset
  have hshrink :
      (∮ w in C(z, R), gNF w) = ∮ w in C(z, r), gNF w :=
    circleIntegral_eq_of_punctured_ball_shrink hr hr_le_R hcontAnnulus hdiffAnnulus
  have hkernelSphere :
      ∀ w ∈ Metric.sphere z r, gNF w = G w / (w - z) := by
    intro w hw
    have hw_norm : ‖w - z‖ = r := by
      simpa [Metric.mem_sphere] using hw
    have hw_ball_NF : w ∈ Metric.ball z δNF := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hw_norm.trans_lt hr_lt_δNF
    have hw_ball_G : w ∈ Metric.ball z δG := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hw_norm.trans_lt hr_lt_δG
    have hw_ne : w ≠ z := Metric.ne_of_mem_sphere hw hr.ne'
    have hGw : gNF w = (w - z) ^ (-1 : ℤ) • G w := by
      exact hδG hw_ball_G (by simpa using hw_ne)
    -- On the small circle, both the normal form and the raw quotient coincide with the same
    -- Cauchy kernel model.
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hGw
  have hcircleSmall :
      ∮ w in C(z, r), gNF w = (2 * Real.pi * Complex.I : ℂ) * G z := by
    have hcongr :
        (∮ w in C(z, r), gNF w) = ∮ w in C(z, r), G w / (w - z) := by
      -- Replace the inner-circle integrand by the explicit simple-pole kernel model.
      refine circleIntegral.integral_congr hr.le ?_
      intro w hw
      exact hkernelSphere w hw
    have hz_ball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
    have hkernel :
        (∮ w in C(z, r), G w / (w - z)) = (2 * Real.pi * Complex.I : ℂ) * G z := by
      -- Cauchy's circle integral formula evaluates the kernel model at the center.
      simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
        hG_diff.circleIntegral_sub_inv_smul hz_ball
    calc
      (∮ w in C(z, r), gNF w) = ∮ w in C(z, r), G w / (w - z) := hcongr
      _ = (2 * Real.pi * Complex.I : ℂ) * G z := hkernel
  have hResidue_eq_G : residue z = G z := by
    have hconst :
        (2 * Real.pi * Complex.I : ℂ) * residue z =
          (2 * Real.pi * Complex.I : ℂ) * G z := by
      calc
        (2 * Real.pi * Complex.I : ℂ) * residue z = ∮ w in C(z, R), gNF w := by
          simpa using hcircleR_nf.symm
        _ = ∮ w in C(z, r), gNF w := hshrink
        _ = (2 * Real.pi * Complex.I : ℂ) * G z := hcircleSmall
    have htwoPiI_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      refine mul_ne_zero ?_ ?_
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    exact mul_left_cancel₀ htwoPiI_ne hconst
  -- Identify the trailing coefficient through the normal form, then replace the circle residue by
  -- the center value `G z` computed above.
  calc
    meromorphicTrailingCoeffAt f z = meromorphicTrailingCoeffAt gNF z := by
      simpa [f, gNF] using (meromorphicTrailingCoeffAt_congr_nhdsNE hEqNF).symm
    _ = G z := hcoeffNF
    _ = residue z := hResidue_eq_G.symm
