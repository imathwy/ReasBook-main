import Mathlib
import cartan.III.section12.SectorArc

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open scoped Interval Topology

/-
Semantic recall note: `lean_leansearch` was unavailable in this environment, so the source-facing
owner was checked against the earlier chapter owner `sectorArcIntegral` for circular arcs and
mathlib's `meromorphicOrderAt`/`meromorphicTrailingCoeffAt` residue API.
-/

/-- Helper for Lemma 4: a point on the positively oriented upper semicircle of radius `r > 0`
lies in the punctured sector `0 ≤ arg z ≤ π`. -/
lemma circleMap_mem_upper_puncturedSector
    {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    circleMap 0 r θ ∈ puncturedSector 0 Real.pi := by
  -- Unpack the punctured sector as the closed sector together with nonvanishing on the arc.
  rw [mem_puncturedSector_iff]
  constructor
  · exact mem_closedSector_iff.2 ⟨r, hr.le, θ, hθ, rfl⟩
  · exact circleMap_ne_center (c := 0) (R := r) (θ := θ) hr.ne'

/-- Helper for Lemma 4: at a simple pole at `0`, the weighted function `z ↦ z * g z` tends to the
canonical residue, so the weighted error tends to `0` on the punctured neighborhood. -/
lemma simple_pole_weighted_tendsto_zero
    {g : ℂ → ℂ}
    (hpole : meromorphicOrderAt g 0 = (-1 : WithTop ℤ)) :
    Tendsto
      (fun z : ℂ ↦ z * g z - meromorphicTrailingCoeffAt g 0)
      (𝓝[≠] (0 : ℂ))
      (𝓝 0) := by
  have hmeromorphic : MeromorphicAt g 0 :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (f := g) (x := 0) (by simp [hpole])
  obtain ⟨u, hu_an, hu_ne, hu_eq⟩ := (meromorphicOrderAt_eq_int_iff hmeromorphic).1 hpole
  have ha : meromorphicTrailingCoeffAt g 0 = u 0 := by
    exact hu_an.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
      (f := g) (x := 0) (n := (-1 : ℤ)) hu_ne hu_eq
  have hu_tendsto :
      Tendsto u (𝓝[≠] (0 : ℂ)) (𝓝 (u 0)) :=
    hu_an.continuousAt.continuousWithinAt.tendsto
  have hweighted' :
      Tendsto
        (fun z : ℂ ↦ z * g z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (meromorphicTrailingCoeffAt g 0)) := by
    -- On the punctured neighborhood, the simple-pole factorization collapses `z * g z` to `u`.
    have hEq :
        (fun z : ℂ ↦ z * g z) =ᶠ[𝓝[≠] (0 : ℂ)] u := by
      filter_upwards [hu_eq, self_mem_nhdsWithin] with z hz hz0
      have hz0' : z ≠ 0 := by simpa using hz0
      rw [hz]
      simp [smul_eq_mul, hz0']
    rw [ha]
    exact hu_tendsto.congr' hEq.symm
  -- Subtract the constant residue to put the weighted remainder in the form used for estimates.
  simpa using
    hweighted'.sub
      (tendsto_const_nhds :
        Tendsto (fun _ : ℂ ↦ meromorphicTrailingCoeffAt g 0) (𝓝[≠] (0 : ℂ))
          (𝓝 (meromorphicTrailingCoeffAt g 0)))

/-- Helper for Lemma 4: a punctured-sector limit at `0` yields a uniform bound on every
sufficiently small upper semicircle. -/
lemma small_upperSemicircle_weighted_bound
    (k : ℂ → ℂ)
    (hlim : Tendsto k (nhdsWithin 0 (puncturedSector 0 Real.pi)) (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃r θ : ℝ⦄, 0 < r → r < δ → θ ∈ Set.Icc 0 Real.pi →
      ‖k (circleMap 0 r θ)‖ < ε := by
  -- Convert the punctured-sector limit into the usual metric `ε`-`δ` estimate.
  obtain ⟨δ, hδ_pos, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds.1 hlim) ε hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro r θ hr hrδ hθ
  have hmem : circleMap 0 r θ ∈ puncturedSector 0 Real.pi :=
    circleMap_mem_upper_puncturedSector hr hθ
  have hdist : dist (circleMap 0 r θ) 0 < δ := by
    simpa [dist_eq_norm, sub_zero, norm_circleMap_zero, abs_of_pos hr] using hrδ
  simpa [dist_eq_norm, sub_zero] using hδ hmem hdist

/-- Helper for Lemma 4: if the weighted remainder is uniformly bounded by `M` on the upper
semicircle of radius `r`, then its contour contribution is bounded by `π M`. -/
lemma norm_upperSemicircle_remainder_le_pi_mul_bound
    (k : ℂ → ℂ) (r M : ℝ)
    (hM : ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi, ‖k (circleMap 0 r θ)‖ ≤ M) :
    ‖∫ θ in (0 : ℝ)..Real.pi, Complex.I * k (circleMap 0 r θ)‖ ≤ Real.pi * M := by
  have hbound :
      ‖∫ θ in (0 : ℝ)..Real.pi, Complex.I * k (circleMap 0 r θ)‖
        ≤ ∫ θ in (0 : ℝ)..Real.pi, M := by
    refine
      intervalIntegral.norm_integral_le_of_norm_le
        (μ := MeasureTheory.volume) Real.pi_pos.le ?_ intervalIntegrable_const
    filter_upwards with θ
    intro hθ
    simpa [norm_mul] using hM θ (Set.Ioc_subset_Icc_self hθ)
  -- Evaluate the constant integral to identify the angular length as `π`.
  calc
    ‖∫ θ in (0 : ℝ)..Real.pi, Complex.I * k (circleMap 0 r θ)‖
      ≤ ∫ θ in (0 : ℝ)..Real.pi, M := hbound
    _ = Real.pi * M := by simp [intervalIntegral.integral_const]

/-- Lemma 4: if `z = 0` is a simple pole of `g(z)`, then the contour integrals of `g` along the
positively oriented upper semicircles `γ(ε)` tend to `π i` times the residue of `g` at `0` as
`ε → 0+`. -/
theorem upperSemicircleIntegralAroundZero_tendsto_pi_I_mul_residue_of_simple_pole
    {g : ℂ → ℂ}
    (hpole : meromorphicOrderAt g 0 = (-1 : WithTop ℤ)) :
    Tendsto
      (fun ε : ℝ ↦ sectorArcIntegral g ε 0 Real.pi)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((Real.pi * Complex.I : ℂ) * meromorphicTrailingCoeffAt g 0)) := by
  let a : ℂ := meromorphicTrailingCoeffAt g 0
  let remainderIntegral : ℝ → ℂ := fun r ↦
    ∫ θ in (0 : ℝ)..Real.pi, Complex.I * (circleMap 0 r θ * g (circleMap 0 r θ) - a)
  have hweighted :
      Tendsto
        (fun z : ℂ ↦ z * g z - a)
        (nhdsWithin 0 (puncturedSector 0 Real.pi))
        (nhds 0) := by
    -- Restrict the punctured-neighborhood weighted limit to the upper punctured sector.
    simpa [a] using
      (simple_pole_weighted_tendsto_zero (g := g) hpole).mono_left
        (nhdsWithin_mono 0 fun z hz ↦ (mem_puncturedSector_iff.1 hz).2)
  have hrem :
      Tendsto remainderIntegral (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    -- Estimate the remainder exactly as in the source proof: make `z * g z - a` uniformly small
    -- on small upper semicircles, then multiply by the fixed angular length `π`.
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    let η := ε / (Real.pi + 1)
    have hη_pos : 0 < η := by
      dsimp [η]
      positivity
    obtain ⟨δ, hδ_pos, hδ⟩ :=
      small_upperSemicircle_weighted_bound (k := fun z : ℂ ↦ z * g z - a) hweighted hη_pos
    refine ⟨δ, hδ_pos, ?_⟩
    intro r hr hrδ
    have hr_pos : 0 < r := by simpa using hr
    have hrδ' : r < δ := by
      simpa [Real.dist_eq, abs_of_pos hr_pos] using hrδ
    have harc :
        ‖remainderIntegral r‖ ≤ Real.pi * η := by
      -- Bound the interval integral by the supremum norm of the weighted remainder on the arc.
      dsimp [remainderIntegral]
      refine norm_upperSemicircle_remainder_le_pi_mul_bound
        (k := fun z : ℂ ↦ z * g z - a) r η ?_
      intro θ hθ
      exact le_of_lt (hδ hr_pos hrδ' hθ)
    have hfrac_lt_one : Real.pi / (Real.pi + 1) < 1 := by
      have hnum_lt : Real.pi < Real.pi + 1 := by linarith
      exact (div_lt_one (by positivity)).2 hnum_lt
    have hlt : Real.pi * η < ε := by
      calc
        Real.pi * η = ε * (Real.pi / (Real.pi + 1)) := by
          dsimp [η]
          ring
        _ < ε * 1 := by
          exact mul_lt_mul_of_pos_left hfrac_lt_one hε
        _ = ε := by ring
    simpa [remainderIntegral, dist_eq_norm, sub_zero] using lt_of_le_of_lt harc hlt
  have hmeromorphic : MeromorphicAt g 0 :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (f := g) (x := 0) (by simp [hpole])
  obtain ⟨u, hu_an, hu_ne, hu_eq⟩ := (meromorphicOrderAt_eq_int_iff hmeromorphic).1 hpole
  have ha : a = u 0 := by
    -- Identify the coefficient in the simple-pole factorization with the canonical residue.
    simpa [a] using
      hu_an.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
        (f := g) (x := 0) (n := (-1 : ℤ)) hu_ne hu_eq
  have hu_ball :
      ∃ ρ : ℝ, 0 < ρ ∧ AnalyticOnNhd ℂ u (Metric.ball 0 ρ) :=
    hu_an.exists_ball_analyticOnNhd
  have hdecomp_eventually :
      ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
        sectorArcIntegral g r 0 Real.pi = remainderIntegral r + (Real.pi * Complex.I) * a := by
    rcases hu_ball with ⟨ρ, hρ_pos, hρ_an⟩
    rw [eventually_nhdsWithin_iff] at hu_eq
    rcases Metric.mem_nhds_iff.1 hu_eq with ⟨δ₀, hδ₀_pos, hδ₀⟩
    let δ : ℝ := min δ₀ ρ
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact lt_min hδ₀_pos hρ_pos
    have hsmall :
        Set.Ioi (0 : ℝ) ∩ Set.Iio δ ∈ 𝓝[>] (0 : ℝ) := by
      have hδ_mem : Set.Iio δ ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hδ_pos
      exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hδ_mem)
    filter_upwards [hsmall] with r hr
    have hr_pos : 0 < r := hr.1
    have hr_ltδ : r < δ := hr.2
    have hr_ltρ : r < ρ := by
      exact lt_of_lt_of_le hr_ltδ (min_le_right _ _)
    have hu_arc :
        ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
          g (circleMap 0 r θ) = (circleMap 0 r θ) ^ (-1 : ℤ) * u (circleMap 0 r θ) := by
      intro θ hθ
      have hr_ltδ₀ : r < δ₀ := by
        exact lt_of_lt_of_le hr_ltδ (min_le_left _ _)
      have hball : circleMap 0 r θ ∈ Metric.ball 0 δ₀ := by
        simp [Metric.mem_ball, dist_eq_norm, sub_zero, norm_circleMap_zero, abs_of_pos hr_pos,
          hr_ltδ₀]
      simpa [smul_eq_mul, sub_zero] using
        (hδ₀ hball) (circleMap_ne_center (c := 0) (R := r) (θ := θ) hr_pos.ne')
    have hu_cont :
        Continuous fun θ : ℝ ↦ u (circleMap 0 r θ) := by
      have hu_ball_cont : ContinuousOn u (Metric.ball 0 ρ) := hρ_an.continuousOn
      refine hu_ball_cont.comp_continuous (continuous_circleMap 0 r) ?_
      intro θ
      simp [Metric.mem_ball, dist_eq_norm, sub_zero, norm_circleMap_zero, abs_of_pos hr_pos, hr_ltρ]
    have hInt_uDiff :
        IntervalIntegrable
          (fun θ : ℝ ↦ Complex.I * (u (circleMap 0 r θ) - a))
          MeasureTheory.volume
          0
          Real.pi := by
      -- After rewriting by the analytic numerator `u`, the remainder integrand is continuous.
      apply Continuous.intervalIntegrable
      exact continuous_const.mul (hu_cont.sub continuous_const)
    have hInt_const :
        IntervalIntegrable (fun θ : ℝ ↦ Complex.I * a) MeasureTheory.volume 0 Real.pi :=
      intervalIntegrable_const
    rw [sectorArcIntegral_def]
    calc
      ∫ θ in (0 : ℝ)..Real.pi, Complex.I * circleMap 0 r θ * g (circleMap 0 r θ)
          = ∫ θ in (0 : ℝ)..Real.pi, Complex.I * u (circleMap 0 r θ) := by
              refine intervalIntegral.integral_congr ?_
              intro θ hθ
              have hfactor := hu_arc θ (by simpa [Set.uIcc_of_le Real.pi_pos.le] using hθ)
              have hne : circleMap 0 r θ ≠ 0 :=
                circleMap_ne_center (c := 0) (R := r) (θ := θ) hr_pos.ne'
              have hmul :
                  circleMap 0 r θ * g (circleMap 0 r θ) = u (circleMap 0 r θ) := by
                rw [hfactor]
                simp [hne]
              simpa [mul_assoc] using congrArg (fun w : ℂ ↦ Complex.I * w) hmul
      _ = ∫ θ in (0 : ℝ)..Real.pi,
            (Complex.I * (u (circleMap 0 r θ) - a) + Complex.I * a) := by
              refine intervalIntegral.integral_congr ?_
              intro θ hθ
              rw [ha]
              ring
      _ = (∫ θ in (0 : ℝ)..Real.pi, Complex.I * (u (circleMap 0 r θ) - a)) +
            Complex.I * (Real.pi * a) := by
              rw [intervalIntegral.integral_add hInt_uDiff hInt_const]
              rw [intervalIntegral.integral_const_mul]
              simp [intervalIntegral.integral_const]
      _ = remainderIntegral r + (Real.pi * Complex.I) * a := by
              have hrem_eq :
                  Complex.I * ∫ θ in (0 : ℝ)..Real.pi, (u (circleMap 0 r θ) - a) =
                    remainderIntegral r := by
                    dsimp [remainderIntegral]
                    rw [intervalIntegral.integral_const_mul]
                    apply congrArg
                    refine intervalIntegral.integral_congr ?_
                    intro θ hθ
                    have hfactor := hu_arc θ (by simpa [Set.uIcc_of_le Real.pi_pos.le] using hθ)
                    have hne : circleMap 0 r θ ≠ 0 :=
                      circleMap_ne_center (c := 0) (R := r) (θ := θ) hr_pos.ne'
                    have hmul :
                        circleMap 0 r θ * g (circleMap 0 r θ) = u (circleMap 0 r θ) := by
                      rw [hfactor]
                      simp [hne]
                    simp [hmul]
              have hmulInt :
                  ∫ θ in (0 : ℝ)..Real.pi, Complex.I * (u (circleMap 0 r θ) - a) =
                    Complex.I * ∫ θ in (0 : ℝ)..Real.pi, (u (circleMap 0 r θ) - a) := by
                rw [intervalIntegral.integral_const_mul]
              calc
                (∫ θ in (0 : ℝ)..Real.pi, Complex.I * (u (circleMap 0 r θ) - a)) +
                    Complex.I * (Real.pi * a)
                    = (Complex.I * ∫ θ in (0 : ℝ)..Real.pi, (u (circleMap 0 r θ) - a)) +
                        Complex.I * (Real.pi * a) := by
                            exact congrArg (fun z : ℂ => z + Complex.I * (Real.pi * a)) hmulInt
                _ = (remainderIntegral r) + Complex.I * (Real.pi * a) := by
                      exact congrArg (fun z : ℂ => z + Complex.I * (Real.pi * a)) hrem_eq
                _ = remainderIntegral r + (Real.pi * Complex.I) * a := by ring
  have htarget :
      Tendsto
        (fun r : ℝ ↦ remainderIntegral r + (Real.pi * Complex.I) * a)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((Real.pi * Complex.I) * a)) := by
    simpa [add_comm, add_left_comm, add_assoc] using tendsto_const_nhds.add hrem
  -- Replace the remainder-plus-constant expression by the original sector-arc integral.
  exact htarget.congr' <| hdecomp_eventually.mono fun _ hr ↦ hr.symm
