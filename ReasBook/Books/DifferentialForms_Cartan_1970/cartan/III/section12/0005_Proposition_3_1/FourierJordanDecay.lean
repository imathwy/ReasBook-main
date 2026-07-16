import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.cartan.III.section12.SectorArc
import DifferentialForms_Cartan_1970.cartan.III.section11.frozen_0003_Theorem_III_5_extra_2

noncomputable section

open Filter
open MeasureTheory
open UpperHalfPlane
open scoped BigOperators Interval Topology

section

variable {f : ℂ → ℂ} {s : Finset ℂ}

/-- Helper for Proposition 3.1: every point on the upper semicircle belongs to the closed upper
half-plane. -/
lemma circleMap_mem_closed_upper_half_plane
    {r θ : ℝ} (hr : 0 ≤ r) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    0 ≤ (circleMap 0 r θ).im := by
  -- The semicircle angle range gives `sin θ ≥ 0`, and the radius is nonnegative.
  rw [circleMap_zero_im]
  exact mul_nonneg hr (Real.sin_nonneg_of_mem_Icc hθ)

/-- Helper for Proposition 3.1: on the upper semicircle with nonnegative radius, the norm of
`circleMap 0 r θ` is exactly `r`. -/
lemma norm_circleMap_upper_semicircle
    {r θ : ℝ} (hr : 0 ≤ r) :
    ‖circleMap 0 r θ‖ = r := by
  -- On nonnegative radii, the absolute value in `norm_circleMap_zero` simplifies.
  rw [norm_circleMap_zero, abs_of_nonneg hr]

/-- Helper for Proposition 3.1: the cocompact decay hypothesis on the closed upper half-plane
gives uniform decay of `f` along the whole upper semicircle `0 ≤ θ ≤ π` as the radius tends to
infinity. -/
lemma upper_semicircle_uniform_decay_of_cocompact
    (hdecay :
      Tendsto
        (fun z : {z : ℂ // 0 ≤ z.im} ↦ f z.1)
        (cocompact {z : ℂ // 0 ≤ z.im})
        (𝓝 0)) :
    TendstoUniformlyOn
      (fun (r : ℝ) θ ↦ f (circleMap 0 r θ))
      0
      atTop
      (Set.Icc 0 Real.pi) := by
  refine Metric.tendstoUniformlyOn_iff.2 ?_
  intro ε hε
  have hsmall :
      {z : {z : ℂ // 0 ≤ z.im} | ‖f z.1‖ < ε} ∈
        cocompact {z : ℂ // 0 ≤ z.im} := by
    -- Turn the cocompact limit into an eventual norm bound on the closed upper half-plane.
    simpa [dist_eq_norm] using (Metric.tendsto_nhds.1 hdecay) ε hε
  obtain ⟨K, hKcompact, hKsubset⟩ := mem_cocompact.1 hsmall
  obtain ⟨R, hRbound⟩ :=
    (hKcompact.image continuous_subtype_val).isBounded.exists_norm_le
  filter_upwards [Filter.eventually_ge_atTop (max 0 (R + 1))] with r hr θ hθ
  have hr_nonneg : 0 ≤ r := le_trans (le_max_left 0 (R + 1)) hr
  let zθ : {z : ℂ // 0 ≤ z.im} :=
    ⟨circleMap 0 r θ, by
      -- Points on the upper semicircle stay in the closed upper half-plane.
      exact circleMap_mem_closed_upper_half_plane hr_nonneg hθ⟩
  have hz_not_mem : zθ ∉ K := by
    -- Large radius excludes the point from the fixed compact obstruction set.
    intro hzK
    have hz_image : (zθ : ℂ) ∈ Subtype.val '' K := ⟨zθ, hzK, rfl⟩
    have hz_le : ‖(zθ : ℂ)‖ ≤ R := hRbound _ hz_image
    have hz_gt : R < ‖(zθ : ℂ)‖ := by
      calc
        R < R + 1 := by linarith
        _ ≤ r := by
          exact le_trans (le_max_right 0 (R + 1)) hr
        _ = ‖circleMap 0 r θ‖ := by
          rw [norm_circleMap_upper_semicircle hr_nonneg]
    exact (not_le_of_gt hz_gt) hz_le
  have hz_small : ‖f zθ.1‖ < ε := by
    exact hKsubset (by simpa using hz_not_mem)
  simpa [dist_eq_norm] using hz_small

/-- Helper for Proposition 3.1: on the upper semicircle, the damping integral
`∫_0^π exp (-r sin θ) r dθ` is bounded above by `π`. -/
theorem exp_neg_sin_mul_intervalIntegral_le_pi
    {r : ℝ} (hr : 0 ≤ r) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-r * Real.sin θ) * r ≤ Real.pi := by
  let g : ℝ → ℝ := fun θ ↦ Real.exp (-r * Real.sin θ) * r
  have hg_cont : Continuous g := by
    -- The damping kernel is continuous on the whole semicircle.
    fun_prop
  have hg_int_left : IntervalIntegrable g MeasureTheory.volume 0 (Real.pi / 2) := by
    exact hg_cont.intervalIntegrable _ _
  have hg_int_right : IntervalIntegrable g MeasureTheory.volume (Real.pi / 2) Real.pi := by
    exact hg_cont.intervalIntegrable _ _
  have hsymm :
      ∫ θ in (Real.pi / 2)..Real.pi, g θ = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
    -- Reflect the second half of the interval using `θ ↦ π - θ`.
    calc
      ∫ θ in (Real.pi / 2)..Real.pi, g θ
          = ∫ θ in (Real.pi / 2)..Real.pi, g (Real.pi - θ) := by
            refine intervalIntegral.integral_congr_ae ?_
            filter_upwards with θ
            simp [g, Real.sin_pi_sub]
      _ = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
            have hpi_half : Real.pi - Real.pi / 2 = Real.pi / 2 := by
              ring
            rw [intervalIntegral.integral_comp_sub_left]
            simp [hpi_half]
  have hleft_bound : ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ ≤ Real.pi / 2 := by
    have hcomparison_int :
        IntervalIntegrable
          (fun θ : ℝ ↦ Real.exp (-(2 / Real.pi * r) * θ) * r)
          MeasureTheory.volume
          0
          (Real.pi / 2) := by
      -- The comparison kernel is also continuous on the compact interval.
      have hcomparison_cont :
          Continuous (fun θ : ℝ ↦ Real.exp (-(2 / Real.pi * r) * θ) * r) := by
        fun_prop
      exact hcomparison_cont.intervalIntegrable _ _
    have hcomparison :
        ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ ≤
          ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (-(2 / Real.pi * r) * θ) * r := by
      -- Jordan's inequality gives the linear lower bound on `sin`.
      refine intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := Real.pi / 2)
        (by positivity) hg_int_left hcomparison_int ?_
      intro θ hθ
      have hsin : 2 / Real.pi * θ ≤ Real.sin θ :=
        Real.mul_le_sin hθ.1 hθ.2
      have hexp :
          Real.exp (-r * Real.sin θ) ≤ Real.exp (-(2 / Real.pi * r) * θ) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hsin, hr]
      exact mul_le_mul_of_nonneg_right hexp hr
    rcases eq_or_lt_of_le hr with rfl | hrpos
    · simpa [g]
        using (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    · let c : ℝ := -(2 / Real.pi * r)
      have hc : c ≠ 0 := by
        dsimp [c]
        exact neg_ne_zero.mpr <| mul_ne_zero (div_ne_zero two_ne_zero Real.pi_ne_zero) hrpos.ne'
      have hc_pi : c * (Real.pi / 2) = -r := by
        dsimp [c]
        field_simp [Real.pi_ne_zero]
      have hrc : r * c⁻¹ = -(Real.pi / 2) := by
        dsimp [c]
        field_simp [Real.pi_ne_zero, hrpos.ne']
      calc
        ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ
            ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (c * θ) * r := by
                simpa [g, c] using hcomparison
        _ = r * ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp (c * θ) := by
              rw [intervalIntegral.integral_mul_const]
              ring
        _ = r * (c⁻¹ * ∫ x in c * (0 : ℝ)..c * (Real.pi / 2), Real.exp x) := by
              simpa [smul_eq_mul] using
                congrArg (fun x : ℝ => r * x)
                  (intervalIntegral.integral_comp_mul_left (f := Real.exp) (a := (0 : ℝ))
                    (b := Real.pi / 2) (c := c) hc)
        _ = r * (c⁻¹ * (Real.exp (c * (Real.pi / 2)) - 1)) := by
              rw [integral_exp, mul_zero, Real.exp_zero]
        _ = Real.pi / 2 * (1 - Real.exp (-r)) := by
              rw [hc_pi]
              calc
                r * (c⁻¹ * (Real.exp (-r) - 1))
                    = (r * c⁻¹) * (Real.exp (-r) - 1) := by ring
                _ = -(Real.pi / 2) * (Real.exp (-r) - 1) := by rw [hrc]
                _ = Real.pi / 2 * (1 - Real.exp (-r)) := by ring
        _ ≤ Real.pi / 2 := by
              have hexp_nonneg : 0 ≤ Real.exp (-r) := Real.exp_nonneg (-r)
              nlinarith [Real.pi_pos]
  have hsplit :
      (∫ θ in (0 : ℝ)..(Real.pi / 2), g θ) + ∫ θ in (Real.pi / 2)..Real.pi, g θ =
        ∫ θ in (0 : ℝ)..Real.pi, g θ := by
    -- Split the upper semicircle into the two symmetric halves.
    simpa using intervalIntegral.integral_add_adjacent_intervals hg_int_left hg_int_right
  have hdouble :
      2 * ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ ≤ 2 * (Real.pi / 2) := by
    linarith [hleft_bound]
  let I : ℝ := ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ
  have hIbound : 2 * I ≤ 2 * (Real.pi / 2) := by
    simpa [I] using hdouble
  calc
    ∫ θ in (0 : ℝ)..Real.pi, g θ
        = I + ∫ θ in (Real.pi / 2)..Real.pi, g θ := by
            simpa [I] using hsplit.symm
    _ = I + I := by
          rw [hsymm]
    _ = 2 * I := by
          ring
    _ ≤ 2 * (Real.pi / 2) := hIbound
    _ = Real.pi := by ring

/-- Helper for Proposition 3.1: the real embedding `x ↦ x : ℂ` is not eventually constant on any
real neighborhood, so codiscrete sets on the real axis pull back through the analytic inclusion. -/
lemma not_eventuallyConst_ofReal_nhds (x : ℝ) :
    ¬ Filter.EventuallyConst (fun y : ℝ ↦ (y : ℂ)) (𝓝 x) := by
  -- Differentiate an eventual constant representative; `ofReal` has derivative `1`, not `0`.
  intro hconst
  obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.mp hconst
  have hderiv : deriv (fun y : ℝ ↦ (y : ℂ)) x = 0 := by
    simpa using hc.deriv.eq_of_nhds
  have hderiv' : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = deriv (fun y : ℝ ↦ (y : ℂ)) x := by
        symm
        exact (Complex.ofRealCLM.hasDerivAt (x := x)).deriv
      _ = 0 := hderiv
  exact one_ne_zero hderiv'

/-- Helper for Proposition 3.1: along the real segment `[-r, r]`, the literal integrand and the
normal-form integrand differ only on a codiscrete subset, so interval integrals may later be
rewritten between them. -/
lemma real_segment_mul_exp_codiscrete_eq_normalForm
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im}) {r : ℝ} :
    (fun x : ℝ ↦ f (x : ℂ) * Complex.exp (Complex.I * x))
      =ᶠ[Filter.codiscreteWithin (Ι (-r) r)]
      (fun x : ℝ ↦
        toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} (x : ℂ) *
          Complex.exp (Complex.I * x)) := by
  let U : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let I : Set ℝ := Ι (-r) r
  have hsubset : (fun x : ℝ ↦ (x : ℂ)) '' I ⊆ U := by
    -- Real points lie on the boundary line `im z = 0`, hence inside the closed upper half-plane.
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    simp [U]
  have hs_eq :
      {z : ℂ | f z = toMeromorphicNFOn f U z} ∈
        Filter.codiscreteWithin ((fun x : ℝ ↦ (x : ℂ)) '' I) := by
    -- Restrict the global normal-form codiscrete equality to the real interval image.
    exact (toMeromorphicNFOn_eqOn_codiscrete (U := U) hmeromorphic).filter_mono
      (Filter.codiscreteWithin_mono hsubset)
  have hpull :
      {x : ℝ | f (x : ℂ) = toMeromorphicNFOn f U (x : ℂ)} ∈
        Filter.codiscreteWithin I := by
    -- Pull the codiscrete equality back through the analytic embedding `ℝ ↪ ℂ`.
    simpa [I] using
      (Complex.ofRealCLM.analyticOnNhd I).preimage_mem_codiscreteWithin
        (fun x hx ↦ not_eventuallyConst_ofReal_nhds x)
        hs_eq
  -- Multiply the codiscrete pointwise equality by the common exponential factor.
  filter_upwards [hpull] with x hx
  simp [U, hx]

/-- Helper for Proposition 3.1: along the upper semicircle, the literal weighted arc integrand and
the corresponding normal-form arc integrand differ only on a codiscrete subset of the parameter
interval. -/
lemma upper_semicircle_mul_exp_codiscrete_eq_normalForm
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im}) {r : ℝ} (hr : 0 < r) :
    (fun θ : ℝ ↦
      Complex.I * circleMap 0 r θ *
        (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ)))
      =ᶠ[Filter.codiscreteWithin (Ι (0 : ℝ) Real.pi)]
      (fun θ : ℝ ↦
        Complex.I * circleMap 0 r θ *
          (toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} (circleMap 0 r θ) *
            Complex.exp (Complex.I * circleMap 0 r θ))) := by
  let U : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let I : Set ℝ := Ι (0 : ℝ) Real.pi
  have hsubset : circleMap 0 r '' I ⊆ U := by
    -- Points of the upper-arc parameter interval satisfy `sin θ ≥ 0`, so the image stays in `U`.
    intro z hz
    rcases hz with ⟨θ, hθ, rfl⟩
    have hθ' : θ ∈ Set.Icc 0 Real.pi := by
      have hθIoc : θ ∈ Set.Ioc (0 : ℝ) Real.pi := by
        simpa [I, Set.uIoc_of_le Real.pi_pos.le] using hθ
      exact ⟨le_of_lt hθIoc.1, hθIoc.2⟩
    rw [Set.mem_setOf_eq, circleMap_zero_im]
    exact mul_nonneg hr.le (Real.sin_nonneg_of_mem_Icc hθ')
  have hs_eq :
      {z : ℂ | f z = toMeromorphicNFOn f U z} ∈
        Filter.codiscreteWithin (circleMap 0 r '' I) := by
    -- Restrict the normal-form codiscrete equality to the actual upper semicircle image.
    exact (toMeromorphicNFOn_eqOn_codiscrete (U := U) hmeromorphic).filter_mono
      (Filter.codiscreteWithin_mono hsubset)
  have hpull :
      {θ : ℝ | f (circleMap 0 r θ) = toMeromorphicNFOn f U (circleMap 0 r θ)} ∈
        Filter.codiscreteWithin I := by
    -- Pull back through the analytic circle parametrization; positive radius rules out local constancy.
    simpa [I] using
      ((analyticOnNhd_circleMap 0 r).mono (by intro x hx; simp)).preimage_mem_codiscreteWithin
        (fun θ hθ ↦ by
          intro hconst
          obtain ⟨a, ha⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.mp hconst
          have := ha.deriv.eq_of_nhds
          simp [hr.ne'] at this)
        hs_eq
  -- Multiply the codiscrete pointwise equality by the common sector-arc weight.
  filter_upwards [hpull] with θ hθ
  simp [U, hθ]

/-- Helper for Proposition 3.1: the norm of the weighted upper-semicircle integrand factors into
the norm of `f` times the scalar damping kernel. -/
lemma norm_sectorArc_exp_integrand
    {f : ℂ → ℂ} {r θ : ℝ} (hr : 0 ≤ r) :
    ‖Complex.I * circleMap 0 r θ *
        (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ))‖ =
      ‖f (circleMap 0 r θ)‖ * (Real.exp (-r * Real.sin θ) * r) := by
  -- Rewrite the complex norm multiplicatively and expose the imaginary part of `circleMap`.
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    circleMap_zero_im, norm_circleMap_zero, abs_of_nonneg hr]
  ring

/-- Helper for Proposition 3.1: the damping integral over a subinterval of `[0, π]` is bounded by
the full upper-semicircle damping integral. -/
theorem intervalIntegral_exp_neg_sin_mul_le_of_subinterval
    {r θ₁ θ₂ : ℝ} (hr : 0 ≤ r) (hθ₁ : 0 ≤ θ₁) (hθ : θ₁ ≤ θ₂) (hθ₂ : θ₂ ≤ Real.pi) :
    ∫ θ in θ₁..θ₂, Real.exp (-r * Real.sin θ) * r ≤
      ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-r * Real.sin θ) * r := by
  let g : ℝ → ℝ := fun θ ↦ Real.exp (-r * Real.sin θ) * r
  have hg_int : IntervalIntegrable g MeasureTheory.volume 0 Real.pi := by
    -- The damping kernel is continuous on the whole semicircle.
    have hg_cont : Continuous g := by
      fun_prop
    exact hg_cont.intervalIntegrable _ _
  have hg_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Real.pi)] g := by
    filter_upwards with θ
    exact mul_nonneg (Real.exp_nonneg _) hr
  -- Monotonicity on nested intervals compares the subsector with the whole semicircle.
  simpa [g] using
    (intervalIntegral.integral_mono_interval (μ := MeasureTheory.volume) (f := g)
      hθ₁ hθ hθ₂ hg_nonneg hg_int)

/-- Helper for Proposition 3.1: once the weighted upper-semicircle parameter integrand is
eventually interval-integrable, uniform decay of `f` on the arc forces the weighted sector-arc
integral to vanish. -/
theorem sectorArcIntegral_mul_exp_tendsto_zero
    (f : ℂ → ℂ) (θ₁ θ₂ : ℝ)
    (hθ₁ : 0 ≤ θ₁) (hθ : θ₁ ≤ θ₂) (hθ₂ : θ₂ ≤ Real.pi)
    (hint :
      ∀ᶠ r : ℝ in Filter.atTop,
        IntervalIntegrable
          (fun θ : ℝ ↦
            Complex.I * circleMap 0 r θ *
              (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ)))
          MeasureTheory.volume
          θ₁
          θ₂)
    (hlim :
      TendstoUniformlyOn
        (fun (r : ℝ) θ ↦ f (circleMap 0 r θ))
        0
        Filter.atTop
        (Set.Icc θ₁ θ₂)) :
    Filter.Tendsto
      (fun r : ℝ ↦ sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r θ₁ θ₂)
      Filter.atTop
      (nhds 0) := by
  rw [Metric.tendstoUniformlyOn_iff] at hlim
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hsmall :
      ∀ᶠ r : ℝ in Filter.atTop,
        ∀ θ ∈ Set.Icc θ₁ θ₂, ‖f (circleMap 0 r θ)‖ < ε / (2 * Real.pi) := by
    -- Uniform convergence turns into a uniform norm bound on the arc.
    have hε' : 0 < ε / (2 * Real.pi) := by
      positivity
    simpa [dist_eq_norm] using hlim (ε / (2 * Real.pi)) hε'
  filter_upwards [hsmall, Filter.eventually_ge_atTop (0 : ℝ), hint] with r hsmall_r hr hInt
  have hbound_int :
      IntervalIntegrable
        (fun θ : ℝ ↦ (ε / (2 * Real.pi)) * (Real.exp (-r * Real.sin θ) * r))
        MeasureTheory.volume
        θ₁
        θ₂ := by
    -- The scalar comparison kernel is continuous on the fixed angle interval.
    have hbound_cont :
        Continuous
          (fun θ : ℝ ↦ (ε / (2 * Real.pi)) * (Real.exp (-r * Real.sin θ) * r)) := by
      fun_prop
    exact hbound_cont.intervalIntegrable _ _
  have hnorm_lt :
      ‖sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r θ₁ θ₂‖ < ε := by
    -- Rewrite the contour integral and bound it by the scalar Jordan kernel.
    rw [sectorArcIntegral_def]
    calc
      ‖∫ θ in θ₁..θ₂,
          Complex.I * circleMap 0 r θ *
            (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ))‖
          ≤ ∫ θ in θ₁..θ₂,
              ‖Complex.I * circleMap 0 r θ *
                (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ))‖ := by
              exact intervalIntegral.norm_integral_le_integral_norm hθ
      _ ≤ ∫ θ in θ₁..θ₂,
            (ε / (2 * Real.pi)) * (Real.exp (-r * Real.sin θ) * r) := by
            refine intervalIntegral.integral_mono_on hθ hInt.norm hbound_int ?_
            intro θ hθ_mem
            have hsmall_θ :
                ‖f (circleMap 0 r θ)‖ ≤ ε / (2 * Real.pi) := by
              exact (hsmall_r θ hθ_mem).le
            rw [norm_sectorArc_exp_integrand hr]
            exact mul_le_mul_of_nonneg_right hsmall_θ
              (mul_nonneg (Real.exp_nonneg _) hr)
      _ = (ε / (2 * Real.pi)) *
            ∫ θ in θ₁..θ₂, Real.exp (-r * Real.sin θ) * r := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ (ε / (2 * Real.pi)) * Real.pi := by
            refine mul_le_mul_of_nonneg_left ?_ ?_
            · exact
                (intervalIntegral_exp_neg_sin_mul_le_of_subinterval hr hθ₁ hθ hθ₂).trans
                  (exp_neg_sin_mul_intervalIntegral_le_pi hr)
            · positivity
      _ = ε / 2 := by
            field_simp [Real.pi_ne_zero]
      _ < ε := by
            linarith
  simpa [dist_eq_norm] using hnorm_lt

/-- Helper for Proposition 3.1: after reducing the problem to eventual interval-integrability of
the weighted semicircle parameterization, the cocompact decay hypothesis makes the upper-semicircle
contribution tend to `0`. -/
lemma eventually_intervalIntegrable_upper_semicircle_weighted_integrand
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hgood_radius :
      ∀ᶠ r : ℝ in atTop,
        0 < r ∧
          (∀ z ∈ s, ‖z‖ < r) ∧
          (∀ θ ∈ Set.Icc 0 Real.pi, ¬ meromorphicOrderAt f (circleMap 0 r θ) < 0)) :
    ∀ᶠ r : ℝ in Filter.atTop,
      IntervalIntegrable
        (fun θ : ℝ ↦
          Complex.I * circleMap 0 r θ *
            (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ)))
        MeasureTheory.volume
        0
        Real.pi := by
  let U : Set ℂ := {z : ℂ | 0 ≤ z.im}
  filter_upwards [hgood_radius] with r hr
  rcases hr with ⟨hr_pos, -, hboundary⟩
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  let g : ℝ → ℂ := fun θ ↦
    Complex.I * circleMap 0 r θ *
      (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ))
  let gNF : ℝ → ℂ := fun θ ↦
    Complex.I * circleMap 0 r θ *
      (toMeromorphicNFOn f U (circleMap 0 r θ) *
        Complex.exp (Complex.I * circleMap 0 r θ))
  have hcontNF : ContinuousOn gNF (Set.Icc 0 Real.pi) := by
    intro θ hθ
    have hzU : circleMap 0 r θ ∈ U := by
      simpa [U] using circleMap_mem_closed_upper_half_plane hr_nonneg hθ
    have horder_nonneg_f : 0 ≤ meromorphicOrderAt f (circleMap 0 r θ) := by
      -- The large-radius invariant excludes poles all along the upper arc.
      by_contra hneg
      exact hboundary θ hθ (lt_of_not_ge hneg)
    have horder_nonneg_nf :
        0 ≤ meromorphicOrderAt (toMeromorphicNFOn f U) (circleMap 0 r θ) := by
      -- Passing to the normal form preserves the meromorphic order on `U`.
      simpa [U] using
        (show
          0 ≤ meromorphicOrderAt (toMeromorphicNFOn f U) (circleMap 0 r θ) from
            by
              rw [meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := U) hmeromorphic hzU]
              exact horder_nonneg_f)
    have hcont_nf_z :
        ContinuousAt (fun z : ℂ ↦ toMeromorphicNFOn f U z) (circleMap 0 r θ) := by
      -- The normal form is analytic, hence continuous, at every non-pole boundary point.
      let hNF : MeromorphicNFAt (toMeromorphicNFOn f U) (circleMap 0 r θ) :=
        (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := U)) hzU
      exact (hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 horder_nonneg_nf).continuousAt
    have hcont_circle : ContinuousAt (fun t : ℝ ↦ circleMap 0 r t) θ := by
      -- The circle parametrization is real-analytic on the whole line.
      exact (analyticOnNhd_circleMap 0 r θ (by simp)).continuousAt
    have hcont_exp :
        ContinuousAt (fun z : ℂ ↦ Complex.exp (Complex.I * z)) (circleMap 0 r θ) := by
      -- The exponential weight is entire.
      exact ((analyticAt_const.mul analyticAt_id).cexp).continuousAt
    -- Combine the continuous factors of the normal-form arc integrand.
    exact
      ((continuousAt_const.mul hcont_circle).mul
        ((hcont_nf_z.comp hcont_circle).mul (hcont_exp.comp hcont_circle))).continuousWithinAt
  have hIntNF :
      IntervalIntegrable gNF MeasureTheory.volume 0 Real.pi := by
    -- Continuity on the compact angle interval gives interval-integrability.
    exact hcontNF.intervalIntegrable_of_Icc Real.pi_pos.le
  have hEq : g =ᶠ[Filter.codiscreteWithin (Ι (0 : ℝ) Real.pi)] gNF := by
    -- The actual arc integrand and the normal-form arc integrand differ only on a codiscrete set.
    simpa [g, gNF, U] using
      upper_semicircle_mul_exp_codiscrete_eq_normalForm (f := f) hmeromorphic hr_pos
  -- Transfer interval-integrability back to the literal weighted arc integrand.
  exact (intervalIntegrable_congr_codiscreteWithin hEq).mpr hIntNF

/-- Helper for Proposition 3.1: after reducing the problem to eventual interval-integrability of
the weighted semicircle parameterization, the cocompact decay hypothesis makes the upper-semicircle
contribution tend to `0`. -/
lemma upper_semicircle_integral_tendsto_zero_mul_exp
    (hint :
      ∀ᶠ r : ℝ in Filter.atTop,
        IntervalIntegrable
          (fun θ : ℝ ↦
            Complex.I * circleMap 0 r θ *
              (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ)))
          MeasureTheory.volume
          0
          Real.pi)
    (hdecay :
      Tendsto
        (fun z : {z : ℂ // 0 ≤ z.im} ↦ f z.1)
        (cocompact {z : ℂ // 0 ≤ z.im})
        (𝓝 0)) :
    Tendsto
      (fun r : ℝ ↦ sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi)
      atTop
      (𝓝 0) := by
  have huniform :
      TendstoUniformlyOn
        (fun (r : ℝ) θ ↦ f (circleMap 0 r θ))
        0
        atTop
        (Set.Icc 0 Real.pi) := by
    -- Reuse the cocompact-to-uniform bridge already verified above.
    exact upper_semicircle_uniform_decay_of_cocompact (f := f) hdecay
  -- The general arc estimate now applies on the full upper semicircle.
  simpa using
    sectorArcIntegral_mul_exp_tendsto_zero
      (f := f) 0 Real.pi le_rfl Real.pi_pos.le le_rfl hint huniform

end
