import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.III.section11.«0001_Proposition_2_1»
import DifferentialForms_Cartan_1970.III.section12.SectorArc
import DifferentialForms_Cartan_1970.III.section11.frozen_0003_Theorem_III_5_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the `lean_leansearch` tool was unavailable in this runner, so the
-- statement surface was checked directly against mathlib's `MeromorphicOn`,
-- `UpperHalfPlane.upperHalfPlaneSet`, `meromorphicOrderAt`,
-- `meromorphicTrailingCoeffAt`, and interval-integral notation.

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

/-- Helper for Proposition 3.1: for all sufficiently large radii, every pole from the prescribed
finite upper-half-plane set lies strictly inside the upper half-disk, so the outer semicircle is
pole-free. -/
lemma eventually_good_upper_half_disk_radius
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s) :
    ∀ᶠ r : ℝ in atTop,
      0 < r ∧
        (∀ z ∈ s, ‖z‖ < r) ∧
        (∀ θ ∈ Set.Icc 0 Real.pi, ¬ meromorphicOrderAt f (circleMap 0 r θ) < 0) := by
  obtain ⟨B, hB⟩ := (s.finite_toSet.isCompact).isBounded.exists_norm_le
  let R : ℝ := max 1 (B + 1)
  filter_upwards [Filter.eventually_ge_atTop R] with r hr
  have hR_one : 1 ≤ R := le_max_left 1 (B + 1)
  have hr_one : 1 ≤ r := le_trans hR_one hr
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr_one
  have hinside_radius : ∀ z ∈ s, ‖z‖ < r := by
    -- Large radius puts each prescribed pole strictly inside the semicircle.
    intro z hz
    have hz_bound : ‖z‖ ≤ B := hB z hz
    have hz_lt : ‖z‖ + 1 ≤ r := le_trans (le_trans (by linarith) (le_max_right 1 _)) hr
    linarith
  refine ⟨hr_pos, hinside_radius, ?_⟩
  · -- Route correction: split the boundary check into the real endpoints and the open arc.
    intro θ hθ hpole
    have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
    have him_nonneg :
        0 ≤ (circleMap 0 r θ).im :=
      circleMap_mem_closed_upper_half_plane hr_nonneg hθ
    by_cases him_zero : (circleMap 0 r θ).im = 0
    · -- On the real axis, the standing hypothesis `hreal` rules out poles.
      have hreal_point : circleMap 0 r θ = ((circleMap 0 r θ).re : ℂ) := by
        apply Complex.ext <;> simp [him_zero]
      rw [hreal_point] at hpole
      exact hreal (circleMap 0 r θ).re hpole
    · -- In the open upper half-plane, `hpoles` forces the point into `s`, contradicting `‖z‖ = r`.
      have him_ne : 0 ≠ (circleMap 0 r θ).im := by
        intro h
        exact him_zero h.symm
      have him_pos : 0 < (circleMap 0 r θ).im := lt_of_le_of_ne him_nonneg him_ne
      have hmem_s : circleMap 0 r θ ∈ s := by
        exact (hpoles (circleMap 0 r θ)).mp ⟨hpole, by simpa using him_pos⟩
      have hinside : ‖circleMap 0 r θ‖ < r := by
        exact hinside_radius _ hmem_s
      rw [norm_circleMap_upper_semicircle hr_nonneg] at hinside
      exact lt_irrefl _ hinside

/-- Helper for Proposition 3.1: away from the finite pole set `s`, the weighted normal-form
integrand is analytic at every point of the closed upper half-plane. -/
lemma analyticAt_weighted_normal_form_of_mem_upper_half_plane_not_mem_pole_finset
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    {z : ℂ} (hzU : z ∈ {z : ℂ | 0 ≤ z.im}) (hzs : z ∉ s) :
    AnalyticAt ℂ
      (fun w ↦
        toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} w *
          Complex.exp (Complex.I * w))
      z := by
  let U : Set ℂ := {w : ℂ | 0 ≤ w.im}
  have horder_nonneg_f : 0 ≤ meromorphicOrderAt f z := by
    -- A point of `U` outside `s` cannot be a pole: on the boundary this is `hreal`, and in the
    -- open upper half-plane it would contradict the pole-classification hypothesis `hpoles`.
    by_contra hneg
    by_cases him_zero : z.im = 0
    · have hreal_point : z = ((z.re : ℂ)) := by
        apply Complex.ext <;> simp [him_zero]
      rw [hreal_point] at hneg
      exact hreal z.re (lt_of_not_ge hneg)
    · have him_pos : 0 < z.im := lt_of_le_of_ne hzU (Ne.symm him_zero)
      have hmem_s : z ∈ s := by
        exact
          (hpoles z).mp
            ⟨lt_of_not_ge hneg, by simpa [UpperHalfPlane.upperHalfPlaneSet] using him_pos⟩
      exact hzs hmem_s
  have horder_nonneg_nf :
      0 ≤ meromorphicOrderAt (toMeromorphicNFOn f U) z := by
    -- On `U`, passing to the meromorphic normal form preserves the local meromorphic order.
    rw [
      meromorphicOrderAt_toMeromorphicNFOn
        (f := f) (U := U) hmeromorphic (by simpa [U] using hzU)
    ]
    exact horder_nonneg_f
  have hNF : MeromorphicNFAt (toMeromorphicNFOn f U) z :=
    (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := U)) (by simpa [U] using hzU)
  have hanalytic_nf : AnalyticAt ℂ (fun w : ℂ ↦ toMeromorphicNFOn f U w) z := by
    -- The normal form is analytic exactly when its meromorphic order is nonnegative.
    exact hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 horder_nonneg_nf
  -- Multiply by the entire exponential factor to recover the weighted integrand from the source.
  simpa [U] using hanalytic_nf.mul ((analyticAt_const.mul analyticAt_id).cexp)

/-- Helper for Proposition 3.1: a holomorphic kernel of the form `g(z) / (z - a)` realizes the
residue `g(a)` on every small circle contained in both `interior K` and `D`. -/
lemma localResidueCircle_div_sub_of_differentiableOn
    {K D : Set ℂ} {g : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hK : Metric.closedBall a r ⊆ interior K)
    (hD : Metric.closedBall a r ⊆ D)
    (hg : DifferentiableOn ℂ g D) :
    LocalResidueCircle K D (fun z ↦ g z / (z - a)) a (g a) := by
  -- Use the given radius as the source-faithful residue circle and restrict differentiability to
  -- that closed ball.
  refine ⟨r, hr, hK, hD, ?_⟩
  have hg_ball : DifferentiableOn ℂ g (Metric.closedBall a r) := hg.mono hD
  have ha_ball : a ∈ Metric.ball a r := Metric.mem_ball_self hr
  -- The standard small-circle Cauchy kernel integral computes the residue as `g(a)`.
  simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    hg_ball.circleIntegral_sub_inv_smul ha_ball

/-- Helper for Proposition 3.1: on a punctured domain, a differentiable numerator gives a
differentiable simple-pole kernel `g(z) / (z - a)`. -/
lemma differentiableOn_div_sub_of_differentiableOn
    {D : Set ℂ} {g : ℂ → ℂ} {a : ℂ}
    (hg : DifferentiableOn ℂ g D) :
    DifferentiableOn ℂ (fun z ↦ g z / (z - a)) (D \ ({a} : Set ℂ)) := by
  intro z hz
  rcases hz with ⟨hzD, hzA⟩
  have hza : z ≠ a := by
    simpa using hzA
  have hnum :
      DifferentiableWithinAt ℂ g (D \ ({a} : Set ℂ)) z :=
    (hg z hzD).mono (by intro w hw; exact hw.1)
  have hden :
      DifferentiableWithinAt ℂ (fun w : ℂ ↦ w - a) (D \ ({a} : Set ℂ)) z :=
    (differentiableAt_id.sub_const a).differentiableWithinAt.mono
      (by intro w hw; exact Set.mem_univ w)
  -- Away from the center, the denominator does not vanish, so the quotient is holomorphic.
  exact hnum.div hden (sub_ne_zero.mpr hza)

/-- Helper for Proposition 3.1: the weighted meromorphic normal form is itself in meromorphic
normal form at every point of the closed upper half-plane. -/
lemma weighted_normal_form_meromorphicNFAt
    {z : ℂ} (hzU : z ∈ {z : ℂ | 0 ≤ z.im}) :
    MeromorphicNFAt
      (fun w ↦
        toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} w *
          Complex.exp (Complex.I * w))
      z := by
  let U : Set ℂ := {w : ℂ | 0 ≤ w.im}
  have hNF : MeromorphicNFAt (toMeromorphicNFOn f U) z :=
    (meromorphicNFOn_toMeromorphicNFOn (f := f) (U := U)) (by simpa [U] using hzU)
  have hexp :
      AnalyticAt ℂ (fun w : ℂ ↦ Complex.exp (Complex.I * w)) z := by
    -- The exponential weight is entire and never vanishes.
    simpa using ((analyticAt_const.mul analyticAt_id).cexp : AnalyticAt ℂ _ z)
  -- Multiply the normal form by the nonvanishing entire factor `exp (i z)`.
  exact
    (meromorphicNFAt_mul_iff_left (f := toMeromorphicNFOn f U)
      (g := fun w : ℂ ↦ Complex.exp (Complex.I * w))
      (x := z) hexp (Complex.exp_ne_zero _)).2 hNF

/-- Helper for Proposition 3.1: away from the pole finset `s`, the weighted normal-form integrand
is differentiable on the punctured closed upper half-plane. -/
lemma weighted_normal_form_differentiableOn_upper_half_plane_punctured
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s) :
    DifferentiableOn ℂ
      (fun z ↦
        toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} z *
          Complex.exp (Complex.I * z))
      ({z : ℂ | 0 ≤ z.im} \ (↑s : Set ℂ)) := by
  intro z hz
  rcases hz with ⟨hzU, hzs⟩
  -- Pointwise analyticity on the punctured set upgrades immediately to differentiability.
  exact
    (analyticAt_weighted_normal_form_of_mem_upper_half_plane_not_mem_pole_finset
      (f := f) (s := s) hmeromorphic hreal hpoles hzU hzs).differentiableAt.differentiableWithinAt

/-- Helper for Proposition 3.1: the weighted normal form and the literal weighted integrand have
the same trailing coefficient at every point of the closed upper half-plane. -/
lemma meromorphicTrailingCoeffAt_weighted_normal_form_eq
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    {z : ℂ} (hzU : z ∈ {z : ℂ | 0 ≤ z.im}) :
    meromorphicTrailingCoeffAt
        (fun w ↦
          toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} w *
            Complex.exp (Complex.I * w))
        z =
      meromorphicTrailingCoeffAt
        (fun w ↦ f w * Complex.exp (Complex.I * w))
        z := by
  let U : Set ℂ := {w : ℂ | 0 ≤ w.im}
  apply meromorphicTrailingCoeffAt_congr_nhdsNE
  have hEqNF := hmeromorphic.toMeromorphicNFOn_eq_self_on_nhdsNE (by simpa [U] using hzU)
  -- The normal form differs from `f` only at the center, so multiplying by the same entire factor
  -- preserves punctured-neighborhood equality.
  filter_upwards [hEqNF] with w hw
  simp [hw]

/-- Helper for Proposition 3.1: every source-side local residue circle for the literal weighted
integrand is also a local residue circle for the weighted meromorphic normal form, because the two
integrands differ only on a codiscrete subset of each admissible circle. -/
lemma weighted_normal_form_localResidueCircle
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        LocalResidueCircle
          {z : ℂ | 0 ≤ z.im}
          {z : ℂ | 0 ≤ z.im}
          (fun w ↦ f w * Complex.exp (Complex.I * w))
          z
          (residue z)) :
    ∀ z ∈ s,
      LocalResidueCircle
        {z : ℂ | 0 ≤ z.im}
        {z : ℂ | 0 ≤ z.im}
        (fun w ↦
          toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} w *
            Complex.exp (Complex.I * w))
        z
        (residue z) := by
  let U : Set ℂ := {z : ℂ | 0 ≤ z.im}
  intro z hz
  rcases hresidue z hz with ⟨R, hR, hRK, hRD, hcircleR⟩
  refine ⟨R, hR, hRK, hRD, ?_⟩
  have hsphere_subset : Metric.sphere z |R| ⊆ U := by
    intro w hw
    have hw_le : dist w z ≤ R := by
      have hw_eq : dist w z = |R| := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hw
      rw [abs_of_pos hR] at hw_eq
      exact le_of_eq hw_eq
    exact hRD (by simpa [Metric.mem_closedBall] using hw_le)
  have hEq :
      (fun w ↦ toMeromorphicNFOn f U w * Complex.exp (Complex.I * w))
        =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
      (fun w ↦ f w * Complex.exp (Complex.I * w)) := by
    have hEqNF :
        (fun w ↦ toMeromorphicNFOn f U w)
          =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)]
        f := by
      exact
        (toMeromorphicNFOn_eqOn_codiscrete (U := U) hmeromorphic).symm.filter_mono
          (Filter.codiscreteWithin_mono hsphere_subset)
    -- Multiply the codiscrete equality by the common exponential factor.
    filter_upwards [hEqNF] with w hw
    simp [hw]
  -- The circle integral is unchanged under codiscrete modifications of the integrand.
  calc
    (∮ w in C(z, R),
        toMeromorphicNFOn f U w * Complex.exp (Complex.I * w)) =
        ∮ w in C(z, R), f w * Complex.exp (Complex.I * w) := by
          exact circleIntegral.circleIntegral_congr_codiscreteWithin hEq hR.ne'
    _ = (2 * Real.pi * Complex.I : ℂ) * residue z := hcircleR

/-- Helper for Proposition 3.1: once a radius strictly contains every pole from `s`, those poles
all lie in the interior of the corresponding closed upper half-disk. -/
lemma pole_finset_subset_interior_upper_half_disk
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    {r : ℝ}
    (hinside : ∀ z ∈ s, ‖z‖ < r) :
    (↑s : Set ℂ) ⊆ interior ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) := by
  intro z hz
  have hz_norm : ‖z‖ < r := hinside z hz
  have hz_upper : z ∈ upperHalfPlaneSet := ((hpoles z).mpr hz).2
  have hz_im : 0 < z.im := by
    simpa [UpperHalfPlane.upperHalfPlaneSet] using hz_upper
  let V : Set ℂ := Metric.ball (0 : ℂ) r ∩ {w : ℂ | 0 < w.im}
  have hV_open : IsOpen V := by
    -- The strict-radius/strict-imaginary-part model is an open neighborhood inside the semidisk.
    exact Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hV_subset :
      V ⊆ ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) := by
    intro w hw
    have hw_norm : ‖w‖ < r := by
      simpa [V, Metric.mem_ball, dist_eq_norm] using hw.1
    constructor
    · exact hw_norm.le
    · exact hw.2.le
  have hzV : z ∈ V := by
    constructor
    · simpa [V, Metric.mem_ball, dist_eq_norm] using hz_norm
    · exact hz_im
  -- Membership in the open model upgrades immediately to interior membership in the semidisk.
  exact ((IsOpen.subset_interior_iff hV_open).2 hV_subset) hzV

/-- Helper for Proposition 3.1: a point with strict radius bound and strictly positive imaginary
part lies in the interior of the closed upper half-disk. -/
lemma mem_interior_upper_half_disk_of_norm_lt_im_pos
    {r : ℝ} {z : ℂ} (hz_norm : ‖z‖ < r) (hz_im : 0 < z.im) :
    z ∈ interior ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) := by
  let V : Set ℂ := Metric.ball (0 : ℂ) r ∩ {w : ℂ | 0 < w.im}
  have hV_open : IsOpen V := by
    -- The strict-radius/strict-imaginary-part model is an open neighborhood inside the semidisk.
    exact Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hV_subset :
      V ⊆ ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) := by
    intro w hw
    have hw_norm : ‖w‖ < r := by
      simpa [V, Metric.mem_ball, dist_eq_norm] using hw.1
    constructor
    · exact hw_norm.le
    · exact hw.2.le
  have hzV : z ∈ V := by
    constructor
    · simpa [V, Metric.mem_ball, dist_eq_norm] using hz_norm
    · exact hz_im
  -- Membership in the same open model upgrades directly to semidisk interior membership.
  exact ((IsOpen.subset_interior_iff hV_open).2 hV_subset) hzV

/-- Helper for Proposition 3.1: the source-facing upper-semicircle path starts at `r`. -/
lemma upper_semicircle_path_source_eq (r : ℝ) :
    (r : ℂ) = circleMap 0 r 0 := by
  -- The angle `0` on `circleMap` is exactly the positive real point of radius `r`.
  simp [circleMap_zero]

/-- Helper for Proposition 3.1: the source-facing upper-semicircle path ends at `-r`. -/
lemma upper_semicircle_path_target_eq (r : ℝ) :
    (-(r : ℂ)) = circleMap 0 r Real.pi := by
  -- The angle `π` on `circleMap` is exactly the negative real point of radius `r`.
  simp [circleMap_zero, Complex.exp_pi_mul_I]

/-- Helper for Proposition 3.1: the explicit upper-semicircle path is the angular segment
`0 ≤ θ ≤ π` mapped through `circleMap`. -/
def upperSemicirclePath (r : ℝ) : Path (r : ℂ) (-(r : ℂ)) :=
  (((Path.segment (0 : ℝ) Real.pi).map (continuous_circleMap 0 r)).cast
    (upper_semicircle_path_source_eq r) (upper_semicircle_path_target_eq r))

/-- Helper for Proposition 3.1: the upper-half-disk boundary path is the real diameter
`[-r, r]` followed by the positively oriented upper semicircle. -/
def upperHalfDiskBoundaryPath (r : ℝ) : Path (-(r : ℂ)) (-(r : ℂ)) :=
  (Path.segment (-(r : ℂ)) (r : ℂ)).trans (upperSemicirclePath r)

/-- Helper for Proposition 3.1: evaluating the explicit upper-semicircle path recovers the usual
parameterization `θ = π t`. -/
@[simp] lemma upperSemicirclePath_apply (r : ℝ) (t : Set.Icc (0 : ℝ) 1) :
    upperSemicirclePath r t = circleMap 0 r (Real.pi * (t : ℝ)) := by
  -- Unfold the casted mapped segment and collapse the affine angle parametrization.
  have hline :
      AffineMap.lineMap (0 : ℝ) Real.pi (t : ℝ) = Real.pi * (t : ℝ) := by
    simpa [mul_comm] using
      (show AffineMap.lineMap (0 : ℝ) Real.pi (t : ℝ) = (t : ℝ) * Real.pi by
        simp [AffineMap.lineMap_apply_module])
  simp [upperSemicirclePath, Path.map_coe, Path.segment_apply, hline]

/-- Helper for Proposition 3.1: the explicit upper-semicircle path covers exactly the radius-`r`
circle with angle parameter in `0 ≤ θ ≤ π`. -/
lemma upper_semicircle_path_range_eq_image_Icc (r : ℝ) :
    Set.range (upperSemicirclePath r) = circleMap 0 r '' Set.Icc 0 Real.pi := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨Real.pi * (t : ℝ), ?_, ?_⟩
    · -- The path parameter `t ∈ [0, 1]` maps into the source angle interval `[0, π]`.
      constructor
      · exact mul_nonneg Real.pi_pos.le t.2.1
      · nlinarith [Real.pi_pos, t.2.2]
    · -- Evaluate the path using the explicit angular parametrization.
      simpa using upperSemicirclePath_apply r t
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨⟨θ / Real.pi, ?_⟩, ?_⟩
    · -- Normalize the angle back to a unit-interval parameter.
      constructor
      · exact div_nonneg hθ.1 Real.pi_pos.le
      · calc
          θ / Real.pi ≤ Real.pi / Real.pi := by
            exact div_le_div_of_nonneg_right hθ.2 Real.pi_pos.le
          _ = 1 := by field_simp [Real.pi_ne_zero]
    · -- The rescaled parameter recovers the original angle exactly.
      have hangle : Real.pi * (θ / Real.pi) = θ := by
        field_simp [Real.pi_ne_zero]
      rw [upperSemicirclePath_apply, hangle]

/-- Helper for Proposition 3.1: the boundary path image splits as the union of the diameter and
upper-semicircle images. -/
lemma upper_half_disk_boundary_path_range_eq_union (r : ℝ) :
    Set.range (upperHalfDiskBoundaryPath r) =
      Set.range (Path.segment (-(r : ℂ)) (r : ℂ)) ∪ Set.range (upperSemicirclePath r) := by
  -- Expand the concatenated boundary path into its two source-facing pieces.
  rw [upperHalfDiskBoundaryPath, Path.trans_range]

/-- Helper for Proposition 3.1: evaluating the horizontal diameter segment reads off the real
affine coordinate `x = (2r)t - r`. -/
lemma upper_half_disk_diameter_path_apply (r : ℝ) (t : Set.Icc (0 : ℝ) 1) :
    Path.segment (-(r : ℂ)) (r : ℂ) t = ((((2 * r) * (t : ℝ) - r : ℝ)) : ℂ) := by
  -- Unfold the segment path and compute its affine line map explicitly on the real axis.
  apply Complex.ext <;> simp [Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg]
  ring

/-- Helper for Proposition 3.1: on the first half of the boundary parameter interval, the
concatenated contour follows the horizontal diameter branch. -/
lemma upper_half_disk_boundary_eq_diameter_of_le_half (r : ℝ)
    {t : Set.Icc (0 : ℝ) 1}
    (ht : (t : ℝ) ≤ 1 / 2) :
    upperHalfDiskBoundaryPath r t = ((((4 * r) * (t : ℝ) - r : ℝ)) : ℂ) := by
  -- On the first half of `Path.trans`, the diameter segment is the active source branch.
  have htrans :
      (upperHalfDiskBoundaryPath r).extend t =
        (Path.segment (-(r : ℂ)) (r : ℂ)).extend (2 * (t : ℝ)) := by
    dsimp [upperHalfDiskBoundaryPath]
    exact
      Path.extend_trans_of_le_half
        (γ₁ := Path.segment (-(r : ℂ)) (r : ℂ))
        (γ₂ := upperSemicirclePath r)
        ht
  have hI : 2 * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [t.2.1, t.2.2, ht]
  calc
    upperHalfDiskBoundaryPath r t = (upperHalfDiskBoundaryPath r).extend t := by
      simpa using (Path.extend_apply (γ := upperHalfDiskBoundaryPath r) t.2)
    _ = (Path.segment (-(r : ℂ)) (r : ℂ)).extend (2 * (t : ℝ)) := htrans
    _ = (Path.segment (-(r : ℂ)) (r : ℂ)) ⟨2 * (t : ℝ), hI⟩ := by
          simpa using
            (Path.extend_apply (γ := Path.segment (-(r : ℂ)) (r : ℂ)) hI)
    _ = ((((2 * r) * (2 * (t : ℝ)) - r : ℝ)) : ℂ) := by
          simpa using upper_half_disk_diameter_path_apply r ⟨2 * (t : ℝ), hI⟩
    _ = ((((4 * r) * (t : ℝ) - r : ℝ)) : ℂ) := by
          congr 1
          ring

/-- Helper for Proposition 3.1: on the second half of the boundary parameter interval, the
concatenated contour follows the upper semicircle branch. -/
lemma upper_half_disk_boundary_eq_arc_of_half_le (r : ℝ)
    {t : Set.Icc (0 : ℝ) 1}
    (ht : 1 / 2 ≤ (t : ℝ)) :
    upperHalfDiskBoundaryPath r t = circleMap 0 r (Real.pi * (2 * (t : ℝ) - 1)) := by
  -- After the midpoint of `Path.trans`, the upper-semicircle branch takes over.
  have htrans :
      (upperHalfDiskBoundaryPath r).extend t =
        (upperSemicirclePath r).extend (2 * (t : ℝ) - 1) := by
    dsimp [upperHalfDiskBoundaryPath]
    exact
      Path.extend_trans_of_half_le
        (γ₁ := Path.segment (-(r : ℂ)) (r : ℂ))
        (γ₂ := upperSemicirclePath r)
        ht
  have hI : 2 * (t : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [t.2.1, t.2.2, ht]
  calc
    upperHalfDiskBoundaryPath r t = (upperHalfDiskBoundaryPath r).extend t := by
      simpa using (Path.extend_apply (γ := upperHalfDiskBoundaryPath r) t.2)
    _ = (upperSemicirclePath r).extend (2 * (t : ℝ) - 1) := htrans
    _ = (upperSemicirclePath r) ⟨2 * (t : ℝ) - 1, hI⟩ := by
          simpa using (Path.extend_apply (γ := upperSemicirclePath r) hI)
    _ = circleMap 0 r
          (Real.pi * ((⟨2 * (t : ℝ) - 1, hI⟩ : Set.Icc (0 : ℝ) 1) : ℝ)) := by
          simpa using upperSemicirclePath_apply r ⟨2 * (t : ℝ) - 1, hI⟩
    _ = circleMap 0 r (Real.pi * (2 * (t : ℝ) - 1)) := by
          simp

/-- Helper for Proposition 3.1: on the first half of the source interval, the real-plane
parametrization of the closed semidisk boundary is exactly the affine diameter model. -/
lemma upper_half_disk_boundary_realCurve_eqOn_diameter_interval (r : ℝ) :
    Set.EqOn
      ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
      (fun t : ℝ ↦ Complex.equivRealProd ((((4 * r) * t - r : ℝ) : ℂ)))
      (Set.Icc (0 : ℝ) (1 / 2)) := by
  intro t ht
  have hI : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact ht.1
    · linarith [ht.2]
  let tI : Set.Icc (0 : ℝ) 1 := ⟨t, hI⟩
  have hbranch :
      upperHalfDiskBoundaryPath r tI = ((((4 * r) * t - r : ℝ)) : ℂ) := by
    -- On the first half-interval, the boundary path is the explicit diameter branch.
    simpa [tI] using upper_half_disk_boundary_eq_diameter_of_le_half r (t := tI) ht.2
  -- Replace `realCurve` by the original path evaluation before using the explicit branch formula.
  calc
    (upperHalfDiskBoundaryPath r).toClosedPath.realCurve t
        = Complex.equivRealProd
            (((upperHalfDiskBoundaryPath r).toClosedPath.toPath).extend t) := by
            rfl
    _ = Complex.equivRealProd (((upperHalfDiskBoundaryPath r).toClosedPath.toPath) tI) := by
          rw [Path.extend_apply (γ := (upperHalfDiskBoundaryPath r).toClosedPath.toPath) hI]
    _ = Complex.equivRealProd (upperHalfDiskBoundaryPath r tI) := by
          simpa [Path.toClosedPath] using
            congrArg Complex.equivRealProd
              (ClosedPath.toPath_apply ((upperHalfDiskBoundaryPath r).toClosedPath) tI)
    _ = Complex.equivRealProd ((((4 * r) * t - r : ℝ) : ℂ)) := by
          rw [hbranch]

/-- Helper for Proposition 3.1: on the second half of the source interval, the real-plane
parametrization of the closed semidisk boundary is exactly the upper-semicircle model. -/
lemma upper_half_disk_boundary_realCurve_eqOn_arc_interval (r : ℝ) :
    Set.EqOn
      ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
      (fun t : ℝ ↦ Complex.equivRealProd (circleMap 0 r (Real.pi * (2 * t - 1))))
      (Set.Icc (1 / 2 : ℝ) 1) := by
  intro t ht
  have hI : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · linarith [ht.1]
    · exact ht.2
  let tI : Set.Icc (0 : ℝ) 1 := ⟨t, hI⟩
  have hbranch :
      upperHalfDiskBoundaryPath r tI = circleMap 0 r (Real.pi * (2 * t - 1)) := by
    -- On the second half-interval, the boundary path is the explicit upper-semicircle branch.
    simpa [tI] using upper_half_disk_boundary_eq_arc_of_half_le r (t := tI) ht.1
  -- As on the diameter branch, first normalize `realCurve` back to the original path.
  calc
    (upperHalfDiskBoundaryPath r).toClosedPath.realCurve t
        = Complex.equivRealProd
            (((upperHalfDiskBoundaryPath r).toClosedPath.toPath).extend t) := by
            rfl
    _ = Complex.equivRealProd (((upperHalfDiskBoundaryPath r).toClosedPath.toPath) tI) := by
          rw [Path.extend_apply (γ := (upperHalfDiskBoundaryPath r).toClosedPath.toPath) hI]
    _ = Complex.equivRealProd (upperHalfDiskBoundaryPath r tI) := by
          simpa [Path.toClosedPath] using
            congrArg Complex.equivRealProd
              (ClosedPath.toPath_apply ((upperHalfDiskBoundaryPath r).toClosedPath) tI)
    _ = Complex.equivRealProd (circleMap 0 r (Real.pi * (2 * t - 1))) := by
          rw [hbranch]

/-- Helper for Proposition 3.1: the semidisk boundary `realCurve` agrees with the explicit
diameter and semicircle models on the two source subintervals. -/
lemma upper_half_disk_boundary_realCurve_eqOn_piece_intervals (r : ℝ) :
    Set.EqOn
      ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
      (fun t : ℝ ↦ Complex.equivRealProd ((((4 * r) * t - r : ℝ) : ℂ)))
      (Set.Icc (0 : ℝ) (1 / 2)) ∧
      Set.EqOn
        ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
        (fun t : ℝ ↦ Complex.equivRealProd (circleMap 0 r (Real.pi * (2 * t - 1))))
        (Set.Icc (1 / 2 : ℝ) 1) := by
  -- Route correction: normalize the closed-path real parametrization branchwise before building
  -- any boundary charts, so later geometry can stay on explicit affine/circle models.
  exact ⟨upper_half_disk_boundary_realCurve_eqOn_diameter_interval r,
    upper_half_disk_boundary_realCurve_eqOn_arc_interval r⟩

/-- Helper for Proposition 3.1: every diameter-branch point of the explicit semidisk contour lies
on the real axis. -/
lemma upper_half_disk_boundary_im_eq_zero_of_le_half (r : ℝ)
    {t : Set.Icc (0 : ℝ) 1}
    (ht : (t : ℝ) ≤ 1 / 2) :
    (upperHalfDiskBoundaryPath r t).im = 0 := by
  -- The first branch is an explicit real segment.
  rw [upper_half_disk_boundary_eq_diameter_of_le_half r ht]
  simp

/-- Helper for Proposition 3.1: on the open arc branch, the explicit semidisk contour has strictly
positive imaginary part. -/
lemma upper_half_disk_boundary_im_pos_of_mem_Ioo_half_one {r : ℝ} (hr : 0 < r)
    {t : Set.Icc (0 : ℝ) 1}
    (ht : (t : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    0 < (upperHalfDiskBoundaryPath r t).im := by
  -- The second branch is the upper semicircle with angle strictly between `0` and `π`.
  rw [upper_half_disk_boundary_eq_arc_of_half_le r ht.1.le, circleMap_zero_im]
  have hθ : Real.pi * (2 * (t : ℝ) - 1) ∈ Set.Ioo (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [ht.1, ht.2, Real.pi_pos]
  exact mul_pos hr (Real.sin_pos_of_mem_Ioo hθ)

/-- Helper for Proposition 3.1: on the upper semicircle, `circleMap` is injective on the source
angle interval `0 ≤ θ ≤ π`. -/
lemma upper_semicircle_circleMap_injective {r α β : ℝ} (hr : r ≠ 0)
    (hα : α ∈ Set.Icc (0 : ℝ) Real.pi) (hβ : β ∈ Set.Icc (0 : ℝ) Real.pi)
    (h : circleMap 0 r α = circleMap 0 r β) :
    α = β := by
  -- Equality on the semicircle forces the angular difference to be a `2π` multiple lying in
  -- `(-2π, 2π)`, hence the multiple is zero.
  rw [circleMap_eq_circleMap_iff (c := (0 : ℂ)) hr] at h
  obtain ⟨n, hn⟩ := h
  have hangle : α = β + n * (2 * Real.pi) := by
    have him := congrArg Complex.im hn
    simpa [mul_add, add_mul, mul_assoc] using him
  have hlt_one_real : (n : ℝ) < 1 := by
    nlinarith [hα.2, hβ.1, Real.pi_pos, hangle]
  have hgt_neg_one_real : (-1 : ℝ) < n := by
    nlinarith [hα.1, hβ.2, Real.pi_pos, hangle]
  have hlt_one : n < 1 := by
    exact_mod_cast hlt_one_real
  have hgt_neg_one : -1 < n := by
    exact_mod_cast hgt_neg_one_real
  have hn_zero : n = 0 := by
    omega
  simpa [hn_zero] using hangle

/-- Helper for Proposition 3.1: equality on the semidisk contour can only occur at the same
parameter or at the identified endpoint pair `(0, 1)` / `(1, 0)`. -/
lemma upper_half_disk_boundary_simple_eq_or_endpoints
    {r : ℝ} (hr : 0 < r) {s t : Set.Icc (0 : ℝ) 1}
    (h :
      (upperHalfDiskBoundaryPath r).toClosedPath.toPath s =
        (upperHalfDiskBoundaryPath r).toClosedPath.toPath t) :
    s = t ∨ (s, t) = ((0 : Set.Icc (0 : ℝ) 1), (1 : Set.Icc (0 : ℝ) 1)) ∨
      (s, t) = ((1 : Set.Icc (0 : ℝ) 1), (0 : Set.Icc (0 : ℝ) 1)) := by
  -- Route correction: prove simplicity from the source contour decomposition itself, using the
  -- diameter/arc branch formulas and the imaginary-part separation between those branches.
  have hpath : upperHalfDiskBoundaryPath r s = upperHalfDiskBoundaryPath r t := by
    simpa [Path.toClosedPath] using h
  by_cases hs_half : (s : ℝ) ≤ 1 / 2
  · by_cases ht_half : (t : ℝ) ≤ 1 / 2
    · -- If both parameters are on the diameter branch, the affine coordinate is injective.
      have hs_eq := upper_half_disk_boundary_eq_diameter_of_le_half r hs_half
      have ht_eq := upper_half_disk_boundary_eq_diameter_of_le_half r ht_half
      have hEq :
          ((((4 * r) * (s : ℝ) - r : ℝ)) : ℂ) =
            ((((4 * r) * (t : ℝ) - r : ℝ)) : ℂ) := by
        simpa [hs_eq, ht_eq] using hpath
      have hre :
          (4 * r) * (s : ℝ) - r = (4 * r) * (t : ℝ) - r := by
        have hre' := congrArg Complex.re hEq
        simpa using hre'
      have hst : (s : ℝ) = (t : ℝ) := by
        nlinarith [hr, hre]
      exact Or.inl (Subtype.ext hst)
    · by_cases ht_one : (t : ℝ) = 1
      · -- Crossing from the diameter to the arc can only happen at the shared endpoint `-r`.
        have hs_eq := upper_half_disk_boundary_eq_diameter_of_le_half r hs_half
        have ht_eq :
            upperHalfDiskBoundaryPath r t = (-(r : ℂ)) := by
          calc
            upperHalfDiskBoundaryPath r t
                = circleMap 0 r (Real.pi * (2 * (t : ℝ) - 1)) := by
                    exact upper_half_disk_boundary_eq_arc_of_half_le r (by
                      have : ¬ (t : ℝ) ≤ 1 / 2 := ht_half
                      linarith [t.2.1])
            _ = circleMap 0 r Real.pi := by
                  rw [ht_one]
                  ring
            _ = (-(r : ℂ)) := by
                  symm
                  exact upper_semicircle_path_target_eq r
        have hEq : ((((4 * r) * (s : ℝ) - r : ℝ)) : ℂ) = (-(r : ℂ)) := by
          simpa [hs_eq, ht_eq] using hpath
        have hre :
            (4 * r) * (s : ℝ) - r = -r := by
          have hre' := congrArg Complex.re hEq
          simpa using hre'
        have hs_zero : (s : ℝ) = 0 := by
          nlinarith [hr, hre]
        have hs_eqI : s = (0 : Set.Icc (0 : ℝ) 1) := Subtype.ext hs_zero
        have ht_eqI : t = (1 : Set.Icc (0 : ℝ) 1) := Subtype.ext ht_one
        exact Or.inr <| Or.inl <| by simpa [hs_eqI, ht_eqI]
      · -- An interior arc point cannot equal a diameter point because their imaginary parts differ.
        have hs_im : (upperHalfDiskBoundaryPath r s).im = 0 :=
          upper_half_disk_boundary_im_eq_zero_of_le_half r hs_half
        have ht_open : (t : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
          constructor
          · have : ¬ (t : ℝ) ≤ 1 / 2 := ht_half
            exact lt_of_not_ge this
          · exact lt_of_le_of_ne t.2.2 (by
              intro ht_eq
              exact ht_one ht_eq)
        have ht_im :
            0 < (upperHalfDiskBoundaryPath r t).im :=
          upper_half_disk_boundary_im_pos_of_mem_Ioo_half_one hr ht_open
        have him := congrArg Complex.im hpath
        rw [hs_im] at him
        linarith
  · by_cases ht_half : (t : ℝ) ≤ 1 / 2
    · by_cases hs_one : (s : ℝ) = 1
      · -- The symmetric branch-crossing case can only occur at the endpoint pair `(1, 0)`.
        have hs_eq :
            upperHalfDiskBoundaryPath r s = (-(r : ℂ)) := by
          calc
            upperHalfDiskBoundaryPath r s
                = circleMap 0 r (Real.pi * (2 * (s : ℝ) - 1)) := by
                    exact upper_half_disk_boundary_eq_arc_of_half_le r (by
                      have : ¬ (s : ℝ) ≤ 1 / 2 := hs_half
                      linarith [s.2.1])
            _ = circleMap 0 r Real.pi := by
                  rw [hs_one]
                  ring
            _ = (-(r : ℂ)) := by
                  symm
                  exact upper_semicircle_path_target_eq r
        have ht_eq := upper_half_disk_boundary_eq_diameter_of_le_half r ht_half
        have hEq : (-(r : ℂ)) = ((((4 * r) * (t : ℝ) - r : ℝ)) : ℂ) := by
          simpa [hs_eq, ht_eq] using hpath
        have hre :
            -r = (4 * r) * (t : ℝ) - r := by
          have hre' := congrArg Complex.re hEq
          simpa using hre'
        have ht_zero : (t : ℝ) = 0 := by
          nlinarith [hr, hre]
        have hs_eqI : s = (1 : Set.Icc (0 : ℝ) 1) := Subtype.ext hs_one
        have ht_eqI : t = (0 : Set.Icc (0 : ℝ) 1) := Subtype.ext ht_zero
        exact Or.inr <| Or.inr <| by simpa [hs_eqI, ht_eqI]
      · -- Again, an interior arc point cannot meet the diameter because the imaginary part is positive.
        have ht_im : (upperHalfDiskBoundaryPath r t).im = 0 :=
          upper_half_disk_boundary_im_eq_zero_of_le_half r ht_half
        have hs_open : (s : ℝ) ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
          constructor
          · have : ¬ (s : ℝ) ≤ 1 / 2 := hs_half
            exact lt_of_not_ge this
          · exact lt_of_le_of_ne s.2.2 (by
              intro hs_eq
              exact hs_one hs_eq)
        have hs_im :
            0 < (upperHalfDiskBoundaryPath r s).im :=
          upper_half_disk_boundary_im_pos_of_mem_Ioo_half_one hr hs_open
        have him := congrArg Complex.im hpath
        rw [ht_im] at him
        linarith
    · -- If both parameters are on the arc branch, injectivity reduces to angle injectivity on
      -- `[0, π]`.
      have hs_ge : 1 / 2 ≤ (s : ℝ) := by
        have : ¬ (s : ℝ) ≤ 1 / 2 := hs_half
        exact (lt_of_not_ge this).le
      have ht_ge : 1 / 2 ≤ (t : ℝ) := by
        have : ¬ (t : ℝ) ≤ 1 / 2 := ht_half
        exact (lt_of_not_ge this).le
      let α : ℝ := Real.pi * (2 * (s : ℝ) - 1)
      let β : ℝ := Real.pi * (2 * (t : ℝ) - 1)
      have hs_eq := upper_half_disk_boundary_eq_arc_of_half_le r hs_ge
      have ht_eq := upper_half_disk_boundary_eq_arc_of_half_le r ht_ge
      have hcircle : circleMap 0 r α = circleMap 0 r β := by
        simpa [α, β, hs_eq, ht_eq] using hpath
      have hα : α ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor <;> nlinarith [hs_ge, s.2.2, Real.pi_pos]
      have hβ : β ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor <;> nlinarith [ht_ge, t.2.2, Real.pi_pos]
      have hαβ : α = β :=
        upper_semicircle_circleMap_injective (by linarith : r ≠ 0) hα hβ hcircle
      have hst : (s : ℝ) = (t : ℝ) := by
        nlinarith [Real.pi_pos, hαβ]
      exact Or.inl (Subtype.ext hst)

/-- Helper for Proposition 3.1: for positive radius, the horizontal diameter segment has range
exactly the real interval `[-r, r]`. -/
lemma upper_half_disk_diameter_path_range_eq_image_Icc {r : ℝ} (hr : 0 < r) :
    Set.range (Path.segment (-(r : ℂ)) (r : ℂ)) =
      (fun x : ℝ ↦ (x : ℂ)) '' Set.Icc (-r) r := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨(2 * r) * (t : ℝ) - r, ?_, ?_⟩
    · -- The affine segment parameter stays inside the diameter interval.
      constructor <;> nlinarith [t.2.1, t.2.2, hr]
    · -- Read the complex segment point in the source real coordinate.
      simpa using (upper_half_disk_diameter_path_apply r t).symm
  · rintro ⟨x, hx, rfl⟩
    let t : Set.Icc (0 : ℝ) 1 := by
      refine ⟨(x + r) / (2 * r), ?_⟩
      -- Rescale the real coordinate back to a unit-interval parameter.
      constructor
      · have htwo : 0 < 2 * r := by positivity
        exact div_nonneg (by linarith [hx.1]) htwo.le
      · have htwo : 0 < 2 * r := by positivity
        have hbound : x + r ≤ 2 * r := by linarith [hx.2]
        have htwo_ne : (2 * r) ≠ 0 := by positivity
        calc
          (x + r) / (2 * r) ≤ (2 * r) / (2 * r) := by
            exact div_le_div_of_nonneg_right hbound htwo.le
          _ = 1 := by field_simp [htwo_ne]
    refine ⟨t, ?_⟩
    have hcoord : (2 * r) * ((t : ℝ)) - r = x := by
      dsimp [t]
      field_simp [hr.ne']
      ring
    -- Substituting that parameter into the affine line map recovers the requested diameter point.
    simpa [hcoord] using upper_half_disk_diameter_path_apply r t

/-- Helper for Proposition 3.1: for a positive radius, the frontier of the closed upper half-disk
is exactly the real diameter `[-r, r]` together with the upper semicircle. -/
lemma frontier_upper_half_disk_eq_diameter_union_upper_arc {r : ℝ} (hr : 0 < r) :
    frontier ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) =
      ((fun x : ℝ ↦ (x : ℂ)) '' Set.Icc (-r) r) ∪ (circleMap 0 r '' Set.Icc 0 Real.pi) := by
  let K : Set ℂ := Metric.closedBall (0 : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}
  have hK : K = ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) := by
    -- Normalize the semidisk to the intersection of the closed disk and the closed upper
    -- half-plane so frontier/interior lemmas apply directly.
    ext z
    simp [K, Metric.mem_closedBall, dist_eq_norm]
  have hKclosed : IsClosed K := by
    -- Both defining pieces are closed, so the semidisk itself is closed.
    exact
      (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : ℂ) r)).inter
        (isClosed_le continuous_const Complex.continuous_im)
  have hKsubset_ball : K ⊆ Metric.closedBall (0 : ℂ) r := by
    intro z hz
    exact hz.1
  have hKsubset_half : K ⊆ {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    exact hz.2
  rw [← hK]
  ext z
  constructor
  · intro hz
    have hzK : z ∈ K := by
      -- Frontier points of the closed semidisk still belong to the semidisk itself.
      simpa [hKclosed.closure_eq] using (frontier_subset_closure hz)
    have hz_split :
        z ∈
          (frontier (Metric.closedBall (0 : ℂ) r) ∩ closure {z : ℂ | 0 ≤ z.im}) ∪
            (closure (Metric.closedBall (0 : ℂ) r) ∩ frontier {z : ℂ | 0 ≤ z.im}) := by
      -- A frontier point of the intersection must come from one of the two defining boundaries.
      exact frontier_inter_subset (Metric.closedBall (0 : ℂ) r) {z : ℂ | 0 ≤ z.im} hz
    rcases hz_split with ⟨hz_ball, _⟩ | ⟨_, hz_half⟩
    · right
      have hz_sphere : z ∈ Metric.sphere (0 : ℂ) r := by
        simpa [frontier_closedBall'] using hz_ball
      have hz_norm : ‖z‖ = r := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz_sphere
      refine ⟨Complex.arg z, ?_, ?_⟩
      · -- On the closed upper half-plane the principal argument lies in `[0, π]`.
        constructor
        · exact (Complex.arg_nonneg_iff).2 hzK.2
        · exact Complex.arg_le_pi z
      · -- Rebuild the boundary point from its norm and principal argument.
        calc
          circleMap 0 r (Complex.arg z)
              = 0 + r * Complex.exp (Complex.arg z * Complex.I) := by
                  simp [circleMap]
          _ = 0 + ‖z‖ * Complex.exp (Complex.arg z * Complex.I) := by
                rw [hz_norm]
          _ = z := by
                rw [Complex.norm_mul_exp_arg_mul_I]
                ring
    · left
      have hz_im : z.im = 0 := by
        -- The frontier of the closed upper half-plane is the real axis.
        simpa [Complex.frontier_setOf_le_im] using hz_half
      have hz_eq_real : z = (z.re : ℂ) := by
        apply Complex.ext <;> simp [hz_im]
      have hz_re_abs : |z.re| ≤ r := by
        exact le_trans (Complex.abs_re_le_norm z) (by
          simpa [K, Metric.mem_closedBall, dist_eq_norm] using hzK.1)
      have hz_re_mem : z.re ∈ Set.Icc (-r) r := by
        exact abs_le.mp hz_re_abs
      exact ⟨z.re, hz_re_mem, hz_eq_real.symm⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨θ, hθ, rfl⟩)
    · have hx_abs : |x| ≤ r := by
        exact abs_le.2 hx
      have hzK : ((x : ℂ) : ℂ) ∈ K := by
        constructor
        · simpa [K, Metric.mem_closedBall, dist_eq_norm] using hx_abs
        · simp
      have hz_not_int_half : ((x : ℂ) : ℂ) ∉ interior {z : ℂ | 0 ≤ z.im} := by
        -- Real points lie on the half-plane frontier, so they cannot be interior points.
        simp [Complex.interior_setOf_le_im]
      have hz_not_int_K : ((x : ℂ) : ℂ) ∉ interior K := by
        intro hz_int
        exact hz_not_int_half (interior_mono hKsubset_half hz_int)
      -- Membership in the semidisk plus failure of interior membership is exactly frontier
      -- membership.
      exact (mem_frontier_iff_notMem_interior hzK).2 hz_not_int_K
    · have hzK : circleMap 0 r θ ∈ K := by
        constructor
        · -- Points of the upper semicircle sit on the boundary circle of radius `r`.
          simpa [K, Metric.mem_closedBall, dist_eq_norm, norm_circleMap_upper_semicircle hr.le]
        · exact circleMap_mem_closed_upper_half_plane hr.le hθ
      have hz_not_int_ball :
          circleMap 0 r θ ∉ interior (Metric.closedBall (0 : ℂ) r) := by
        -- A point of norm exactly `r` cannot lie in the open ball.
        simpa [interior_closedBall', hr.ne', Metric.mem_ball, dist_eq_norm,
          norm_circleMap_upper_semicircle hr.le]
      have hz_not_int_K : circleMap 0 r θ ∉ interior K := by
        intro hz_int
        exact hz_not_int_ball (interior_mono hKsubset_ball hz_int)
      -- The arc lies in the semidisk but not in its interior, so it lies on the frontier.
      exact (mem_frontier_iff_notMem_interior hzK).2 hz_not_int_K

/-- Helper for Proposition 3.1: for positive radius, the explicit upper-half-disk contour range is
exactly the frontier of the closed upper half-disk. -/
lemma upper_half_disk_boundary_path_range_eq_frontier {r : ℝ} (hr : 0 < r) :
    Set.range (upperHalfDiskBoundaryPath r) =
      frontier ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) := by
  -- Rewrite the contour range into the diameter-plus-arc union already matched with the frontier.
  rw [upper_half_disk_boundary_path_range_eq_union,
    upper_half_disk_diameter_path_range_eq_image_Icc hr,
    upper_semicircle_path_range_eq_image_Icc,
    frontier_upper_half_disk_eq_diameter_union_upper_arc hr]

/-- Helper for Proposition 3.1: every frontier point of the closed upper half-disk is an analytic
point of the weighted meromorphic normal form, provided the outer semicircle avoids poles. -/
lemma upper_half_disk_frontier_weighted_normal_form_analyticAt
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    {r : ℝ} (hr : 0 < r)
    (hboundary :
      ∀ θ ∈ Set.Icc 0 Real.pi, ¬ meromorphicOrderAt f (circleMap 0 r θ) < 0)
    {z : ℂ}
    (hz : z ∈ frontier ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ)) :
    AnalyticAt ℂ
      (fun w ↦
        toMeromorphicNFOn f {w : ℂ | 0 ≤ w.im} w *
          Complex.exp (Complex.I * w))
      z := by
  -- Split the frontier into the real diameter and the upper semicircle, then use the pole-free
  -- hypotheses on each branch to invoke the existing analyticity package.
  rw [frontier_upper_half_disk_eq_diameter_union_upper_arc hr] at hz
  rcases hz with hz | hz
  · rcases hz with ⟨x, hx, rfl⟩
    have hx_not_mem : ((x : ℂ)) ∉ s := by
      intro hxS
      have hxUpper : (x : ℂ) ∈ upperHalfPlaneSet := ((hpoles (x : ℂ)).mpr hxS).2
      have hxim : (0 : ℝ) < ((x : ℂ)).im := by
        simpa [UpperHalfPlane.upperHalfPlaneSet] using hxUpper
      simp at hxim
    -- Real boundary points belong to the closed upper half-plane and avoid the pole finset.
    simpa using
      analyticAt_weighted_normal_form_of_mem_upper_half_plane_not_mem_pole_finset
        (f := f) (s := s) hmeromorphic hreal hpoles (by simp) hx_not_mem
  · rcases hz with ⟨θ, hθ, rfl⟩
    have hz_not_mem : circleMap 0 r θ ∉ s := by
      intro hzS
      have hpole : meromorphicOrderAt f (circleMap 0 r θ) < 0 := ((hpoles _).mpr hzS).1
      exact hboundary θ hθ hpole
    have hzU : circleMap 0 r θ ∈ ({w : ℂ | 0 ≤ w.im} : Set ℂ) := by
      simpa using circleMap_mem_closed_upper_half_plane hr.le hθ
    -- On the semicircular branch, the large-radius hypothesis excludes poles pointwise.
    simpa using
      analyticAt_weighted_normal_form_of_mem_upper_half_plane_not_mem_pole_finset
        (f := f) (s := s) hmeromorphic hreal hpoles hzU hz_not_mem

/-- Helper for Proposition 3.1: a good upper-half-disk radius makes the explicit boundary contour
disjoint from the pole finset, because the contour lies on the frontier while the poles lie in the
interior. -/
lemma upper_half_disk_boundary_disjoint_pole_finset
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    {r : ℝ} (hr : 0 < r)
    (hinside : ∀ z ∈ s, ‖z‖ < r) :
    Disjoint (Set.range (upperHalfDiskBoundaryPath r)) (↑s : Set ℂ) := by
  have hsInterior :
      (↑s : Set ℂ) ⊆ interior ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) :=
    pole_finset_subset_interior_upper_half_disk (f := f) (s := s) hpoles hinside
  rw [upper_half_disk_boundary_path_range_eq_frontier hr]
  refine Set.disjoint_left.2 ?_
  intro z hzFront hzS
  -- Frontier points cannot coincide with points that are already packaged strictly inside the
  -- semidisk.
  exact (Set.disjoint_left.1 disjoint_interior_frontier) (hsInterior hzS) hzFront

/-- Helper for Proposition 3.1: a good radius admits an open owner containing the closed upper
half-disk on which the weighted normal-form integrand is differentiable away from the pole finset.
-/
lemma upper_half_disk_differentiable_owner
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    {r : ℝ} (hr : 0 < r)
    (hboundary :
      ∀ θ ∈ Set.Icc 0 Real.pi, ¬ meromorphicOrderAt f (circleMap 0 r θ) < 0) :
    ∃ D : Set ℂ,
      IsOpen D ∧
        ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) ⊆ D ∧
        DifferentiableOn ℂ
          (fun z ↦
            toMeromorphicNFOn f {z : ℂ | 0 ≤ z.im} z *
              Complex.exp (Complex.I * z))
          (D \ (↑s : Set ℂ)) := by
  let U : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let K : Set ℂ := {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im}
  let G : ℂ → ℂ := fun z ↦ toMeromorphicNFOn f U z * Complex.exp (Complex.I * z)
  let D : Set ℂ := interior K ∪ {z : ℂ | AnalyticAt ℂ G z}
  have hKU : K ⊆ U := by
    intro z hz
    exact hz.2
  refine ⟨D, ?_, ?_, ?_⟩
  · -- The owner is the union of the semidisk interior with the open analyticity locus of `G`.
    exact isOpen_interior.union (isOpen_analyticAt ℂ G)
  · intro z hzK
    by_cases hzInt : z ∈ interior K
    · exact Or.inl hzInt
    · have hzFront : z ∈ frontier K := (mem_frontier_iff_notMem_interior hzK).2 hzInt
      -- Boundary points are inserted using the frontier analyticity lemma proved just above.
      exact Or.inr <| by
        simpa [G, K, U] using
          upper_half_disk_frontier_weighted_normal_form_analyticAt
            (f := f) (s := s) hmeromorphic hreal hpoles hr hboundary hzFront
  · intro z hz
    rcases hz with ⟨hzD, hzs⟩
    rcases hzD with hzInt | hzAnalytic
    · have hzU : z ∈ U := hKU (interior_subset hzInt)
      have hzAnalytic :
          AnalyticAt ℂ G z := by
        -- Interior points are also covered by the pointwise analyticity statement on `U \ s`.
        simpa [G, U] using
          analyticAt_weighted_normal_form_of_mem_upper_half_plane_not_mem_pole_finset
            (f := f) (s := s) hmeromorphic hreal hpoles hzU hzs
      exact hzAnalytic.differentiableAt.differentiableWithinAt
    · -- Boundary points were inserted precisely because `G` is analytic there.
      exact hzAnalytic.differentiableAt.differentiableWithinAt

/-- Helper for Proposition 3.1: the singleton closed-path family attached to
`upperHalfDiskBoundaryPath r` has union equal to the actual contour range. This is the stable
adapter from the explicit contour to the later `Unit`-indexed `IsOrientedBoundaryOf` API. -/
lemma upper_half_disk_boundary_singleton_iUnion_range (r : ℝ) :
    (⋃ i : Unit,
        Set.range ((((fun _ : Unit ↦ (upperHalfDiskBoundaryPath r).toClosedPath) i).toPath))) =
      Set.range (upperHalfDiskBoundaryPath r) := by
  ext z
  constructor
  · intro hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
    cases i
    -- Collapse the singleton indexed closed-path family back to the explicit contour.
    simpa [Path.toClosedPath] using hi
  · intro hz
    refine Set.mem_iUnion.mpr ?_
    refine ⟨(), ?_⟩
    -- Repackage the explicit contour as the unique member of the singleton family.
    simpa [Path.toClosedPath] using hz

/-- Helper for Proposition 3.1: unpacking a loop through `toClosedPath.toPath` only inserts the
endpoint cast forced by the closed-path packaging. -/
lemma loop_toClosedPath_toPath_eq_cast {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.toPath =
      γ.cast (by simpa [Path.toClosedPath] using γ.source)
        (by simpa [Path.toClosedPath] using γ.source) := by
  -- The packaged closed path remembers exactly the original loop, up to the endpoint cast.
  cases γ
  rfl

/-- Helper for Proposition 3.1: the real-curve parametrization of a loop closed path is the
original path extension written in real coordinates. -/
lemma toClosedPath_realCurve_eq {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.realCurve = Complex.equivRealProd ∘ γ.extend := by
  -- After destructing the loop, the real-curve wrapper is definitionally the original extension.
  cases γ
  rfl

/-- Helper for Proposition 3.1: the explicit upper-semicircle branch is globally differentiable. -/
lemma upper_semicircle_path_isDifferentiable (r : ℝ) :
    (upperSemicirclePath r).IsDifferentiable := by
  -- The upper semicircle is the standard `circleMap` restricted to the affine angle interval
  -- `θ = π t`, so the path is `C¹` on the whole unit interval.
  rw [Path.IsDifferentiable]
  let g : ℝ → ℂ := fun t ↦ circleMap 0 r (Real.pi * t)
  have hlin : ContDiff ℝ 1 (fun t : ℝ ↦ Real.pi * t) := by
    simpa [one_mul] using (contDiff_const.mul contDiff_id)
  have hg : ContDiff ℝ 1 g := by
    simpa [g] using (contDiff_circleMap 0 r).comp hlin
  refine hg.contDiffOn.congr ?_
  intro t ht
  have hpath :
      (upperSemicirclePath r).extend t = circleMap 0 r (Real.pi * t) := by
    rw [Path.extend_apply (γ := upperSemicirclePath r) ht]
    simpa [g] using upperSemicirclePath_apply r ⟨t, ht⟩
  simpa [g] using hpath

/-- Helper for Proposition 3.1: the explicit semidisk contour is piecewise differentiable because
it is the concatenation of a line segment and a smooth upper semicircle. -/
lemma upper_half_disk_boundary_isPiecewiseDifferentiable (r : ℝ) :
    (upperHalfDiskBoundaryPath r).IsPiecewiseDifferentiable := by
  -- Promote the smooth semicircle branch and concatenate it to the already piecewise
  -- differentiable diameter segment.
  exact
    (Path.segment_isPiecewiseDifferentiable (-(r : ℂ)) (r : ℂ)).trans_of_isDifferentiable
      (upper_semicircle_path_isDifferentiable r)

/-- Helper for Proposition 3.1: quarter-turning a complex tangent in real coordinates is
multiplication by `I` before converting back to `Plane`. -/
lemma upper_half_disk_rot90_equivRealProd_eq_equivRealProd_mul_I (z : ℂ) :
    rot90 (Complex.equivRealProd z) = Complex.equivRealProd (z * Complex.I) := by
  -- `Complex.equivRealProd` identifies multiplication by `I` with the standard quarter-turn.
  ext <;> simp [rot90, Complex.equivRealProd]

/-- Helper for Proposition 3.1: a tube map around a `C¹` branch has the expected tangent and
transverse derivative columns at the base point. -/
lemma upper_half_disk_radial_tube_hasFDerivAt {γ n : ℝ → ℂ} {t₀ : ℝ} {v : ℂ}
    (hγCont : ContDiffAt ℝ 1 γ t₀) (hγDeriv : HasDerivAt γ v t₀)
    (hnCont : ContDiffAt ℝ 1 n t₀) :
    ContDiffAt ℝ 1 (fun p : Plane ↦ γ p.1 + p.2 • n p.1) (t₀, 0) ∧
      HasFDerivAt (fun p : Plane ↦ γ p.1 + p.2 • n p.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (n t₀))
        (t₀, 0) := by
  constructor
  · -- The tube map is the sum of the branch and the varying transverse direction.
    have hγfst : ContDiffAt ℝ 1 (fun p : Plane ↦ γ p.1) (t₀, 0) := by
      simpa using hγCont.comp (x := (t₀, 0)) contDiffAt_fst
    have hnfst : ContDiffAt ℝ 1 (fun p : Plane ↦ n p.1) (t₀, 0) := by
      simpa using hnCont.comp (x := (t₀, 0)) contDiffAt_fst
    simpa using hγfst.add (contDiffAt_snd.smul hnfst)
  · -- At `p.2 = 0`, the transverse derivative contributes only the actual normal vector.
    have hγfst :
        HasFDerivAt (fun p : Plane ↦ γ p.1)
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v) (t₀, (0 : ℝ)) := by
      simpa [ContinuousLinearMap.smulRight_apply] using
        hγDeriv.hasFDerivAt.comp (t₀, (0 : ℝ))
          (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    have hnfst :
        HasFDerivAt (fun p : Plane ↦ n p.1)
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (deriv n t₀)) (t₀, (0 : ℝ)) := by
      simpa [ContinuousLinearMap.smulRight_apply] using
        (hnCont.differentiableAt one_ne_zero).hasDerivAt.hasFDerivAt.comp (t₀, (0 : ℝ))
          (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    have hsnd :
        HasFDerivAt (fun p : Plane ↦ p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (t₀, (0 : ℝ)) := by
      simpa using
        (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    simpa [ContinuousLinearMap.smulRight_apply] using hγfst.add (hsnd.smul hnfst)

/-- Helper for Proposition 3.1: rescaling the second plane coordinate by a nonzero real factor is
a continuous linear automorphism. -/
noncomputable def upper_half_disk_plane_second_rescale (c : ℝ) (hc : c ≠ 0) : Plane ≃L[ℝ] Plane :=
  { toLinearEquiv :=
      { toFun := fun p ↦ (p.1, p.2 / c)
        invFun := fun p ↦ (p.1, c * p.2)
        left_inv := by
          intro p
          ext
          · rfl
          · field_simp [hc]
        right_inv := by
          intro p
          ext
          · rfl
          · field_simp [hc]
        map_add' := by
          intro p q
          ext <;> simp [div_eq_mul_inv, add_mul]
        map_smul' := by
          intro s p
          ext <;> simp [div_eq_mul_inv, mul_assoc] }
    continuous_toFun := by
      fun_prop
    continuous_invFun := by
      fun_prop }

/-- Helper for Proposition 3.1: the distance from `a` to a radial exponential point is the
absolute value of its real radial coefficient. -/
lemma upper_half_disk_dist_add_real_mul_exp_eq_abs {a : ℂ} {s θ : ℝ} :
    dist (a + (s : ℂ) * Complex.exp (θ * Complex.I)) a = |s| := by
  -- The exponential factor has norm `1`, so only the real radius contributes to the distance.
  rw [dist_eq_norm]
  calc
    ‖a + (s : ℂ) * Complex.exp (θ * Complex.I) - a‖ =
        ‖(s : ℂ) * Complex.exp (θ * Complex.I)‖ := by
          ring_nf
    _ = ‖(s : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := norm_mul _ _
    _ = |s| := by simp [Complex.norm_exp]

/-- Helper for Proposition 3.1: the affine angle parameter on the upper-semicircle branch has
constant derivative `2π`. -/
lemma upper_half_disk_arc_arg_hasDerivAt (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.pi * (2 * t - 1)) (2 * Real.pi) t₀ := by
  -- The branch angle is an affine reparametrization of the standard semicircle angle.
  simpa [sub_eq_add_neg, mul_add, add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using
    ((((hasDerivAt_id t₀).const_mul 2).sub_const 1).const_mul Real.pi)

/-- Helper for Proposition 3.1: quarter-turning the upper-semicircle tangent yields the inward
radial direction scaled by `2πr`. -/
lemma upper_half_disk_arc_rot90_tangent_eq_scaled_inward {r t₀ : ℝ} :
    rot90
      (Complex.equivRealProd
        ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I *
          Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I))) =
      (2 * Real.pi * r) •
        Complex.equivRealProd (-Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) := by
  -- Multiplication by `I` turns the tangent into the inward radial direction.
  rw [upper_half_disk_rot90_equivRealProd_eq_equivRealProd_mul_I]
  have hz :
      (((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
            Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) * Complex.I =
        ((2 * Real.pi * r) : ℝ) • (-Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) := by
    calc
      (((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
            Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) * Complex.I =
          ((((2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) * (Complex.I * Complex.I) := by
              ring
      _ = ((((2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) * (-1) := by
            simp
      _ = -((((2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) := by
            ring
      _ = ((2 * Real.pi * r) : ℝ) •
            (-Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) := by
            simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  simpa using congrArg Complex.equivRealProd hz

/-- Helper for Proposition 3.1: the diameter model has tangent `4r` at the diameter/arc junction
parameter `1 / 2`. -/
lemma upper_half_disk_boundary_diameter_hasDerivWithinAt_half (r : ℝ) :
    HasDerivWithinAt
      (fun t : ℝ ↦ ((((4 * r) * t - r : ℝ)) : ℂ))
      (((4 * r : ℝ)) : ℂ)
      (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  -- The diameter branch is an affine real-to-complex map.
  have hreal :
      HasDerivAt (fun t : ℝ ↦ (4 * r) * t - r) (4 * r) (1 / 2 : ℝ) := by
    simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
      (((hasDerivAt_id (1 / 2 : ℝ)).const_mul (4 * r)).sub_const r)
  have hmodel :
      HasDerivAt (fun t : ℝ ↦ ((((4 * r) * t - r : ℝ)) : ℂ))
        (((4 * r : ℝ)) : ℂ) (1 / 2 : ℝ) := by
    simpa using hreal.ofReal_comp
  exact hmodel.hasDerivWithinAt

/-- Helper for Proposition 3.1: the upper-semicircle model has tangent `2πri` at the
diameter/arc junction parameter `1 / 2`. -/
lemma upper_half_disk_boundary_arc_hasDerivWithinAt_half (r : ℝ) :
    HasDerivWithinAt
      (fun t : ℝ ↦ circleMap 0 r (Real.pi * (2 * t - 1)))
      ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I)
      (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
  -- Compose `circleMap` with the affine angle and then simplify the angle value `θ(1/2) = 0`.
  have hderivComp :
      HasDerivAt
        ((circleMap 0 r) ∘ fun t : ℝ ↦ Real.pi * (2 * t - 1))
        ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) (1 / 2 : ℝ) := by
    simpa [circleMap_zero, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_circleMap 0 r (Real.pi * (2 * (1 / 2 : ℝ) - 1))).scomp (1 / 2 : ℝ)
        (upper_half_disk_arc_arg_hasDerivAt (1 / 2 : ℝ)))
  -- The ordinary derivative immediately restricts to the branch interval.
  simpa [Function.comp] using hderivComp.hasDerivWithinAt

/-- Helper for Proposition 3.1: the midpoint parameter is a genuine corner of the semidisk
boundary, so the closed-path real curve is not differentiable there within `[0, 1]`. -/
lemma upper_half_disk_boundary_not_differentiable_at_half
    {r : ℝ} (hr : 0 < r) :
    ¬ DifferentiableWithinAt ℝ ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
  -- Route correction: compare the diameter and upper-semicircle tangents at the shared parameter,
  -- then use uniqueness of within-derivatives on the two closed branch intervals.
  intro hdiff
  let γ : ℝ → ℂ := (upperHalfDiskBoundaryPath r).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ)
  let diameter : ℝ → ℂ := fun t ↦ ((((4 * r) * t - r : ℝ)) : ℂ)
  let arc : ℝ → ℂ := fun t ↦ circleMap 0 r (Real.pi * (2 * t - 1))
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
    -- Undo the `Complex.equivRealProd` wrapper so the tangent comparison happens in `ℂ`.
    simpa [γ, toClosedPath_realCurve_eq, Function.comp] using
      (Complex.equivRealProdCLM.comp_differentiableWithinAt_iff.mp hdiff)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
    simpa [d, γ] using hγdiff.hasDerivWithinAt
  have hdiamMain :
      HasDerivWithinAt γ d (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    -- Restrict the ambient derivative to the diameter branch interval.
    apply hmain.mono
    intro t ht
    constructor
    · exact ht.1
    · linarith [ht.2]
  have harcMain :
      HasDerivWithinAt γ d (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
    -- Restrict the same derivative to the semicircle branch interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · exact ht.2
  have hdiamγ :
      HasDerivWithinAt γ ((((4 * r : ℝ)) : ℂ))
        (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    -- Transfer the explicit affine derivative to the original contour on the diameter branch.
    exact (upper_half_disk_boundary_diameter_hasDerivWithinAt_half r).congr_of_mem
      (fun t ht ↦ by
        have hI : t ∈ Set.Icc (0 : ℝ) 1 := by
          constructor
          · exact ht.1
          · linarith [ht.2]
        let tI : Set.Icc (0 : ℝ) 1 := ⟨t, hI⟩
        calc
          γ t = upperHalfDiskBoundaryPath r tI := by
            simpa [γ, tI] using (Path.extend_apply (γ := upperHalfDiskBoundaryPath r) hI)
          _ = diameter t := by
            simpa [diameter, tI] using
              upper_half_disk_boundary_eq_diameter_of_le_half r (t := tI) ht.2)
      (by constructor <;> norm_num)
  have harcγ :
      HasDerivWithinAt γ ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I)
        (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
    -- Transfer the explicit circular derivative to the original contour on the arc branch.
    exact (upper_half_disk_boundary_arc_hasDerivWithinAt_half r).congr_of_mem
      (fun t ht ↦ by
        have hI : t ∈ Set.Icc (0 : ℝ) 1 := by
          constructor
          · linarith [ht.1]
          · exact ht.2
        let tI : Set.Icc (0 : ℝ) 1 := ⟨t, hI⟩
        calc
          γ t = upperHalfDiskBoundaryPath r tI := by
            simpa [γ, tI] using (Path.extend_apply (γ := upperHalfDiskBoundaryPath r) hI)
          _ = arc t := by
            simpa [arc, tI] using
              upper_half_disk_boundary_eq_arc_of_half_le r (t := tI) ht.1)
      (by constructor <;> norm_num)
  have hdiamUD :
      UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    (uniqueDiffOn_Icc (show (0 : ℝ) < 1 / 2 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have harcUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 2 : ℝ) < 1 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hcompare :
      ((((4 * r : ℝ)) : ℂ)) = ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) := by
    -- Uniqueness of within-derivatives forces the two branch tangents to agree.
    calc
      ((((4 * r : ℝ)) : ℂ))
          = derivWithin γ (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
              symm
              exact hdiamγ.derivWithin hdiamUD
      _ = d := hdiamMain.derivWithin hdiamUD
      _ = derivWithin γ (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
            symm
            exact harcMain.derivWithin harcUD
      _ = ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) := harcγ.derivWithin harcUD
  have him_eq : (0 : ℝ) = 2 * Real.pi * r := by
    simpa using congrArg Complex.im hcompare
  nlinarith [hr, Real.pi_pos]

/-- Helper for Proposition 3.1: every regular interior parameter of the semidisk boundary lies on
exactly one of the two smooth open branches. -/
lemma upper_half_disk_boundary_regular_parameter_mem_branch
    {r : ℝ} (hr : 0 < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀) :
    t₀ ∈ Set.Ioo (0 : ℝ) (1 / 2) ∨ t₀ ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
  -- Exclude the corner parameter `1 / 2`, then dispatch by order on the interval.
  by_cases ht_half : t₀ < 1 / 2
  · exact Or.inl ⟨ht₀.1, ht_half⟩
  · have hne : t₀ ≠ 1 / 2 := by
      intro ht_eq
      exact (upper_half_disk_boundary_not_differentiable_at_half hr) (by simpa [ht_eq] using hdiff)
    have hgt : 1 / 2 < t₀ := lt_of_le_of_ne (le_of_not_gt ht_half) (Ne.symm hne)
    exact Or.inr ⟨hgt, ht₀.2⟩

/-- Helper for Proposition 3.1: an interior diameter parameter admits a quantitative strip
around the affine branch where positive height enters the semidisk interior and negative height
leaves the owner immediately through the lower half-plane. -/
lemma upper_half_disk_diameter_local_strip_data
    {r t₀ : ℝ} (hr : 0 < r) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∃ eps_t eps_u, 0 < eps_t ∧ 0 < eps_u ∧
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) ∧
      ∀ {t u : ℝ},
        t ∈ Set.Ioo (t₀ - eps_t) (t₀ + eps_t) →
        u ∈ Set.Ioo (-eps_u) eps_u →
        (u < 0 →
          ((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I) ∉
            ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)) ∧
        (0 < u →
          ((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I) ∈
            interior ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)) := by
  let μ : ℝ := min t₀ (1 / 2 - t₀)
  have hμ_pos : 0 < μ := by
    -- The open diameter branch stays a positive distance away from both endpoints.
    exact lt_min ht₀.1 (by linarith [ht₀.2])
  refine ⟨μ / 4, r * μ, by positivity, by positivity, ?_, ?_⟩
  · intro t ht
    constructor
    · -- The chosen `t`-strip remains inside the open diameter parameter interval.
      have hμ_le : μ ≤ t₀ := min_le_left _ _
      have hleft : 0 < t₀ - μ / 4 := by
        nlinarith [hμ_pos, hμ_le]
      exact lt_trans hleft ht.1
    · have hμ_le : μ ≤ 1 / 2 - t₀ := min_le_right _ _
      have hright : t₀ + μ / 4 < 1 / 2 := by
        nlinarith [hμ_pos, hμ_le]
      exact lt_trans ht.2 hright
  · intro t u ht hu
    constructor
    · intro hu_neg hz
      -- Negative height forces a strictly negative imaginary part, so the point is outside.
      have hz_im : 0 ≤
          (((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I)).im := hz.2
      exact (not_le_of_gt (by simpa using hu_neg)) (by simpa using hz_im)
    · intro hu_pos
      have ht_abs : |t - t₀| < μ / 4 := by
        -- Recenter the strip at `t₀` so the affine branch estimate can use absolute values.
        refine abs_lt.2 ?_
        constructor <;> linarith [ht.1, ht.2]
      have hu_abs : |u| < r * μ := by
        -- The vertical strip already records the exact height bound we need.
        exact abs_lt.2 ⟨hu.1, hu.2⟩
      have hμ_formula : |4 * t₀ - 1| = 1 - 4 * μ := by
        -- The distance from `t₀` to the midpoint `1 / 4` is exactly encoded by `μ`.
        by_cases hquarter : t₀ ≤ 1 / 4
        · have hquarter' : t₀ ≤ 1 / 2 - t₀ := by
            linarith
          have hμ_eq : μ = t₀ := min_eq_left hquarter'
          have hsign : 4 * t₀ - 1 ≤ 0 := by linarith
          rw [hμ_eq, abs_of_nonpos hsign]
          ring
        · have hquarter' : 1 / 4 < t₀ := lt_of_not_ge hquarter
          have hμ_eq : μ = 1 / 2 - t₀ := by
            apply min_eq_right
            linarith [ht₀.2, hquarter']
          have hsign : 0 ≤ 4 * t₀ - 1 := by linarith
          rw [hμ_eq, abs_of_nonneg hsign]
          ring
      have hx0_abs : |(4 * r) * t₀ - r| = r * (1 - 4 * μ) := by
        -- Rewrite the center point on the diameter as `r * (4 t₀ - 1)`.
        calc
          |(4 * r) * t₀ - r| = |r * (4 * t₀ - 1)| := by ring_nf
          _ = |r| * |4 * t₀ - 1| := by rw [abs_mul]
          _ = r * (1 - 4 * μ) := by rw [abs_of_pos hr, hμ_formula]
      have hxdiff :
          |((4 * r) * t - r) - ((4 * r) * t₀ - r)| < r * μ := by
        -- The diameter branch is affine, so the horizontal displacement is controlled directly by
        -- the `t`-strip width.
        calc
          |((4 * r) * t - r) - ((4 * r) * t₀ - r)| = |(4 * r) * (t - t₀)| := by ring_nf
          _ = |4 * r| * |t - t₀| := by rw [abs_mul]
          _ = (4 * r) * |t - t₀| := by
                rw [abs_of_nonneg (by positivity : 0 ≤ 4 * r)]
          _ < (4 * r) * (μ / 4) := by
                gcongr
          _ = r * μ := by ring
      have hx_abs : |(4 * r) * t - r| < r := by
        -- The horizontal coordinate stays away from the radius bound by a margin larger than the
        -- allowed vertical height.
        calc
          |(4 * r) * t - r|
              = |((4 * r) * t₀ - r) +
                  (((4 * r) * t - r) - ((4 * r) * t₀ - r))| := by ring_nf
          _ ≤ |(4 * r) * t₀ - r| +
                |((4 * r) * t - r) - ((4 * r) * t₀ - r)| := abs_add_le _ _
          _ < r * (1 - 4 * μ) + r * μ := by
                rw [hx0_abs]
                gcongr
          _ < r := by
                nlinarith [hr, hμ_pos]
      have hz_norm :
          ‖((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ < r := by
        have htriangle :
            ‖((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ ≤
              |(4 * r) * t - r| + |u| := by
          -- The affine real part and the vertical displacement contribute additively to the norm.
          calc
            ‖((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖
                ≤ ‖(((4 * r) * t - r : ℝ) : ℂ)‖ + ‖(u : ℂ) * Complex.I‖ := norm_add_le _ _
            _ = |(4 * r) * t - r| + |u| := by
                  rw [Complex.norm_real, norm_mul]
                  simp
        refine lt_of_le_of_lt htriangle ?_
        calc
          |(4 * r) * t - r| + |u|
              < (r * (1 - 4 * μ) + r * μ) + r * μ := by
                have hx_bound : |(4 * r) * t - r| < r * (1 - 4 * μ) + r * μ := by
                  calc
                    |(4 * r) * t - r|
                        = |((4 * r) * t₀ - r) +
                            (((4 * r) * t - r) - ((4 * r) * t₀ - r))| := by ring_nf
                    _ ≤ |(4 * r) * t₀ - r| +
                          |((4 * r) * t - r) - ((4 * r) * t₀ - r)| := abs_add_le _ _
                    _ < r * (1 - 4 * μ) + r * μ := by
                          rw [hx0_abs]
                          gcongr
                gcongr
          _ < r := by
            nlinarith [hr, hμ_pos]
      have hz_im :
          0 < (((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I)).im := by
        -- Positive height is exactly positive imaginary part on this affine strip.
        simpa using hu_pos
      exact mem_interior_upper_half_disk_of_norm_lt_im_pos hz_norm hz_im

/-- Helper for Proposition 3.1: moving a semicircle point by the inward unit normal only changes
the radius, replacing `r` by `r - u`. -/
lemma upper_half_disk_arc_add_real_mul_inward_eq_circleMap_radius_sub
    {r u θ : ℝ} :
    circleMap 0 r θ + (u : ℂ) * (-Complex.exp (θ * Complex.I)) =
      circleMap 0 (r - u) θ := by
  -- Route correction: normalize the radial tube to a pure `circleMap` radius change before any
  -- side-condition estimates.
  rw [circleMap_zero, circleMap_zero]
  calc
    (r : ℂ) * Complex.exp (θ * Complex.I) + (u : ℂ) * (-Complex.exp (θ * Complex.I))
        = (r : ℂ) * Complex.exp (θ * Complex.I) - (u : ℂ) * Complex.exp (θ * Complex.I) := by
            ring
    _ = ((r : ℂ) - (u : ℂ)) * Complex.exp (θ * Complex.I) := by
          ring
    _ = (((r - u : ℝ)) : ℂ) * Complex.exp (θ * Complex.I) := by
          simp

/-- Helper for Proposition 3.1: near any regular point of the upper-semicircle branch, decreasing
the radius exits the closed semidisk while increasing it enters the interior. -/
lemma upper_half_disk_arc_local_strip_data
    {r t₀ : ℝ} (hr : 0 < r) (ht₀ : t₀ ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ eps_t eps_u, 0 < eps_t ∧ 0 < eps_u ∧ eps_u < r ∧
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (1 / 2 : ℝ) 1 ∧
      ∀ {t u : ℝ},
        t ∈ Set.Ioo (t₀ - eps_t) (t₀ + eps_t) →
        u ∈ Set.Ioo (-eps_u) eps_u →
        (u < 0 →
          circleMap 0 (r - u) (Real.pi * (2 * t - 1)) ∉
            ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)) ∧
        (0 < u →
          circleMap 0 (r - u) (Real.pi * (2 * t - 1)) ∈
            interior ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)) := by
  let μ : ℝ := min (t₀ - 1 / 2) (1 - t₀)
  have hμ_pos : 0 < μ := by
    -- The regular arc parameter stays a positive distance away from both arc endpoints.
    exact lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
  refine ⟨μ / 4, r / 2, by positivity, by positivity, ?_, ?_, ?_⟩
  · -- The chosen radial strip stays strictly inside the positive radius regime.
    nlinarith [hr]
  · intro t ht
    constructor
    · -- The `t`-strip remains on the open arc branch, away from the midpoint corner.
      have hμ_le : μ ≤ t₀ - 1 / 2 := min_le_left _ _
      have hleft : 1 / 2 < t₀ - μ / 4 := by
        nlinarith [hμ_pos, hμ_le]
      exact lt_trans hleft ht.1
    · have hμ_le : μ ≤ 1 - t₀ := min_le_right _ _
      have hright : t₀ + μ / 4 < 1 := by
        nlinarith [hμ_pos, hμ_le]
      exact lt_trans ht.2 hright
  · intro t u ht hu
    have htArc : t ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
      -- First move from the local strip back to the actual arc-branch parameter interval.
      have hstrip_param :
          Set.Ioo (t₀ - μ / 4) (t₀ + μ / 4) ⊆ Set.Ioo (1 / 2 : ℝ) 1 := by
        intro s hs
        constructor
        · have hμ_le : μ ≤ t₀ - 1 / 2 := min_le_left _ _
          have hleft : 1 / 2 < t₀ - μ / 4 := by
            nlinarith [hμ_pos, hμ_le]
          exact lt_trans hleft hs.1
        · have hμ_le : μ ≤ 1 - t₀ := min_le_right _ _
          have hright : t₀ + μ / 4 < 1 := by
            nlinarith [hμ_pos, hμ_le]
          exact lt_trans hs.2 hright
      exact hstrip_param ht
    have htheta :
        Real.pi * (2 * t - 1) ∈ Set.Ioo (0 : ℝ) Real.pi := by
      -- On the open arc branch, the normalized angle lies strictly between `0` and `π`.
      constructor
      · nlinarith [Real.pi_pos, htArc.1]
      · nlinarith [Real.pi_pos, htArc.2]
    constructor
    · intro hu_neg hz
      -- Negative transverse height increases the radius beyond `r`, so the point leaves the
      -- closed semidisk already by the norm bound.
      have hrad_nonneg : 0 ≤ r - u := by
        linarith
      have hrad_gt : r < r - u := by
        linarith
      have hz_norm :
          ‖circleMap 0 (r - u) (Real.pi * (2 * t - 1))‖ ≤ r := hz.1
      rw [norm_circleMap_upper_semicircle hrad_nonneg] at hz_norm
      exact (not_le_of_gt hrad_gt) hz_norm
    · intro hu_pos
      have hrad_nonneg : 0 ≤ r - u := by
        nlinarith [hr, hu.2]
      have hrad_pos : 0 < r - u := by
        nlinarith [hr, hu.2]
      have hz_norm :
          ‖circleMap 0 (r - u) (Real.pi * (2 * t - 1))‖ < r := by
        rw [norm_circleMap_upper_semicircle hrad_nonneg]
        nlinarith
      have hz_im :
          0 < (circleMap 0 (r - u) (Real.pi * (2 * t - 1))).im := by
        -- Positive radius together with `0 < θ < π` keeps the point strictly above the real axis.
        rw [circleMap_zero_im]
        exact mul_pos hrad_pos (Real.sin_pos_of_mem_Ioo htheta)
      exact mem_interior_upper_half_disk_of_norm_lt_im_pos hz_norm hz_im

/-- Helper for Proposition 3.1: the local diameter strip data packages directly into an explicit
affine boundary-straightening chart on `Plane`. -/
lemma upper_half_disk_affine_strip_chart_exists
    {r t₀ eps_t eps_u : ℝ} (hr : 0 < r)
    (hεt_pos : 0 < eps_t) (hεu_pos : 0 < eps_u)
    (hstrip_param : Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hstrip_side :
      ∀ {t u : ℝ},
        t ∈ Set.Ioo (t₀ - eps_t) (t₀ + eps_t) →
        u ∈ Set.Ioo (-eps_u) eps_u →
        (u < 0 →
          ((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I) ∉
            ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)) ∧
        (0 < u →
          ((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I) ∈
            interior ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ))) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt
        ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
        ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t₀ δ := by
  let hx : ℝ ≃ₜ ℝ :=
    (Homeomorph.smulOfNeZero (4 * r) (by positivity : (4 * r) ≠ 0)).trans
      (Homeomorph.addRight (-r))
  let δ₀ : Plane ≃ₜ Plane := hx.prodCongr (Homeomorph.refl ℝ)
  let δ₁ : OpenPartialHomeomorph Plane Plane := δ₀.toOpenPartialHomeomorph
  let strip : Set Plane :=
    Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ×ˢ Set.Ioo (-eps_u) eps_u
  let δ : OpenPartialHomeomorph Plane Plane := δ₁.restrOpen strip (isOpen_Ioo.prod isOpen_Ioo)
  have hδ₁_source : (t₀, 0) ∈ δ₁.source := by
    simp [δ₁, δ₀, hx]
  have hsource_subset : δ.source ⊆ δ₁.source := by
    intro p hp
    exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp).1
  have htarget_subset : δ.target ⊆ δ₁.target := by
    intro q hq
    exact (show q ∈ δ₁.target ∩ δ₁.symm ⁻¹' strip by simpa [δ, strip] using hq).1
  have hδ_contDiff :
      ContDiffOn ℝ 1 δ δ.source := by
    -- The restricted chart still has the same global affine forward formula.
    have hglobal :
        ContDiff ℝ 1 (fun p : Plane ↦ (((4 * r) * p.1 - r), p.2)) := by
      fun_prop
    simpa [δ, δ₁, δ₀, hx, strip] using hglobal.contDiffOn
  have hδsymm_contDiff :
      ContDiffOn ℝ 1 δ.symm δ.target := by
    -- The inverse chart is again affine: undo the translation and divide by `4r`.
    have hglobal :
        ContDiff ℝ 1 (fun p : Plane ↦ (((p.1 + r) / (4 * r)), p.2)) := by
      fun_prop
    have hsymm_formula :
        (δ.symm : Plane → Plane) = fun p : Plane ↦ (((p.1 + r) / (4 * r)), p.2) := by
      ext p
      · simp [δ, δ₁, δ₀, hx, div_eq_mul_inv, sub_eq_add_neg]
        have hadd : (Homeomorph.addRight (-r)).symm p.1 = p.1 + r := by
          simp [Homeomorph.addRight]
        rw [hadd]
        ring
      · simp [δ, δ₁, δ₀, hx]
    simpa [hsymm_formula] using hglobal.contDiffOn
  have hmap_axis :
      ∀ {t : ℝ}, t ∈ δ.horizontalAxisDomain →
        δ (t, 0) = ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t := by
    intro t ht
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    have htIoo : t ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) := hstrip_param htStrip.1
    have htIcc : t ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) := ⟨htIoo.1.le, htIoo.2.le⟩
    calc
      δ (t, 0) = (((4 * r) * t - r), 0) := by
        simp [δ, δ₁, δ₀, hx, sub_eq_add_neg]
      _ = Complex.equivRealProd ((((4 * r) * t - r : ℝ) : ℂ)) := by
        simp [Complex.equivRealProd]
      _ = ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t := by
        symm
        exact upper_half_disk_boundary_realCurve_eqOn_diameter_interval r htIcc
  refine ⟨δ, ?_⟩
  refine
    { basePoint_mem_source := ?_
      source_subset := ?_
      contDiffOn := hδ_contDiff
      contDiffOn_symm := hδsymm_contDiff
      map_horizontal_axis := fun ht ↦ hmap_axis ht
      isImage_horizontalAxis := ?_
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- The base point belongs to the explicit strip centered at `(t₀, 0)`.
    have hstrip : (t₀, 0) ∈ strip := by
      constructor
      · constructor <;> linarith
      · constructor <;> linarith
    simpa [δ, strip] using And.intro hδ₁_source hstrip
  · intro p hp
    -- The source restriction keeps the parameter inside the local diameter branch, hence in `(0,1)`.
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp).2
    have hpBranch : p.1 ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) := hstrip_param hpStrip.1
    exact ⟨⟨hpBranch.1, lt_trans hpBranch.2 (by norm_num)⟩, Set.mem_univ _⟩
  · -- The chart image of the diameter branch is exactly the horizontal axis in the restricted strip.
    apply curve_image_is_horizontal_axis
    intro t ht
    exact hmap_axis ht
  · rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rcases hz.1 with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp.1).2
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          ((((4 * r) * p.1 - r : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) := by
      rw [Complex.equivRealProdCLM_symm_apply]
      simp [δ, δ₁, δ₀, hx, mul_comm, mul_left_comm, mul_assoc]
      ring
    have houtside :
        Complex.equivRealProdCLM.symm (δ p) ∉ ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) := by
      rw [hformula]
      exact (hstrip_side hpStrip.1 hpStrip.2).1 hp.2
    exact houtside hz.2
  · intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp.1).2
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          ((((4 * r) * p.1 - r : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) := by
      rw [Complex.equivRealProdCLM_symm_apply]
      simp [δ, δ₁, δ₀, hx, mul_comm, mul_left_comm, mul_assoc]
      ring
    -- Positive transverse height enters the semidisk interior by the local strip estimates.
    rw [hformula]
    exact (hstrip_side hpStrip.1 hpStrip.2).2 hp.2

/-- Helper for Proposition 3.1: every regular parameter on the open diameter branch admits an
explicit affine boundary-straightening chart for the closed upper semidisk. -/
lemma upper_half_disk_boundary_diameter_branch_exists_boundary_chart
    {r : ℝ} (hr : 0 < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt
        ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
        ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: the quantitative strip estimates are now isolated in
  -- `upper_half_disk_diameter_local_strip_data`, so the remaining work is to package that affine
  -- strip as an `OpenPartialHomeomorph` and feed the side estimates into
  -- `IsBoundaryStraighteningAt.exterior_on_right` and `.interior_on_left`.
  obtain ⟨eps_t, eps_u, hεt_pos, hεu_pos, hstrip_param, hstrip_side⟩ :=
    upper_half_disk_diameter_local_strip_data hr ht₀
  exact upper_half_disk_affine_strip_chart_exists
    hr hεt_pos hεu_pos hstrip_param hstrip_side

/-- Helper for Proposition 3.1: every regular parameter on the open upper-semicircle branch
admits an explicit radial boundary-straightening chart for the closed upper semidisk. -/
lemma upper_half_disk_boundary_arc_branch_exists_boundary_chart
    {r : ℝ} (hr : 0 < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt
        ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
        ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: normalize the radial tube first with
  -- `upper_half_disk_arc_add_real_mul_inward_eq_circleMap_radius_sub`, then package the resulting
  -- radius/angle strip as the arc branch boundary chart.
  obtain ⟨eps_t, eps_u, hεt_pos, hεu_pos, hεu_lt, hstrip_param, hstrip_side⟩ :=
    upper_half_disk_arc_local_strip_data hr ht₀
  let θ : ℝ → ℝ := fun t ↦ Real.pi * (2 * t - 1)
  let γ : ℝ → ℂ := fun t ↦ circleMap 0 r (θ t)
  let n : ℝ → ℂ := fun t ↦ -Complex.exp (θ t * Complex.I)
  let tangent : ℂ := (2 * Real.pi : ℝ) • (circleMap 0 r (θ t₀) * Complex.I)
  let Ψ : Plane → ℂ := fun p ↦ γ p.1 + p.2 • n p.1
  let Φ : Plane → Plane := fun p ↦ Complex.equivRealProd (Ψ p)
  have _hkeep_radius : eps_u < r := hεu_lt
  have hθCont : ContDiffAt ℝ 1 θ t₀ := by
    -- The semicircle angle is an affine function of the source parameter.
    have hθ : ContDiff ℝ 1 θ := by
      fun_prop
    exact hθ.contDiffAt
  have hγCont : ContDiffAt ℝ 1 γ t₀ := by
    -- The boundary branch is smooth after composing `circleMap` with the affine angle.
    simpa [γ] using (contDiff_circleMap 0 r).contDiffAt.comp t₀ hθCont
  have hnCont : ContDiffAt ℝ 1 n t₀ := by
    -- The inward radial field varies smoothly along the open arc branch.
    have hθComplex : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ)) t₀ := by
      simpa using (Complex.ofRealCLM.contDiff.contDiffAt.comp t₀ hθCont)
    have hinner : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ) * Complex.I) t₀ := by
      simpa [one_mul] using hθComplex.mul contDiffAt_const
    simpa [n] using (Complex.contDiff_exp.contDiffAt.comp t₀ hinner).neg
  have hγDeriv : HasDerivAt γ tangent t₀ := by
    -- Differentiate the upper-semicircle branch by the chain rule.
    simpa [γ, tangent] using
      ((hasDerivAt_circleMap 0 r (θ t₀)).scomp t₀ (upper_half_disk_arc_arg_hasDerivAt t₀))
  have htangent_formula :
      tangent = ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
        Complex.exp (θ t₀ * Complex.I) := by
    -- Rewrite the chain-rule derivative into the explicit tangent form used by the frame lemma.
    calc
      tangent = ((2 * Real.pi : ℝ) : ℂ) * (circleMap 0 r (θ t₀) * Complex.I) := by
        simp [tangent, smul_eq_mul]
      _ = ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
          Complex.exp (θ t₀ * Complex.I) := by
            rw [circleMap, zero_add]
            simp [mul_assoc, mul_left_comm, mul_comm]
  obtain ⟨hΨcont, hΨderiv⟩ := upper_half_disk_radial_tube_hasFDerivAt
    (γ := γ) (n := n) (t₀ := t₀) (v := tangent) hγCont hγDeriv hnCont
  have hΦcont : ContDiffAt ℝ 1 Φ (t₀, 0) := by
    -- Converting the complex tube to plane coordinates preserves the `C¹` regularity.
    simpa [Φ] using
      ((Complex.equivRealProdCLM : ℂ ≃L[ℝ] Plane).comp_contDiffAt_iff).2 hΨcont
  let v : Plane := Complex.equivRealProd tangent
  let radial : Plane := Complex.equivRealProd (n t₀)
  have hv : v ≠ 0 := by
    -- The arc tangent is nonzero because both the radius and the exponential factor are nonzero.
    intro hv0
    have htangent : tangent = 0 := by
      exact Complex.equivRealProd.injective (by simpa [v] using hv0)
    have hscale : ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      exact_mod_cast mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hr.ne'
    have hmul :
        ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
          Complex.exp (θ t₀ * Complex.I) = 0 := by
      simpa [htangent_formula] using htangent
    exact Complex.exp_ne_zero (θ t₀ * Complex.I) ((mul_eq_zero.mp hmul).resolve_left hscale)
  have hrot : rot90 v = (2 * Real.pi * r) • radial := by
    -- Quarter-turning the tangent gives the inward radial direction on the semicircle.
    simpa [v, radial, n, θ, htangent_formula] using
      upper_half_disk_arc_rot90_tangent_eq_scaled_inward (r := r) (t₀ := t₀)
  obtain ⟨e₀, he₀⟩ := rot90_frame_equiv_of_ne_zero v hv
  let c : ℝ := 2 * Real.pi * r
  have hc : c ≠ 0 := by
    positivity
  let e : Plane ≃L[ℝ] Plane := (upper_half_disk_plane_second_rescale c hc).trans e₀
  have hderiv_map :
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] Plane).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight tangent +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (n t₀))) =
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial := by
    -- Convert the complex tangent/normal columns to their plane-coordinate versions.
    apply ContinuousLinearMap.ext
    intro q
    rcases q with ⟨x, y⟩
    simp [ContinuousLinearMap.comp_apply, v, radial, ContinuousLinearMap.smulRight_apply]
  have hΦderiv :
      HasFDerivAt Φ
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial)
        (t₀, 0) := by
    -- The real-plane tube has tangent column `v` and inward-normal column `radial`.
    simpa [Φ, hderiv_map] using
      ((Complex.equivRealProdCLM : ℂ ≃L[ℝ] Plane).comp_hasFDerivAt_iff).2 hΨderiv
  have he : (e : Plane →L[ℝ] Plane) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial := by
    -- Rescaling the second frame coordinate turns the `rot90` column into the actual inward
    -- radial column.
    apply ContinuousLinearMap.ext
    intro q
    rcases q with ⟨x, y⟩
    change e₀ (x, y / c) = x • v + y • radial
    calc
      e₀ (x, y / c) = x • v + (y / c) • rot90 v := by
        simpa [ContinuousLinearMap.smulRight_apply] using
          congrArg (fun f : Plane →L[ℝ] Plane => f (x, y / c)) he₀
      _ = x • v + (y / c) • (c • radial) := by
            rw [hrot]
      _ = x • v + (((y / c) * c) • radial) := by
            rw [smul_smul]
      _ = x • v + y • radial := by
            have hyc : y * c⁻¹ * c = y := by
              calc
                y * c⁻¹ * c = y * (c⁻¹ * c) := by ring
                _ = y := by simp [hc]
            simp [div_eq_mul_inv, hyc]
  have hΦderiv' : HasFDerivAt Φ (e : Plane →L[ℝ] Plane) (t₀, 0) := by
    -- This is the invertible derivative required by the inverse function theorem.
    simpa [he] using hΦderiv
  let δ₀ : OpenPartialHomeomorph Plane Plane :=
    hΦcont.toOpenPartialHomeomorph Φ hΦderiv' one_ne_zero
  let δ₁ : OpenPartialHomeomorph Plane Plane := δ₀.restrContDiff ℝ 1 (by norm_num)
  let strip : Set Plane :=
    Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ×ˢ Set.Ioo (-eps_u) eps_u
  let δ : OpenPartialHomeomorph Plane Plane := δ₁.restrOpen strip (isOpen_Ioo.prod isOpen_Ioo)
  have hδ₀_source : (t₀, 0) ∈ δ₀.source := by
    -- The inverse function theorem keeps the base point in the source chart.
    exact hΦcont.mem_toOpenPartialHomeomorph_source hΦderiv' one_ne_zero
  have hδ₀_symm : ContDiffAt ℝ 1 δ₀.symm (Φ (t₀, 0)) := by
    -- The local inverse remains `C¹` at the image of the base point.
    simpa [δ₀, Φ] using hΦcont.to_localInverse hΦderiv' one_ne_zero
  have hδ₁_source : (t₀, 0) ∈ δ₁.source := by
    -- Restricting to the `C¹` locus keeps the base point available.
    simpa [δ₁, δ₀, Φ] using And.intro hδ₀_source (And.intro hΦcont hδ₀_symm)
  have hsource_subset : δ.source ⊆ δ₁.source := by
    intro p hp
    exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp).1
  have htarget_subset : δ.target ⊆ δ₁.target := by
    intro q hq
    exact (show q ∈ δ₁.target ∩ δ₁.symm ⁻¹' strip by simpa [δ, strip] using hq).1
  refine ⟨δ, ?_⟩
  refine
    { basePoint_mem_source := ?_
      source_subset := ?_
      contDiffOn := ?_
      contDiffOn_symm := ?_
      map_horizontal_axis := ?_
      isImage_horizontalAxis := ?_
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- The base point lies in the local strip because `t₀` is centered there and `0` is between
    -- `-eps_u` and `eps_u`.
    have hstrip : (t₀, 0) ∈ strip := by
      constructor
      · constructor <;> linarith
      · constructor <;> linarith
    simpa [δ, strip] using And.intro hδ₁_source hstrip
  · -- The source restriction keeps the first coordinate on the open arc branch.
    intro p hp
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp).2
    exact ⟨⟨by linarith [(hstrip_param hpStrip.1).1], (hstrip_param hpStrip.1).2⟩, Set.mem_univ _⟩
  · -- Restricting the inverse-function chart preserves the `C¹` regularity on the smaller
    -- source.
    exact
      (OpenPartialHomeomorph.contDiffOn_restrContDiff_source (𝕜 := ℝ) (f := δ₀)
        (n := 1) (by norm_num)).mono hsource_subset
  · -- The same inheritance applies to the local inverse on the smaller target.
    exact
      (OpenPartialHomeomorph.contDiffOn_restrContDiff_target (𝕜 := ℝ) (f := δ₀)
        (n := 1) (by norm_num)).mono htarget_subset
  · intro t ht
    -- Along the horizontal axis, the chart reproduces the arc branch of the semidisk contour.
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    have htIcc : t ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨(hstrip_param htStrip.1).1.le, (hstrip_param htStrip.1).2.le⟩
    calc
      δ (t, 0) = Complex.equivRealProd (γ t) := by
        simp [δ, δ₁, δ₀, Φ, Ψ]
      _ = Complex.equivRealProd (circleMap 0 r (Real.pi * (2 * t - 1))) := by
            simp [γ, θ]
      _ = ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t := by
            symm
            exact upper_half_disk_boundary_realCurve_eqOn_arc_interval r htIcc
  · -- The chart image of the arc branch is exactly the horizontal axis in the restricted strip.
    apply curve_image_is_horizontal_axis
    intro t ht
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    have htIcc : t ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨(hstrip_param htStrip.1).1.le, (hstrip_param htStrip.1).2.le⟩
    calc
      δ (t, 0) = Complex.equivRealProd (γ t) := by
        simp [δ, δ₁, δ₀, Φ, Ψ]
      _ = Complex.equivRealProd (circleMap 0 r (Real.pi * (2 * t - 1))) := by
            simp [γ, θ]
      _ = ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t := by
            symm
            exact upper_half_disk_boundary_realCurve_eqOn_arc_interval r htIcc
  · rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rcases hz.1 with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp.1).2
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          circleMap 0 (r - p.2) (θ p.1) := by
      calc
        Complex.equivRealProdCLM.symm (δ p) = Complex.equivRealProdCLM.symm (Φ p) := by
          simp [δ, δ₁, δ₀]
        _ = Ψ p := by
            rw [Complex.equivRealProdCLM_symm_apply]
            exact Complex.re_add_im (Ψ p)
        _ = γ p.1 + p.2 • n p.1 := by
            simp [Ψ]
        _ = circleMap 0 r (θ p.1) + (p.2 : ℂ) * (-Complex.exp (θ p.1 * Complex.I)) := by
            simp [γ, n, smul_eq_mul]
        _ = circleMap 0 (r - p.2) (θ p.1) := by
            rw [upper_half_disk_arc_add_real_mul_inward_eq_circleMap_radius_sub]
    have houtside :
        Complex.equivRealProdCLM.symm (δ p) ∉ ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) := by
      rw [hformula]
      exact (hstrip_side hpStrip.1 hpStrip.2).1 hp.2
    exact houtside hz.2
  · intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpStrip : p ∈ strip := by
      exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp.1).2
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          circleMap 0 (r - p.2) (θ p.1) := by
      calc
        Complex.equivRealProdCLM.symm (δ p) = Complex.equivRealProdCLM.symm (Φ p) := by
          simp [δ, δ₁, δ₀]
        _ = Ψ p := by
            rw [Complex.equivRealProdCLM_symm_apply]
            exact Complex.re_add_im (Ψ p)
        _ = γ p.1 + p.2 • n p.1 := by
            simp [Ψ]
        _ = circleMap 0 r (θ p.1) + (p.2 : ℂ) * (-Complex.exp (θ p.1 * Complex.I)) := by
            simp [γ, n, smul_eq_mul]
        _ = circleMap 0 (r - p.2) (θ p.1) := by
            rw [upper_half_disk_arc_add_real_mul_inward_eq_circleMap_radius_sub]
    -- Positive transverse height enters the semidisk interior by the local strip estimates.
    rw [hformula]
    exact (hstrip_side hpStrip.1 hpStrip.2).2 hp.2

/-- Helper for Proposition 3.1: every regular interior parameter of the explicit semidisk contour
admits a local boundary-straightening chart for the closed upper half-disk. -/
lemma upper_half_disk_boundary_exists_boundary_straightening_at_regular_point
    {r : ℝ} (hr : 0 < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt
        ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
        ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: first exclude the midpoint corner, then dispatch to the explicit affine or
  -- radial chart depending on whether the regular parameter lies on the diameter or the arc.
  let _ := hderiv
  rcases upper_half_disk_boundary_regular_parameter_mem_branch hr ht₀ hdiff with hdiam | harc
  · exact upper_half_disk_boundary_diameter_branch_exists_boundary_chart hr hdiam
  · exact upper_half_disk_boundary_arc_branch_exists_boundary_chart hr harc

/-- Helper for Proposition 3.1: the explicit semidisk contour is an oriented boundary of the
closed upper half-disk. -/
theorem upper_half_disk_boundary_isOrientedBoundaryOf {r : ℝ} (hr : 0 < r) :
    IsOrientedBoundaryOf ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
      (fun _ : Unit ↦ (upperHalfDiskBoundaryPath r).toClosedPath) := by
  classical
  let K : Set ℂ := {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im}
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (upperHalfDiskBoundaryPath r).toClosedPath
  change IsOrientedBoundaryOf K Γ
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- The semidisk is the intersection of a compact closed ball with the closed upper half-plane.
    let K' : Set ℂ := Metric.closedBall (0 : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}
    have hK' : IsCompact K' := by
      exact (isCompact_closedBall (0 : ℂ) r).inter_right
        (isClosed_le continuous_const Complex.continuous_im)
    convert hK' using 1
    ext z
    simp [K', K, Metric.mem_closedBall, dist_eq_norm]
  · rintro ⟨⟩
    -- The singleton closed-path family inherits the explicit contour regularity.
    simpa [Γ, Path.toClosedPath] using upper_half_disk_boundary_isPiecewiseDifferentiable r
  · rintro ⟨⟩ s t hst
    -- Simplicity is already proved directly from the diameter/arc branch decomposition.
    simpa [Γ, Path.toClosedPath] using upper_half_disk_boundary_simple_eq_or_endpoints hr hst
  · intro i j hij
    -- A singleton family is pairwise disjoint for the trivial reason.
    exact (hij rfl).elim
  · -- Collapse the singleton family back to the explicit contour and rewrite its range as the
    -- semidisk frontier.
    calc
      (⋃ i : Unit, Set.range (Γ i).toPath) = Set.range (upperHalfDiskBoundaryPath r) := by
          simpa [Γ] using upper_half_disk_boundary_singleton_iUnion_range r
      _ = frontier K := by
          simpa [K] using upper_half_disk_boundary_path_range_eq_frontier hr
  · rintro ⟨⟩ t₀ ht₀ hdiff hderiv
    -- The only geometric input not already encoded above is the regular-point straightening
    -- chart for this explicit semidisk contour.
    simpa [K, Γ] using
      upper_half_disk_boundary_exists_boundary_straightening_at_regular_point
        (r := r) hr ht₀ hdiff hderiv

/-- Helper for Proposition 3.1: the curve integral along the real diameter `[-r, r]` is the
ordinary interval integral on the real axis. -/
lemma upper_half_disk_diameter_curveIntegral_eq_intervalIntegral
    (g : ℂ → ℂ) (r : ℝ) :
    ∫ᶜ z in Path.segment (-(r : ℂ)) (r : ℂ), (g dz) z =
      ∫ x in -r..r, g (x : ℂ) := by
  -- Rewrite the diameter integral through the affine segment parametrization `x = (2r)t - r`.
  rw [curveIntegral_segment]
  have hline :
      ∀ t : ℝ,
        AffineMap.lineMap (-(r : ℂ)) (r : ℂ) t = (((2 * r) * t - r : ℝ) : ℂ) := by
    intro t
    apply Complex.ext <;> simp [AffineMap.lineMap_apply, sub_eq_add_neg]
    ring
  have hdir : (r : ℂ) - (-(r : ℂ)) = (((2 * r : ℝ)) : ℂ) := by
    simp [two_mul]
  calc
    ∫ t in (0 : ℝ)..1,
        (g dz) (AffineMap.lineMap (-(r : ℂ)) (r : ℂ) t) ((r : ℂ) - (-(r : ℂ))) =
        ∫ t in (0 : ℝ)..1, (((2 * r : ℝ)) : ℂ) * g ((((2 * r) * t - r : ℝ) : ℂ)) := by
          refine intervalIntegral.integral_congr_ae ?_
          refine Filter.Eventually.of_forall ?_
          intro t ht
          rw [hline, hdir, Complex.scalarOneForm_apply]
    _ = (((2 * r : ℝ)) : ℂ) * ∫ t in (0 : ℝ)..1, g ((((2 * r) * t - r : ℝ) : ℂ)) := by
          rw [intervalIntegral.integral_const_mul]
    _ = (2 * r) • ∫ t in (0 : ℝ)..1, g ((((2 * r) * t - r : ℝ) : ℂ)) := by
          simp
    _ = ∫ x in (2 * r) * (0 : ℝ) + -r..(2 * r) * 1 + -r, g (x : ℂ) := by
          simpa using
            (intervalIntegral.smul_integral_comp_mul_add
              (f := fun x : ℝ ↦ g (x : ℂ)) (a := (0 : ℝ)) (b := 1) (c := 2 * r) (d := -r))
    _ = ∫ x in -r..r, g (x : ℂ) := by
          ring_nf

/-- Helper for Proposition 3.1: once both boundary pieces are curve-integrable, the explicit
upper-half-disk contour integral splits into the diameter contribution plus the arc contribution. -/
lemma upper_half_disk_boundary_curveIntegral_eq_diameter_add_arc
    (g : ℂ → ℂ) {r : ℝ}
    (hdiam : CurveIntegrable (g dz) (Path.segment (-(r : ℂ)) (r : ℂ)))
    (harc : CurveIntegrable (g dz) (upperSemicirclePath r)) :
    ∫ᶜ z in upperHalfDiskBoundaryPath r, (g dz) z =
      (∫ᶜ z in Path.segment (-(r : ℂ)) (r : ℂ), (g dz) z) +
        ∫ᶜ z in upperSemicirclePath r, (g dz) z := by
  -- Expand the concatenated contour into its two curve-integrable source pieces.
  simpa [upperHalfDiskBoundaryPath] using curveIntegral_trans hdiam harc

/-- Helper for Proposition 3.1: the explicit upper-semicircle path integral is exactly the
source-facing sector-arc integral on `0 ≤ θ ≤ π`. -/
lemma upper_semicircle_curveIntegral_eq_sectorArcIntegral
    (g : ℂ → ℂ) (r : ℝ) :
    ∫ᶜ z in upperSemicirclePath r, (g dz) z =
      sectorArcIntegral g r 0 Real.pi := by
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun z ↦ (g dz) z
  let h : ℝ → ℂ := fun θ ↦ ω (circleMap 0 r θ) (deriv (circleMap 0 r) θ)
  have hcongr_ae :
      (fun t : ℝ ↦
        ω ((upperSemicirclePath r).extend t) (deriv ((upperSemicirclePath r).extend) t))
        =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)]
          (fun t ↦ (Real.pi : ℝ) • h (t * Real.pi)) := by
    rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have hlocal :
        (upperSemicirclePath r).extend =ᶠ[nhds t]
          fun s : ℝ ↦ circleMap 0 r (s * Real.pi) := by
      have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
      filter_upwards [hIoo] with s hs
      have hline : AffineMap.lineMap (0 : ℝ) Real.pi s = s * Real.pi := by
        simp [AffineMap.lineMap_apply_module]
      rw [Path.extend_apply (upperSemicirclePath r) ⟨hs.1.le, hs.2.le⟩]
      simp [upperSemicirclePath, Path.map_coe, Path.segment_apply, hline]
    have hderiv :
        deriv (upperSemicirclePath r).extend t =
          (Real.pi : ℂ) * deriv (circleMap 0 r) (t * Real.pi) := by
      rw [Filter.EventuallyEq.deriv_eq hlocal]
      simpa [smul_eq_mul] using
        (((hasDerivAt_circleMap 0 r (t * Real.pi)).scomp t
          (hasDerivAt_mul_const (Real.pi : ℝ))).deriv)
    have hext :
        (upperSemicirclePath r).extend t = circleMap 0 r (t * Real.pi) :=
      Filter.EventuallyEq.eq_of_nhds hlocal
    -- Evaluate the scalar one-form on the chain-rule tangent vector of the upper semicircle.
    calc
      ω ((upperSemicirclePath r).extend t) (deriv ((upperSemicirclePath r).extend) t) =
          ω (circleMap 0 r (t * Real.pi))
            ((Real.pi : ℂ) * deriv (circleMap 0 r) (t * Real.pi)) := by
        rw [hext, hderiv]
      _ = (Real.pi : ℝ) • h (t * Real.pi) := by
        simp [h, ω, smul_eq_mul, Complex.scalarOneForm_apply, deriv_circleMap, mul_assoc,
          mul_comm, mul_left_comm]
  have hsmul :
      ∫ t in (0 : ℝ)..1, (Real.pi : ℝ) • h (t * Real.pi) =
        (Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * Real.pi) := by
    simpa using intervalIntegral.integral_smul (a := (0 : ℝ)) (b := 1)
      (r := (Real.pi : ℝ)) (f := fun t ↦ h (t * Real.pi))
  -- Rewrite the curve integral into the angular interval form and then perform `θ = π t`.
  rw [curveIntegral_eq_intervalIntegral_deriv, sectorArcIntegral_def]
  calc
    ∫ t in (0 : ℝ)..1,
        ω ((upperSemicirclePath r).extend t) (deriv ((upperSemicirclePath r).extend) t) =
      ∫ t in (0 : ℝ)..1, (Real.pi : ℝ) • h (t * Real.pi) := by
        exact intervalIntegral.integral_congr_ae_restrict hcongr_ae
    _ = (Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * Real.pi) := hsmul
    _ = ∫ θ in (0 : ℝ) * Real.pi..1 * Real.pi, h θ := by
          simpa using
            (intervalIntegral.smul_integral_comp_mul_right
              (f := h) (a := (0 : ℝ)) (b := 1) (c := Real.pi))
    _ = ∫ θ in (0 : ℝ)..Real.pi, h θ := by
          simp
    _ = ∫ θ in (0 : ℝ)..Real.pi, Complex.I * circleMap 0 r θ * g (circleMap 0 r θ) := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards with θ
          simp [h, ω, Complex.scalarOneForm_apply, deriv_circleMap, mul_assoc, mul_comm,
            mul_left_comm]

/-- Helper for Proposition 3.1: once the boundary is split into the diameter and the upper
semicircle, both source-facing rewrites can be performed in one step. -/
lemma upper_half_disk_boundary_curveIntegral_eq_intervalIntegral_add_sectorArcIntegral
    (g : ℂ → ℂ) {r : ℝ}
    (hdiam : CurveIntegrable (g dz) (Path.segment (-(r : ℂ)) (r : ℂ)))
    (harc : CurveIntegrable (g dz) (upperSemicirclePath r)) :
    ∫ᶜ z in upperHalfDiskBoundaryPath r, (g dz) z =
      (∫ x in -r..r, g (x : ℂ)) + sectorArcIntegral g r 0 Real.pi := by
  -- First split the contour into its diameter and arc pieces, then rewrite each piece in the
  -- source coordinates used by Proposition 3.1.
  rw [upper_half_disk_boundary_curveIntegral_eq_diameter_add_arc (g := g) hdiam harc,
    upper_half_disk_diameter_curveIntegral_eq_intervalIntegral,
    upper_semicircle_curveIntegral_eq_sectorArcIntegral]

/-- Helper for Proposition 3.1: if a closed ball stays in the strict upper half-plane and its
center-plus-radius is strictly smaller than `r`, then that whole ball lies in the interior of the
closed upper half-disk of radius `r`. -/
lemma closedBall_subset_interior_upper_half_disk_of_upper_half_plane
    {z : ℂ} {ρ r : ℝ}
    (hupper : Metric.closedBall z ρ ⊆ {w : ℂ | 0 < w.im})
    (hlarge : ‖z‖ + ρ < r) :
    Metric.closedBall z ρ ⊆ interior ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) := by
  let V : Set ℂ := Metric.ball (0 : ℂ) r ∩ {w : ℂ | 0 < w.im}
  have hV_open : IsOpen V := by
    -- The strict-radius/strict-imaginary-part model is open in `ℂ`.
    exact Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hV_subset :
      V ⊆ ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) := by
    intro w hw
    constructor
    · have hw_norm : ‖w‖ < r := by
        simpa [V, Metric.mem_ball, dist_eq_norm] using hw.1
      exact hw_norm.le
    · exact hw.2.le
  intro w hw
  have hw_im : 0 < w.im := hupper hw
  have hw_dist : dist w z ≤ ρ := by
    simpa [Metric.mem_closedBall] using hw
  have hw_norm_le : ‖w‖ ≤ ρ + ‖z‖ := by
    calc
      ‖w‖ = ‖(w - z) + z‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
      _ ≤ ρ + ‖z‖ := by linarith
  have hw_norm_lt : ‖w‖ < r := by
    have hzρ : ρ + ‖z‖ < r := by simpa [add_comm] using hlarge
    exact lt_of_le_of_lt hw_norm_le hzρ
  have hwV : w ∈ V := by
    constructor
    · simpa [V, Metric.mem_ball, dist_eq_norm] using hw_norm_lt
    · exact hw_im
  -- Membership in the open model upgrades immediately to interior membership in the semidisk.
  exact ((IsOpen.subset_interior_iff hV_open).2 hV_subset) hwV

/-- Helper for Proposition 3.1: once the original source residue-circle radii are fixed, any large
upper half-disk that contains those full circles may reuse the same circles as local residue
circles for the semidisk owner. -/
lemma upper_half_disk_localResidueCircle_of_large_radius
    (residue : ℂ → ℂ) {ρ : s → ℝ} {r : ℝ} {D : Set ℂ} {G : ℂ → ℂ}
    (hρpos : ∀ z : s, 0 < ρ z)
    (hρU :
      ∀ z : s,
        Metric.closedBall (z : ℂ) (ρ z) ⊆ interior ({w : ℂ | 0 ≤ w.im} : Set ℂ))
    (hρcircle :
      ∀ z : s,
        (∮ w in C((z : ℂ), ρ z), G w) = (2 * Real.pi * Complex.I : ℂ) * residue z)
    (hKD : ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) ⊆ D)
    (hlarge : ∀ z : s, ‖(z : ℂ)‖ + ρ z < r) :
    ∀ z ∈ s,
      LocalResidueCircle
        ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ)
        D
        G
        z
        (residue z) := by
  intro z hz
  let z' : s := ⟨z, hz⟩
  have hupper :
      Metric.closedBall z (ρ z') ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    have hwU : w ∈ interior ({u : ℂ | 0 ≤ u.im} : Set ℂ) := hρU z' hw
    simpa [Complex.interior_setOf_le_im] using hwU
  have hballK :
      Metric.closedBall z (ρ z') ⊆
        interior ({w : ℂ | ‖w‖ ≤ r ∧ 0 ≤ w.im} : Set ℂ) := by
    -- The same source circle lies strictly inside the large semidisk.
    exact
      closedBall_subset_interior_upper_half_disk_of_upper_half_plane hupper
        (hlarge z')
  have hballD :
      Metric.closedBall z (ρ z') ⊆ D := by
    -- After entering the semidisk interior, the owner inclusion upgrades it to `D`.
    exact hballK.trans (interior_subset.trans hKD)
  -- Reuse the original source circle unchanged; only the owner inclusions change.
  refine ⟨ρ z', hρpos z', hballK, hballD, ?_⟩
  simpa [z'] using hρcircle z'

/-- Helper for Proposition 3.1: for all sufficiently large radii, the explicit upper-half-disk
contour identity holds, namely the real diameter integral plus the upper-semicircle integral equals
the prescribed source residue sum for the weighted meromorphic integrand. -/
lemma eventually_upper_half_disk_contour_identity
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        LocalResidueCircle
          {z : ℂ | 0 ≤ z.im}
          {z : ℂ | 0 ≤ z.im}
          (fun w ↦ f w * Complex.exp (Complex.I * w))
          z
          (residue z)) :
    ∀ᶠ r : ℝ in atTop,
      (∫ x in -r..r, f x * Complex.exp (Complex.I * x)) +
          sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi =
        ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := by
  classical
  let U : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let G : ℂ → ℂ := fun z ↦ toMeromorphicNFOn f U z * Complex.exp (Complex.I * z)
  have hgood_radius :
      ∀ᶠ r : ℝ in atTop,
        0 < r ∧
          (∀ z ∈ s, ‖z‖ < r) ∧
          (∀ θ ∈ Set.Icc 0 Real.pi, ¬ meromorphicOrderAt f (circleMap 0 r θ) < 0) := by
    -- The source route first freezes a large radius that contains every pole and keeps the outer
    -- semicircle free of poles.
    exact eventually_good_upper_half_disk_radius (f := f) (s := s) hreal hpoles
  have hanalytic_off_poles :
      ∀ z : ℂ, z ∈ U → z ∉ s → AnalyticAt ℂ G z := by
    -- This is the pointwise analytic bridge needed in the later compact-cover step.
    intro z hzU hzs
    simpa [G, U] using
      analyticAt_weighted_normal_form_of_mem_upper_half_plane_not_mem_pole_finset
        (f := f) (s := s) hmeromorphic hreal hpoles hzU hzs
  have hhol :
      DifferentiableOn ℂ G (U \ (↑s : Set ℂ)) := by
    -- This is the set-level holomorphic input needed by the residue theorem package.
    simpa [G, U] using
      weighted_normal_form_differentiableOn_upper_half_plane_punctured
        (f := f) (s := s) hmeromorphic hreal hpoles
  have hNF :
      ∀ z ∈ s, MeromorphicNFAt G z := by
    intro z hz
    have hzUpper : z ∈ upperHalfPlaneSet := by
      exact ((hpoles z).mpr hz).2
    have hzU : z ∈ U := by
      exact le_of_lt (by simpa [UpperHalfPlane.upperHalfPlaneSet] using hzUpper)
    -- Every enclosed pole lies in the upper half-plane, hence in the ambient closed half-plane.
    simpa [G, U] using
      weighted_normal_form_meromorphicNFAt (f := f) hzU
  have hresidue_eq :
      ∀ z ∈ s,
        meromorphicTrailingCoeffAt G z =
          meromorphicTrailingCoeffAt (fun w ↦ f w * Complex.exp (Complex.I * w)) z := by
    intro z hz
    have hzUpper : z ∈ upperHalfPlaneSet := by
      exact ((hpoles z).mpr hz).2
    have hzU : z ∈ U := by
      exact le_of_lt (by simpa [UpperHalfPlane.upperHalfPlaneSet] using hzUpper)
    -- The normal-form replacement does not change punctured-neighborhood residue data.
    simpa [G, U] using
      meromorphicTrailingCoeffAt_weighted_normal_form_eq (f := f) hmeromorphic hzU
  have hresidueG :
      ∀ z ∈ s, LocalResidueCircle U U G z (residue z) := by
    -- Transfer the given source-side residue circles to the weighted normal form before any
    -- contour geometry is invoked.
    simpa [G, U] using
      weighted_normal_form_localResidueCircle
        (f := f) (s := s) hmeromorphic residue hresidue
  have hsource_radii :
      ∀ z : s,
        ∃ ρ > 0,
          Metric.closedBall (z : ℂ) ρ ⊆ interior U ∧
            Metric.closedBall (z : ℂ) ρ ⊆ U ∧
              (∮ w in C((z : ℂ), ρ), G w) =
                (2 * Real.pi * Complex.I : ℂ) * residue z := by
    intro z
    -- Freeze one source-faithful residue-circle radius for each pole in `s`.
    exact hresidueG z.1 z.2
  choose ρ hρpos hρU hρUD hρcircle using hsource_radii
  have hρU' :
      ∀ z : s,
        Metric.closedBall (z : ℂ) (ρ z) ⊆ interior ({w : ℂ | 0 ≤ w.im} : Set ℂ) := by
    simpa [U] using hρU
  have hlarge_radius :
      ∀ᶠ r : ℝ in atTop, ∀ z : s, ‖(z : ℂ)‖ + ρ z < r := by
    let M : ℝ := Finset.sum s.attach fun z ↦ ‖(z : ℂ)‖ + ρ z
    have hterm_nonneg : ∀ z : s, 0 ≤ ‖(z : ℂ)‖ + ρ z := by
      intro z
      exact add_nonneg (norm_nonneg _) (le_of_lt (hρpos z))
    filter_upwards [Filter.eventually_ge_atTop (M + 1)] with r hr z
    have hz_le_M : ‖(z : ℂ)‖ + ρ z ≤ M := by
      -- Each individual pole-radius contribution is bounded by the full finite sum.
      simpa [M] using
        (Finset.single_le_sum (s := s.attach) (a := z)
          (f := fun w : s ↦ ‖(w : ℂ)‖ + ρ w)
          (fun w hw ↦ hterm_nonneg w)
          (by simpa using Finset.mem_attach z) :
            ‖(z : ℂ)‖ + ρ z ≤ Finset.sum s.attach (fun w ↦ ‖(w : ℂ)‖ + ρ w))
    -- Any radius larger than `M + 1` strictly contains every fixed source residue circle.
    linarith
  have hsInterior :
      ∀ᶠ r : ℝ in atTop,
        (↑s : Set ℂ) ⊆ interior ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) := by
    filter_upwards [hgood_radius] with r hr
    rcases hr with ⟨hr_pos, hinside, _⟩
    -- For a good radius, every prescribed pole is strictly inside the upper half-disk.
    let _ := hr_pos
    exact pole_finset_subset_interior_upper_half_disk (f := f) (s := s) hpoles hinside
  have hboundary_disjoint :
      ∀ᶠ r : ℝ in atTop,
        Disjoint (Set.range (upperHalfDiskBoundaryPath r)) (↑s : Set ℂ) := by
    filter_upwards [hgood_radius] with r hr
    rcases hr with ⟨hr_pos, hinside, _⟩
    -- The contour range lives on the frontier while every pole lies strictly inside the semidisk.
    exact upper_half_disk_boundary_disjoint_pole_finset (f := f) (s := s) hpoles hr_pos hinside
  have howner :
      ∀ᶠ r : ℝ in atTop,
        ∃ D : Set ℂ,
          IsOpen D ∧
            ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) ⊆ D ∧
            DifferentiableOn ℂ G (D \ (↑s : Set ℂ)) := by
    filter_upwards [hgood_radius] with r hr
    rcases hr with ⟨hr_pos, _, hboundary⟩
    -- The owner is the union of the semidisk interior with the analytic boundary locus.
    exact
      upper_half_disk_differentiable_owner
        (f := f) (s := s) hmeromorphic hreal hpoles hr_pos hboundary
  have hresidue_owner :
      ∀ᶠ r : ℝ in atTop,
        ∃ D : Set ℂ,
          IsOpen D ∧
            ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) ⊆ D ∧
            DifferentiableOn ℂ G (D \ (↑s : Set ℂ)) ∧
            ∀ z ∈ s,
              LocalResidueCircle
                ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)
                D
                G
                z
                (residue z) := by
    filter_upwards [howner, hlarge_radius] with r howner_r hlarge_r
    rcases howner_r with ⟨D, hDopen, hKD, hholD⟩
    refine ⟨D, hDopen, hKD, hholD, ?_⟩
    -- Reuse the fixed source circles once the outer radius is large enough to contain them.
    exact
      upper_half_disk_localResidueCircle_of_large_radius
        (s := s) (residue := residue) (ρ := ρ) (G := G)
        hρpos hρU' hρcircle hKD hlarge_r
  filter_upwards [hgood_radius, hboundary_disjoint, hresidue_owner] with
    r hr hboundary_r hresidue_r
  rcases hr with ⟨hr_pos, _, _⟩
  rcases hresidue_r with ⟨D, hDopen, hKD, hholD, hresD⟩
  let K : Set ℂ := {z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im}
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (upperHalfDiskBoundaryPath r).toClosedPath
  have hΓ : IsOrientedBoundaryOf K Γ := by
    -- Package the explicit semidisk contour as the oriented boundary of the closed upper
    -- half-disk before invoking the frozen residue theorem.
    simpa [K, Γ] using upper_half_disk_boundary_isOrientedBoundaryOf (r := r) hr_pos
  have hΓdisjoint :
      ∀ i : Unit, Disjoint (Set.range (Γ i).toPath) (↑s : Set ℂ) := by
    intro i
    cases i
    -- Collapse the singleton family back to the explicit contour range disjointness.
    simpa [Γ, Path.toClosedPath] using hboundary_r
  have hboundary_sum :
      ∑ i : Unit, ∫ᶜ z in (Γ i).toPath, (G dz) z =
        ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := by
    -- Apply the frozen oriented-boundary residue theorem to the singleton semidisk owner.
    exact
      orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
        (Γ := Γ) (K := K) (D := D) (f := G) (s := s) (residue := residue)
        hΓ hKD hDopen hΓdisjoint hholD hresD
  have hKclosed : IsClosed K := by
    -- The semidisk is cut out by two closed inequalities.
    exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_im)
  have hboundary_subset :
      Set.range (upperHalfDiskBoundaryPath r) ⊆ D \ (↑s : Set ℂ) := by
    intro z hz
    have hzFront :
        z ∈ frontier ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ) := by
      rwa [upper_half_disk_boundary_path_range_eq_frontier hr_pos] at hz
    have hzFrontK : z ∈ frontier K := by
      simpa [K] using hzFront
    have hzK : z ∈ K := by
      -- The contour is the frontier of a closed set, so it still lies inside the set.
      simpa [hKclosed.closure_eq] using frontier_subset_closure hzFrontK
    have hz_not_mem : z ∉ s := by
      intro hzS
      exact (Set.disjoint_left.mp hboundary_r) hz hzS
    exact ⟨hKD hzK, hz_not_mem⟩
  have hdiam_range :
      Set.range (Path.segment (-(r : ℂ)) (r : ℂ)) ⊆ D \ (↑s : Set ℂ) := by
    intro z hz
    apply hboundary_subset
    -- The diameter branch is one of the two pieces of the explicit semidisk contour.
    rw [upper_half_disk_boundary_path_range_eq_union]
    exact Or.inl hz
  have harc_range :
      Set.range (upperSemicirclePath r) ⊆ D \ (↑s : Set ℂ) := by
    intro z hz
    apply hboundary_subset
    -- The upper semicircle branch is the other piece of the semidisk contour.
    rw [upper_half_disk_boundary_path_range_eq_union]
    exact Or.inr hz
  have hdiam :
      CurveIntegrable (fun z ↦ (G dz) z) (Path.segment (-(r : ℂ)) (r : ℂ)) := by
    -- Continuity of `G` on the pole-free owner makes the diameter branch curve-integrable.
    exact
      Path.curveIntegrable_scalarOneForm_of_piecewiseDifferentiable
        (γ := Path.segment (-(r : ℂ)) (r : ℂ))
        (Path.segment_isPiecewiseDifferentiable (-(r : ℂ)) (r : ℂ))
        hholD.continuousOn
        hdiam_range
  have harc :
      CurveIntegrable (fun z ↦ (G dz) z) (upperSemicirclePath r) := by
    -- The same owner continuity gives curve-integrability along the upper semicircle branch.
    exact
      Path.curveIntegrable_scalarOneForm_of_piecewiseDifferentiable
        (γ := upperSemicirclePath r)
        (upper_semicircle_path_isDifferentiable r).isPiecewiseDifferentiable
        hholD.continuousOn
        harc_range
  have hcontour_eq :
      ∫ᶜ z in upperHalfDiskBoundaryPath r, (G dz) z =
        ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := by
    have hclosed_eq :
        ∫ᶜ z in ((upperHalfDiskBoundaryPath r).toClosedPath.toPath), (G dz) z =
          ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := by
      -- Collapse the singleton boundary sum to the unique closed path in the family.
      simpa [Γ] using hboundary_sum
    have hclosed_cast :
        ∫ᶜ z in ((upperHalfDiskBoundaryPath r).toClosedPath.toPath), (G dz) z =
          ∫ᶜ z in upperHalfDiskBoundaryPath r, (G dz) z := by
      rw [loop_toClosedPath_toPath_eq_cast (γ := upperHalfDiskBoundaryPath r)]
      simp
    -- Unpack the closed-path wrapper back to the original loop.
    exact hclosed_cast.symm.trans hclosed_eq
  have hnormal_eq :
      (∫ x in -r..r, G (x : ℂ)) + sectorArcIntegral G r 0 Real.pi =
        ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := by
    -- Rewrite the unique boundary loop into the source diameter-plus-arc decomposition.
    calc
      (∫ x in -r..r, G (x : ℂ)) + sectorArcIntegral G r 0 Real.pi =
          ∫ᶜ z in upperHalfDiskBoundaryPath r, (G dz) z := by
            symm
            exact
              upper_half_disk_boundary_curveIntegral_eq_intervalIntegral_add_sectorArcIntegral
                (g := G) hdiam harc
      _ = ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := hcontour_eq
  have hrealIntegral :
      ∫ x in -r..r, f x * Complex.exp (Complex.I * x) =
        ∫ x in -r..r, G (x : ℂ) := by
    have hreal_ae :
        (fun x : ℝ ↦ f x * Complex.exp (Complex.I * x)) =ᵐ[MeasureTheory.volume.restrict (Ι (-r) r)]
          (fun x : ℝ ↦ G (x : ℂ)) := by
      have hreal_codiscrete :
          (fun x : ℝ ↦ f x * Complex.exp (Complex.I * x)) =ᶠ[Filter.codiscreteWithin (Ι (-r) r)]
            (fun x : ℝ ↦ G (x : ℂ)) := by
        simpa [G, U] using
          real_segment_mul_exp_codiscrete_eq_normalForm
            (f := f) hmeromorphic (r := r)
      exact
        hreal_codiscrete.filter_mono
          (ae_restrict_le_codiscreteWithin measurableSet_uIoc)
    -- Along the real diameter, the literal weighted integrand agrees a.e. with its normal form.
    apply intervalIntegral.integral_congr_ae_restrict
    exact hreal_ae
  have harcIntegral :
      sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi =
        sectorArcIntegral G r 0 Real.pi := by
    have harc_ae :
        (fun θ : ℝ ↦
          Complex.I * circleMap 0 r θ *
            (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ)))
          =ᵐ[MeasureTheory.volume.restrict (Ι (0 : ℝ) Real.pi)]
        (fun θ : ℝ ↦
          Complex.I * circleMap 0 r θ *
            (G (circleMap 0 r θ))) := by
      have harc_codiscrete :
          (fun θ : ℝ ↦
            Complex.I * circleMap 0 r θ *
              (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ)))
            =ᶠ[Filter.codiscreteWithin (Ι (0 : ℝ) Real.pi)]
          (fun θ : ℝ ↦
            Complex.I * circleMap 0 r θ *
              (G (circleMap 0 r θ))) := by
        simpa [G, U] using
          upper_semicircle_mul_exp_codiscrete_eq_normalForm
            (f := f) hmeromorphic hr_pos
      exact
        harc_codiscrete.filter_mono
          (ae_restrict_le_codiscreteWithin measurableSet_uIoc)
    -- The same codiscrete comparison rewrites the semicircle integral back to the literal source
    -- integrand.
    rw [sectorArcIntegral_def, sectorArcIntegral_def]
    apply intervalIntegral.integral_congr_ae_restrict
    exact harc_ae
  calc
    (∫ x in -r..r, f x * Complex.exp (Complex.I * x)) +
        sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi =
      (∫ x in -r..r, G (x : ℂ)) + sectorArcIntegral G r 0 Real.pi := by
        rw [hrealIntegral, harcIntegral]
    _ = ((2 * Real.pi * Complex.I : ℂ) * s.sum residue) := hnormal_eq

/-- Proposition 3.1 (1): if `f` tends to `0` at infinity on the closed upper half-plane, has no
real poles, is meromorphic on the closed upper half-plane, and has exactly the poles in `s` inside
the open upper half-plane, then the symmetric real-line integrals of
`x ↦ f x * exp (i x)` converge to `2π i` times the source residue data of
`z ↦ f z * exp (i z)` at those poles. -/
theorem residue_fourier_intervalIntegral_tendsto_upper_half_plane
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hdecay :
      Tendsto
        (fun z : {z : ℂ // 0 ≤ z.im} ↦ f z.1)
        (cocompact {z : ℂ // 0 ≤ z.im})
        (𝓝 0))
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        LocalResidueCircle
          {z : ℂ | 0 ≤ z.im}
          {z : ℂ | 0 ≤ z.im}
          (fun w ↦ f w * Complex.exp (Complex.I * w))
          z
          (residue z)) :
    Tendsto
      (fun r : ℝ ↦ ∫ x in -r..r, f x * Complex.exp (Complex.I * x))
      atTop
        (𝓝
        ((2 * Real.pi * Complex.I : ℂ) *
          s.sum residue)) := by
  have hgood_radius :
      ∀ᶠ r : ℝ in atTop,
        0 < r ∧
          (∀ z ∈ s, ‖z‖ < r) ∧
          (∀ θ ∈ Set.Icc 0 Real.pi, ¬ meromorphicOrderAt f (circleMap 0 r θ) < 0) := by
    -- First freeze a large upper-half-disk containing every prescribed pole and avoiding poles on
    -- the outer semicircle.
    exact eventually_good_upper_half_disk_radius (f := f) (s := s) hreal hpoles
  have hint :
      ∀ᶠ r : ℝ in Filter.atTop,
        IntervalIntegrable
          (fun θ : ℝ ↦
            Complex.I * circleMap 0 r θ *
              (f (circleMap 0 r θ) * Complex.exp (Complex.I * circleMap 0 r θ)))
          MeasureTheory.volume
          0
          Real.pi := by
    -- The meromorphic input and the good-radius invariant provide interval integrability of the
    -- weighted upper-semicircle parametrization for all large radii.
    exact
      eventually_intervalIntegrable_upper_semicircle_weighted_integrand
        (f := f) (s := s) hmeromorphic hgood_radius
  have harc_tendsto :
      Tendsto
        (fun r : ℝ ↦
          sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi)
        atTop
        (𝓝 0) := by
    -- Jordan decay on the upper semicircle removes the arc contribution in the limit.
    exact upper_semicircle_integral_tendsto_zero_mul_exp (f := f) hint hdecay
  have hcontour_tendsto :
      Tendsto
        (fun r : ℝ ↦
          (∫ x in -r..r, f x * Complex.exp (Complex.I * x)) +
            sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi)
        atTop
        (𝓝 ((2 * Real.pi * Complex.I : ℂ) * s.sum residue)) := by
    have hcontour_eq :
        (fun r : ℝ ↦
          (∫ x in -r..r, f x * Complex.exp (Complex.I * x)) +
            sectorArcIntegral (fun z ↦ f z * Complex.exp (Complex.I * z)) r 0 Real.pi)
          =ᶠ[atTop]
            fun _ : ℝ ↦ (2 * Real.pi * Complex.I : ℂ) * s.sum residue := by
      filter_upwards
        [eventually_upper_half_disk_contour_identity
          (f := f) (s := s) hmeromorphic hreal hpoles residue hresidue] with r hr
      exact hr
    -- The finite-radius contour identity is eventually constant in the target residue sum.
    exact Tendsto.congr' hcontour_eq.symm tendsto_const_nhds
  -- Subtract the vanishing arc term to recover the symmetric real-axis integrals.
  simpa using hcontour_tendsto.sub harc_tendsto

/-- Helper for Proposition 3.1: absolute integrability of `f` on `ℝ` implies integrability of the
oscillatory weighting `x ↦ f x * exp (i x)`. -/
lemma integrable_mul_exp_of_integrable
    (hintegrable : Integrable (fun x : ℝ ↦ f x)) :
    Integrable (fun x : ℝ ↦ f x * Complex.exp (Complex.I * x)) := by
  -- The exponential factor has constant norm `1`, so it is globally bounded.
  refine hintegrable.mul_bdd (c := 1) ?_ ?_
  · have hcont : Continuous (fun x : ℝ ↦ Complex.exp (Complex.I * x)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards with x
    exact le_of_eq <| by
      simpa [mul_comm] using (Complex.norm_exp_ofReal_mul_I x)

/-- Proposition 3.1 (2): if, in addition, `f` is absolutely integrable on the real axis, then the
improper integral of `x ↦ f x * exp (i x)` over `ℝ` equals the same residue sum. -/
theorem residue_fourier_integral_eq_sum_upper_half_plane
    (hmeromorphic : MeromorphicOn f {z : ℂ | 0 ≤ z.im})
    (hdecay :
      Tendsto
        (fun z : {z : ℂ // 0 ≤ z.im} ↦ f z.1)
        (cocompact {z : ℂ // 0 ≤ z.im})
        (𝓝 0))
    (hreal : ∀ x : ℝ, ¬ meromorphicOrderAt f (x : ℂ) < 0)
    (hpoles : ∀ z : ℂ, meromorphicOrderAt f z < 0 ∧ z ∈ upperHalfPlaneSet ↔ z ∈ s)
    (residue : ℂ → ℂ)
    (hresidue :
      ∀ z ∈ s,
        LocalResidueCircle
          {z : ℂ | 0 ≤ z.im}
          {z : ℂ | 0 ≤ z.im}
          (fun w ↦ f w * Complex.exp (Complex.I * w))
          z
          (residue z))
    (hintegrable : Integrable (fun x : ℝ ↦ f x)) :
    ∫ x : ℝ, f x * Complex.exp (Complex.I * x) =
      (2 * Real.pi * Complex.I : ℂ) * s.sum residue := by
  let g : ℝ → ℂ := fun x ↦ f x * Complex.exp (Complex.I * x)
  have hg_integrable : Integrable g := by
    -- Absolute integrability of `f` transfers to the oscillatory integrand because `|exp (ix)|=1`.
    simpa [g] using integrable_mul_exp_of_integrable (f := f) hintegrable
  have hleft_tendsto :
      Tendsto (fun r : ℝ ↦ ∫ x in -r..0, g x) atTop (𝓝 (∫ x in Set.Iic 0, g x)) := by
    -- The left half-line improper integral is the limit of the intervals `[-r, 0]`.
    simpa using
      (MeasureTheory.intervalIntegral_tendsto_integral_Iic
        (μ := MeasureTheory.volume) (f := g) (l := atTop) (a := fun r : ℝ ↦ -r) 0
        (show IntegrableOn g (Set.Iic 0) MeasureTheory.volume from hg_integrable.integrableOn)
        tendsto_neg_atTop_atBot)
  have hright_tendsto :
      Tendsto (fun r : ℝ ↦ ∫ x in 0..r, g x) atTop (𝓝 (∫ x in Set.Ioi 0, g x)) := by
    -- The right half-line improper integral is the limit of the intervals `[0, r]`.
    simpa using
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
        (μ := MeasureTheory.volume) (f := g) (l := atTop) 0
        (b := fun r : ℝ ↦ r)
        (show IntegrableOn g (Set.Ioi 0) MeasureTheory.volume from hg_integrable.integrableOn)
        tendsto_id)
  have hsplit :
      ∀ᶠ r : ℝ in atTop,
        ∫ x in -r..r, g x = (∫ x in -r..0, g x) + ∫ x in 0..r, g x := by
    filter_upwards with r
    -- Split the symmetric interval at the origin.
    simpa using
      (intervalIntegral.integral_add_adjacent_intervals
        (μ := MeasureTheory.volume) (f := g) (a := -r) (b := 0) (c := r)
        (hg_integrable.intervalIntegrable (a := -r) (b := 0))
        (hg_integrable.intervalIntegrable (a := 0) (b := r))).symm
  have hsymmetric_tendsto :
      Tendsto
        (fun r : ℝ ↦ ∫ x in -r..r, g x)
        atTop
        (𝓝 ((∫ x in Set.Iic 0, g x) + ∫ x in Set.Ioi 0, g x)) := by
    have hsplit_eq :
        (fun r : ℝ ↦ ∫ x in -r..r, g x)
          =ᶠ[atTop]
            fun r : ℝ ↦ (∫ x in -r..0, g x) + ∫ x in 0..r, g x := by
      filter_upwards [hsplit] with r hr
      exact hr
    -- The split limits add to the full symmetric-interval limit.
    exact Tendsto.congr' hsplit_eq.symm (hleft_tendsto.add hright_tendsto)
  have hinterval_tendsto_integral :
      Tendsto (fun r : ℝ ↦ ∫ x in -r..r, g x) atTop (𝓝 (∫ x : ℝ, g x)) := by
    have hwhole :
        (∫ x in Set.Iic 0, g x) + ∫ x in Set.Ioi 0, g x = ∫ x : ℝ, g x := by
      exact
        intervalIntegral.integral_Iic_add_Ioi
          (μ := MeasureTheory.volume) (f := g) (b := 0)
          (show IntegrableOn g (Set.Iic 0) MeasureTheory.volume from hg_integrable.integrableOn)
          (show IntegrableOn g (Set.Ioi 0) MeasureTheory.volume from hg_integrable.integrableOn)
    -- Reassemble the two half-line integrals into the whole-space integral.
    simpa [hwhole] using hsymmetric_tendsto
  have hresidue_tendsto :
      Tendsto
        (fun r : ℝ ↦ ∫ x in -r..r, g x)
        atTop
        (𝓝 ((2 * Real.pi * Complex.I : ℂ) * s.sum residue)) := by
    -- Part (1) already identified the symmetric-interval limit with the residue sum.
    simpa [g] using
      residue_fourier_intervalIntegral_tendsto_upper_half_plane
        (f := f) (s := s) hmeromorphic hdecay hreal hpoles residue hresidue
  -- The two limits of the same net must agree.
  exact tendsto_nhds_unique hinterval_tendsto_integral hresidue_tendsto

end
