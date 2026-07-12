import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.II.section06.«0005_Corollary_1»

open scoped BigOperators Topology unitInterval

noncomputable section

universe u

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: the positively oriented circle
centered at `a` with radius `r`, written as an explicit loop for the later excision bookkeeping.
-/
def boundary_circle_path (a : ℂ) (r : ℝ) : Path (a + r) (a + r) :=
  Path.mk
    ⟨fun t ↦ circleMap a r (2 * Real.pi * (t : ℝ)), by
      fun_prop⟩
    (by
      simp [circleMap])
    (by
      simp [circleMap, Complex.exp_two_pi_mul_I])

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: unpacking a loop through
`toClosedPath.toPath` only inserts the endpoint cast forced by the closed-path packaging. -/
lemma loop_toClosedPath_toPath_eq_cast {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.toPath =
      γ.cast (by simpa [Path.toClosedPath] using γ.source)
        (by simpa [Path.toClosedPath] using γ.source) := by
  cases γ
  rfl

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: the real-curve parametrization of a
loop closed path is the original path extension written in real coordinates. -/
lemma toClosedPath_realCurve_eq {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.realCurve = Complex.equivRealProd ∘ γ.extend := by
  cases γ
  rfl

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: on the unit interval, the explicit
boundary-circle loop is the standard `circleMap` parametrization. -/
lemma boundary_circle_path_extend_eq_circleMap {a : ℂ} {r t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (boundary_circle_path a r).extend t = circleMap a r (2 * Real.pi * t) := by
  simpa [boundary_circle_path] using
    (Path.extend_apply (γ := boundary_circle_path a r) ht)

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: the positive boundary circle has image
exactly the geometric sphere it bounds. -/
lemma range_boundary_circle_path_eq_sphere {a : ℂ} {r : ℝ} (hr : 0 < r) :
    Set.range (boundary_circle_path a r) = Metric.sphere a r := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simpa [boundary_circle_path, abs_of_pos hr] using
      circleMap_mem_sphere' a r (2 * Real.pi * (t : ℝ))
  · intro hz
    have hz' : z ∈ Metric.sphere a |r| := by
      simpa [abs_of_pos hr] using hz
    rw [← image_circleMap_Ioc a r] at hz'
    rcases hz' with ⟨θ, hθ, rfl⟩
    refine ⟨⟨θ / (2 * Real.pi), ?_, ?_⟩, ?_⟩
    · exact div_nonneg hθ.1.le (by positivity)
    · exact (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2 (by simpa using hθ.2)
    · have hscale : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by
        field_simp [Real.pi_ne_zero]
      simp [boundary_circle_path, hscale]

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: the boundary circle is globally `C¹`,
hence piecewise differentiable. -/
lemma boundary_circle_path_isPiecewiseDifferentiable (a : ℂ) (r : ℝ) :
    (boundary_circle_path a r).IsPiecewiseDifferentiable := by
  have hdiff : (boundary_circle_path a r).IsDifferentiable := by
    rw [Path.IsDifferentiable]
    let g : ℝ → ℂ := fun t ↦ circleMap a r (2 * Real.pi * t)
    have hlin : ContDiff ℝ 1 (fun t : ℝ ↦ 2 * Real.pi * t) := by
      simpa [one_mul] using (contDiff_const.mul contDiff_id)
    have hg : ContDiff ℝ 1 g := by
      simpa [g] using (contDiff_circleMap a r).comp hlin
    refine hg.contDiffOn.congr ?_
    intro t ht
    simpa [g] using boundary_circle_path_extend_eq_circleMap (a := a) (r := r) (t := t) ht
  exact hdiff.isPiecewiseDifferentiable

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: the positive boundary circle
identifies only equal parameters or the two endpoints of the unit interval. -/
lemma boundary_circle_path_simple_eq_or_endpoints {a : ℂ} {r : ℝ} (hr : r ≠ 0)
    {s t : Set.Icc (0 : ℝ) 1} (h : boundary_circle_path a r s = boundary_circle_path a r t) :
    s = t ∨ ((s : ℝ) = 0 ∧ (t : ℝ) = 1) ∨ ((s : ℝ) = 1 ∧ (t : ℝ) = 0) := by
  let α : ℝ := 2 * Real.pi * (s : ℝ)
  let β : ℝ := 2 * Real.pi * (t : ℝ)
  have hcircle : circleMap a r α = circleMap a r β := by
    simpa [boundary_circle_path, α, β] using h
  have hlen : |(0 : ℝ) - 2 * Real.pi| ≤ 2 * Real.pi := by
    simpa [abs_of_nonneg Real.two_pi_pos.le]
  have hinj :=
    injOn_circleMap_of_abs_sub_le (c := a) (R := r) (a := (0 : ℝ)) (b := 2 * Real.pi) hr hlen
  by_cases hs0 : (s : ℝ) = 0
  · by_cases ht0 : (t : ℝ) = 0
    · exact Or.inl (Subtype.ext (hs0.trans ht0.symm))
    · have htpos : 0 < (t : ℝ) := by
        exact lt_of_le_of_ne t.2.1 (by
          intro htEq
          exact ht0 htEq.symm)
      have hβmem : β ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [β]
          nlinarith [Real.two_pi_pos, htpos]
        · dsimp [β]
          nlinarith [Real.two_pi_pos, t.2.2]
      have h2πmem : (2 * Real.pi : ℝ) ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · nlinarith [Real.pi_pos]
        · exact le_rfl
      have hβ2π : circleMap a r β = circleMap a r (2 * Real.pi) := by
        calc
          circleMap a r β = circleMap a r 0 := by
            simpa [α, hs0] using hcircle.symm
          _ = circleMap a r (2 * Real.pi) := by
            simp [circleMap, Complex.exp_two_pi_mul_I]
      have hβeq : β = 2 * Real.pi := hinj hβmem h2πmem hβ2π
      have ht1 : (t : ℝ) = 1 := by
        dsimp [β] at hβeq
        nlinarith [Real.two_pi_pos, hβeq]
      right
      left
      exact ⟨hs0, ht1⟩
  · by_cases ht0 : (t : ℝ) = 0
    · have hspos : 0 < (s : ℝ) := by
        exact lt_of_le_of_ne s.2.1 (by
          intro hsEq
          exact hs0 hsEq.symm)
      have hαmem : α ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [α]
          nlinarith [Real.two_pi_pos, hspos]
        · dsimp [α]
          nlinarith [Real.two_pi_pos, s.2.2]
      have h2πmem : (2 * Real.pi : ℝ) ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · nlinarith [Real.pi_pos]
        · exact le_rfl
      have hα2π : circleMap a r α = circleMap a r (2 * Real.pi) := by
        calc
          circleMap a r α = circleMap a r 0 := by
            simpa [β, ht0] using hcircle
          _ = circleMap a r (2 * Real.pi) := by
            simp [circleMap, Complex.exp_two_pi_mul_I]
      have hαeq : α = 2 * Real.pi := hinj hαmem h2πmem hα2π
      have hs1 : (s : ℝ) = 1 := by
        dsimp [α] at hαeq
        nlinarith [Real.two_pi_pos, hαeq]
      right
      right
      exact ⟨hs1, ht0⟩
    · have hspos : 0 < (s : ℝ) := by
        exact lt_of_le_of_ne s.2.1 (by
          intro hsEq
          exact hs0 hsEq.symm)
      have htpos : 0 < (t : ℝ) := by
        exact lt_of_le_of_ne t.2.1 (by
          intro htEq
          exact ht0 htEq.symm)
      have hαmem : α ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [α]
          nlinarith [Real.two_pi_pos, hspos]
        · dsimp [α]
          nlinarith [Real.two_pi_pos, s.2.2]
      have hβmem : β ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [β]
          nlinarith [Real.two_pi_pos, htpos]
        · dsimp [β]
          nlinarith [Real.two_pi_pos, t.2.2]
      have hαeqβ : α = β := hinj hαmem hβmem hcircle
      have hst : (s : ℝ) = (t : ℝ) := by
        dsimp [α, β] at hαeqβ
        nlinarith [Real.two_pi_pos, hαeqβ]
      exact Or.inl (Subtype.ext hst)

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: reversing the boundary circle
preserves its geometric image, so the clockwise loop still traces the same sphere. -/
lemma range_clockwise_boundary_circle_toPath_eq_sphere {a : ℂ} {r : ℝ} (hr : 0 < r) :
    Set.range (((boundary_circle_path a r).symm).toClosedPath.toPath) = Metric.sphere a r := by
  calc
    Set.range (((boundary_circle_path a r).symm).toClosedPath.toPath) =
        Set.range ((boundary_circle_path a r).symm) := by
          rw [loop_toClosedPath_toPath_eq_cast]
          simp
    _ = Set.range (boundary_circle_path a r) := Path.symm_range _
    _ = Metric.sphere a r := range_boundary_circle_path_eq_sphere hr

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: integrating a complex-valued `1`-form
along the explicit positive boundary circle is the textbook `θ`-integral after `θ = 2π t`. -/
lemma curveIntegral_boundary_circle_path_eq_intervalIntegral
    {ω : ℂ → ℂ →L[ℝ] ℂ} {a : ℂ} {r : ℝ} :
    ∫ᶜ z in boundary_circle_path a r, ω z =
      ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
  let h : ℝ → ℂ := fun θ ↦ ω (circleMap a r θ) (deriv (circleMap a r) θ)
  have hcongr :
      ∫ t in (0 : ℝ)..1,
          ω ((boundary_circle_path a r).extend t) (deriv ((boundary_circle_path a r).extend) t) =
        ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := by
    have hcongr_ae :
        (fun t ↦
            ω ((boundary_circle_path a r).extend t) (deriv ((boundary_circle_path a r).extend) t))
          =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)]
              (fun t ↦ (2 * Real.pi : ℝ) • h (t * (2 * Real.pi))) := by
      rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have hlocal :
          (boundary_circle_path a r).extend =ᶠ[nhds t]
            fun s : ℝ ↦ circleMap a r (s * (2 * Real.pi)) := by
        have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
        filter_upwards [hIoo] with s hs
        rw [Path.extend_apply (boundary_circle_path a r) ⟨hs.1.le, hs.2.le⟩]
        simp [boundary_circle_path, mul_comm]
      have hderiv :
          deriv (boundary_circle_path a r).extend t =
            (2 * Real.pi : ℝ) • deriv (circleMap a r) (t * (2 * Real.pi)) := by
        rw [Filter.EventuallyEq.deriv_eq hlocal]
        simpa using
          (((hasDerivAt_circleMap a r (t * (2 * Real.pi))).scomp t
            (hasDerivAt_mul_const (2 * Real.pi : ℝ))).deriv)
      have hext :
          (boundary_circle_path a r).extend t = circleMap a r (t * (2 * Real.pi)) :=
        Filter.EventuallyEq.eq_of_nhds hlocal
      calc
        ω ((boundary_circle_path a r).extend t) (deriv ((boundary_circle_path a r).extend) t) =
            ω (circleMap a r (t * (2 * Real.pi)))
              ((2 * Real.pi : ℝ) • deriv (circleMap a r) (t * (2 * Real.pi))) := by
          rw [hext, hderiv]
        _ = (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := by
          change
            ω (circleMap a r (t * (2 * Real.pi)))
                ((2 * Real.pi : ℝ) • deriv (circleMap a r) (t * (2 * Real.pi))) =
              (2 * Real.pi : ℝ) •
                ω (circleMap a r (t * (2 * Real.pi))) (deriv (circleMap a r) (t * (2 * Real.pi)))
          rw [map_smul]
    exact intervalIntegral.integral_congr_ae_restrict hcongr_ae
  have hsmul :
      ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) =
        (2 * Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * (2 * Real.pi)) := by
    simpa using intervalIntegral.integral_smul (a := (0 : ℝ)) (b := 1)
      (r := (2 * Real.pi : ℝ)) (f := fun t ↦ h (t * (2 * Real.pi)))
  rw [curveIntegral_eq_intervalIntegral_deriv]
  calc
    ∫ t in (0 : ℝ)..1,
        ω ((boundary_circle_path a r).extend t) (deriv ((boundary_circle_path a r).extend) t) =
      ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := hcongr
    _ = (2 * Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * (2 * Real.pi)) := hsmul
    _ = ∫ θ in (0 : ℝ) * (2 * Real.pi)..1 * (2 * Real.pi), h θ := by
      simpa using (intervalIntegral.smul_integral_comp_mul_right
        (f := h) (a := (0 : ℝ)) (b := 1) (c := 2 * Real.pi))
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi, h θ := by
      simp
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
      rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
        MeasureTheory.restrict_Ioc_eq_restrict_Icc]

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: the closed-path wrapper used by the
oriented-boundary API does not change the positive-circle integral. -/
lemma curveIntegral_boundary_circle_toClosedPath_eq_intervalIntegral
    {ω : ℂ → ℂ →L[ℝ] ℂ} {a : ℂ} {r : ℝ} :
    ∫ᶜ z in (boundary_circle_path a r).toClosedPath.toPath, ω z =
      ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
  calc
    ∫ᶜ z in (boundary_circle_path a r).toClosedPath.toPath, ω z =
        ∫ᶜ z in boundary_circle_path a r, ω z := by
          rw [loop_toClosedPath_toPath_eq_cast]
          simp
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
      exact curveIntegral_boundary_circle_path_eq_intervalIntegral (ω := ω)

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: the explicit positive boundary-circle
path realizes the standard complex `circleIntegral`. -/
lemma curveIntegral_boundary_circle_eq_circleIntegral
    {f : ℂ → ℂ} {a : ℂ} {r : ℝ} :
    ∫ᶜ z in boundary_circle_path a r, (f dz) z = ∮ w in C(a, r), f w := by
  calc
    ∫ᶜ z in boundary_circle_path a r, (f dz) z =
        ∫ᶜ z in (boundary_circle_path a r).toClosedPath.toPath, (f dz) z := by
          rw [loop_toClosedPath_toPath_eq_cast]
          simp
    _ = ∫ᶜ z in (boundary_circle_path a r).toClosedPath.toPath, Complex.realScalarOneForm f z := by
          simpa [Complex.realScalarOneForm] using
            (curveIntegral_restrictScalars
              (γ := (boundary_circle_path a r).toClosedPath.toPath)
              (ω := fun z ↦ (f dz) z) (𝕜 := ℂ) (𝕝 := ℝ)).symm
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
          (Complex.realScalarOneForm f) (circleMap a r θ) (deriv (circleMap a r) θ) := by
          exact curveIntegral_boundary_circle_toClosedPath_eq_intervalIntegral
            (ω := Complex.realScalarOneForm f) (a := a) (r := r)
    _ = ∮ w in C(a, r), f w := by
      rw [circleIntegral_def_Icc]
      let g : ℝ → ℂ := fun θ ↦
        (Complex.realScalarOneForm f) (circleMap a r θ) (deriv (circleMap a r) θ)
      let h : ℝ → ℂ := fun θ ↦ f (circleMap a r θ) * deriv (circleMap a r) θ
      have hAE : g =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))] h := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ hθ
        simp [g, h, Complex.realScalarOneForm, smul_eq_mul, mul_comm]
      simpa [g, h, mul_comm] using intervalIntegral.integral_congr_ae_restrict hAE

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: reversing the explicit boundary circle
changes the sign of the integral, so the clockwise inner boundary contributes the negative circle
integral. -/
lemma curveIntegral_clockwise_boundary_circle_eq_neg_circleIntegral
    {f : ℂ → ℂ} {a : ℂ} {r : ℝ} :
    ∫ᶜ z in ((boundary_circle_path a r).symm.toClosedPath).toPath, (f dz) z =
      -(∮ w in C(a, r), f w) := by
  calc
    ∫ᶜ z in ((boundary_circle_path a r).symm.toClosedPath).toPath, (f dz) z =
        ∫ᶜ z in (boundary_circle_path a r).symm, (f dz) z := by
          rw [loop_toClosedPath_toPath_eq_cast]
          simp
    _ = -∫ᶜ z in boundary_circle_path a r, (f dz) z := by
      simpa using curveIntegral_symm (γ := boundary_circle_path a r) (ω := fun z ↦ (f dz) z)
    _ = -(∮ w in C(a, r), f w) := by
      rw [curveIntegral_boundary_circle_eq_circleIntegral]
