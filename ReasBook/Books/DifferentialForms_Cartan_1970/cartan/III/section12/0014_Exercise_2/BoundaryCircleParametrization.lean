import Mathlib

open Complex MeasureTheory
open scoped MeasureTheory Real Manifold

section

variable {f : ℂ → ℂ} {R : ℝ}
variable (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))

/-- Helper for Exercise 2: the boundary parametrization `θ ↦ f (circleMap 0 R θ)` has speed
`R * ‖f'(circleMap 0 R θ)‖`. -/
lemma boundary_circle_param_speed
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (hR : 0 ≤ R) (θ : ℝ) :
    ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ =
      R * ‖deriv f (circleMap 0 R θ)‖ := by
  -- The chain rule identifies the derivative of the boundary parametrization.
  have hderiv :
      HasDerivAt (fun t : ℝ ↦ f (circleMap 0 R t))
        (deriv (circleMap 0 R) θ * deriv f (circleMap 0 R θ)) θ := by
    simpa [Function.comp] using
      ((hf (circleMap 0 R θ) (circleMap_mem_closedBall 0 hR θ)).differentiableAt.hasDerivAt).scomp
        θ (hasDerivAt_circleMap 0 R θ)
  -- The norm of `circleMap 0 R θ * I` is exactly `R`.
  calc
    ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ =
        ‖deriv (circleMap 0 R) θ * deriv f (circleMap 0 R θ)‖ := by
          rw [hderiv.deriv]
    _ = ‖deriv (circleMap 0 R) θ‖ * ‖deriv f (circleMap 0 R θ)‖ := norm_mul _ _
    _ = R * ‖deriv f (circleMap 0 R θ)‖ := by
          simp [deriv_circleMap, norm_circleMap_zero, abs_of_nonneg hR]

/-- Helper for Exercise 2: the boundary image can be rewritten using the standard angular
parametrization on `Set.Ioc (0 : ℝ) (2 * π)`. -/
lemma boundary_image_eq_circle_param_image
    (hR : 0 ≤ R) :
    f '' Metric.sphere (0 : ℂ) R =
      (fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π) := by
  -- Rewrite the geometric circle as the image of `circleMap`, then push forward by `f`.
  have hsphere :
      circleMap (0 : ℂ) R '' Set.Ioc (0 : ℝ) (2 * π) = Metric.sphere (0 : ℂ) R := by
    simpa [abs_of_nonneg hR] using image_circleMap_Ioc (0 : ℂ) R
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hsphere] at hz
    rcases hz with ⟨θ, hθ, rfl⟩
    exact ⟨θ, hθ, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨circleMap 0 R θ, ?_, rfl⟩
    simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R θ

/-- Helper for Exercise 2: injectivity of `f` on the geometric boundary transfers to injectivity of
the angular boundary parametrization on `Set.Ioc (0 : ℝ) (2 * π)` when `R ≠ 0`. -/
lemma boundary_circle_param_injOn
    (hR : 0 ≤ R) (hR0 : R ≠ 0)
    (hinj : Set.InjOn f (Metric.sphere (0 : ℂ) R)) :
    Set.InjOn (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Ioc (0 : ℝ) (2 * π)) := by
  -- First use the geometric injectivity of `f` to identify boundary points, then use the strict
  -- bound `|θ - φ| < 2π` to recover equality of the angles from the `circleMap` equality.
  intro θ hθ φ hφ hEq
  have hcircleEq : circleMap 0 R θ = circleMap 0 R φ := by
    apply hinj
    · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R θ
    · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R φ
    · exact hEq
  apply eq_of_circleMap_eq hR0
  · rw [abs_lt]
    constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2, Real.two_pi_pos]
  · exact hcircleEq

include hf

/-- Helper for Exercise 2: the angular boundary parametrization is `C¹` on
`[0, 2 π]`. -/
lemma boundary_circle_param_contDiffOn
    (hR : 0 ≤ R) :
    ContDiffOn ℝ 1 (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc (0 : ℝ) (2 * π)) := by
  -- Restrict the analytic regularity of `f` to real scalars and compose with the smooth circle
  -- map.
  have hfcontComplex : ContDiffOn ℂ 1 f (Metric.closedBall (0 : ℂ) R) :=
    hf.contDiffOn_of_completeSpace
  have hfcont : ContDiffOn ℝ 1 f (Metric.closedBall (0 : ℂ) R) :=
    hfcontComplex.restrict_scalars ℝ
  exact hfcont.comp (contDiff_circleMap 0 R).contDiffOn fun θ hθ ↦
    circleMap_mem_closedBall 0 hR θ

/-- Helper for Exercise 2: the angular boundary parametrization closes after one full turn. -/
lemma boundary_circle_param_endpoint_eq :
    (fun θ : ℝ ↦ f (circleMap 0 R θ)) (0 : ℝ) =
      (fun θ : ℝ ↦ f (circleMap 0 R θ)) (2 * π) := by
  -- `circleMap` returns to the starting point at angle `2π`.
  simp [circleMap_zero, Complex.exp_two_pi_mul_I]

/-- Helper for Exercise 2: integrating the boundary speed of the angular parametrization gives the
textbook factor `R * ∫ ‖f'(circleMap 0 R θ)‖`. -/
lemma boundary_circle_param_integral_speed_eq
    (hR : 0 ≤ R) :
    ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ =
      R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ := by
  -- Integrate the pointwise speed formula from `boundary_circle_param_speed`.
  calc
    ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖ =
        ∫ θ in (0 : ℝ)..(2 * π), R * ‖deriv f (circleMap 0 R θ)‖ := by
          apply intervalIntegral.integral_congr_ae_restrict
            (a := (0 : ℝ)) (b := 2 * π) (μ := volume)
            (f := fun θ : ℝ ↦ ‖deriv (fun t : ℝ ↦ f (circleMap 0 R t)) θ‖)
            (g := fun θ : ℝ ↦ R * ‖deriv f (circleMap 0 R θ)‖)
          exact Filter.Eventually.of_forall fun θ ↦
            boundary_circle_param_speed (hf := hf) hR θ
    _ = R * ∫ θ in (0 : ℝ)..(2 * π), ‖deriv f (circleMap 0 R θ)‖ := by
          rw [intervalIntegral.integral_const_mul]

/-- Helper for Exercise 2: injectivity on the circle transfers to injectivity on each closed
half-arc of the angular parametrization. -/
lemma boundary_circle_param_half_injOn
    (hR : 0 ≤ R) (hR0 : R ≠ 0)
    (hinj : Set.InjOn f (Metric.sphere (0 : ℂ) R)) :
    Set.InjOn (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc (0 : ℝ) π) ∧
      Set.InjOn (fun θ : ℝ ↦ f (circleMap 0 R θ)) (Set.Icc π (2 * π)) := by
  constructor
  · intro θ hθ φ hφ hEq
    have hcircleEq : circleMap 0 R θ = circleMap 0 R φ := by
      apply hinj
      · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R θ
      · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R φ
      · exact hEq
    -- On `[0, π]` the angular difference is automatically strictly smaller than `2π`.
    apply eq_of_circleMap_eq hR0
    · rw [abs_lt]
      constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2, Real.pi_pos, Real.two_pi_pos]
    · exact hcircleEq
  · intro θ hθ φ hφ hEq
    have hcircleEq : circleMap 0 R θ = circleMap 0 R φ := by
      apply hinj
      · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R θ
      · simpa [abs_of_nonneg hR] using circleMap_mem_sphere' (0 : ℂ) R φ
      · exact hEq
    -- The same argument works on `[π, 2π]`, where the difference lies in `[-π, π]`.
    apply eq_of_circleMap_eq hR0
    · rw [abs_lt]
      constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2, Real.pi_pos, Real.two_pi_pos]
    · exact hcircleEq

/-- Helper for Exercise 2: the open-closed full-turn image is exactly the union of the two closed
half-arc images. -/
lemma boundary_circle_param_image_eq_half_union :
    (fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Ioc (0 : ℝ) (2 * π) =
      ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) ∪
        ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π)) := by
  let γ : ℝ → ℂ := fun θ ↦ f (circleMap 0 R θ)
  -- Split the angular parameter domain at `π`, using the endpoint identification at `0` and `2π`.
  ext z
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    by_cases hθπ : θ ≤ π
    · exact Or.inl ⟨θ, ⟨hθ.1.le, hθπ⟩, rfl⟩
    · exact Or.inr ⟨θ, ⟨le_of_not_ge hθπ, hθ.2⟩, rfl⟩
  · rintro (⟨θ, hθ, rfl⟩ | ⟨θ, hθ, rfl⟩)
    · by_cases hθ0 : θ = 0
      · -- The missing left endpoint is recovered from the right endpoint `2π`.
        refine ⟨2 * π, ⟨by positivity, le_rfl⟩, ?_⟩
        simpa [γ, hθ0] using (boundary_circle_param_endpoint_eq (hf := hf) (f := f) (R := R)).symm
      · refine ⟨θ, ⟨lt_of_le_of_ne hθ.1 (by simpa [eq_comm] using hθ0), ?_⟩, rfl⟩
        linarith [hθ.2, Real.pi_pos]
    · refine ⟨θ, ⟨?_, hθ.2⟩, rfl⟩
      linarith [hθ.1, Real.pi_pos]

/-- Helper for Exercise 2: after the midpoint split, the Hausdorff `1`-measure of the full boundary
image is the sum of the two half-image measures because the overlap has measure zero. -/
lemma boundary_circle_param_half_union_measure_eq
    (hR : 0 ≤ R)
    (hhalfOverlap :
      μHE[1]
          (((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) ∩
            ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π))) = 0) :
    μHE[1]
        (((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) ∪
          ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π))) =
      μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc (0 : ℝ) π) +
        μHE[1] ((fun θ : ℝ ↦ f (circleMap 0 R θ)) '' Set.Icc π (2 * π)) := by
  let γ : ℝ → ℂ := fun θ ↦ f (circleMap 0 R θ)
  have hcont :
      ContDiffOn ℝ 1 γ (Set.Icc (0 : ℝ) (2 * π)) :=
    boundary_circle_param_contDiffOn (hf := hf) (f := f) (R := R) hR
  have hleftMeas : MeasurableSet (γ '' Set.Icc (0 : ℝ) π) := by
    -- Each half-image is compact because the parametrization is continuous on the closed interval.
    exact
      (isCompact_Icc.image_of_continuousOn
        (hcont.continuousOn.mono <| by
          intro θ hθ
          exact ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)).measurableSet
  have hrightMeas : MeasurableSet (γ '' Set.Icc π (2 * π)) := by
    -- The right half-image is handled by the same compact-image argument.
    exact
      (isCompact_Icc.image_of_continuousOn
        (hcont.continuousOn.mono <| by
          intro θ hθ
          exact ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)).measurableSet
  have hunion :
      μHE[1] ((γ '' Set.Icc (0 : ℝ) π) ∪ (γ '' Set.Icc π (2 * π))) +
          μHE[1] ((γ '' Set.Icc (0 : ℝ) π) ∩ (γ '' Set.Icc π (2 * π))) =
        μHE[1] (γ '' Set.Icc (0 : ℝ) π) + μHE[1] (γ '' Set.Icc π (2 * π)) := by
    simpa [γ] using
      (measure_union_add_inter (μ := (μHE[1] : Measure ℂ))
        (γ '' Set.Icc (0 : ℝ) π) hrightMeas)
  -- Collapse the intersection term using the already-proved zero-overlap fact.
  rw [hhalfOverlap, add_zero] at hunion
  exact hunion

end
