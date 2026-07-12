import Mathlib
import DifferentialForms_Cartan_1970.I.section04.«0031_Exercise_16»
import DifferentialForms_Cartan_1970.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.II.section05.«0015_Proposition_5_1»
import DifferentialForms_Cartan_1970.II.section05.«0019_Theorem_2»
import DifferentialForms_Cartan_1970.II.section05.«0027_Remark_II_1_extra_17»
import DifferentialForms_Cartan_1970.II.section06.«0005_Corollary_1»
import DifferentialForms_Cartan_1970.II.section06.«0018_Exercise_3»
import DifferentialForms_Cartan_1970.II.section06.«0029_Exercise_14»
import DifferentialForms_Cartan_1970.III.section10.«0001_Definition_III_4_extra_1»
import DifferentialForms_Cartan_1970.III.section10.«0006_Proposition_4_1»
import DifferentialForms_Cartan_1970.III.section10.«0008_Definition_III_4_extra_6»
import DifferentialForms_Cartan_1970.III.section10.«0009_Theorem_III_4_extra_7»
import DifferentialForms_Cartan_1970.III.section10.«0010_Remark_III_4_extra_8»

open Metric Set
open scoped Topology unitInterval

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the loop
`t ↦ (standardCirclePath r t) ^ n` has winding index `n` about `0`. -/
lemma standardCirclePath_zpow_hasIndexAt_zero
    (r : NNReal) (hr : 0 < (r : ℝ)) (n : ℤ) :
    let γ : Path (((r : ℂ) ^ n)) (((r : ℂ) ^ n)) :=
      Path.mk
        ⟨fun t : I ↦ (standardCirclePath r t) ^ n, by
          -- The standard circle never meets `0`, so integer powers stay continuous on it.
          have harg : Continuous fun t : I ↦ 2 * Real.pi * (t : ℝ) := by
            fun_prop
          have hcircle : Continuous fun t : I ↦ standardCirclePath r t := by
            simpa [standardCirclePath_apply] using (continuous_circleMap 0 (r : ℝ)).comp harg
          exact hcircle.zpow₀ n <| by
            intro t
            left
            simpa [standardCirclePath_apply] using
              circleMap_ne_center (c := 0) (R := (r : ℝ))
                (θ := 2 * Real.pi * (t : ℝ)) hr.ne'
        ⟩
        (by simp)
        (by simp)
    ; γ.HasIndexAt 0 n := by
  dsimp
  refine ⟨⟨fun t ↦ (n : ℂ) * (Complex.log (r : ℂ) + ((2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I),
      by fun_prop⟩, ?_, ?_⟩
  · intro t
    -- The explicit logarithm branch records the integer-power monodromy of the circle.
    change Complex.exp ((n : ℂ) * (Complex.log (r : ℂ) +
        ((2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I)) =
      (standardCirclePath r t) ^ n - 0
    have hbase :
        Complex.exp (Complex.log (r : ℂ) + ((2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I) =
          standardCirclePath r t := by
      calc
        Complex.exp (Complex.log (r : ℂ) + ((2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I) =
            Complex.exp (Complex.log (r : ℂ)) *
              Complex.exp (((2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I) := by
                simp [Complex.exp_add]
        _ = (r : ℂ) * Complex.exp (((2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I) := by
              rw [Complex.exp_log]
              exact_mod_cast ne_of_gt hr
        _ = standardCirclePath r t := by
              simp [standardCirclePath_apply, circleMap]
    calc
      Complex.exp ((n : ℂ) * (Complex.log (r : ℂ) + ((2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I)) =
          Complex.exp (Complex.log (r : ℂ) +
            ((2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I) ^ n := by
              simpa using
                (Complex.exp_int_mul
                  (Complex.log (r : ℂ) + ((2 * Real.pi * (t : ℝ)) : ℂ) * Complex.I) n)
      _ = (standardCirclePath r t) ^ n := by rw [hbase]
      _ = (standardCirclePath r t) ^ n - 0 := by ring
  · -- One full turn changes the branch by exactly `2πni`.
    simp
    ring

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on an open set, the
logarithmic derivative of an analytic function that never vanishes is analytic. -/
lemma analyticOnNhd_logDeriv_of_avoids_zero
    {s : Set ℂ} (hs : IsOpen s) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F s)
    (hF_ne : ∀ z ∈ s, F z ≠ 0) :
    AnalyticOnNhd ℂ (logDeriv F) s := by
  -- The logarithmic derivative is the quotient of the ordinary derivative by the function value.
  simpa [logDeriv] using (hF.deriv_of_isOpen hs).div hF hF_ne

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: every complex open annulus is
an open subset of `ℂ`. -/
lemma isOpen_complexOpenAnnulus (ρ₂ ρ₁ : ENNReal) : IsOpen (complexOpenAnnulus ρ₂ ρ₁) := by
  -- Both annulus inequalities are open conditions on the norm.
  simpa [complexOpenAnnulus] using
    (isOpen_lt (continuous_const : Continuous fun _ : ℂ ↦ ρ₂)
      (ENNReal.continuous_coe.comp continuous_nnnorm)).inter
      (isOpen_lt (ENNReal.continuous_coe.comp continuous_nnnorm)
        (continuous_const : Continuous fun _ : ℂ ↦ ρ₁))

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: a standard circle of radius
strictly between `ρ₂` and `ρ₁` stays inside `complexOpenAnnulus ρ₂ ρ₁`. -/
lemma standardCirclePath_mem_complexOpenAnnulus
    {ρ₂ ρ₁ ρ : NNReal} (hρ_left : ρ₂ < ρ) (hρ_right : ρ < ρ₁) (t : I) :
    standardCirclePath ρ t ∈ complexOpenAnnulus ρ₂ ρ₁ := by
  -- Normalize the annulus-membership goal to the explicit norm inequalities of the circle.
  change ((ρ₂ : ENNReal) < (‖standardCirclePath ρ t‖₊ : ENNReal) ∧
      (‖standardCirclePath ρ t‖₊ : ENNReal) < (ρ₁ : ENNReal))
  have hsphere : ‖standardCirclePath ρ t‖ = (ρ : ℝ) := by
    simpa [Metric.mem_sphere, dist_eq_norm, sub_zero, standardCirclePath_apply,
      norm_circleMap_zero, abs_of_nonneg ρ.2] using
      (circleMap_mem_sphere (0 : ℂ) ρ.2 (2 * Real.pi * (t : ℝ)))
  have hnnorm : ‖standardCirclePath ρ t‖₊ = ρ := NNReal.eq hsphere
  rw [hnnorm]
  constructor
  · exact_mod_cast hρ_left
  · exact_mod_cast hρ_right

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the standard circle path is
globally `C¹`, hence piecewise differentiable. -/
lemma standardCirclePath_isPiecewiseDifferentiable (r : NNReal) :
    (standardCirclePath r).IsPiecewiseDifferentiable := by
  -- The explicit `circleMap` parametrization is smooth on all of `ℝ`, so the path needs no
  -- subdivision.
  refine Path.IsDifferentiable.isPiecewiseDifferentiable ?_
  change ContDiffOn ℝ 1 (standardCirclePath r).extend I
  have hcircle :
      ContDiff ℝ 1 (fun t : ℝ ↦ circleMap 0 (r : ℝ) (2 * Real.pi * t)) := by
    -- Compose the smooth circle map with the affine angle parameter `t ↦ 2πt`.
    simpa using
      (contDiff_circleMap 0 (r : ℝ)).comp
        (by fun_prop : ContDiff ℝ 1 fun t : ℝ ↦ 2 * Real.pi * t)
  refine hcircle.contDiffOn.congr ?_
  intro t ht
  rw [Path.extend_apply (standardCirclePath r) ⟨ht.1, ht.2⟩, standardCirclePath_apply]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on a standard circle inside an
annulus, the logarithmic-derivative integral of `G` is the index integral of the mapped loop. -/
lemma logDerivIntegral_eq_mappedLoopIndex_onStandardCircle
    {G : ℂ → ℂ} {ρ₂ ρ₁ ρ : NNReal}
    (hG_diff : DifferentiableOn ℂ G (complexOpenAnnulus ρ₂ ρ₁))
    (hG_ne : ∀ z ∈ complexOpenAnnulus ρ₂ ρ₁, G z ≠ 0)
    (hρ_left : ρ₂ < ρ) (hρ_right : ρ < ρ₁) :
    ∫ᶜ z in standardCirclePath ρ, ((logDeriv G) dz) z =
      ∫ᶜ w in
        (standardCirclePath ρ).map' <|
          (hG_diff.continuousOn).mono <| by
            rintro _ ⟨t, rfl⟩
            exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t,
        indexForm 0 w := by
  have hAnn_open : IsOpen (complexOpenAnnulus ρ₂ ρ₁) :=
    isOpen_complexOpenAnnulus _ _
  have hcircle_range :
      Set.range (standardCirclePath ρ) ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
    rintro _ ⟨t, rfl⟩
    exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t
  have hinv_cont :
      ContinuousOn (fun w : ℂ ↦ w⁻¹) (G '' Set.range (standardCirclePath ρ)) := by
    refine ContinuousOn.inv₀ continuous_id.continuousOn ?_
    rintro w ⟨z, hz, rfl⟩
    rcases hz with ⟨t, rfl⟩
    exact hG_ne _ (standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t)
  have hmap :
      ∫ᶜ w in
        (standardCirclePath ρ).map' <|
          (hG_diff.continuousOn).mono <| by
            rintro _ ⟨t, rfl⟩
            exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t,
        ((fun w : ℂ ↦ w⁻¹) dz) w =
      ∫ᶜ w in
        (standardCirclePath ρ).map' <|
          (hG_diff.continuousOn).mono <| by
            rintro _ ⟨t, rfl⟩
            exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t,
        indexForm 0 w := by
    -- The mapped-loop form is literally `dz / w`, i.e. `indexForm 0`.
    simp [indexForm, Complex.scalarOneForm]
  -- Change variables along the mapped circle, then rewrite the target form as `indexForm 0`.
  calc
    ∫ᶜ z in standardCirclePath ρ, ((logDeriv G) dz) z =
        ∫ᶜ w in
          (standardCirclePath ρ).map' <|
            (hG_diff.continuousOn).mono <| by
              rintro _ ⟨t, rfl⟩
              exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t,
          ((fun w : ℂ ↦ w⁻¹) dz) w := by
          simpa [logDeriv, Complex.scalarOneForm, div_eq_mul_inv, mul_comm, mul_left_comm,
            mul_assoc] using
            (Path.curveIntegral_map'_eq_curveIntegral_mul_deriv
              (γ := standardCirclePath ρ)
              (standardCirclePath_isPiecewiseDifferentiable ρ)
              hAnn_open hcircle_range hG_diff hinv_cont).symm
    _ =
        ∫ᶜ w in
          (standardCirclePath ρ).map' <|
            (hG_diff.continuousOn).mono <| by
              rintro _ ⟨t, rfl⟩
              exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t,
          indexForm 0 w := hmap

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the logarithmic index form
`indexForm 0` is continuous, after restricting scalars to `ℝ`, on any set avoiding the origin. -/
lemma indexForm_zero_continuousOn {s : Set ℂ} (hs : s ⊆ ({0} : Set ℂ)ᶜ) :
    ContinuousOn (fun z : ℂ ↦ (indexForm 0 z).restrictScalars ℝ) s := by
  -- Rewrite `indexForm 0` as the scalar-one-form of inversion and use the owner continuity of
  -- inversion away from `0`.
  have hInv : ContinuousOn (fun z : ℂ ↦ z⁻¹) s := by
    refine continuousOn_inv₀.mono ?_
    intro z hz
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hs hz
  have hsmul : ContinuousOn (fun z : ℂ ↦ z⁻¹ • (1 : ℂ →L[ℝ] ℂ)) s := by
    exact hInv.smul (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ)) s)
  simpa [indexForm, Complex.scalarOneForm] using hsmul

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the mapped standard-circle loop
has a curve-integrable logarithmic index form whenever the map is differentiable and nonvanishing
on the ambient annulus. -/
lemma mappedStandardCirclePath_indexForm_curveIntegrable
    {G : ℂ → ℂ} {ρ₂ ρ₁ ρ : NNReal}
    (hG_diff : DifferentiableOn ℂ G (complexOpenAnnulus ρ₂ ρ₁))
    (hG_ne : ∀ z ∈ complexOpenAnnulus ρ₂ ρ₁, G z ≠ 0)
    (hρ_left : ρ₂ < ρ) (hρ_right : ρ < ρ₁) :
    CurveIntegrable (indexForm 0)
      ((standardCirclePath ρ).map' <|
        (hG_diff.continuousOn).mono <| by
          rintro _ ⟨t, rfl⟩
          exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t) := by
  have hcircle_range :
      Set.range (standardCirclePath ρ) ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
    rintro _ ⟨t, rfl⟩
    exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t
  have hmap_piece :
      ((standardCirclePath ρ).map' <|
        (hG_diff.continuousOn).mono <| by
          rintro _ ⟨t, rfl⟩
          exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t).IsPiecewiseDifferentiable := by
    -- Compose the standard circle with the annulus map using the chapter-II mapped-path owner.
    exact (standardCirclePath_isPiecewiseDifferentiable ρ).map'_of_differentiableOn
      (hD := isOpen_complexOpenAnnulus _ _) hcircle_range hG_diff
  have hmap_range :
      Set.range
          ((standardCirclePath ρ).map' <|
            (hG_diff.continuousOn).mono <| by
              rintro _ ⟨t, rfl⟩
              exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t)
        ⊆ ({0} : Set ℂ)ᶜ := by
    rintro _ ⟨t, rfl⟩
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using
      hG_ne (standardCirclePath ρ t) (standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t)
  -- Feed the explicit mapped-path regularity and range control into the owner curve-integrability
  -- theorem.
  have hInt :
      CurveIntegrable (fun z : ℂ ↦ (indexForm 0 z).restrictScalars ℝ)
        ((standardCirclePath ρ).map' <|
          (hG_diff.continuousOn).mono <| by
            rintro _ ⟨t, rfl⟩
            exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t) :=
    Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
      (ω := fun z : ℂ ↦ (indexForm 0 z).restrictScalars ℝ)
      (indexForm_zero_continuousOn subset_rfl) hmap_piece hmap_range
  simpa using hInt

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: mapping the standard circle by
an annulus-holomorphic function preserves piecewise differentiability. -/
lemma mappedStandardCirclePath_isPiecewiseDifferentiable
    {G : ℂ → ℂ} {ρ₂ ρ₁ ρ : NNReal}
    (hG_diff : DifferentiableOn ℂ G (complexOpenAnnulus ρ₂ ρ₁))
    (hρ_left : ρ₂ < ρ) (hρ_right : ρ < ρ₁) :
    ((standardCirclePath ρ).map' <|
      (hG_diff.continuousOn).mono <| by
        rintro _ ⟨t, rfl⟩
        exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t).IsPiecewiseDifferentiable := by
  have hcircle_range :
      Set.range (standardCirclePath ρ) ⊆ complexOpenAnnulus ρ₂ ρ₁ := by
    rintro _ ⟨t, rfl⟩
    exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t
  -- Compose the standard circle with the annulus map using the chapter-II mapped-path owner.
  exact (standardCirclePath_isPiecewiseDifferentiable ρ).map'_of_differentiableOn
    (hD := isOpen_complexOpenAnnulus _ _) hcircle_range hG_diff

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the image of a standard circle
under a nonvanishing map on an annulus has integer normalized index integral about `0`. -/
lemma mappedStandardCirclePath_invIntegral_isInt
    {G : ℂ → ℂ} {ρ₂ ρ₁ ρ : NNReal}
    (hG_diff : DifferentiableOn ℂ G (complexOpenAnnulus ρ₂ ρ₁))
    (hG_ne : ∀ z ∈ complexOpenAnnulus ρ₂ ρ₁, G z ≠ 0)
    (hρ_left : ρ₂ < ρ) (hρ_right : ρ < ρ₁) :
    ∃ n : ℤ,
      (∫ᶜ w in
        (standardCirclePath ρ).map' <|
          (hG_diff.continuousOn).mono <| by
            rintro _ ⟨t, rfl⟩
            exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t,
        indexForm 0 w) / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ) := by
  have hγ₀ :
      ∀ t : I,
        ((standardCirclePath ρ).map' <|
          (hG_diff.continuousOn).mono <| by
            rintro _ ⟨s, rfl⟩
            exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right s) t ≠ 0 := by
    intro t
    -- Nonvanishing of `G` on the annulus makes the mapped circle avoid the origin.
    exact hG_ne (standardCirclePath ρ t) (standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t)
  have hInt :
      CurveIntegrable (indexForm 0)
        ((standardCirclePath ρ).map' <|
          (hG_diff.continuousOn).mono <| by
            rintro _ ⟨t, rfl⟩
            exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t) :=
    mappedStandardCirclePath_indexForm_curveIntegrable hG_diff hG_ne hρ_left hρ_right
  have hmap_piece :
      ((standardCirclePath ρ).map' <|
        (hG_diff.continuousOn).mono <| by
          rintro _ ⟨t, rfl⟩
          exact standardCirclePath_mem_complexOpenAnnulus hρ_left hρ_right t).IsPiecewiseDifferentiable := by
    -- Reuse the dedicated mapped-circle regularity bridge instead of reopening the path proof.
    exact mappedStandardCirclePath_isPiecewiseDifferentiable hG_diff hρ_left hρ_right
  -- The chapter-II index theorem now records the mapped-loop winding number as an integer.
  exact Path.curveIntegral_inv_div_two_pi_I_eq_int hγ₀ hmap_piece hInt

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: any annulus whose outer radius
is below `ε` lies inside the punctured ball `0 < ‖z‖ < ε`. -/
lemma complexOpenAnnulus_subset_puncturedBall
    {ρ₂ ρ₁ : NNReal} {ε : ℝ}
    (hρ₁ε : (ρ₁ : ℝ) < ε) :
    complexOpenAnnulus ρ₂ ρ₁ ⊆ ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
  intro z hz
  change ((ρ₂ : ENNReal) < (‖z‖₊ : ENNReal) ∧ (‖z‖₊ : ENNReal) < (ρ₁ : ENNReal)) at hz
  constructor
  · -- The outer annulus inequality already puts `z` inside the radius-`ε` ball.
    have hz_lt_nn : ‖z‖₊ < ρ₁ := by
      exact_mod_cast hz.2
    have hz_lt : ‖z‖ < (ρ₁ : ℝ) := by
      exact_mod_cast hz_lt_nn
    have hz_ball : ‖z‖ < ε := lt_trans hz_lt hρ₁ε
    simpa [Metric.mem_ball, dist_eq_norm] using hz_ball
  · -- The inner annulus inequality forces `‖z‖ > 0`, so `z` cannot be the puncture.
    have hz_gt_nn : ρ₂ < ‖z‖₊ := by
      exact_mod_cast hz.1
    have hz_pos_nn : (0 : NNReal) < ‖z‖₊ := lt_of_le_of_lt ρ₂.2 hz_gt_nn
    have hz_pos : 0 < ‖z‖ := by
      exact_mod_cast hz_pos_nn
    have hz_ne : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hz_pos)
    simpa [Set.mem_singleton_iff] using hz_ne

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: a closed path in `ℂ \ {0}`
admits an integer winding witness about `0`. -/
lemma hasIndexAt_zero_of_closedPath_avoids_zero
    {z : ℂ} {γ : Path z z} (hγ₀ : ∀ t : I, γ t ≠ 0) :
    ∃ n : ℤ, γ.HasIndexAt 0 n := by
  let loop : C(I, {w : ℂ // w ≠ 0}) :=
    ⟨fun t ↦ ⟨γ t, hγ₀ t⟩, by
      fun_prop⟩
  have hzero :
      loop 0 =
        (⟨Complex.exp (Complex.log (γ 0)),
          Complex.exp_ne_zero (Complex.log (γ 0))⟩ : {w : ℂ // w ≠ 0}) := by
    -- Start the covering lift from the principal logarithm at the base point.
    apply Subtype.ext
    simpa [loop, γ.source] using (Complex.exp_log (hγ₀ 0)).symm
  let w : C(I, ℂ) := Complex.isCoveringMap_exp.liftPath loop (Complex.log (γ 0)) hzero
  have hw :
      (fun u : ℂ ↦ (⟨Complex.exp u, Complex.exp_ne_zero u⟩ : {w : ℂ // w ≠ 0})) ∘ w = loop :=
    Complex.isCoveringMap_exp.liftPath_lifts loop _ hzero
  have hwexp : ∀ t : I, Complex.exp (w t) = γ t := by
    intro t
    -- Read the covering equation back on the underlying complex values.
    have ht := congrArg Subtype.val (congr_fun hw t)
    simpa [loop] using ht
  have hExp : Complex.exp (w 1) = Complex.exp (w 0) := by
    -- The path is closed, so its logarithm lift changes by a period.
    rw [hwexp, hwexp, γ.target, γ.source]
  rcases Complex.exp_eq_exp_iff_exists_int.mp hExp with ⟨n, hn⟩
  refine ⟨n, w, ?_, ?_⟩
  · intro t
    simpa using hwexp t
  · simpa [mul_assoc, mul_left_comm, mul_comm] using hn

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the same-radius `m`-turn circle
of radius `ρ`. -/
noncomputable def circleTurns (ρ : NNReal) (m : ℤ) : Path (ρ : ℂ) (ρ : ℂ) :=
  Path.mk
    ⟨fun t : I ↦
        (ρ : ℂ) *
          Complex.exp
            ((((2 * Real.pi : ℂ) * (m : ℂ) * (t : ℝ)) : ℂ) * Complex.I), by
      fun_prop⟩
    (by simp)
    (by
      have hExp :
          Complex.exp ((((2 * Real.pi : ℂ) * (m : ℂ) * (1 : ℝ)) : ℂ) * Complex.I) = 1 := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Complex.exp_int_mul_two_pi_mul_I m)
      -- One full `m`-turn traversal returns to the same point on the circle.
      simpa using congrArg (fun z : ℂ ↦ (ρ : ℂ) * z) hExp)

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: explicit pointwise formula for
the same-radius `m`-turn circle. -/
@[simp] lemma circleTurns_apply (ρ : NNReal) (m : ℤ) (t : I) :
    circleTurns ρ m t =
      (ρ : ℂ) *
        Complex.exp
          ((((2 * Real.pi : ℂ) * (m : ℂ) * (t : ℝ)) : ℂ) * Complex.I) := by
  rfl

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the same-radius `m`-turn circle
stays inside the punctured ball when `0 < ρ < ε`. -/
lemma circleTurns_mem_puncturedBall
    {ρ : NNReal} {m : ℤ} {ε : ℝ}
    (hρpos : 0 < (ρ : ℝ)) (hρε : (ρ : ℝ) < ε) (t : I) :
    circleTurns ρ m t ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
  constructor
  · -- The radius is constant along the entire `m`-turn circle.
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, circleTurns_apply, norm_mul, Complex.norm_exp]
    have hnormρ : ‖(ρ : ℂ)‖ = (ρ : ℝ) := by
      exact_mod_cast (show |(ρ : ℝ)| = (ρ : ℝ) by exact abs_of_nonneg ρ.2)
    rw [hnormρ]
    simpa using hρε
  · -- Positivity of the radius keeps the loop away from the puncture.
    rw [Set.mem_singleton_iff, circleTurns_apply]
    exact mul_ne_zero (by exact_mod_cast hρpos.ne') (Complex.exp_ne_zero _)

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the same-radius `m`-turn circle
has winding index `m` about `0`. -/
lemma circleTurns_hasIndexAt_zero
    (ρ : NNReal) (m : ℤ) (hρpos : 0 < (ρ : ℝ)) :
    (circleTurns ρ m).HasIndexAt 0 m := by
  refine ⟨⟨fun t ↦
      Complex.log (ρ : ℂ) +
        ((((2 * Real.pi : ℂ) * (m : ℂ) * (t : ℝ)) : ℂ) * Complex.I), by
      fun_prop⟩, ?_, ?_⟩
  · intro t
    -- The explicit logarithm branch tracks the `m` turns with the correct endpoint jump.
    change
      Complex.exp
          (Complex.log (ρ : ℂ) +
            ((((2 * Real.pi : ℂ) * (m : ℂ) * (t : ℝ)) : ℂ) * Complex.I)) =
        circleTurns ρ m t - 0
    rw [circleTurns_apply]
    calc
      Complex.exp
          (Complex.log (ρ : ℂ) +
            ((((2 * Real.pi : ℂ) * (m : ℂ) * (t : ℝ)) : ℂ) * Complex.I)) =
        Complex.exp (Complex.log (ρ : ℂ)) *
          Complex.exp
            ((((2 * Real.pi : ℂ) * (m : ℂ) * (t : ℝ)) : ℂ) * Complex.I) := by
          simp [Complex.exp_add]
      _ =
        (ρ : ℂ) *
          Complex.exp
            ((((2 * Real.pi : ℂ) * (m : ℂ) * (t : ℝ)) : ℂ) * Complex.I) := by
          rw [Complex.exp_log]
          exact_mod_cast ne_of_gt hρpos
      _ = circleTurns ρ m t := by rw [circleTurns_apply ρ m t]
      _ = circleTurns ρ m t - 0 := by ring
  · -- The endpoint jump is exactly `2πmi`.
    simp

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the same-radius concatenation
model obtained by repeating `standardCirclePath ρ` exactly `n` times. -/
noncomputable def circleTurnsConcatNat (ρ : NNReal) : ℕ → Path (ρ : ℂ) (ρ : ℂ)
  | 0 => Path.refl (ρ : ℂ)
  | n + 1 => (circleTurnsConcatNat ρ n).trans (standardCirclePath ρ)

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the last logarithmic segment in
the recursive lift of `circleTurnsConcatNat ρ (n + 1)`. -/
noncomputable def circleTurnsConcatNatLogSegment (ρ : NNReal) (n : ℕ) :
    Path (Complex.log (ρ : ℂ) + ((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I)
      (Complex.log (ρ : ℂ) + ((2 * Real.pi : ℂ) * ((n + 1 : ℕ) : ℂ)) * Complex.I) :=
  Path.mk
    ⟨fun t : I ↦
        Complex.log (ρ : ℂ) + ((2 * Real.pi : ℂ) * ((n : ℂ) + (t : ℝ))) * Complex.I, by
      fun_prop⟩
    (by simp)
    (by simp)

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the concatenation model admits
an explicit logarithmic lift starting at `Complex.log ρ`. -/
noncomputable def circleTurnsConcatNatLogLift (ρ : NNReal) : ∀ n : ℕ,
    Path (Complex.log (ρ : ℂ))
      (Complex.log (ρ : ℂ) + ((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I)
  | 0 => by
      refine Path.mk ⟨fun _ : I ↦ Complex.log (ρ : ℂ), by fun_prop⟩ ?_ ?_
      · simp
      · simp
  | n + 1 =>
      (circleTurnsConcatNatLogLift ρ n).trans (circleTurnsConcatNatLogSegment ρ n)

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: exponentiating the last lift
segment recovers one more traversal of `standardCirclePath ρ`. -/
lemma circleTurnsConcatNatLogSegment_exp
    (ρ : NNReal) (n : ℕ) (hρpos : 0 < (ρ : ℝ)) (t : I) :
    Complex.exp (circleTurnsConcatNatLogSegment ρ n t) = standardCirclePath ρ t := by
  -- Split off the integer period so the remaining exponential is the standard circle itself.
  change
    Complex.exp
        (Complex.log (ρ : ℂ) + ((2 * Real.pi : ℂ) * ((n : ℂ) + (t : ℝ))) * Complex.I) =
      standardCirclePath ρ t
  have hsplit :
      ((2 * Real.pi : ℂ) * ((n : ℂ) + (t : ℝ))) * Complex.I =
        ((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I +
          ((2 * Real.pi : ℂ) * (t : ℝ)) * Complex.I := by
    ring
  have hperiod :
      Complex.exp (((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I) = 1 := by
    rw [show (((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I) =
        (n : ℂ) * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  calc
    Complex.exp
        (Complex.log (ρ : ℂ) + ((2 * Real.pi : ℂ) * ((n : ℂ) + (t : ℝ))) * Complex.I) =
      Complex.exp (Complex.log (ρ : ℂ)) *
        Complex.exp (((2 * Real.pi : ℂ) * ((n : ℂ) + (t : ℝ))) * Complex.I) := by
          simp [Complex.exp_add]
    _ = (ρ : ℂ) * Complex.exp (((2 * Real.pi : ℂ) * ((n : ℂ) + (t : ℝ))) * Complex.I) := by
          rw [Complex.exp_log]
          exact_mod_cast ne_of_gt hρpos
    _ = (ρ : ℂ) *
          (Complex.exp (((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I) *
            Complex.exp (((2 * Real.pi : ℂ) * (t : ℝ)) * Complex.I)) := by
          rw [hsplit, Complex.exp_add]
    _ = (ρ : ℂ) * Complex.exp (((2 * Real.pi : ℂ) * (t : ℝ)) * Complex.I) := by
          rw [hperiod, one_mul]
    _ = standardCirclePath ρ t := by
          simpa [standardCirclePath_apply, circleMap]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: exponentiating the recursive
lift recovers the concatenation model pointwise. -/
lemma circleTurnsConcatNatLogLift_exp
    (ρ : NNReal) (n : ℕ) (hρpos : 0 < (ρ : ℝ)) (t : I) :
    Complex.exp (circleTurnsConcatNatLogLift ρ n t) = circleTurnsConcatNat ρ n t := by
  induction n generalizing t with
  | zero =>
      -- The base lift is constant at `Complex.log ρ`, so its exponential is the constant basepoint.
      simpa [circleTurnsConcatNatLogLift, circleTurnsConcatNat] using
        (Complex.exp_log (by exact_mod_cast ne_of_gt hρpos : (ρ : ℂ) ≠ 0))
  | succ n ih =>
      -- Unfold both recursive concatenations and compare the same branch of `Path.trans`.
      rw [circleTurnsConcatNatLogLift, circleTurnsConcatNat, Path.trans_apply, Path.trans_apply]
      by_cases ht : (t : ℝ) ≤ 1 / 2
      · have hu : 2 * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith [t.2.1, t.2.2]
        let u : I := ⟨2 * (t : ℝ), hu⟩
        rw [dif_pos ht, dif_pos ht]
        exact ih u
      · have hu : 2 * (t : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith [t.2.1, t.2.2, ht]
        let u : I := ⟨2 * (t : ℝ) - 1, hu⟩
        rw [dif_neg ht, dif_neg ht]
        exact circleTurnsConcatNatLogSegment_exp ρ n hρpos u

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the repeated same-radius
concatenation model still winds `n` times around `0`. -/
lemma circleTurnsConcatNat_hasIndexAt_zero
    (ρ : NNReal) (n : ℕ) (hρpos : 0 < (ρ : ℝ)) :
    (circleTurnsConcatNat ρ n).HasIndexAt 0 (n : ℤ) :=
  by
  refine ⟨circleTurnsConcatNatLogLift ρ n, ?_, ?_⟩
  · intro t
    -- The recursive logarithmic lift exponentiates back to the concatenated loop.
    calc
      Complex.exp (circleTurnsConcatNatLogLift ρ n t) = circleTurnsConcatNat ρ n t :=
        circleTurnsConcatNatLogLift_exp ρ n hρpos t
      _ = circleTurnsConcatNat ρ n t - 0 := by ring
  · -- The endpoint of the lift records exactly the total `2πni` jump.
    change circleTurnsConcatNatLogLift ρ n 1 =
      circleTurnsConcatNatLogLift ρ n 0 + ((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I
    simp

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the concatenation model stays
inside the punctured ball whenever the reference radius does. -/
lemma circleTurnsConcatNat_mem_puncturedBall
    {ρ : NNReal} {n : ℕ} {ε : ℝ}
    (hρpos : 0 < (ρ : ℝ)) (hρε : (ρ : ℝ) < ε) (t : I) :
    circleTurnsConcatNat ρ n t ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
  induction n generalizing t with
  | zero =>
      -- The constant basepoint of the concatenation model is the same nonzero radius-`ρ` point.
      constructor
      · rw [circleTurnsConcatNat, Path.refl_apply, Metric.mem_ball, dist_eq_norm, sub_zero]
        have hnormρ : ‖(ρ : ℂ)‖ = (ρ : ℝ) := by
          exact_mod_cast (show |(ρ : ℝ)| = (ρ : ℝ) by exact abs_of_nonneg ρ.2)
        rw [hnormρ]
        simpa using hρε
      · have hnormρ : ‖(ρ : ℂ)‖ = (ρ : ℝ) := by
          exact_mod_cast (show |(ρ : ℝ)| = (ρ : ℝ) by exact abs_of_nonneg ρ.2)
        have hne : (ρ : ℂ) ≠ 0 := by
          apply norm_ne_zero_iff.mp
          rw [hnormρ]
          exact ne_of_gt hρpos
        simpa [circleTurnsConcatNat, Path.refl_apply, Set.mem_singleton_iff] using hne
  | succ n ih =>
      -- Each segment of the concatenation is either an earlier piece or one more standard circle.
      rw [circleTurnsConcatNat, Path.trans_apply]
      split_ifs with ht
      · exact ih _
      · have ht' : 2 * (t : ℝ) - 1 ∈ I := by
          constructor <;> linarith [t.2.1, t.2.2]
        let s : I := ⟨2 * (t : ℝ) - 1, ht'⟩
        have hsphere : ‖standardCirclePath ρ s‖ = (ρ : ℝ) := by
          simpa [Metric.mem_sphere, dist_eq_norm, sub_zero, standardCirclePath_apply,
            norm_circleMap_zero, abs_of_nonneg ρ.2] using
            (circleMap_mem_sphere (0 : ℂ) ρ.2 (2 * Real.pi * (s : ℝ)))
        constructor
        · rw [Metric.mem_ball, dist_eq_norm, sub_zero, hsphere]
          simpa using hρε
        · have hne : standardCirclePath ρ s ≠ 0 := by
            apply norm_ne_zero_iff.mp
            rw [hsphere]
            exact ne_of_gt hρpos
          simpa [Set.mem_singleton_iff] using hne

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the explicit same-radius
`m`-turn loop is globally `C¹`, hence piecewise differentiable. -/
lemma circleTurns_isPiecewiseDifferentiable (ρ : NNReal) (m : ℤ) :
    (circleTurns ρ m).IsPiecewiseDifferentiable := by
  -- The explicit exponential parametrization is smooth on all of `ℝ`, so no subdivision is
  -- needed.
  refine Path.IsDifferentiable.isPiecewiseDifferentiable ?_
  change ContDiffOn ℝ 1 (circleTurns ρ m).extend I
  have hcircle :
      ContDiff ℝ 1 (fun t : ℝ ↦ circleMap 0 (ρ : ℝ) (2 * Real.pi * (m : ℝ) * t)) := by
    simpa [mul_assoc] using
      (contDiff_circleMap 0 (ρ : ℝ)).comp
        (by fun_prop : ContDiff ℝ 1 fun t : ℝ ↦ 2 * Real.pi * (m : ℝ) * t)
  refine hcircle.contDiffOn.congr ?_
  intro t ht
  rw [Path.extend_apply (circleTurns ρ m) ⟨ht.1, ht.2⟩, circleTurns_apply]
  simp [circleMap, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the logarithmic index form is
curve-integrable along every same-radius reference loop inside the punctured ball. -/
lemma circleTurns_indexForm_curveIntegrable
    {ρ : NNReal} {m : ℤ} {ε : ℝ}
    (hρpos : 0 < (ρ : ℝ)) (hρε : (ρ : ℝ) < ε) :
    CurveIntegrable (indexForm 0) (circleTurns ρ m) := by
  let U : Set ℂ := ball (0 : ℂ) ε \ ({0} : Set ℂ)
  have hcircleU : Set.range (circleTurns ρ m) ⊆ U := by
    rintro _ ⟨t, rfl⟩
    simpa [U] using circleTurns_mem_puncturedBall hρpos hρε t
  have hU_ne : U ⊆ ({0} : Set ℂ)ᶜ := by
    intro z hz
    simpa [U, Set.mem_compl_iff, Set.mem_singleton_iff] using hz.2
  -- The explicit circle is piecewise differentiable and stays inside the punctured ball where the
  -- logarithmic form is continuous.
  have hInt : CurveIntegrable (fun z : ℂ ↦ (indexForm 0 z).restrictScalars ℝ) (circleTurns ρ m) :=
    Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
      (ω := fun z : ℂ ↦ (indexForm 0 z).restrictScalars ℝ)
      (indexForm_zero_continuousOn hU_ne)
      (circleTurns_isPiecewiseDifferentiable ρ m) hcircleU
  simpa using hInt

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the repeated concatenation
model is piecewise differentiable by construction. -/
lemma circleTurnsConcatNat_isPiecewiseDifferentiable (ρ : NNReal) :
    ∀ n : ℕ, (circleTurnsConcatNat ρ n).IsPiecewiseDifferentiable
  | 0 => by
      -- The zero-turn model is the constant basepoint loop.
      simpa [circleTurnsConcatNat] using Path.isPiecewiseDifferentiable_refl (ρ : ℂ)
  | n + 1 => by
      -- Concatenating one more standard circle preserves piecewise differentiability.
      simpa [circleTurnsConcatNat] using
        Path.IsPiecewiseDifferentiable.trans
          (circleTurnsConcatNat_isPiecewiseDifferentiable ρ n)
          (standardCirclePath_isPiecewiseDifferentiable ρ)

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: negative turn numbers are the
reverse of the corresponding positive-turn loop. -/
lemma circleTurns_negSucc_eq_symm_succ (ρ : NNReal) (k : ℕ) :
    circleTurns ρ (Int.negSucc k) = (circleTurns ρ ((k + 1 : ℕ) : ℤ)).symm := by
  ext t
  -- Compare the two explicit exponential parametrizations and absorb the extra full turn into the
  -- standard `2π i` period.
  by_cases hρ0 : (ρ : ℂ) = 0
  · simp [circleTurns_apply, hρ0]
  · rw [Path.symm_apply]
    simp [circleTurns_apply]
    left
    change Complex.exp (2 * Real.pi * (-1 + -((k : ℂ))) * (t : ℝ) * Complex.I) =
      Complex.exp (2 * Real.pi * ((k : ℂ) + 1) * (1 - (t : ℝ)) * Complex.I)
    have hperiod :
        Complex.exp (((2 * Real.pi : ℂ) * ((k + 1 : ℕ) : ℂ)) * Complex.I) = 1 := by
      rw [show (((2 * Real.pi : ℂ) * ((k + 1 : ℕ) : ℂ)) * Complex.I) =
          ((k + 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_nat_mul_two_pi_mul_I (k + 1)
    calc
      Complex.exp (2 * Real.pi * (-1 + -((k : ℂ))) * (t : ℝ) * Complex.I) =
        Complex.exp
          (((2 * Real.pi * ((k : ℂ) + 1) * (1 - (t : ℝ)) * Complex.I) : ℂ) -
            (((2 * Real.pi : ℂ) * ((k + 1 : ℕ) : ℂ)) * Complex.I)) := by
              congr 1
              have hk' : (((k + 1 : ℕ) : ℂ)) = (k : ℂ) + 1 := by
                norm_num
              rw [hk']
              ring
      _ =
        Complex.exp (2 * Real.pi * ((k : ℂ) + 1) * (1 - (t : ℝ)) * Complex.I) := by
            rw [Complex.exp_sub, hperiod, div_one]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the positive-turn
concatenation model repeats the one-turn logarithmic-derivative period linearly. -/
lemma circleTurnsConcatNat_logDerivIntegral
    {G : ℂ → ℂ} {ε : ℝ} {ρ : NNReal} {c : ℂ}
    (hG_analytic : AnalyticOnNhd ℂ (logDeriv G) (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hρpos : 0 < (ρ : ℝ)) (hρε : (ρ : ℝ) < ε)
    (hperiod :
      ∫ᶜ z in standardCirclePath ρ, ((logDeriv G) dz) z = c) :
    ∀ k : ℕ,
      ∫ᶜ z in circleTurnsConcatNat ρ k, ((logDeriv G) dz) z = (k : ℂ) * c
  | 0 => by
      -- The zero-turn reference loop is constant, so its contour integral vanishes.
      simp [circleTurnsConcatNat]
  | k + 1 => by
      have hcircle_int : CurveIntegrable ((logDeriv G) dz) (standardCirclePath ρ) := by
        -- The standard circle is globally `C¹`, so continuity of the logarithmic derivative on its
        -- image gives curve integrability directly.
        have hscalar_cont : ContinuousOn (logDeriv G) (Set.range (standardCirclePath ρ)) := by
          refine hG_analytic.continuousOn.mono ?_
          rintro _ ⟨t, rfl⟩
          simpa [standardCirclePath_apply, circleMap] using
            (circleTurns_mem_puncturedBall (ρ := ρ) (m := (1 : ℤ)) hρpos hρε t)
        have hcircle_cont :
            ContinuousOn ((logDeriv G) dz) (Set.range (standardCirclePath ρ)) := by
          have hone :
              ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) (Set.range (standardCirclePath ρ)) :=
            continuousOn_const
          have hform : ((logDeriv G) dz) = fun z ↦ logDeriv G z • (1 : ℂ →L[ℂ] ℂ) := by
            ext z v
            simp [Complex.scalarOneForm, smul_eq_mul]
          rw [hform]
          exact hscalar_cont.smul hone
        have hcircle_diff : ContDiffOn ℝ 1 (standardCirclePath ρ).extend I := by
          change (standardCirclePath ρ).IsDifferentiable
          change ContDiffOn ℝ 1 (standardCirclePath ρ).extend I
          have hbase :
              ContDiff ℝ 1 (fun t : ℝ ↦ circleMap 0 (ρ : ℝ) (2 * Real.pi * t)) := by
            simpa using
              (contDiff_circleMap 0 (ρ : ℝ)).comp
                (by fun_prop : ContDiff ℝ 1 fun t : ℝ ↦ 2 * Real.pi * t)
          refine hbase.contDiffOn.congr ?_
          intro t ht
          rw [Path.extend_apply (standardCirclePath ρ) ⟨ht.1, ht.2⟩, standardCirclePath_apply]
        exact hcircle_cont.curveIntegrable_of_contDiffOn hcircle_diff fun t ↦ by
          exact ⟨t, rfl⟩
      have hconcat_int : CurveIntegrable ((logDeriv G) dz) (circleTurnsConcatNat ρ k) := by
        -- Repeated concatenation preserves integrability because each piece is the same one-turn
        -- circle.
        induction k with
        | zero =>
            simpa [circleTurnsConcatNat] using CurveIntegrable.refl ((logDeriv G) dz) (ρ : ℂ)
        | succ k ih =>
            simpa [circleTurnsConcatNat] using ih.trans hcircle_int
      calc
        ∫ᶜ z in circleTurnsConcatNat ρ (k + 1), ((logDeriv G) dz) z =
            ∫ᶜ z in circleTurnsConcatNat ρ k, ((logDeriv G) dz) z +
              ∫ᶜ z in standardCirclePath ρ, ((logDeriv G) dz) z := by
                simpa [circleTurnsConcatNat] using
                  curveIntegral_trans hconcat_int hcircle_int
        _ = (k : ℂ) * c + c := by
              rw [circleTurnsConcatNat_logDerivIntegral hG_analytic hρpos hρε hperiod k, hperiod]
        _ = ((k + 1 : ℕ) : ℂ) * c := by
              calc
                (k : ℂ) * c + c = ((k : ℂ) + 1) * c := by ring
                _ = ((k + 1 : ℕ) : ℂ) * c := by norm_num

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: interpolating two logarithmic
lifts inside the radius-`ε` ball stays inside that ball. -/
lemma interpolatedExpNormLt
    {ε : ℝ} (hε : 0 < ε) {u v : ℂ} {s : I}
    (hu : ‖Complex.exp u‖ < ε) (hv : ‖Complex.exp v‖ < ε) :
    ‖Complex.exp (((1 : ℂ) - ((s : ℝ) : ℂ)) * u + ((s : ℝ) : ℂ) * v)‖ < ε := by
  rw [Complex.norm_exp] at hu hv ⊢
  rw [← Real.lt_log_iff_exp_lt hε] at hu hv ⊢
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have hRe :
      ((((1 : ℂ) - ((s : ℝ) : ℂ)) * u + ((s : ℝ) : ℂ) * v)).re =
        (1 - (s : ℝ)) * u.re + (s : ℝ) * v.re := by
    simp [sub_eq_add_neg]
  rw [hRe]
  have hx : 0 < Real.log ε - u.re := by
    linarith
  have hy : 0 < Real.log ε - v.re := by
    linarith
  have hcomb :
      0 <
        (1 - (s : ℝ)) * (Real.log ε - u.re) +
          (s : ℝ) * (Real.log ε - v.re) := by
    rcases lt_or_eq_of_le hs1 with hslt | hsEq
    · have h1s_pos : 0 < 1 - (s : ℝ) := by
        linarith
      have hfirst :
          0 < (1 - (s : ℝ)) * (Real.log ε - u.re) := by
        exact mul_pos h1s_pos hx
      have hsecond :
          0 ≤ (s : ℝ) * (Real.log ε - v.re) := by
        exact mul_nonneg hs0 hy.le
      linarith
    · simpa [hsEq] using hy
  have hcomb' :
      (1 - (s : ℝ)) * (Real.log ε - u.re) +
          (s : ℝ) * (Real.log ε - v.re) =
        Real.log ε - ((1 - (s : ℝ)) * u.re + (s : ℝ) * v.re) := by
    ring
  linarith [hcomb, hcomb']

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: two closed loops in the
punctured ball with the same winding index about `0` are homotopic through closed loops that stay
inside the same punctured ball. -/
lemma closedPathHomotopicIn_puncturedBall_of_sameIndexAtZero
    {ε : ℝ} (hε : 0 < ε)
    {z₀ z₁ : ℂ} {γ₀ : Path z₀ z₀} {γ₁ : Path z₁ z₁} {n : ℤ}
    (hγ₀U : Set.range γ₀ ⊆ ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hγ₁U : Set.range γ₁ ⊆ ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hγ₀ : γ₀.HasIndexAt 0 n) (hγ₁ : γ₁.HasIndexAt 0 n) :
    ClosedPathHomotopicIn (ball (0 : ℂ) ε \ ({0} : Set ℂ)) γ₀ γ₁ := by
  rcases hγ₀ with ⟨w₀, hw₀exp, hw₀jump⟩
  rcases hγ₁ with ⟨w₁, hw₁exp, hw₁jump⟩
  let Δ : ℂ := ((2 * Real.pi : ℂ) * (n : ℂ)) * Complex.I
  have hΔexp : Complex.exp Δ = 1 := by
    rw [show Δ = (n : ℂ) * (2 * Real.pi * Complex.I) by
      dsimp [Δ]
      ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  refine ⟨{ toHomotopy := ?_, prop' := ?_ }⟩
  · refine
      { toFun := Path.interpolated_homotopy_fun 0 w₀ w₁
        continuous_toFun := Path.continuous_interpolated_homotopy_fun
        map_zero_left := ?_
        map_one_left := ?_ }
    · intro t
      -- The left edge is the original loop `γ₀`.
      exact Path.interpolated_homotopy_apply_zero hw₀exp t
    · intro t
      -- The right edge is the original loop `γ₁`.
      exact Path.interpolated_homotopy_apply_one hw₁exp t
  · intro s
    rw [isClosedPathIn_iff_forall]
    constructor
    · -- The interpolated lift preserves the common logarithmic jump `Δ`.
      have hEndpoint :
          (((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 1 + ((s : ℝ) : ℂ) * w₁ 1) =
            (((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 0 + ((s : ℝ) : ℂ) * w₁ 0) + Δ :=
        Path.interpolated_log_lift_endpoint_eq s hw₀jump hw₁jump
      have hClosed :
          Complex.exp ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 0) + (((s : ℝ) : ℂ) * w₁ 0)) =
            Complex.exp ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 1) + (((s : ℝ) : ℂ) * w₁ 1)) := by
        calc
          Complex.exp ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 0) + (((s : ℝ) : ℂ) * w₁ 0)) =
              Complex.exp
                ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 0 + ((s : ℝ) : ℂ) * w₁ 0) + Δ) := by
            exact (Path.exp_add_eq_self_of_exp_eq_one hΔexp).symm
          _ =
              Complex.exp
                ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ 1) + (((s : ℝ) : ℂ) * w₁ 1)) := by
            rw [hEndpoint.symm]
      simpa [IsClosedPath, Path.interpolated_homotopy_fun] using hClosed
    · intro t
      constructor
      · -- The convexity estimate keeps every interpolated loop point inside the radius-`ε` ball.
        have h₀ : ‖Complex.exp (w₀ t)‖ < ε := by
          simpa [hw₀exp t, Metric.mem_ball, dist_eq_norm] using (hγ₀U ⟨t, rfl⟩).1
        have h₁ : ‖Complex.exp (w₁ t)‖ < ε := by
          simpa [hw₁exp t, Metric.mem_ball, dist_eq_norm] using (hγ₁U ⟨t, rfl⟩).1
        simpa [Path.interpolated_homotopy_fun, Metric.mem_ball, dist_eq_norm] using
          interpolatedExpNormLt hε h₀ h₁
      · -- Exponentials never vanish, so the homotopy also avoids the puncture.
        simpa [Path.interpolated_homotopy_fun] using
          Path.interpolated_log_lift_avoids_center (0 : ℂ)
            ((((1 : ℂ) - ((s : ℝ) : ℂ)) * w₀ t) + (((s : ℝ) : ℂ) * w₁ t))

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the standard-circle period
controls every integer-turn same-radius reference loop. -/
lemma circleTurns_logDerivIntegral_eq_int_mul_standardCirclePeriod
    {G : ℂ → ℂ} {ε : ℝ} {ρ : NNReal} {c : ℂ}
    (hε : 0 < ε)
    (hG_analytic : AnalyticOnNhd ℂ (logDeriv G) (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hρpos : 0 < (ρ : ℝ)) (hρε : (ρ : ℝ) < ε)
    (hperiod :
      ∫ᶜ z in standardCirclePath ρ, ((logDeriv G) dz) z = c) :
    ∀ m : ℤ,
      ∫ᶜ z in circleTurns ρ m, ((logDeriv G) dz) z = (m : ℂ) * c := by
  have hω_closed :
      IsClosedOn (Complex.realScalarOneForm (logDeriv G))
        (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    intro z hz
    rcases holomorphic_has_local_primitive
        (Metric.isOpen_ball.inter isOpen_ne) hG_analytic.differentiableOn hz with
      ⟨r, hr, hball, hExact⟩
    refine ⟨Metric.ball z r, Metric.isOpen_ball, Metric.mem_ball_self hr, hball, ?_⟩
    simpa [Complex.realScalarOneForm] using hExact.hasPrimitiveOn
  have hNat :
      ∀ k : ℕ,
        ∫ᶜ z in circleTurns ρ (k : ℤ), ((logDeriv G) dz) z = ((k : ℂ) * c) := by
    intro k
    have hω_cont :
        ContinuousOn (Complex.realScalarOneForm (logDeriv G))
          (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
        rw [show Complex.realScalarOneForm (logDeriv G) =
            fun z ↦ logDeriv G z • (1 : ℂ →L[ℝ] ℂ) by
              funext z
              exact Complex.realScalarOneForm_eq_smul (logDeriv G) z]
        exact hG_analytic.continuousOn.smul (continuousOn_const : ContinuousOn
          (fun _ : ℂ ↦ (1 : ℂ →L[ℝ] ℂ)) (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    have hhom :
        ClosedPathHomotopicIn (ball (0 : ℂ) ε \ ({0} : Set ℂ))
          (circleTurns ρ (k : ℤ)) (circleTurnsConcatNat ρ k) := by
      refine closedPathHomotopicIn_puncturedBall_of_sameIndexAtZero hε ?_ ?_
        (circleTurns_hasIndexAt_zero ρ (k : ℤ) hρpos)
        (circleTurnsConcatNat_hasIndexAt_zero ρ k hρpos)
      · rintro _ ⟨t, rfl⟩
        exact circleTurns_mem_puncturedBall hρpos hρε t
      · rintro _ ⟨t, rfl⟩
        exact circleTurnsConcatNat_mem_puncturedBall hρpos hρε t
    have hcircle_integrable :
        CurveIntegrable (Complex.realScalarOneForm (logDeriv G)) (circleTurns ρ (k : ℤ)) := by
      exact Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        (ω := Complex.realScalarOneForm (logDeriv G)) hω_cont
        (circleTurns_isPiecewiseDifferentiable ρ (k : ℤ)) <| by
          rintro _ ⟨t, rfl⟩
          exact circleTurns_mem_puncturedBall hρpos hρε t
    have hconcat_integrable :
        CurveIntegrable (Complex.realScalarOneForm (logDeriv G)) (circleTurnsConcatNat ρ k) := by
      exact Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        (ω := Complex.realScalarOneForm (logDeriv G)) hω_cont
        (circleTurnsConcatNat_isPiecewiseDifferentiable ρ k) <| by
          rintro _ ⟨t, rfl⟩
          exact circleTurnsConcatNat_mem_puncturedBall hρpos hρε t
    calc
      ∫ᶜ z in circleTurns ρ (k : ℤ), ((logDeriv G) dz) z =
          ∫ᶜ z in circleTurnsConcatNat ρ k, ((logDeriv G) dz) z := by
            have hEq :
                ∫ᶜ z in circleTurns ρ (k : ℤ), Complex.realScalarOneForm (logDeriv G) z =
                  ∫ᶜ z in circleTurnsConcatNat ρ k, Complex.realScalarOneForm (logDeriv G) z :=
              Path.curveIntegral_eq_of_homotopic_closed_paths_of_closed_form
                hhom (circleTurns_isPiecewiseDifferentiable ρ (k : ℤ))
                (circleTurnsConcatNat_isPiecewiseDifferentiable ρ k)
                hcircle_integrable hconcat_integrable hω_closed
            have hEq' :
                ∫ᶜ z in circleTurns ρ (k : ℤ), logDeriv G z • (1 : ℂ →L[ℝ] ℂ) =
                  ∫ᶜ z in circleTurnsConcatNat ρ k, logDeriv G z • (1 : ℂ →L[ℝ] ℂ) := by
              simpa [Complex.realScalarOneForm] using hEq
            have hEq'' :
                ∫ᶜ z in circleTurns ρ (k : ℤ), (((logDeriv G) dz) z).restrictScalars ℝ =
                  ∫ᶜ z in circleTurnsConcatNat ρ k, (((logDeriv G) dz) z).restrictScalars ℝ := by
              simpa using hEq'
            rw [curveIntegral_restrictScalars, curveIntegral_restrictScalars] at hEq''
            exact hEq''
      _ = (k : ℂ) * c := by
            exact circleTurnsConcatNat_logDerivIntegral hG_analytic hρpos hρε hperiod k
  intro m
  cases m with
  | ofNat k =>
      simpa [Int.ofNat_eq_natCast] using hNat k
  | negSucc k =>
      -- Reverse the corresponding positive-turn loop and use the sign change of the contour
      -- integral under path reversal.
      have hpos :
          ∫ᶜ z in circleTurns ρ ((k + 1 : ℕ) : ℤ), ((logDeriv G) dz) z =
            (((k + 1 : ℕ) : ℂ) * c) := by
        simpa [Int.ofNat_eq_natCast] using hNat (k + 1)
      rw [circleTurns_negSucc_eq_symm_succ]
      calc
        ∫ᶜ z in (circleTurns ρ ((k + 1 : ℕ) : ℤ)).symm, ((logDeriv G) dz) z =
            -∫ᶜ z in circleTurns ρ ((k + 1 : ℕ) : ℤ), ((logDeriv G) dz) z := by
              rw [curveIntegral_symm]
        _ = -(((k + 1 : ℕ) : ℂ) * c) := by
              rw [hpos]
        _ = ((Int.negSucc k : ℤ) : ℂ) * c := by
              calc
                -(((k + 1 : ℕ) : ℂ) * c) = (-(((k + 1 : ℕ) : ℂ))) * c := by ring
                _ = ((Int.negSucc k : ℤ) : ℂ) * c := by norm_num [Int.negSucc_eq]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: every closed loop in the
punctured ball is homotopic to a same-radius reference circle with the same winding index. -/
lemma closedLoop_homotopic_to_circleTurns_puncturedBall
    {ε : ℝ} {ρ : NNReal} (hε : 0 < ε)
    (hρpos : 0 < (ρ : ℝ)) (hρε : (ρ : ℝ) < ε) :
    ∀ {z : ℂ} (γ : Path z z),
      Set.range γ ⊆ ball (0 : ℂ) ε \ ({0} : Set ℂ) →
        ∃ m : ℤ, ClosedPathHomotopicIn
          (ball (0 : ℂ) ε \ ({0} : Set ℂ)) γ (circleTurns ρ m) := by
  intro z γ hγU
  obtain ⟨m, hγIndex⟩ := hasIndexAt_zero_of_closedPath_avoids_zero fun t ↦ (hγU ⟨t, rfl⟩).2
  refine ⟨m, ?_⟩
  -- Match the loop to the explicit reference circle by the punctured-ball homotopy owner.
  refine closedPathHomotopicIn_puncturedBall_of_sameIndexAtZero hε hγU ?_
    hγIndex (circleTurns_hasIndexAt_zero ρ m hρpos)
  rintro _ ⟨t, rfl⟩
  exact circleTurns_mem_puncturedBall hρpos hρε t
