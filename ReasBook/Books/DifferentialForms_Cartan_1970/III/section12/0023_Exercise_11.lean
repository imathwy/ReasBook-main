import Mathlib
import DifferentialForms_Cartan_1970.III.section12.CircleSupNorm

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the statement
-- surface was checked against Mathlib's `AnalyticOnNhd`, `Metric.closedBall`, and nearby
-- circle-supremum precedent in this section.

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Complex Metric Set

/-- The supremum of `Re (f z)` on the centered circle of radius `r`. -/
noncomputable def circleSupRealPart (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z : ℂ ↦ re (f z)) '' sphere (0 : ℂ) r)

/-- Helper for Exercise 11: any boundary value of `Re (f z)` is bounded by the boundary supremum. -/
lemma re_apply_le_circleSupRealPart {f : ℂ → ℂ} {r : ℝ}
    (hf : ContinuousOn f (sphere (0 : ℂ) r)) {z : ℂ} (hz : z ∈ sphere (0 : ℂ) r) :
    (f z).re ≤ circleSupRealPart f r := by
  -- The real-part image of the compact circle is bounded above, so each boundary value is below
  -- its supremum.
  have hre : ContinuousOn (fun w : ℂ ↦ (f w).re) (sphere (0 : ℂ) r) := by
    simpa [Function.comp] using
      Complex.continuous_re.continuousOn.comp hf (Set.mapsTo_univ _ _)
  exact le_csSup ((isCompact_sphere (0 : ℂ) r).bddAbove_image hre) (mem_image_of_mem _ hz)

/-- Helper for Exercise 11: on a circle, the maximum modulus of `exp ∘ f` is `exp` of the maximum
real part of `f`. -/
lemma circleSupNorm_exp_eq_exp_circleSupRealPart {f : ℂ → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hf : ContinuousOn f (sphere (0 : ℂ) r)) :
    circleSupNorm (fun z ↦ Complex.exp (f z)) r = Real.exp (circleSupRealPart f r) := by
  let g : ℂ → ℂ := fun z ↦ Complex.exp (f z)
  have hg : ContinuousOn g (sphere (0 : ℂ) r) := hf.cexp
  have hgB :
      BddAbove ((fun z : ℂ ↦ ‖g z‖) '' sphere (0 : ℂ) r) :=
    (isCompact_sphere (0 : ℂ) r).bddAbove_image hg.norm
  refine le_antisymm ?_ ?_
  · -- Every boundary value of `‖exp (f z)‖` is controlled by `exp (A(r))`.
    refine csSup_le (Set.Nonempty.image _ ((NormedSpace.sphere_nonempty (x := (0 : ℂ)) (r := r)).2 hr)) ?_
    rintro y ⟨z, hz, rfl⟩
    simpa [g, Complex.norm_exp] using
      (Real.exp_le_exp.mpr (re_apply_le_circleSupRealPart hf hz))
  · -- A maximizer of `Re (f z)` on the compact circle gives the reverse inequality.
    obtain ⟨z, hz, hzmax⟩ :=
      (isCompact_sphere (0 : ℂ) r).exists_isMaxOn
        ((NormedSpace.sphere_nonempty (x := (0 : ℂ)) (r := r)).2 hr)
        (by
          simpa [Function.comp] using
            Complex.continuous_re.continuousOn.comp hf (Set.mapsTo_univ _ _))
    have hsSup :
        circleSupRealPart f r = (f z).re := by
      have hgreatest :
          IsGreatest ((fun w : ℂ ↦ (f w).re) '' sphere (0 : ℂ) r) ((f z).re) := by
        refine ⟨mem_image_of_mem _ hz, ?_⟩
        rintro y ⟨w, hw, rfl⟩
        exact hzmax hw
      simpa [circleSupRealPart] using hgreatest.csSup_eq
    calc
      Real.exp (circleSupRealPart f r) = Real.exp ((f z).re) := by rw [hsSup]
      _ = ‖g z‖ := by rw [Complex.norm_exp]
      _ ≤ circleSupNorm g r := hg.norm_le_circleSupNorm hz

/-- Helper for Exercise 11: the radius-zero supremum is just the value at the origin. -/
lemma circleSupRealPart_zero {f : ℂ → ℂ} :
    circleSupRealPart f 0 = (f 0).re := by
  -- The zero-radius circle is the singleton `{0}`.
  rw [circleSupRealPart, Metric.sphere_zero, Set.image_singleton, csSup_singleton]

/-- Helper for Exercise 11: on a nonnegative radius, the boundary real-part supremum is the
supremum over the standard angular parameter interval. -/
lemma circleSupRealPart_eq_sSup_image_Icc {f : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r) :
    circleSupRealPart f r =
      sSup ((fun θ : ℝ ↦ (f (circleMap (0 : ℂ) r θ)).re) '' Icc (0 : ℝ) (2 * Real.pi)) := by
  have hcircle :
      circleMap (0 : ℂ) r '' Icc (0 : ℝ) (2 * Real.pi) = sphere (0 : ℂ) r := by
    refine Subset.antisymm ?_ ?_
    · rintro z ⟨θ, hθ, rfl⟩
      simpa using circleMap_mem_sphere (0 : ℂ) hr θ
    · have hIoc : circleMap (0 : ℂ) r '' Ioc (0 : ℝ) (2 * Real.pi) = sphere (0 : ℂ) r := by
        simpa [abs_of_nonneg hr] using (image_circleMap_Ioc (0 : ℂ) r)
      rw [← hIoc]
      rintro z ⟨θ, hθ, rfl⟩
      exact ⟨θ, Ioc_subset_Icc_self hθ, rfl⟩
  -- Rewrite the boundary image through the fixed angular parametrization.
  calc
    circleSupRealPart f r = sSup ((fun z : ℂ ↦ (f z).re) '' sphere (0 : ℂ) r) := rfl
    _ =
        sSup ((fun z : ℂ ↦ (f z).re) ''
          (circleMap (0 : ℂ) r '' Icc (0 : ℝ) (2 * Real.pi))) := by
      rw [hcircle]
    _ =
        sSup (((fun z : ℂ ↦ (f z).re) ∘ circleMap (0 : ℂ) r) ''
          Icc (0 : ℝ) (2 * Real.pi)) := by
      have himage :
          (fun z : ℂ ↦ (f z).re) '' (circleMap (0 : ℂ) r '' Icc (0 : ℝ) (2 * Real.pi)) =
            (((fun z : ℂ ↦ (f z).re) ∘ circleMap (0 : ℂ) r) ''
              Icc (0 : ℝ) (2 * Real.pi)) := by
        ext t
        constructor
        · rintro ⟨z, ⟨θ, hθ, rfl⟩, rfl⟩
          exact ⟨θ, hθ, rfl⟩
        · rintro ⟨θ, hθ, rfl⟩
          exact ⟨circleMap (0 : ℂ) r θ, ⟨θ, hθ, rfl⟩, rfl⟩
      rw [himage]
    _ =
        sSup ((fun θ : ℝ ↦ (f (circleMap (0 : ℂ) r θ)).re) ''
          Icc (0 : ℝ) (2 * Real.pi)) := rfl

/-- Helper for Exercise 11: continuity on a closed centered disc makes the boundary real-part
supremum continuous on the corresponding radius interval. -/
lemma circleSupRealPart_continuousOn_Icc_of_continuousOn_closedBall
    {f : ℂ → ℂ} {ρ : ℝ}
    (hf : ContinuousOn f (closedBall (0 : ℂ) ρ)) :
    ContinuousOn (circleSupRealPart f) (Icc (0 : ℝ) ρ) := by
  let circleParam : Icc (0 : ℝ) ρ × Icc (0 : ℝ) (2 * Real.pi) → ℂ :=
    fun p ↦ circleMap (0 : ℂ) p.1.1 p.2.1
  let g : Icc (0 : ℝ) ρ → Icc (0 : ℝ) (2 * Real.pi) → ℝ :=
    fun r θ ↦ (f (circleParam (r, θ))).re
  have hparam_mem : ∀ p, circleParam p ∈ closedBall (0 : ℂ) ρ := by
    intro p
    have hsphere : circleParam p ∈ sphere (0 : ℂ) p.1.1 := by
      exact circleMap_mem_sphere (0 : ℂ) p.1.2.1 p.2.1
    exact (closedBall_subset_closedBall p.1.2.2) <| sphere_subset_closedBall hsphere
  have hcircle : Continuous circleParam := by
    -- The centered-circle parametrization is jointly continuous in radius and angle.
    fun_prop
  have hg : Continuous ↿g := by
    -- Compose closed-ball continuity of `f` with the parameterization, then take real parts.
    have hcont : Continuous (fun p ↦ f (circleParam p)) :=
      hf.comp_continuous hcircle hparam_mem
    simpa [g, Function.comp] using Complex.continuous_re.comp hcont
  have hsSup :
      Continuous fun r : Icc (0 : ℝ) ρ ↦
        sSup (g r '' (univ : Set (Icc (0 : ℝ) (2 * Real.pi)))) :=
    isCompact_univ.continuous_sSup hg
  rw [continuousOn_iff_continuous_restrict]
  -- Identify the restricted radius function with the compact supremum family above.
  refine hsSup.congr ?_
  intro r
  have himage :
      g r '' (univ : Set (Icc (0 : ℝ) (2 * Real.pi))) =
        (fun θ : ℝ ↦ (f (circleMap (0 : ℂ) r.1 θ)).re) '' Icc (0 : ℝ) (2 * Real.pi) := by
    ext t
    constructor
    · rintro ⟨θ, -, rfl⟩
      exact ⟨θ.1, θ.2, rfl⟩
    · rintro ⟨θ, hθ, rfl⟩
      exact ⟨⟨θ, hθ⟩, mem_univ _, rfl⟩
  -- The subtype-restricted function is exactly `circleSupRealPart`.
  simpa [Set.restrict, himage] using
    (circleSupRealPart_eq_sSup_image_Icc (f := f) r.2.1).symm

/-- Exercise 11 (1): if `f` is holomorphic on a neighborhood of the closed disc `|z| ≤ R`, then
`r ↦ A(r)`, defined as the supremum of `Re (f z)` on `|z| = r`, is continuous on `0 ≤ r ≤ R`. -/
theorem circleSupRealPart_continuousOn
    {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R)) :
    ContinuousOn (circleSupRealPart f) (Icc (0 : ℝ) R) := by
  -- Route correction: replace the unavailable sibling-import route with the local compact angular
  -- parametrization argument on `[0, R] × [0, 2π]`.
  exact circleSupRealPart_continuousOn_Icc_of_continuousOn_closedBall hf.continuousOn

/-- Exercise 11 (2): if `f` is holomorphic on a neighborhood of the closed disc `|z| ≤ R`, then
`r ↦ A(r)`, defined as the supremum of `Re (f z)` on `|z| = r`, is monotone increasing on
`0 ≤ r ≤ R`. -/
theorem circleSupRealPart_monotoneOn
    {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R)) :
    MonotoneOn (circleSupRealPart f) (Icc (0 : ℝ) R) := by
  intro r₁ hr₁ r₂ hr₂ hr₁₂
  rcases eq_or_lt_of_le hr₂.1 with (rfl | hr₂pos)
  · have hr₁zero : r₁ = 0 := le_antisymm hr₁₂ hr₁.1
    simp [hr₁zero, circleSupRealPart_zero]
  have hsubset : closedBall (0 : ℂ) r₂ ⊆ closedBall (0 : ℂ) R :=
    closedBall_subset_closedBall hr₂.2
  let g : ℂ → ℂ := fun z ↦ Complex.exp (f z)
  have hg_hd : DiffContOnCl ℂ g (ball (0 : ℂ) r₂) := by
    -- `exp ∘ f` is analytic on the smaller closed disc, hence differentiable on the open disc and
    -- continuous up to the boundary.
    exact ((hf.mono hsubset).cexp.differentiableOn).diffContOnCl_ball subset_rfl
  have hfr₁ : ContinuousOn f (sphere (0 : ℂ) r₁) := hf.continuousOn.mono <| by
    intro z hz
    exact closedBall_subset_closedBall hr₁.2 (sphere_subset_closedBall hz)
  have hrealB :
      BddAbove ((fun z : ℂ ↦ (f z).re) '' sphere (0 : ℂ) r₁) :=
    (isCompact_sphere (0 : ℂ) r₁).bddAbove_image <| by
      simpa [Function.comp] using
        Complex.continuous_re.continuousOn.comp hfr₁ (Set.mapsTo_univ _ _)
  refine csSup_le
    (Set.Nonempty.image _ ((NormedSpace.sphere_nonempty (x := (0 : ℂ)) (r := r₁)).2 hr₁.1)) ?_
  rintro y ⟨z, hz, rfl⟩
  have hzClosure : z ∈ closure (ball (0 : ℂ) r₂) := by
    have hzClosed : z ∈ closedBall (0 : ℂ) r₂ := by
      rw [mem_closedBall_zero_iff, mem_sphere_zero_iff_norm.mp hz]
      exact hr₁₂
    simpa [closure_ball (0 : ℂ) hr₂pos.ne'] using hzClosed
  have hboundary :
      ∀ w ∈ frontier (ball (0 : ℂ) r₂), ‖g w‖ ≤ Real.exp (circleSupRealPart f r₂) := by
    intro w hw
    rw [frontier_ball (0 : ℂ) hr₂pos.ne'] at hw
    have hfw : ContinuousOn f (sphere (0 : ℂ) r₂) := hf.continuousOn.mono <| by
      intro u hu
      exact closedBall_subset_closedBall hr₂.2 (sphere_subset_closedBall hu)
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (re_apply_le_circleSupRealPart hfw hw)
  have hnorm :
      ‖g z‖ ≤ Real.exp (circleSupRealPart f r₂) :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg_hd hboundary hzClosure
  rw [Complex.norm_exp] at hnorm
  exact (Real.exp_le_exp.mp hnorm)

/-- Helper for Exercise 11: every interior point of the open disc has real part bounded by the
boundary supremum at radius `R`. -/
lemma mapsTo_re_le_circleSupRealPart {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R)) (hR : 0 < R) :
    MapsTo f (ball (0 : ℂ) R) {z | z.re ≤ circleSupRealPart f R} := by
  intro z hz
  let ρ : ℝ := ‖z‖
  have hρ : 0 ≤ ρ := norm_nonneg z
  have hρR : ρ ≤ R := le_of_lt (mem_ball_zero_iff.mp hz)
  have hfz : ContinuousOn f (sphere (0 : ℂ) ρ) := hf.continuousOn.mono <| by
    intro w hw
    exact closedBall_subset_closedBall hρR (sphere_subset_closedBall hw)
  have hzρ : z ∈ sphere (0 : ℂ) ρ := by
    simpa [ρ] using mem_sphere_zero_iff_norm.mpr rfl
  have hzle : (f z).re ≤ circleSupRealPart f ρ :=
    re_apply_le_circleSupRealPart hfz hzρ
  have hmono := circleSupRealPart_monotoneOn hf
  exact hzle.trans (hmono ⟨hρ, hρR⟩ ⟨hR.le, le_rfl⟩ hρR)

/-- Helper for Exercise 11: if the outer real-part supremum is zero and `f(0)=0`, then the inner
boundary supremum of `‖f‖` vanishes as well. -/
lemma circleSupNorm_eq_zero_of_circleSupRealPart_eq_zero {f : ℂ → ℂ} {r R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hf0 : f 0 = 0)
    (hr : 0 ≤ r) (hrR : r < R)
    (hA : circleSupRealPart f R = 0) :
    circleSupNorm f r = 0 := by
  rcases eq_or_lt_of_le hr with (rfl | hrpos)
  · -- On the degenerate circle, only the origin appears.
    simp [circleSupNorm, Metric.sphere_zero, hf0]
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hmaps0 : MapsTo f (ball (0 : ℂ) R) {z | z.re ≤ 0} := by
    intro z hz
    simpa [hA] using mapsTo_re_le_circleSupRealPart hf hR hz
  have hcontf : ContinuousOn f (sphere (0 : ℂ) r) := hf.continuousOn.mono <| by
    intro z hz
    exact closedBall_subset_closedBall (le_of_lt hrR) (sphere_subset_closedBall hz)
  have hnormB :
      BddAbove ((fun z : ℂ ↦ ‖f z‖) '' sphere (0 : ℂ) r) :=
    (isCompact_sphere (0 : ℂ) r).bddAbove_image hcontf.norm
  have hnonneg : 0 ≤ circleSupNorm f r := by
    obtain ⟨z, hz⟩ := (NormedSpace.sphere_nonempty (x := (0 : ℂ)) (r := r)).2 hr
    exact (norm_nonneg _).trans (le_csSup hnormB (mem_image_of_mem _ hz))
  refine le_antisymm ?_ hnonneg
  by_contra hpos
  have hpos' : 0 < circleSupNorm f r := lt_of_not_ge hpos
  let ε : ℝ := circleSupNorm f r * (R - r) / (4 * r)
  have hεpos : 0 < ε := by
    have hRr : 0 < R - r := sub_pos.mpr hrR
    positivity
  have hmapsε : MapsTo f (ball (0 : ℂ) R) {z | z.re ≤ ε} := by
    intro z hz
    exact (hmaps0 hz).trans hεpos.le
  have hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) R) :=
    hf.differentiableOn.mono ball_subset_closedBall
  have hbound : circleSupNorm f r ≤ 2 * ε * r / (R - r) := by
    refine csSup_le
      (Set.Nonempty.image _ ((NormedSpace.sphere_nonempty (x := (0 : ℂ)) (r := r)).2 hr)) ?_
    rintro y ⟨z, hz, rfl⟩
    have hzball : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hz]
      exact hrR
    have hzNorm : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
    have hbc := Complex.borelCaratheodory_zero hεpos hdiff hmapsε hR hzball hf0
    rw [hzNorm] at hbc
    exact hbc
  have hhalf : 2 * ε * r / (R - r) = circleSupNorm f r / 2 := by
    have hRr : R - r ≠ 0 := sub_ne_zero.mpr hrR.ne'
    have hrne : (r : ℝ) ≠ 0 := hrpos.ne'
    dsimp [ε]
    field_simp [hRr, hrne]
    ring
  linarith [hbound]

/-- Exercise 11 (3): if `f` is holomorphic on a neighborhood of the closed disc `|z| ≤ R` and
`f 0 = 0`, then for `0 ≤ r < R` the maximum modulus on `|z| = r` is bounded by
`(2r / (R - r)) A(R)`. -/
theorem circleSupNorm_le_mul_circleSupRealPart_of_zero
    {f : ℂ → ℂ} {r R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hf0 : f 0 = 0)
    (hr : 0 ≤ r) (hrR : r < R) :
    circleSupNorm f r ≤
      (2 * r / (R - r)) * circleSupRealPart f R := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hmaps : MapsTo f (ball (0 : ℂ) R) {z | z.re ≤ circleSupRealPart f R} :=
    mapsTo_re_le_circleSupRealPart hf hR
  have hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) R) :=
    hf.differentiableOn.mono ball_subset_closedBall
  by_cases hApos : 0 < circleSupRealPart f R
  · -- The positive branch is the direct Borel–Carathéodory estimate on each boundary point.
    have hcontf : ContinuousOn f (sphere (0 : ℂ) r) := hf.continuousOn.mono <| by
      intro z hz
      exact closedBall_subset_closedBall (le_of_lt hrR) (sphere_subset_closedBall hz)
    have hnormB :
        BddAbove ((fun z : ℂ ↦ ‖f z‖) '' sphere (0 : ℂ) r) :=
      (isCompact_sphere (0 : ℂ) r).bddAbove_image hcontf.norm
    refine csSup_le
      (Set.Nonempty.image _ ((NormedSpace.sphere_nonempty (x := (0 : ℂ)) (r := r)).2 hr)) ?_
    rintro y ⟨z, hz, rfl⟩
    have hzball : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hz]
      exact hrR
    have hzNorm : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
    have hbc := Complex.borelCaratheodory_zero hApos hdiff hmaps hR hzball hf0
    rw [hzNorm] at hbc
    calc
      ‖f z‖ ≤ 2 * circleSupRealPart f R * r / (R - r) := hbc
      _ = (2 * r / (R - r)) * circleSupRealPart f R := by ring
  · -- If `A(R) ≤ 0`, monotonicity and `f(0)=0` force `A(R)=0`, hence `f` vanishes on the inner
    -- boundary.
    have hmono := circleSupRealPart_monotoneOn hf
    have hA0 : circleSupRealPart f 0 = 0 := by simpa [hf0] using circleSupRealPart_zero (f := f)
    have hAnonneg : 0 ≤ circleSupRealPart f R := by
      have := hmono ⟨le_rfl, hR.le⟩ ⟨hR.le, le_rfl⟩ hR.le
      simpa [hA0] using this
    have hAeq : circleSupRealPart f R = 0 := le_antisymm (not_lt.mp hApos) hAnonneg
    have hzero : circleSupNorm f r = 0 :=
      circleSupNorm_eq_zero_of_circleSupRealPart_eq_zero hf hf0 hr hrR hAeq
    simpa [hzero, hAeq]

/-- Exercise 11 (4): if `f` is holomorphic on a neighborhood of the closed disc `|z| ≤ R`, then
for `0 ≤ r < R` the maximum modulus on `|z| = r` is bounded by
`(2r / (R - r)) A(R) + ((R + r) / (R - r)) |f 0|`. -/
theorem circleSupNorm_le_mul_circleSupRealPart_add_norm_zero
    {f : ℂ → ℂ} {r R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hr : 0 ≤ r) (hrR : r < R) :
    circleSupNorm f r ≤
      (2 * r / (R - r)) * circleSupRealPart f R +
        ((R + r) / (R - r)) * ‖f 0‖ := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  let g : ℂ → ℂ := fun z ↦ f z - f 0
  have hg : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) R) :=
    hf.sub analyticOnNhd_const
  have hg0 : g 0 = 0 := by simp [g]
  have hg_cont : ContinuousOn g (sphere (0 : ℂ) r) := hg.continuousOn.mono <| by
    intro z hz
    exact closedBall_subset_closedBall (le_of_lt hrR) (sphere_subset_closedBall hz)
  have hf_cont : ContinuousOn f (sphere (0 : ℂ) r) := hf.continuousOn.mono <| by
    intro z hz
    exact closedBall_subset_closedBall (le_of_lt hrR) (sphere_subset_closedBall hz)
  have hnormB :
      BddAbove ((fun z : ℂ ↦ ‖f z‖) '' sphere (0 : ℂ) r) :=
    (isCompact_sphere (0 : ℂ) r).bddAbove_image hf_cont.norm
  have hshift :
      circleSupNorm f r ≤ circleSupNorm g r + ‖f 0‖ := by
    -- Pointwise, `‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖`; taking the boundary supremum preserves it.
    refine csSup_le
      (Set.Nonempty.image _ ((NormedSpace.sphere_nonempty (x := (0 : ℂ)) (r := r)).2 hr)) ?_
    rintro y ⟨z, hz, rfl⟩
    calc
      ‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
      _ ≤ circleSupNorm g r + ‖f 0‖ := by
        gcongr
        simpa [g] using hg_cont.norm_le_circleSupNorm hz
  have hshiftA :
      circleSupRealPart g R ≤ circleSupRealPart f R + ‖f 0‖ := by
    have hgR_cont : ContinuousOn g (sphere (0 : ℂ) R) := hg.continuousOn.mono sphere_subset_closedBall
    have hreB :
        BddAbove ((fun z : ℂ ↦ (g z).re) '' sphere (0 : ℂ) R) :=
      (isCompact_sphere (0 : ℂ) R).bddAbove_image <| by
        simpa [Function.comp] using
          Complex.continuous_re.continuousOn.comp hgR_cont (Set.mapsTo_univ _ _)
    refine csSup_le
      (Set.Nonempty.image _ ((NormedSpace.sphere_nonempty (x := (0 : ℂ)) (r := R)).2 hR.le)) ?_
    rintro y ⟨z, hz, rfl⟩
    have hzA : (f z).re ≤ circleSupRealPart f R :=
      re_apply_le_circleSupRealPart (hf.continuousOn.mono sphere_subset_closedBall) hz
    calc
      (g z).re = (f z).re - (f 0).re := by simp [g, sub_re]
      _ ≤ circleSupRealPart f R + ‖f 0‖ := by
        have hre_norm : |(f 0).re| ≤ ‖f 0‖ := Complex.abs_re_le_norm (f 0)
        linarith [hzA, neg_le_abs ((f 0).re), hre_norm]
  have hzero_case :
      circleSupNorm g r ≤ (2 * r / (R - r)) * circleSupRealPart g R :=
    circleSupNorm_le_mul_circleSupRealPart_of_zero hg hg0 hr hrR
  have hden : (R - r) ≠ 0 := sub_ne_zero.mpr hrR.ne'
  calc
    circleSupNorm f r ≤ circleSupNorm g r + ‖f 0‖ := hshift
    _ ≤ (2 * r / (R - r)) * circleSupRealPart g R + ‖f 0‖ := by
      gcongr
    _ ≤ (2 * r / (R - r)) * (circleSupRealPart f R + ‖f 0‖) + ‖f 0‖ := by
      gcongr
    _ = (2 * r / (R - r)) * circleSupRealPart f R +
          ((R + r) / (R - r)) * ‖f 0‖ := by
      field_simp [hden]
      ring
