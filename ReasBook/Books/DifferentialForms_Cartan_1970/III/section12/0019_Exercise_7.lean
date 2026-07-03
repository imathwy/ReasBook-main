import Mathlib
import cartan.III.section12.CircleSupNorm

-- Semantic recall tool `lean_leansearch` was unavailable in this environment; I matched the
-- statement surface against nearby local precedent in this section using `AnalyticOnNhd` and
-- circle supremum norms on `Metric.sphere`.

open Metric Set

section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {f : ℂ → F} {R r s ρ : ℝ}

/-- Helper for Exercise 7: analyticity on a larger disc restricts to the `DiffContOnCl` package on
any smaller centered disc. -/
lemma diffContOnCl_ball_of_lt_radius
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R)) (hr : r < R) :
    DiffContOnCl ℂ f (ball (0 : ℂ) r) := by
  -- Restrict the holomorphic data from the ambient disc to the smaller closed ball.
  exact hf.differentiableOn.diffContOnCl_ball <| closedBall_subset_ball hr

/-- Helper for Exercise 7: on a nonnegative radius, the circle supremum norm is the supremum over
the standard angular parameter interval. -/
lemma circleSupNorm_eq_sSup_image_Icc (hr : 0 ≤ r) :
    circleSupNorm f r =
      sSup ((fun θ : ℝ ↦ ‖f (circleMap (0 : ℂ) r θ)‖) '' Icc (0 : ℝ) (2 * Real.pi)) := by
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
  -- Rewrite the sphere supremum as the supremum of the angularly-parameterized family.
  calc
    circleSupNorm f r = sSup ((fun z : ℂ ↦ ‖f z‖) '' sphere (0 : ℂ) r) := rfl
    _ = sSup ((fun z : ℂ ↦ ‖f z‖) '' (circleMap (0 : ℂ) r '' Icc (0 : ℝ) (2 * Real.pi))) := by
      rw [hcircle]
    _ = sSup (((fun z : ℂ ↦ ‖f z‖) ∘ circleMap (0 : ℂ) r) '' Icc (0 : ℝ) (2 * Real.pi)) := by
      have himage :
          (fun z : ℂ ↦ ‖f z‖) '' (circleMap (0 : ℂ) r '' Icc (0 : ℝ) (2 * Real.pi)) =
            ((fun z : ℂ ↦ ‖f z‖) ∘ circleMap (0 : ℂ) r) '' Icc (0 : ℝ) (2 * Real.pi) := by
        ext t
        constructor
        · rintro ⟨z, ⟨θ, hθ, rfl⟩, rfl⟩
          exact ⟨θ, hθ, rfl⟩
        · rintro ⟨θ, hθ, rfl⟩
          exact ⟨circleMap (0 : ℂ) r θ, ⟨θ, hθ, rfl⟩, rfl⟩
      rw [himage]
    _ = sSup ((fun θ : ℝ ↦ ‖f (circleMap (0 : ℂ) r θ)‖) '' Icc (0 : ℝ) (2 * Real.pi)) := rfl

/-- Helper for Exercise 7: the maximum of `‖f‖` on a centered circle is attained at some point of
that circle. -/
lemma exists_mem_sphere_norm_eq_circleSupNorm
    (hr : 0 ≤ r) (hcont : ContinuousOn f (sphere (0 : ℂ) r)) :
    ∃ z ∈ sphere (0 : ℂ) r, ‖f z‖ = circleSupNorm f r := by
  have hne : (sphere (0 : ℂ) r).Nonempty :=
    ⟨circleMap (0 : ℂ) r 0, circleMap_mem_sphere (0 : ℂ) hr 0⟩
  -- Compactness of the circle produces a maximizer for the norm.
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_sphere (0 : ℂ) r).exists_sSup_image_eq hne hcont.norm
  exact ⟨z, hz, by simpa [circleSupNorm] using hmax.symm⟩

/-- Helper for Exercise 7: continuity on a closed centered disc makes the circle supremum norm
continuous on the corresponding radius interval. -/
lemma circleSupNorm_continuousOn_Icc_of_continuousOn_closedBall
    (hf : ContinuousOn f (closedBall (0 : ℂ) ρ)) :
    ContinuousOn (circleSupNorm f) (Icc (0 : ℝ) ρ) := by
  let circleParam : Icc (0 : ℝ) ρ × Icc (0 : ℝ) (2 * Real.pi) → ℂ :=
    fun p ↦ circleMap (0 : ℂ) p.1.1 p.2.1
  let g : Icc (0 : ℝ) ρ → Icc (0 : ℝ) (2 * Real.pi) → ℝ :=
    fun r θ ↦ ‖f (circleParam (r, θ))‖
  have hparam_mem : ∀ p, circleParam p ∈ closedBall (0 : ℂ) ρ := by
    intro p
    have hsphere : circleParam p ∈ sphere (0 : ℂ) p.1.1 := by
      exact circleMap_mem_sphere (0 : ℂ) p.1.2.1 p.2.1
    exact (closedBall_subset_closedBall p.1.2.2) <| sphere_subset_closedBall hsphere
  have hcircle : Continuous circleParam := by
    -- The joint circle parameterization is continuous in both radius and angle.
    fun_prop
  have hg : Continuous ↿g := by
    -- Compose the continuous parameterization with the closed-ball continuity of `f`.
    have hcont : Continuous (fun p ↦ f (circleParam p)) :=
      hf.comp_continuous hcircle hparam_mem
    simpa [g] using hcont.norm
  have hsSup : Continuous fun r : Icc (0 : ℝ) ρ ↦
      sSup (g r '' (univ : Set (Icc (0 : ℝ) (2 * Real.pi)))) :=
    isCompact_univ.continuous_sSup hg
  rw [continuousOn_iff_continuous_restrict]
  -- Identify the restricted radius function with the compact supremum family above.
  refine hsSup.congr ?_
  intro r
  have himage :
      g r '' (univ : Set (Icc (0 : ℝ) (2 * Real.pi))) =
        (fun θ : ℝ ↦ ‖f (circleMap (0 : ℂ) r.1 θ)‖) '' Icc (0 : ℝ) (2 * Real.pi) := by
    ext t
    constructor
    · rintro ⟨θ, -, rfl⟩
      exact ⟨θ.1, θ.2, rfl⟩
    · rintro ⟨θ, hθ, rfl⟩
      exact ⟨⟨θ, hθ⟩, mem_univ _, rfl⟩
  -- The subtype-restricted function is exactly `circleSupNorm`.
  simpa [Set.restrict, himage] using (circleSupNorm_eq_sSup_image_Icc (f := f) r.2.1).symm

/-- Helper for Exercise 7: the maximum modulus principle bounds every point of a closed centered
disc by the circle supremum norm on its boundary. -/
lemma norm_le_circleSupNorm_of_mem_closedBall
    (hd : DiffContOnCl ℂ f (ball (0 : ℂ) s)) (hs : 0 < s) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) s) :
    ‖f z‖ ≤ circleSupNorm f s := by
  have hz' : z ∈ closure (ball (0 : ℂ) s) := by
    simpa [closure_ball (0 : ℂ) hs.ne'] using hz
  -- Apply the frontier form of the maximum modulus principle to the centered disc.
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_ hz'
  intro w hw
  rw [frontier_ball (0 : ℂ) hs.ne'] at hw
  exact (hd.continuousOn_ball.mono sphere_subset_closedBall).norm_le_circleSupNorm hw

/-- Helper for Exercise 7: if the circle supremum norm agrees at two radii, then the function is
already constant on the larger disc. -/
lemma eqOn_const_ball_of_circleSupNorm_eq
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R))
    (hr0 : 0 ≤ r) (hrs : r < s) (hsR : s < R)
    (heq : circleSupNorm f r = circleSupNorm f s) :
    ∃ c : ℂ, EqOn f (fun _ ↦ c) (ball (0 : ℂ) s) := by
  have hs : 0 < s := lt_of_le_of_lt hr0 hrs
  have hd : DiffContOnCl ℂ f (ball (0 : ℂ) s) := diffContOnCl_ball_of_lt_radius hf hsR
  have hcontSphere : ContinuousOn f (sphere (0 : ℂ) r) :=
    (hd.continuousOn_ball.mono <|
      sphere_subset_closedBall.trans <| closedBall_subset_closedBall hrs.le)
  obtain ⟨z, hz, hzEq⟩ := exists_mem_sphere_norm_eq_circleSupNorm (f := f) hr0 hcontSphere
  have hzBall : z ∈ ball (0 : ℂ) s := by
    exact (closedBall_subset_ball hrs) <| sphere_subset_closedBall hz
  have hzClosed : z ∈ closedBall (0 : ℂ) s := by
    exact (closedBall_subset_closedBall hrs.le) <| sphere_subset_closedBall hz
  have hzOuter : ‖f z‖ = circleSupNorm f s := hzEq.trans heq
  have hzMax : IsMaxOn (norm ∘ f) (ball (0 : ℂ) s) z := by
    -- Equality of the two boundary suprema upgrades the inner maximizer to a global maximizer.
    intro w hw
    calc
      ‖f w‖ ≤ circleSupNorm f s := by
        exact norm_le_circleSupNorm_of_mem_closedBall (f := f) hd hs (ball_subset_closedBall hw)
      _ = ‖f z‖ := hzOuter.symm
  refine ⟨f z, ?_⟩
  -- An interior maximum for `‖f‖` forces constancy on the whole larger ball.
  simpa [Function.const] using Complex.eq_const_of_exists_max hd.differentiableOn hzBall hzMax

/-- Exercise 7 (1): if `f` is holomorphic on the disc `‖z‖ < R`, then the maximum modulus
`M(r) = sup_{‖z‖ = r} ‖f z‖` is continuous for `0 ≤ r < R`. -/
theorem circleSupNorm_continuousOn
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R)) :
    ContinuousOn (circleSupNorm f) (Ico (0 : ℝ) R) := by
  intro r hr
  obtain ⟨ρ, hrρ, hρR⟩ := exists_between hr.2
  have hd : DiffContOnCl ℂ f (ball (0 : ℂ) ρ) := diffContOnCl_ball_of_lt_radius hf hρR
  have hcontρ : ContinuousOn (circleSupNorm f) (Icc (0 : ℝ) ρ) :=
    circleSupNorm_continuousOn_Icc_of_continuousOn_closedBall (f := f) hd.continuousOn_ball
  have hlocal : Icc (0 : ℝ) ρ ∈ nhdsWithin r (Ico (0 : ℝ) R) := by
    -- The smaller closed interval is a neighborhood within the larger half-open interval.
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
    refine ⟨Iio ρ, isOpen_Iio.mem_nhds hrρ, ?_⟩
    intro y hy
    exact ⟨hy.2.1, hy.1.le⟩
  exact (hcontρ r ⟨hr.1, hrρ.le⟩).mono_of_mem_nhdsWithin hlocal

/-- Exercise 7 (2): if `f` is holomorphic on the disc `‖z‖ < R`, then the maximum modulus
`M(r) = sup_{‖z‖ = r} ‖f z‖` is monotone increasing for `0 ≤ r < R`. -/
theorem circleSupNorm_monotoneOn
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R)) :
    MonotoneOn (circleSupNorm f) (Ico (0 : ℝ) R) := by
  intro r hr s hs hrs
  by_cases hrs' : r = s
  · simpa [hrs']
  have hrslt : r < s := lt_of_le_of_ne hrs hrs'
  have hspos : 0 < s := lt_of_le_of_lt hr.1 hrslt
  have hd : DiffContOnCl ℂ f (ball (0 : ℂ) s) := diffContOnCl_ball_of_lt_radius hf hs.2
  have hcontSphere : ContinuousOn f (sphere (0 : ℂ) r) :=
    (hd.continuousOn_ball.mono <|
      sphere_subset_closedBall.trans <| closedBall_subset_closedBall hrs)
  obtain ⟨z, hz, hzEq⟩ := exists_mem_sphere_norm_eq_circleSupNorm (f := f) hr.1 hcontSphere
  have hzClosed : z ∈ closedBall (0 : ℂ) s := by
    exact (closedBall_subset_closedBall hrs) <| sphere_subset_closedBall hz
  -- Compare the inner boundary maximizer with the outer boundary supremum.
  calc
    circleSupNorm f r = ‖f z‖ := hzEq.symm
    _ ≤ circleSupNorm f s := norm_le_circleSupNorm_of_mem_closedBall (f := f) hd hspos hzClosed

end

/-- Exercise 7 (3): if `f` is holomorphic on the disc `‖z‖ < R` and is not constant there, then
the maximum modulus `M(r)` is strictly increasing for `0 ≤ r < R`. -/
theorem circleSupNorm_strictMonoOn_of_not_constant
    {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball (0 : ℂ) R))
    (hfnc : ¬ ∃ c : ℂ, EqOn f (fun _ ↦ c) (ball (0 : ℂ) R)) :
    StrictMonoOn (circleSupNorm f) (Ico (0 : ℝ) R) := by
  intro r hr s hs hrs
  have hmono := circleSupNorm_monotoneOn (f := f) hf
  have hle : circleSupNorm f r ≤ circleSupNorm f s := hmono hr hs hrs.le
  have hne : circleSupNorm f r ≠ circleSupNorm f s := by
    intro heq
    rcases eqOn_const_ball_of_circleSupNorm_eq (f := f) hf hr.1 hrs hs.2 heq with ⟨c, hc⟩
    have hspos : 0 < s := lt_of_le_of_lt hr.1 hrs
    have hconstR : EqOn f (fun _ ↦ c) (ball (0 : ℂ) R) := by
      have hEvent : f =ᶠ[nhds (0 : ℂ)] (fun _ ↦ c) := by
        -- Constancy on the smaller ball gives eventual equality at the center.
        refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) hspos) ?_
        intro z hz
        exact hc hz
      have hpre : IsPreconnected (ball (0 : ℂ) R) := (convex_ball (0 : ℂ) R).isPreconnected
      have hzero : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self (lt_trans hspos hs.2)
      exact hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hpre hzero hEvent
    exact hfnc ⟨c, hconstR⟩
  exact lt_of_le_of_ne hle hne
