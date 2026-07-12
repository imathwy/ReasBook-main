import Mathlib
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import DifferentialForms_Cartan_1970.IV.section16.«0002_Theorem_IV_4_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

open Complex Filter InnerProductSpace Metric Real Set

-- Semantic search tool `lean_leansearch` is unavailable in this session; the statement shape was
-- chosen by local section precedent together with the section IV.4-extra Dirichlet API and
-- mathlib's `Real.circleAverage` and `HarmonicContOnCl` APIs.

/-- A real-valued function is subharmonic on `D` if it is continuous there and satisfies the
sub-mean inequality on all sufficiently small circles centered at points of `D`. -/
def IsSubharmonicOn (f : ℂ → ℝ) (D : Set ℂ) : Prop :=
  ContinuousOn f D ∧
    ∀ ⦃a : ℂ⦄, a ∈ D →
      ∃ ε > 0, ∀ ⦃r : ℝ⦄, 0 < r → r < ε →
        closedBall a r ⊆ D ∧ f a ≤ Real.circleAverage f a r

/-- A subharmonic function is continuous on its domain. -/
theorem IsSubharmonicOn.continuousOn {f : ℂ → ℝ} {D : Set ℂ} (hf : IsSubharmonicOn f D) :
    ContinuousOn f D :=
  hf.1

/-- On each admissible circle, the circle integrability in the sub-mean inequality comes from
continuity. -/
theorem IsSubharmonicOn.circleIntegrable {f : ℂ → ℝ} {D : Set ℂ} (hf : IsSubharmonicOn f D)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hball : closedBall a r ⊆ D) :
    CircleIntegrable f a r :=
  (hf.continuousOn.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hr.le

/-- Helper for Exercise 5: if the Poisson pole lies strictly inside a circle, then the Poisson
kernel is continuous along that boundary circle. -/
lemma poissonKernel_continuousOn_sphere_of_mem_ball {c z : ℂ} {r : ℝ}
    (hz : z ∈ ball c r) :
    ContinuousOn (poissonKernel c z) (sphere c r) := by
  -- The numerator and denominator are continuous, and the interior pole keeps the denominator away
  -- from zero on the boundary circle.
  have h_num :
      ContinuousOn (fun x : ℂ ↦ ‖x - c‖ ^ 2 - ‖z - c‖ ^ 2) (sphere c r) := by
    exact ((continuousOn_id.sub continuousOn_const).norm.pow 2).sub continuousOn_const
  have h_den :
      ContinuousOn (fun x : ℂ ↦ ‖(x - c) - (z - c)‖ ^ 2) (sphere c r) := by
    exact (((continuousOn_id.sub continuousOn_const).sub continuousOn_const).norm.pow 2)
  refine ContinuousOn.div h_num h_den ?_
  intro x hx
  have hx_ne : x ≠ z := by
    intro hxz
    have : ‖z - c‖ = r := by simpa [hxz] using hx
    exact (mem_ball_iff_norm.mp hz).ne this
  have hsub_eq : (x - c) - (z - c) = x - z := by ring
  have hdiff : (x - c) - (z - c) ≠ 0 := by
    rw [hsub_eq]
    exact sub_ne_zero.mpr hx_ne
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hdiff)

/-- Subtracting a harmonic function from a subharmonic one preserves subharmonicity on a ball. -/
theorem IsSubharmonicOn.sub_harmonicContOnCl_ball {f g : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hf : IsSubharmonicOn f (ball c R)) (hg : HarmonicContOnCl g (ball c R)) :
    IsSubharmonicOn (f - g) (ball c R) := by
  refine ⟨hf.continuousOn.sub (hg.continuousOn.mono subset_closure), ?_⟩
  intro a ha
  rcases hf.2 ha with ⟨ε, hε_pos, hε⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro r hr_pos hr_lt
  rcases hε hr_pos hr_lt with ⟨hclosed, hmean⟩
  have hg_ball : HarmonicContOnCl g (ball a r) :=
    hg.mono (ball_subset_closedBall.trans hclosed)
  have hg_abs : HarmonicContOnCl g (ball a |r|) := by
    simpa [abs_of_pos hr_pos] using hg_ball
  have hgi : CircleIntegrable g a r := by
    exact (hg_ball.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable hr_pos.le
  refine ⟨hclosed, ?_⟩
  calc
    (f - g) a = f a - g a := by simp
    _ ≤ Real.circleAverage f a r - g a := sub_le_sub_right hmean _
    _ = Real.circleAverage f a r - Real.circleAverage g a r := by
      rw [HarmonicContOnCl.circleAverage_eq hg_abs]
    _ = Real.circleAverage (f - g) a r := by
      rw [← Real.circleAverage_sub (hf.circleIntegrable hr_pos hclosed) hgi]

/-- Exercise 5 (2). The textbook radial mean
`m(r) = (2π)⁻¹ ∫ θ in 0..2 * π, f (Complex.circleMap 0 r θ)` of a subharmonic function on
`|z| < R` is continuous for `0 ≤ r < R`; in mathlib this is `Real.circleAverage f 0 r`. -/
theorem isSubharmonicOn_ball_circleAverage_continuous {f : ℂ → ℝ} {R : ℝ}
    (hf : IsSubharmonicOn f (ball (0 : ℂ) R)) :
    ContinuousOn (fun r : ℝ ↦ Real.circleAverage f 0 r) (Ico (0 : ℝ) R) := by
  -- The circle-average continuity theorem applies once the ambient set is rewritten as the disc.
  refine ContinuousOn.circleAverage ?_ fun r hr ↦ hr.1
  convert hf.continuousOn using 1
  ext z
  simp [Set.mem_Ico, mem_ball, dist_eq_norm]

/-- Helper for Exercise 5: a subharmonic function on a disc remains subharmonic on each smaller
concentric disc. -/
theorem IsSubharmonicOn.mono_ball {f : ℂ → ℝ} {r₁ R : ℝ}
    (hf : IsSubharmonicOn f (ball (0 : ℂ) R)) (hr₁R : r₁ < R) :
    IsSubharmonicOn f (ball (0 : ℂ) r₁) := by
  refine ⟨hf.continuousOn.mono (ball_subset_ball hr₁R.le), ?_⟩
  intro a ha
  rcases hf.2 (ball_subset_ball hr₁R.le ha) with ⟨ε, hε_pos, hε⟩
  have ha_norm : ‖a‖ < r₁ := by
    simpa [mem_ball, dist_eq_norm] using ha
  refine ⟨min ε (r₁ - ‖a‖), lt_min hε_pos (sub_pos.mpr ha_norm), ?_⟩
  intro r hr_pos hr_lt
  rcases hε hr_pos (lt_of_lt_of_le hr_lt (min_le_left _ _)) with ⟨hclosed, hmean⟩
  refine ⟨?_, hmean⟩
  intro z hz
  have hz_norm : ‖z - a‖ ≤ r := by
    simpa [mem_closedBall, dist_eq_norm] using hz
  -- The smaller admissible radius keeps the whole closed ball strictly inside `ball 0 r₁`.
  have hz_lt : ‖z‖ < r₁ := by
    have hr_bound : r < r₁ - ‖a‖ := lt_of_lt_of_le hr_lt (min_le_right _ _)
    calc
      ‖z‖ = ‖(z - a) + a‖ := by
        congr 1
        ring
      _ ≤ ‖z - a‖ + ‖a‖ := norm_add_le _ _
      _ < r₁ := by
        linarith
  simpa [mem_ball, dist_eq_norm] using hz_lt

/-- Helper for Exercise 5: if a subharmonic function achieves the closed-disc maximum at an
interior point, then it is constant on a smaller disc around that point. -/
lemma IsSubharmonicOn.eqOn_ball_of_max_closedBall {u : ℂ → ℝ} {r₁ : ℝ}
    (hu : IsSubharmonicOn u (ball (0 : ℂ) r₁)) {a : ℂ} (ha : a ∈ ball (0 : ℂ) r₁) {M : ℝ}
    (hmax : ∀ z ∈ closedBall (0 : ℂ) r₁, u z ≤ M) (haM : u a = M) :
    ∃ ρ > 0, EqOn u (fun _ ↦ M) (ball a ρ) := by
  rcases hu.2 ha with ⟨ε, hε_pos, hε⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro y hy
  by_cases hya : y = a
  · simpa [hya] using haM
  · let s : ℝ := dist y a
    have hs_pos : 0 < s := by
      dsimp [s]
      exact dist_pos.mpr hya
    have hs_lt : s < ε := by
      simpa [s, mem_ball] using hy
    rcases hε hs_pos hs_lt with ⟨hclosed, hmean⟩
    have hy_closed : y ∈ closedBall a s := by
      simp [s, mem_closedBall]
    have hy_le : u y ≤ M := hmax y (ball_subset_closedBall (hclosed hy_closed))
    have hu_int : CircleIntegrable u a s := hu.circleIntegrable hs_pos hclosed
    have hconst_int : CircleIntegrable (fun _ : ℂ ↦ M) a s := by
      have hconst_cont :
          ContinuousOn (fun _ : ℂ ↦ M) (sphere a s) := continuousOn_const
      exact hconst_cont.circleIntegrable hs_pos.le
    have hmean_le : Real.circleAverage u a s ≤ M := by
      calc
        Real.circleAverage u a s ≤ Real.circleAverage (fun _ : ℂ ↦ M) a s := by
          refine Real.circleAverage_mono hu_int hconst_int ?_
          intro z hz
          have hz' : z ∈ sphere a s := by
            simpa [abs_of_pos hs_pos] using hz
          exact hmax z (ball_subset_closedBall (hclosed (sphere_subset_closedBall hz')))
        _ = M := by
          simpa using (Real.circleAverage_const M a s)
    have hmean_ge : M ≤ Real.circleAverage u a s := by
      simpa [haM] using hmean
    have hmean_eq : Real.circleAverage u a s = M := le_antisymm hmean_le hmean_ge
    by_contra hyM
    have hy_lt : u y < M := lt_of_le_of_ne hy_le hyM
    let ψ : ℝ → ℝ := fun θ ↦ u (circleMap a s θ)
    have hψ_cont : ContinuousOn ψ (Icc 0 (2 * Real.pi)) := by
      exact
        (hu.continuousOn.mono hclosed).comp (t := closedBall a s)
          (continuous_circleMap a s).continuousOn
          (fun θ _ ↦ circleMap_mem_closedBall a hs_pos.le θ)
    have hψ_le : ∀ θ ∈ Ioc 0 (2 * Real.pi), ψ θ ≤ M := by
      intro θ hθ
      exact hmax (circleMap a s θ)
        (ball_subset_closedBall (hclosed (circleMap_mem_closedBall a hs_pos.le θ)))
    have hy_eq_circleMap : circleMap a s (y - a).arg = y := by
      calc
        circleMap a s (y - a).arg
            = a + ‖y - a‖ * Complex.exp ((y - a).arg * Complex.I) := by
                simp [circleMap, s, dist_eq_norm]
        _ = a + (y - a) := by
            rw [Complex.norm_mul_exp_arg_mul_I]
        _ = y := by
            ring
    let θ₀ : ℝ := if 0 ≤ (y - a).arg then (y - a).arg else (y - a).arg + 2 * Real.pi
    have hθ₀_mem : θ₀ ∈ Icc 0 (2 * Real.pi) := by
      by_cases harg : 0 ≤ (y - a).arg
      · simp [θ₀, harg]
        linarith [Complex.arg_le_pi (y - a), Real.pi_pos]
      · have harg_le : (y - a).arg ≤ 0 := le_of_not_ge harg
        simp [θ₀, harg]
        constructor
        · linarith [Complex.neg_pi_lt_arg (y - a), Real.pi_pos]
        · linarith
    have hθ₀_eq : circleMap a s θ₀ = y := by
      by_cases harg : 0 ≤ (y - a).arg
      · simp [θ₀, harg, hy_eq_circleMap]
      · calc
          circleMap a s θ₀ = circleMap a s ((y - a).arg + 2 * Real.pi) := by simp [θ₀, harg]
          _ = circleMap a s (y - a).arg := by
              simpa [add_comm] using periodic_circleMap a s ((y - a).arg)
          _ = y := hy_eq_circleMap
    have hψ_lt : ∃ θ ∈ Icc 0 (2 * Real.pi), ψ θ < M := by
      refine ⟨θ₀, hθ₀_mem, ?_⟩
      simpa [ψ, hθ₀_eq] using hy_lt
    have hlt_int :
        (∫ θ in 0..2 * Real.pi, ψ θ) < ∫ θ in 0..2 * Real.pi, M :=
      intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        (by positivity) hψ_cont continuousOn_const hψ_le hψ_lt
    have hlt_avg :
        Real.circleAverage u a s < M := by
      have hlt_avg_const :
          Real.circleAverage u a s < Real.circleAverage (fun _ : ℂ ↦ M) a s := by
        have htwo_pi_pos : 0 < 2 * Real.pi := by positivity
        rw [Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
        rw [interval_average_eq_div, interval_average_eq_div]
        exact div_lt_div_of_pos_right hlt_int (by simpa using htwo_pi_pos)
      simpa using hlt_avg_const.trans_eq (Real.circleAverage_const M a s)
    exact (lt_irrefl M) (hmean_eq ▸ hlt_avg)

/-- Helper for Exercise 5: a continuous subharmonic function on a closed disc is bounded above by
its boundary values. -/
lemma isSubharmonicOn_nonpos_of_boundary_nonpos_ball {u : ℂ → ℝ} {r₁ : ℝ}
    (hu : IsSubharmonicOn u (ball (0 : ℂ) r₁))
    (hu_cont : ContinuousOn u (closedBall (0 : ℂ) r₁))
    (hboundary : ∀ z ∈ sphere (0 : ℂ) r₁, u z ≤ 0) :
    ∀ z ∈ ball (0 : ℂ) r₁, u z ≤ 0 := by
  by_cases hr₁ : 0 < r₁
  · let K : Set ℂ := closedBall (0 : ℂ) r₁
    have hK_compact : IsCompact K := isCompact_closedBall (0 : ℂ) r₁
    obtain ⟨a, haK, haMax⟩ := hK_compact.exists_isMaxOn (nonempty_closedBall.mpr hr₁.le) hu_cont
    let M : ℝ := u a
    have hmax : ∀ z ∈ K, u z ≤ M := by
      intro z hz
      simpa [M] using haMax hz
    have htarget : M ≤ 0 := by
      by_contra hM_pos
      have hM_pos' : 0 < M := lt_of_not_ge hM_pos
      have ha_ball : a ∈ ball (0 : ℂ) r₁ := by
        by_contra ha_ball
        have ha_sphere : a ∈ sphere (0 : ℂ) r₁ := by
          rw [mem_sphere]
          exact le_antisymm (by simpa [K, mem_closedBall] using haK)
            (not_lt.mp (by simpa [mem_ball] using ha_ball))
        exact (not_lt_of_ge (hboundary a ha_sphere)) hM_pos'
      obtain ⟨ρ, hρ_pos, hρ_eq⟩ := hu.eqOn_ball_of_max_closedBall ha_ball hmax rfl
      let S : Set K := {x | u x = M}
      have hS_closed : IsClosed S := by
        have hu_restrict : Continuous fun x : K ↦ u x := hu_cont.restrict
        simpa [S] using isClosed_eq hu_restrict continuous_const
      have hS_open : IsOpen S := by
        rw [Metric.isOpen_iff]
        intro x hx
        have hx_not_sphere : x.1 ∉ sphere (0 : ℂ) r₁ := by
          intro hx_sphere
          have : u x.1 ≤ 0 := hboundary x.1 hx_sphere
          rw [hx] at this
          exact (not_lt_of_ge this) hM_pos'
        have hx_ball : x.1 ∈ ball (0 : ℂ) r₁ := by
          by_contra hx_ball
          have hx_sphere : x.1 ∈ sphere (0 : ℂ) r₁ := by
            have hx_closed : x.1 ∈ closedBall (0 : ℂ) r₁ := by
              change x.1 ∈ K
              exact x.2
            have hx_dist_le : dist x.1 0 ≤ r₁ := by
              rwa [mem_closedBall] at hx_closed
            rw [mem_sphere]
            exact le_antisymm hx_dist_le
              (not_lt.mp (by simpa [mem_ball] using hx_ball))
          exact hx_not_sphere hx_sphere
        obtain ⟨σ, hσ_pos, hσ_eq⟩ := hu.eqOn_ball_of_max_closedBall hx_ball hmax hx
        refine ⟨σ, hσ_pos, ?_⟩
        intro y hy
        have hy' : y.1 ∈ ball x.1 σ := by simpa using hy
        exact hσ_eq hy'
      have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
      have hS_nonempty : S.Nonempty := ⟨⟨a, haK⟩, rfl⟩
      haveI : PreconnectedSpace K := Subtype.preconnectedSpace isPreconnected_closedBall
      have hS_univ : S = univ := hS_clopen.eq_univ hS_nonempty
      let b : ℂ := circleMap 0 r₁ 0
      have hbK : b ∈ K := by
        exact circleMap_mem_closedBall (0 : ℂ) hr₁.le 0
      have hb_sphere : b ∈ sphere (0 : ℂ) r₁ := by
        exact circleMap_mem_sphere (0 : ℂ) hr₁.le 0
      have hbM : u b = M := by
        have : (⟨b, hbK⟩ : K) ∈ S := by simp [hS_univ]
        exact this
      have : u b ≤ 0 := hboundary b hb_sphere
      rw [hbM] at this
      exact (not_lt_of_ge this) hM_pos'
    intro z hz
    exact (hmax z (ball_subset_closedBall hz)).trans htarget
  · intro z hz
    exfalso
    simp [ball_eq_empty.2 (le_of_not_gt hr₁)] at hz

/-- Exercise 5 (1). If `f` is subharmonic on `|z| < r₁`, extends continuously to `|z| ≤ r₁`, and
`g` is a harmonic solution of the
Dirichlet problem on `|z| ≤ r₁` with boundary data `f`, then `g` majorizes `f` throughout
`|z| < r₁`. -/
theorem harmonic_dirichlet_solution_ge_of_isSubharmonicOn_ball {f g : ℂ → ℝ} {r₁ : ℝ}
    (hf : IsSubharmonicOn f (ball (0 : ℂ) r₁))
    (hf_cont : ContinuousOn f (closedBall (0 : ℂ) r₁))
    (hg : HarmonicContOnCl g (ball (0 : ℂ) r₁)) (hboundary : EqOn g f (sphere (0 : ℂ) r₁))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) r₁) :
    f z ≤ g z := by
  have hsub : IsSubharmonicOn (f - g) (ball (0 : ℂ) r₁) :=
    hf.sub_harmonicContOnCl_ball hg
  have hr₁_pos : 0 < r₁ := pos_of_mem_ball hz
  have hg_cont : ContinuousOn g (closedBall (0 : ℂ) r₁) := by
    simpa [closure_ball (0 : ℂ) hr₁_pos.ne'] using hg.continuousOn
  have hcont : ContinuousOn (f - g) (closedBall (0 : ℂ) r₁) :=
    hf_cont.sub hg_cont
  have hboundary_nonpos : ∀ w ∈ sphere (0 : ℂ) r₁, (f - g) w ≤ 0 := by
    intro w hw
    simp [hboundary hw]
  exact sub_nonpos.mp <|
    isSubharmonicOn_nonpos_of_boundary_nonpos_ball hsub hcont hboundary_nonpos z hz

/-- Cartan section17 0014_Exercise_5: continuous boundary data on a closed disc admit a harmonic
solution of the Dirichlet problem on the corresponding open disc. -/
theorem exists_harmonic_dirichlet_solution_ball {φ : ℂ → ℝ} {r₁ : ℝ}
    (hφ : ContinuousOn φ (closedBall (0 : ℂ) r₁)) (hr₁ : 0 < r₁) :
    ∃ g : ℂ → ℝ, HarmonicContOnCl g (ball (0 : ℂ) r₁) ∧
      EqOn g φ (sphere (0 : ℂ) r₁) := by
  -- Restrict the closed-disc continuity to the boundary circle expected by the Dirichlet API.
  have hφ_sphere : ContinuousOn φ (sphere (0 : ℂ) r₁) := by
    exact hφ.mono sphere_subset_closedBall
  have hφ_absSphere : ContinuousOn φ (sphere (0 : ℂ) |r₁|) := by
    -- The positivity assumption identifies the absolute-value radius with the original radius.
    simpa [abs_of_pos hr₁] using hφ_sphere
  -- Specialize the canonical disc Dirichlet existence theorem at center `0` and radius `r₁`.
  simpa [abs_of_pos hr₁] using
    dirichlet_problem_disc_exists (c := (0 : ℂ)) (R := |r₁|) hφ_absSphere

/-- Helper for Exercise 5: the radial circle average on a subharmonic disc function increases
strictly with the radius. -/
lemma circleAverage_le_circleAverage_of_lt_radius {f : ℂ → ℝ} {r r₁ R : ℝ}
    (hf : IsSubharmonicOn f (ball (0 : ℂ) R))
    (hr_nonneg : 0 ≤ r) (hr_lt : r < r₁) (hr₁_lt : r₁ < R) :
    Real.circleAverage f 0 r ≤ Real.circleAverage f 0 r₁ := by
  have hr₁_pos : 0 < r₁ := lt_of_le_of_lt hr_nonneg hr_lt
  have hf_small : IsSubharmonicOn f (ball (0 : ℂ) r₁) := hf.mono_ball hr₁_lt
  -- Restrict the boundary data to the closed smaller disc so the Dirichlet solver can be used.
  have hf_cont : ContinuousOn f (closedBall (0 : ℂ) r₁) := by
    exact hf.continuousOn.mono (closedBall_subset_ball hr₁_lt)
  obtain ⟨g, hg, hboundary⟩ := exists_harmonic_dirichlet_solution_ball hf_cont hr₁_pos
  have hg_small : HarmonicContOnCl g (ball (0 : ℂ) r) := hg.mono (ball_subset_ball hr_lt.le)
  have hg_abs : HarmonicContOnCl g (ball (0 : ℂ) |r|) := by
    simpa [abs_of_nonneg hr_nonneg] using hg_small
  have hg₁_abs : HarmonicContOnCl g (ball (0 : ℂ) |r₁|) := by
    simpa [abs_of_pos hr₁_pos] using hg
  -- Exercise 5 (1) turns the harmonic Dirichlet solution into a pointwise majorant on the
  -- inner circle.
  have hle_sphere : ∀ z ∈ sphere (0 : ℂ) r, f z ≤ g z := by
    intro z hz
    exact harmonic_dirichlet_solution_ge_of_isSubharmonicOn_ball
      hf_small hf_cont hg hboundary (sphere_subset_ball hr_lt hz)
  have hle_sphere_abs : ∀ z ∈ sphere (0 : ℂ) |r|, f z ≤ g z := by
    simpa [abs_of_nonneg hr_nonneg] using hle_sphere
  have hboundary_abs : EqOn g f (sphere (0 : ℂ) |r₁|) := by
    simpa [abs_of_pos hr₁_pos] using hboundary
  have hf_int : CircleIntegrable f 0 r := by
    have hf_sphere : ContinuousOn f (sphere (0 : ℂ) r) := by
      exact hf.continuousOn.mono (sphere_subset_ball (hr_lt.trans hr₁_lt))
    exact hf_sphere.circleIntegrable hr_nonneg
  have hg_int : CircleIntegrable g 0 r := by
    exact (hg_small.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable hr_nonneg
  calc
    Real.circleAverage f 0 r ≤ Real.circleAverage g 0 r := by
      exact Real.circleAverage_mono hf_int hg_int hle_sphere_abs
    _ = g 0 := by
      rw [HarmonicContOnCl.circleAverage_eq hg_abs]
    _ = Real.circleAverage g 0 r₁ := by
      rw [HarmonicContOnCl.circleAverage_eq hg₁_abs]
    _ = Real.circleAverage f 0 r₁ := by
      apply circleAverage_congr_sphere
      intro z hz
      exact hboundary_abs hz

/-- Exercise 5 (3). The textbook radial mean
`m(r) = (2π)⁻¹ ∫ θ in 0..2 * π, f (Complex.circleMap 0 r θ)` of a subharmonic function on
`|z| < R` is monotone increasing in the broad sense for `0 ≤ r < R`; in mathlib this is
`Real.circleAverage f 0 r`. -/
theorem isSubharmonicOn_ball_circleAverage_monotone {f : ℂ → ℝ} {R : ℝ}
    (hf : IsSubharmonicOn f (ball (0 : ℂ) R)) :
    MonotoneOn (fun r : ℝ ↦ Real.circleAverage f 0 r) (Ico (0 : ℝ) R) := by
  intro r hr s hs hrs
  rcases eq_or_lt_of_le hrs with rfl | hrs_lt
  · rfl
  -- The strict-radius comparison is the only nontrivial step; the equality case is immediate.
  exact circleAverage_le_circleAverage_of_lt_radius hf hr.1 hrs_lt hs.2

/-- Summary for Cartan section17 0014_Exercise_5: if `f` is subharmonic on the disc `|z| < R`,
then every harmonic Dirichlet solution on a smaller disc with boundary data `f` majorizes `f`,
and the radial mean `r ↦ Real.circleAverage f 0 r` is continuous and monotone on `0 ≤ r < R`. -/
theorem subharmonicOn_ball_dirichlet_majorizes_and_circleAverage_regular
    {f : ℂ → ℝ} {R : ℝ} (hf : IsSubharmonicOn f (ball (0 : ℂ) R)) :
    (∀ ⦃r₁ : ℝ⦄, 0 < r₁ → r₁ < R →
      ∀ ⦃g : ℂ → ℝ⦄, HarmonicContOnCl g (ball (0 : ℂ) r₁) →
        EqOn g f (sphere (0 : ℂ) r₁) →
          ∀ ⦃z : ℂ⦄, z ∈ ball (0 : ℂ) r₁ → f z ≤ g z) ∧
      ContinuousOn (fun r : ℝ ↦ Real.circleAverage f 0 r) (Ico (0 : ℝ) R) ∧
      MonotoneOn (fun r : ℝ ↦ Real.circleAverage f 0 r) (Ico (0 : ℝ) R) := by
  refine ⟨?_, isSubharmonicOn_ball_circleAverage_continuous hf,
    isSubharmonicOn_ball_circleAverage_monotone hf⟩
  intro r₁ hr₁_pos hr₁R g hg hboundary z hz
  have hf_small : IsSubharmonicOn f (ball (0 : ℂ) r₁) := hf.mono_ball hr₁R
  -- Restrict continuity from the larger disc to the closed smaller disc used by the Dirichlet data.
  have hf_cont : ContinuousOn f (closedBall (0 : ℂ) r₁) := by
    exact hf.continuousOn.mono (closedBall_subset_ball hr₁R)
  exact harmonic_dirichlet_solution_ge_of_isSubharmonicOn_ball
    hf_small hf_cont hg hboundary hz
