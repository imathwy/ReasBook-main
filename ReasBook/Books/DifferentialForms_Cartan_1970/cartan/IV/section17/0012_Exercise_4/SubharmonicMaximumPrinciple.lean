import Mathlib
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import DifferentialForms_Cartan_1970.cartan.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22»
import DifferentialForms_Cartan_1970.cartan.IV.section16.«0002_Theorem_IV_4_extra_2»
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0012_Exercise_4».SubharmonicCore

open Filter InnerProductSpace Laplacian Metric Real Set Topology
open scoped BigOperators InnerProductSpace
/-- Helper for Exercise 4: the pointwise maximum of two subharmonic functions is subharmonic. -/
lemma isSubharmonicOn_max {D : Set ℂ} {f g : ℂ → ℝ} (hf : IsSubharmonicOn f D)
    (hg : IsSubharmonicOn g D) :
    IsSubharmonicOn (fun z ↦ f z ⊔ g z) D := by
  constructor
  · -- Continuity is preserved under the lattice operation `sup`.
    exact hf.continuousOn.sup hg.continuousOn
  · intro a ha
    rcases hf.2 ha with ⟨εf, hεf_pos, hεf⟩
    rcases hg.2 ha with ⟨εg, hεg_pos, hεg⟩
    refine ⟨min εf εg, lt_min hεf_pos hεg_pos, ?_⟩
    intro r hr_pos hr_lt
    have hrf : r < εf := lt_of_lt_of_le hr_lt (min_le_left _ _)
    have hrg : r < εg := lt_of_lt_of_le hr_lt (min_le_right _ _)
    rcases hεf hr_pos hrf with ⟨hballf, hmeanf⟩
    rcases hεg hr_pos hrg with ⟨hballg, hmeang⟩
    refine ⟨hballf, ?_⟩
    have hsup_int : CircleIntegrable (fun z ↦ f z ⊔ g z) a r := by
      exact ((hf.continuousOn.sup hg.continuousOn).mono
        (sphere_subset_closedBall.trans hballf)).circleIntegrable hr_pos.le
    have hcircle_f :
        Real.circleAverage f a r ≤ Real.circleAverage (fun z ↦ f z ⊔ g z) a r := by
      apply Real.circleAverage_mono (hf.circleIntegrable hr_pos hballf) hsup_int
      intro z hz
      exact le_sup_left
    have hcircle_g :
        Real.circleAverage g a r ≤ Real.circleAverage (fun z ↦ f z ⊔ g z) a r := by
      apply Real.circleAverage_mono (hg.circleIntegrable hr_pos hballg) hsup_int
      intro z hz
      exact le_sup_right
    -- Each branch at the center is controlled by the same average of the pointwise supremum.
    exact sup_le (hmeanf.trans hcircle_f) (hmeang.trans hcircle_g)

/-- Helper for Exercise 4: restricting a subharmonic function to an open subset preserves
subharmonicity. -/
theorem IsSubharmonicOn.mono {f : ℂ → ℝ} {U V : Set ℂ} (hf : IsSubharmonicOn f V)
    (hU_open : IsOpen U) (hUV : U ⊆ V) :
    IsSubharmonicOn f U := by
  refine ⟨hf.continuousOn.mono hUV, ?_⟩
  intro a ha
  rcases hf.2 (hUV ha) with ⟨εV, hεV_pos, hεV⟩
  rcases Metric.isOpen_iff.mp hU_open a ha with ⟨εU, hεU_pos, hεU⟩
  refine ⟨min εV εU, lt_min hεV_pos hεU_pos, ?_⟩
  intro r hr_pos hr_lt
  have hrV : r < εV := lt_of_lt_of_le hr_lt (min_le_left _ _)
  have hrU : r < εU := lt_of_lt_of_le hr_lt (min_le_right _ _)
  rcases hεV hr_pos hrV with ⟨_, hmean⟩
  refine ⟨(Metric.closedBall_subset_ball hrU).trans hεU, hmean⟩

/-- Helper for Exercise 4: if a subharmonic function attains the closed-disc maximum at an
interior point, then it is constant on a smaller ball around that point. -/
lemma IsSubharmonicOn.eqOn_ball_of_closedBall_max {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : IsSubharmonicOn u (Metric.ball c R)) {a : ℂ} (ha : a ∈ Metric.ball c R) {M : ℝ}
    (hmax : ∀ z ∈ Metric.closedBall c R, u z ≤ M) (haM : u a = M) :
    ∃ ρ > 0, Set.EqOn u (fun _ ↦ M) (Metric.ball a ρ) := by
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
      simpa [s, Metric.mem_ball] using hy
    rcases hε hs_pos hs_lt with ⟨hclosed, hmean⟩
    have hy_closed : y ∈ Metric.closedBall a s := by
      simp [s, Metric.mem_closedBall]
    have hy_le : u y ≤ M := by
      exact hmax y (Metric.ball_subset_closedBall (hclosed hy_closed))
    have hu_int : CircleIntegrable u a s := hu.circleIntegrable hs_pos hclosed
    have hconst_int : CircleIntegrable (fun _ : ℂ ↦ M) a s := by
      exact continuousOn_const.circleIntegrable hs_pos.le
    have hmean_le : Real.circleAverage u a s ≤ M := by
      calc
        Real.circleAverage u a s ≤ Real.circleAverage (fun _ : ℂ ↦ M) a s := by
          refine Real.circleAverage_mono hu_int hconst_int ?_
          intro z hz
          have hz' : z ∈ Metric.sphere a s := by
            simpa [abs_of_pos hs_pos] using hz
          exact hmax z (Metric.ball_subset_closedBall (hclosed (Metric.sphere_subset_closedBall hz')))
        _ = M := by
          simpa using (Real.circleAverage_const M a s)
    have hmean_ge : M ≤ Real.circleAverage u a s := by
      simpa [haM] using hmean
    have hmean_eq : Real.circleAverage u a s = M := le_antisymm hmean_le hmean_ge
    by_contra hyM
    have hy_lt : u y < M := lt_of_le_of_ne hy_le hyM
    let ψ : ℝ → ℝ := fun θ ↦ u (circleMap a s θ)
    have hψ_cont : ContinuousOn ψ (Set.Icc 0 (2 * Real.pi)) := by
      exact
        (hu.continuousOn.mono hclosed).comp (t := Metric.closedBall a s)
          (continuous_circleMap a s).continuousOn
          (fun θ _ ↦ circleMap_mem_closedBall a hs_pos.le θ)
    have hψ_le : ∀ θ ∈ Set.Ioc 0 (2 * Real.pi), ψ θ ≤ M := by
      intro θ hθ
      exact hmax (circleMap a s θ)
        (Metric.ball_subset_closedBall (hclosed (circleMap_mem_closedBall a hs_pos.le θ)))
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
    have hθ₀_mem : θ₀ ∈ Set.Icc 0 (2 * Real.pi) := by
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
    have hψ_lt : ∃ θ ∈ Set.Icc 0 (2 * Real.pi), ψ θ < M := by
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

/-- Helper for Exercise 4: a continuous subharmonic function on a closed disc is bounded above by
its nonpositive boundary values. -/
lemma isSubharmonicOn_nonpos_of_boundary_nonpos_closedBall {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : IsSubharmonicOn u (Metric.ball c R))
    (hu_cont : ContinuousOn u (Metric.closedBall c R))
    (hboundary : ∀ z ∈ Metric.sphere c R, u z ≤ 0) :
    ∀ z ∈ Metric.ball c R, u z ≤ 0 := by
  by_cases hR : 0 < R
  · let K : Set ℂ := Metric.closedBall c R
    have hK_compact : IsCompact K := isCompact_closedBall c R
    obtain ⟨a, haK, haMax⟩ := hK_compact.exists_isMaxOn
      (Metric.nonempty_closedBall.mpr hR.le) hu_cont
    let M : ℝ := u a
    have hmax : ∀ z ∈ K, u z ≤ M := by
      intro z hz
      simpa [M] using haMax hz
    have htarget : M ≤ 0 := by
      by_contra hM_pos
      have hM_pos' : 0 < M := lt_of_not_ge hM_pos
      have ha_ball : a ∈ Metric.ball c R := by
        by_contra ha_ball
        have ha_sphere : a ∈ Metric.sphere c R := by
          rw [Metric.mem_sphere]
          exact le_antisymm (by simpa [K, Metric.mem_closedBall] using haK)
            (not_lt.mp (by simpa [Metric.mem_ball] using ha_ball))
        exact (not_lt_of_ge (hboundary a ha_sphere)) hM_pos'
      obtain ⟨ρ, hρ_pos, hρ_eq⟩ := hu.eqOn_ball_of_closedBall_max ha_ball hmax rfl
      let S : Set K := {x | u x = M}
      have hS_closed : IsClosed S := by
        have hu_restrict : Continuous fun x : K ↦ u x := hu_cont.restrict
        simpa [S] using isClosed_eq hu_restrict continuous_const
      have hS_open : IsOpen S := by
        rw [Metric.isOpen_iff]
        intro x hx
        have hx_not_sphere : x.1 ∉ Metric.sphere c R := by
          intro hx_sphere
          have : u x.1 ≤ 0 := hboundary x.1 hx_sphere
          rw [hx] at this
          exact (not_lt_of_ge this) hM_pos'
        have hx_ball : x.1 ∈ Metric.ball c R := by
          by_contra hx_ball
          have hx_sphere : x.1 ∈ Metric.sphere c R := by
            have hx_closed : x.1 ∈ Metric.closedBall c R := by
              change x.1 ∈ K
              exact x.2
            have hx_dist_le : dist x.1 c ≤ R := by
              rwa [Metric.mem_closedBall] at hx_closed
            rw [Metric.mem_sphere]
            exact le_antisymm hx_dist_le
              (not_lt.mp (by simpa [Metric.mem_ball] using hx_ball))
          exact hx_not_sphere hx_sphere
        obtain ⟨σ, hσ_pos, hσ_eq⟩ := hu.eqOn_ball_of_closedBall_max hx_ball hmax hx
        refine ⟨σ, hσ_pos, ?_⟩
        intro y hy
        have hy' : y.1 ∈ Metric.ball x.1 σ := by simpa using hy
        exact hσ_eq hy'
      have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
      have hS_nonempty : S.Nonempty := ⟨⟨a, haK⟩, rfl⟩
      haveI : PreconnectedSpace K := Subtype.preconnectedSpace isPreconnected_closedBall
      have hS_univ : S = Set.univ := hS_clopen.eq_univ hS_nonempty
      let b : ℂ := circleMap c R 0
      have hbK : b ∈ K := by
        exact circleMap_mem_closedBall c hR.le 0
      have hb_sphere : b ∈ Metric.sphere c R := by
        exact circleMap_mem_sphere c hR.le 0
      have hbM : u b = M := by
        have : (⟨b, hbK⟩ : K) ∈ S := by simp [hS_univ]
        exact this
      have : u b ≤ 0 := hboundary b hb_sphere
      rw [hbM] at this
      exact (not_lt_of_ge this) hM_pos'
    intro z hz
    exact (hmax z (Metric.ball_subset_closedBall hz)).trans htarget
  · intro z hz
    exfalso
    simp [Metric.ball_eq_empty.2 (le_of_not_gt hR)] at hz

/-- Helper for Exercise 4: on a ball, subtracting a harmonic function from a subharmonic one
preserves subharmonicity. -/
theorem IsSubharmonicOn.sub_harmonicContOnCl {f g : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hf : IsSubharmonicOn f (Metric.ball c R)) (hg : HarmonicContOnCl g (Metric.ball c R)) :
    IsSubharmonicOn (fun z ↦ f z - g z) (Metric.ball c R) := by
  refine ⟨hf.continuousOn.sub (hg.continuousOn.mono subset_closure), ?_⟩
  intro a ha
  rcases hf.2 ha with ⟨ε, hε_pos, hε⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro r hr_pos hr_lt
  rcases hε hr_pos hr_lt with ⟨hclosed, hmean⟩
  have hg_ball : HarmonicContOnCl g (Metric.ball a r) :=
    hg.mono (ball_subset_closedBall.trans hclosed)
  have hg_abs : HarmonicContOnCl g (Metric.ball a |r|) := by
    simpa [abs_of_pos hr_pos] using hg_ball
  have hg_circle : CircleIntegrable g a r := by
    -- The harmonic comparison function is continuous on the boundary circle of the smaller ball.
    exact (hg_ball.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable hr_pos.le
  refine ⟨hclosed, ?_⟩
  -- Rewrite the mean inequality for `f - g` via the harmonic mean-value identity for `g`.
  calc
    (f a - g a) = f a - g a := by rfl
    _ ≤ Real.circleAverage f a r - g a := sub_le_sub_right hmean _
    _ = Real.circleAverage f a r - Real.circleAverage g a r := by
      rw [← HarmonicContOnCl.circleAverage_eq hg_abs]
    _ = Real.circleAverage (fun z ↦ f z - g z) a r := by
      rw [← Real.circleAverage_fun_sub (hf.circleIntegrable hr_pos hclosed) hg_circle]

/-- Helper for Exercise 4: on a disc, a harmonic majorant with larger boundary values dominates a
subharmonic function throughout the interior. -/
theorem isSubharmonicOn_le_harmonicContOnCl_of_boundary_le_ball {u g : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : IsSubharmonicOn u (Metric.ball c R))
    (hu_cont : ContinuousOn u (Metric.closedBall c R))
    (hg : HarmonicContOnCl g (Metric.ball c R))
    (hboundary : ∀ z ∈ Metric.sphere c R, u z ≤ g z) :
    ∀ z ∈ Metric.ball c R, u z ≤ g z := by
  intro z hz
  have hR_pos : 0 < R := pos_of_mem_ball hz
  have hsub : IsSubharmonicOn (fun w ↦ u w - g w) (Metric.ball c R) :=
    hu.sub_harmonicContOnCl hg
  have hg_cont : ContinuousOn g (Metric.closedBall c R) := by
    simpa [closure_ball c hR_pos.ne'] using hg.continuousOn
  have hsub_cont : ContinuousOn (fun w ↦ u w - g w) (Metric.closedBall c R) :=
    hu_cont.sub hg_cont
  have hboundary_nonpos :
      ∀ w ∈ Metric.sphere c R, (u w - g w) ≤ 0 := by
    intro w hw
    exact sub_nonpos.mpr (hboundary w hw)
  exact sub_nonpos.mp <|
    isSubharmonicOn_nonpos_of_boundary_nonpos_closedBall hsub hsub_cont hboundary_nonpos z hz

/-- Helper for Exercise 4: uniform convergence on a fixed closed ball implies convergence of the
corresponding circle averages. -/
lemma tendsto_circleAverage_of_tendstoUniformlyOn_closedBall {u : ℕ → ℂ → ℝ} {f : ℂ → ℝ}
    {a : ℂ} {r : ℝ} (hr : 0 ≤ r) (hu_cont : ∀ n, ContinuousOn (u n) (Metric.closedBall a r))
    (htu : TendstoUniformlyOn u f atTop (Metric.closedBall a r)) :
    Tendsto (fun n ↦ Real.circleAverage (u n) a r) atTop (𝓝 (Real.circleAverage f a r)) := by
  let U : ℕ → ℝ → ℝ := fun n θ ↦ u n (circleMap a r θ)
  let F : ℝ → ℝ := fun θ ↦ f (circleMap a r θ)
  have hU_cont : ∀ᶠ n in atTop, ContinuousOn (U n) (Set.uIcc 0 (2 * Real.pi)) := by
    -- Continuity on the closed ball transfers to continuity of the circle parametrization.
    refine Filter.Eventually.of_forall ?_
    intro n
    dsimp [U]
    exact (hu_cont n).comp (t := Metric.closedBall a r) (continuous_circleMap a r).continuousOn
      (fun θ _ ↦ circleMap_mem_closedBall a hr θ)
  have hU_tendsto : TendstoUniformlyOn U F atTop (Set.uIcc 0 (2 * Real.pi)) := by
    -- Restrict the composed uniform convergence to the compact parameter interval.
    exact (htu.comp (circleMap a r)).mono fun θ _ ↦ circleMap_mem_closedBall a hr θ
  have hInt :
      Tendsto (fun n ↦ ∫ θ in 0..2 * Real.pi, U n θ) atTop (𝓝 (∫ θ in 0..2 * Real.pi, F θ)) := by
    -- The interval-integral convergence theorem handles the fixed compact parameter interval.
    exact TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn hU_cont hU_tendsto
  have hAvg :
      Tendsto
        (fun n ↦ ((2 * Real.pi) - 0)⁻¹ * ∫ θ in 0..2 * Real.pi, U n θ)
        atTop
        (𝓝 (((2 * Real.pi) - 0)⁻¹ * ∫ θ in 0..2 * Real.pi, F θ)) := by
    -- Multiplying by the constant normalization factor turns integral convergence into average
    -- convergence.
    simpa using tendsto_const_nhds.mul hInt
  -- Rewrite the circle averages as interval averages, then as scaled interval integrals.
  simpa [U, F, Real.circleAverage_eq_intervalAverage, interval_average_eq_div, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hAvg
