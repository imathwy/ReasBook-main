import Mathlib
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import DifferentialForms_Cartan_1970.cartan.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0035_Theorem_II_1_extra_22»
import DifferentialForms_Cartan_1970.cartan.IV.section16.«0002_Theorem_IV_4_extra_2»
import DifferentialForms_Cartan_1970.cartan.IV.section17.«0012_Exercise_4».Index

-- Declarations for this item will be appended below by the statement pipeline.

open Filter InnerProductSpace Laplacian Metric Real Set Topology
open scoped BigOperators InnerProductSpace

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the statement surface was chosen by local inspection of mathlib's `Real.circleAverage`,
-- `CircleIntegrable`, `TendstoUniformlyOn`, and Laplacian APIs, together with nearby section-IV.5
-- precedent.


/-- Exercise 4 (1). Helper for Cartan section17 0012_Exercise_4: if `f` is holomorphic on the open
set `D`, then `z ↦ ‖f z‖^p`, written with
`Real.rpow`, is subharmonic on `D` for every real exponent `p ≥ 0`. -/
theorem differentiableOn_norm_rpow_isSubharmonicOn {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) {p : ℝ} (hp : 0 ≤ p) :
    IsSubharmonicOn (fun z ↦ Real.rpow ‖f z‖ p) D := by
  by_cases hp0 : p = 0
  · -- The exponent-zero branch is the constant-one function.
    simpa [hp0, Real.rpow_zero] using isSubharmonicOn_const hD 1
  · have hp_pos : 0 < p := lt_of_le_of_ne hp <| by simpa [eq_comm] using hp0
    refine ⟨?_, ?_⟩
    · -- Continuity follows from continuity of `f`, then `‖f‖`, then `Real.rpow`.
      simpa using
        (hf.continuousOn.norm.rpow_const (p := p) fun z hz ↦ Or.inr hp :
          ContinuousOn (fun z ↦ Real.rpow ‖f z‖ p) D)
    · intro a ha
      by_cases hfa : f a = 0
      · rcases Metric.isOpen_iff.mp hD a ha with ⟨ε, hε_pos, hε⟩
        refine ⟨ε, hε_pos, ?_⟩
        intro r hr_pos hr_lt
        refine ⟨(Metric.closedBall_subset_ball hr_lt).trans hε, ?_⟩
        -- The center value is zero, while the whole circle average is nonnegative.
        have hcenter : (fun z ↦ Real.rpow ‖f z‖ p) a = 0 := by
          simp [hfa, Real.zero_rpow hp0]
        rw [hcenter]
        exact Real.circleAverage_nonneg_of_nonneg fun z hz ↦
          Real.rpow_nonneg (norm_nonneg _) _
      · obtain ⟨R, hR_pos, hRsubset, hRzero⟩ :=
          exists_zero_free_closedBall_of_mem_open_of_ne_zero hD hf.continuousOn ha hfa
        refine ⟨R, hR_pos, ?_⟩
        intro r hr_pos hr_lt
        have hclosed : Metric.closedBall a r ⊆ D :=
          (Metric.closedBall_subset_closedBall (le_of_lt hr_lt)).trans hRsubset
        have hzero : ∀ z ∈ Metric.closedBall a r, f z ≠ 0 := fun z hz ↦
          hRzero z ((Metric.closedBall_subset_closedBall (le_of_lt hr_lt)) hz)
        have hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall a r) :=
          (hf.analyticOnNhd hD).mono hclosed
        refine ⟨hclosed, ?_⟩
        -- Route correction: once the disc is fixed inside `D` and zero-free, the source proof
        -- closes this branch by Jensen on `log ‖f‖`.
        exact circleAverage_norm_rpow_ge_center_of_analytic_nonvanishing hp hr_pos hanalytic hzero

/-- Exercise 4 (2). On an open set `D`, a finite nonnegative linear combination of subharmonic
functions on `D` is again subharmonic on `D`. -/
theorem isSubharmonicOn_finset_nonneg_sum {ι : Type} {s : Finset ι} {a : ι → ℝ}
    {f : ι → ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D) (hf : ∀ i ∈ s, IsSubharmonicOn (f i) D)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    IsSubharmonicOn (fun z ↦ s.sum fun i ↦ a i * f i z) D := by
  classical
  -- Route correction: the original empty-set statement was false, so the induction now starts from
  -- the constant-zero function on the ambient open set `D`.
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is the zero function.
      simpa using isSubharmonicOn_const hD 0
  | @insert i s hi ih =>
      have hfi : IsSubharmonicOn (f i) D := hf i (by simp)
      have hai : 0 ≤ a i := ha i (by simp)
      have hfs : ∀ j ∈ s, IsSubharmonicOn (f j) D := by
        intro j hj
        exact hf j (by simp [hj])
      have has : ∀ j ∈ s, 0 ≤ a j := by
        intro j hj
        exact ha j (by simp [hj])
      have hsum : IsSubharmonicOn (fun z ↦ s.sum fun j ↦ a j * f j z) D := ih hfs has
      have hscaled : IsSubharmonicOn (fun z ↦ a i * f i z) D :=
        hfi.smul_nonneg hai
      -- Split the inserted sum into the new term plus the previous partial sum.
      convert hscaled.add hsum using 1
      ext z
      simp [Finset.sum_insert, hi]


/-- Exercise 4 (3). The pointwise supremum of a finite nonempty family of subharmonic functions on
`D` is subharmonic on `D`. -/
theorem isSubharmonicOn_finset_sup {ι : Type} {s : Finset ι} (hs : s.Nonempty) {f : ι → ℂ → ℝ}
    {D : Set ℂ} (hf : ∀ i ∈ s, IsSubharmonicOn (f i) D) :
    IsSubharmonicOn (fun z ↦ s.sup' hs fun i ↦ f i z) D := by
  classical
  -- Induct over the nonempty finite set, using the binary `max` closure lemma at each step.
  revert hf
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
      intro hf
      simpa using hf i (by simp)
  | cons i s hi hs ih =>
      intro hf
      have hfi : IsSubharmonicOn (f i) D := hf i (by simp)
      have hfs : IsSubharmonicOn (fun z ↦ s.sup' hs fun j ↦ f j z) D := by
        apply ih
        intro j hj
        exact hf j (by simp [hj])
      -- Rewrite the new finite supremum as a binary `sup` and reuse the helper.
      convert isSubharmonicOn_max hfi hfs using 1
      ext z
      simpa [Finset.cons_eq_insert] using
        (Finset.sup'_insert (s := s) (H := hs) (b := i) (f := fun x ↦ f x z))


/-- Exercise 4 (4). A compact-open uniform limit of subharmonic functions is subharmonic. -/
theorem isSubharmonicOn_of_tendstoUniformlyOn_compacts {D : Set ℂ} {u : ℕ → ℂ → ℝ}
    {f : ℂ → ℝ} (hu : ∀ n, IsSubharmonicOn (u n) D)
    (hlimit : ∀ ⦃K : Set ℂ⦄, IsCompact K → K ⊆ D → TendstoUniformlyOn u f atTop K) :
    IsSubharmonicOn f D := by
  have hD_open : IsOpen D := (hu 0).isOpen
  have hloc : TendstoLocallyUniformlyOn u f atTop D := by
    -- Compact-open uniform convergence is exactly local uniform convergence on the open set `D`.
    refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hD_open).2 ?_
    intro K hKD hK
    exact hlimit hK hKD
  have hf_cont : ContinuousOn f D := by
    -- The locally uniform limit of continuous functions remains continuous on `D`.
    exact hloc.continuousOn <| Filter.Frequently.of_forall fun n ↦ (hu n).continuousOn
  refine ⟨hf_cont, ?_⟩
  intro a ha
  rcases Metric.isOpen_iff.mp hD_open a ha with ⟨ρ, hρ_pos, hρball⟩
  refine ⟨ρ, hρ_pos, ?_⟩
  intro r hr_pos hr_lt
  have hr_nonneg : 0 ≤ r := hr_pos.le
  have hclosed : Metric.closedBall a r ⊆ D :=
    (Metric.closedBall_subset_ball hr_lt).trans hρball
  have hclosed_compact : IsCompact (Metric.closedBall a r) := isCompact_closedBall a r
  have htu_closed :
      TendstoUniformlyOn u f atTop (Metric.closedBall a r) := hlimit hclosed_compact hclosed
  have hcircle_tendsto :
      Tendsto (fun n ↦ Real.circleAverage (u n) a r) atTop (𝓝 (Real.circleAverage f a r)) := by
    -- The boundary averages converge once the functions converge uniformly on the closed ball.
    exact tendsto_circleAverage_of_tendstoUniformlyOn_closedBall hr_nonneg
      (fun n ↦ (hu n).continuousOn.mono hclosed) htu_closed
  have hcenter_tendsto : Tendsto (fun n ↦ u n a) atTop (𝓝 (f a)) := hloc.tendsto_at ha
  have hsubmean : ∀ n, u n a ≤ Real.circleAverage (u n) a r := by
    intro n
    have hun_ball : IsSubharmonicOn (u n) (Metric.ball a r) := by
      -- Restrict to the fixed ball so that the radius `r` is admissible for every approximant.
      refine (hu n).mono Metric.isOpen_ball ?_
      intro z hz
      exact hclosed (Metric.ball_subset_closedBall hz)
    have hun_cont : ContinuousOn (u n) (Metric.closedBall a r) :=
      (hu n).continuousOn.mono hclosed
    obtain ⟨g, hg, hboundary⟩ :=
      dirichlet_problem_disc_exists <|
        (hu n).continuousOn.mono (Metric.sphere_subset_closedBall.trans hclosed)
    have hmajor :
        u n a ≤ g a := by
      -- Compare `u n` with the harmonic Dirichlet solution having the same boundary values.
      exact isSubharmonicOn_le_harmonicContOnCl_of_boundary_le_ball hun_ball hun_cont hg
        (fun z hz ↦ le_of_eq (hboundary hz).symm) a (by simpa [Metric.mem_ball] using hr_pos)
    have hg_abs : HarmonicContOnCl g (Metric.ball a |r|) := by
      simpa [abs_of_pos hr_pos] using hg
    have hboundary_abs : Set.EqOn g (u n) (Metric.sphere a |r|) := by
      simpa [abs_of_pos hr_pos] using hboundary
    calc
      u n a ≤ g a := hmajor
      _ = Real.circleAverage g a r := by
        rw [HarmonicContOnCl.circleAverage_eq hg_abs]
      _ = Real.circleAverage (u n) a r := by
        exact circleAverage_congr_sphere hboundary_abs
  refine ⟨hclosed, ?_⟩
  -- Order is closed in `ℝ`, so the fixed-radius inequalities pass to the limit.
  exact le_of_tendsto_of_tendsto' hcenter_tendsto hcircle_tendsto hsubmean

/-- Exercise 4 (5). A subharmonic function with a relative maximum at an interior point is locally
constant near that point. -/
theorem isSubharmonicOn_eqOn_ball_of_isLocalMaxOn {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : IsSubharmonicOn f D) {a : ℂ} (ha : a ∈ D) (hmax : IsLocalMaxOn f D a) :
    ∃ r > 0, Set.EqOn f (fun _ ↦ f a) (Metric.ball a r) := by
  have hupper : {z | f z ≤ f a} ∈ 𝓝[D] a := hmax
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hupper with ⟨s, hs_nhds, hs_subset⟩
  have hsD_nhds : s ∩ D ∈ 𝓝 a := Filter.inter_mem hs_nhds (hD.mem_nhds ha)
  rcases Metric.mem_nhds_iff.mp hsD_nhds with ⟨R, hR_pos, hRsubset⟩
  let ρ : ℝ := R / 2
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ_lt : ρ < R := by
    dsimp [ρ]
    linarith
  have hclosed_subset : Metric.closedBall a ρ ⊆ s ∩ D :=
    (Metric.closedBall_subset_ball hρ_lt).trans hRsubset
  have hf_ball : IsSubharmonicOn f (Metric.ball a ρ) := by
    -- Shrink to a ball where both the domain and the local upper bound are available.
    refine hf.mono Metric.isOpen_ball ?_
    intro z hz
    exact (hclosed_subset (Metric.ball_subset_closedBall hz)).2
  have hmax_closed : ∀ z ∈ Metric.closedBall a ρ, f z ≤ f a := by
    intro z hz
    exact hs_subset (hclosed_subset hz)
  -- The closed-ball maximum lemma turns the local upper bound into local constancy.
  exact hf_ball.eqOn_ball_of_closedBall_max
    (by simpa [Metric.mem_ball] using hρ_pos) hmax_closed rfl

/-- Exercise 4 (6). A continuous subharmonic function on a bounded connected open set is bounded
above by any upper bound for its boundary values. -/
theorem isSubharmonicOn_le_of_le_frontier {D : Set ℂ} (hD_open : IsOpen D)
    (hD_connected : IsConnected D) (hD_bounded : Bornology.IsBounded D) {f : ℂ → ℝ}
    (hf_cont : ContinuousOn f (closure D)) (hf_subharmonic : IsSubharmonicOn f D) {M : ℝ}
    (hM : ∀ z ∈ frontier D, f z ≤ M) :
    ∀ z ∈ D, f z ≤ M := by
  intro z hz
  by_contra hzM
  have hz_gt : M < f z := lt_of_not_ge hzM
  let K : Set ℂ := closure D
  have hK_compact : IsCompact K := by
    simpa [K] using hD_bounded.isCompact_closure
  obtain ⟨a, haK, haMax⟩ := hK_compact.exists_isMaxOn ⟨z, subset_closure hz⟩ hf_cont
  let M₀ : ℝ := f a
  have hM₀_ge : ∀ w ∈ D, f w ≤ M₀ := by
    intro w hw
    simpa [M₀] using haMax (subset_closure hw)
  have hM₀_gt : M < M₀ := by
    exact lt_of_lt_of_le hz_gt (hM₀_ge z hz)
  have ha_union : a ∈ D ∪ frontier D := by
    simpa [K, closure_eq_self_union_frontier] using haK
  rcases ha_union with haD | haFrontier
  · let S : Set D := {x | f x = M₀}
    have hS_closed : IsClosed S := by
      have hf_restrict : Continuous fun x : D ↦ f x := hf_subharmonic.continuousOn.restrict
      simpa [S] using isClosed_eq hf_restrict continuous_const
    have hS_open : IsOpen S := by
      rw [Metric.isOpen_iff]
      intro x hx
      have hmax_x : IsMaxOn f D x := by
        intro y hy
        rw [hx]
        exact hM₀_ge y hy
      obtain ⟨r, hr_pos, hr_eq⟩ :=
        isSubharmonicOn_eqOn_ball_of_isLocalMaxOn hD_open hf_subharmonic x.2 hmax_x.localize
      refine ⟨r, hr_pos, ?_⟩
      intro y hy
      have hy' : y.1 ∈ Metric.ball x.1 r := by
        simpa using hy
      have hy_eq : f y.1 = M₀ := by
        exact (hr_eq hy').trans hx
      simpa [S] using hy_eq
    have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
    letI : PreconnectedSpace D := Subtype.preconnectedSpace hD_connected.isPreconnected
    have hS_univ : S = Set.univ := hS_clopen.eq_univ ⟨⟨a, haD⟩, rfl⟩
    have hEqD : Set.EqOn f (fun _ ↦ M₀) D := by
      intro w hw
      have : (⟨w, hw⟩ : D) ∈ S := by
        simp [hS_univ]
      simpa [S] using this
    have hEqClosure : Set.EqOn f (fun _ ↦ M₀) (closure D) :=
      Set.EqOn.of_subset_closure hEqD hf_cont continuousOn_const subset_closure Subset.rfl
    have hD_ne_univ : D ≠ Set.univ := by
      intro hDu
      exact NormedSpace.unbounded_univ (𝕜 := ℂ) (E := ℂ) (hDu ▸ hD_bounded)
    obtain ⟨b, hb⟩ : (frontier D).Nonempty := by
      exact (nonempty_frontier_iff).2 ⟨⟨z, hz⟩, hD_ne_univ⟩
    have hb_eq : f b = M₀ := hEqClosure (frontier_subset_closure hb)
    exact (not_lt_of_ge (hM b hb)) (hb_eq ▸ hM₀_gt)
  · exact (not_lt_of_ge (hM a haFrontier)) hM₀_gt

/-- Exercise 4 (7). If a continuous subharmonic function on a bounded connected open set attains
its boundary supremum at an interior point, then it is constant on the domain. -/
theorem isSubharmonicOn_eq_constant_of_eq_frontier_sup {D : Set ℂ} (hD_open : IsOpen D)
    (hD_connected : IsConnected D) (hD_bounded : Bornology.IsBounded D) {f : ℂ → ℝ}
    (hf_cont : ContinuousOn f (closure D)) (hf_subharmonic : IsSubharmonicOn f D) {M : ℝ}
    (hM : ∀ z ∈ frontier D, f z ≤ M) {a : ℂ} (ha : a ∈ D) (haM : f a = M) :
    Set.EqOn f (fun _ ↦ M) D := by
  have hle : ∀ z ∈ D, f z ≤ M :=
    isSubharmonicOn_le_of_le_frontier hD_open hD_connected hD_bounded hf_cont hf_subharmonic hM
  let S : Set D := {x | f x = M}
  have hS_closed : IsClosed S := by
    have hf_restrict : Continuous fun x : D ↦ f x := hf_subharmonic.continuousOn.restrict
    simpa [S] using isClosed_eq hf_restrict continuous_const
  have hS_open : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro x hx
    have hmax_x : IsMaxOn f D x := by
      intro y hy
      rw [hx]
      exact hle y hy
    obtain ⟨r, hr_pos, hr_eq⟩ :=
      isSubharmonicOn_eqOn_ball_of_isLocalMaxOn hD_open hf_subharmonic x.2 hmax_x.localize
    refine ⟨r, hr_pos, ?_⟩
    intro y hy
    have hy' : y.1 ∈ Metric.ball x.1 r := by
      simpa using hy
    have hy_eq : f y.1 = M := by
      exact (hr_eq hy').trans hx
    simpa [S] using hy_eq
  have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
  letI : PreconnectedSpace D := Subtype.preconnectedSpace hD_connected.isPreconnected
  have hS_univ : S = Set.univ := hS_clopen.eq_univ ⟨⟨a, ha⟩, haM⟩
  intro z hz
  have : (⟨z, hz⟩ : D) ∈ S := by
    simp [hS_univ]
  simpa [S] using this

/-- Exercise 4 (8). For a `C²` real-valued function on an open set, the integral of the Laplacian
over a sufficiently small closed disc equals the integral of the radial derivative over the
boundary circle. -/
theorem integral_laplacianWithin_closedBall_eq_integral_deriv_circleMap {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 2 f D) {a : ℂ} (ha : a ∈ D) :
    ∃ ε > 0, ∀ ⦃r : ℝ⦄, 0 < r → r < ε →
      Metric.closedBall a r ⊆ D ∧
        (∫ z in Metric.closedBall a r, (Δ[D] f) z) =
          ∫ θ in 0..2 * Real.pi, deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := by
  rcases Metric.isOpen_iff.mp hD a ha with ⟨ε, hε_pos, hε⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro r hr_pos hr_lt
  have hclosed : Metric.closedBall a r ⊆ D := (Metric.closedBall_subset_ball hr_lt).trans hε
  refine ⟨hclosed, ?_⟩
  let ω : ℂ → ℂ →L[ℝ] ℝ :=
    (fun w ↦ -fderiv ℝ f w Complex.I) dx + (fun w ↦ fderiv ℝ f w 1) dy
  have hgreen :
      (∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ)) =
        ∫ z in Metric.closedBall a r,
          (iteratedFDeriv ℝ 2 f z ![1, 1]) -
            (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) := by
    -- Convert the raw closed-path identity from Green-Riemann into the explicit circle parameter.
    calc
      ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) =
          ∫ᶜ z in (positive_circle_path a r).toClosedPath.toPath, ω z := by
            symm
            exact curveIntegral_positive_circle_toClosedPath_eq_intervalIntegral (ω := ω)
      _ = ∫ z in Metric.closedBall a r,
            (iteratedFDeriv ℝ 2 f z ![1, 1]) -
              (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) := by
            exact singleton_closedBall_green_riemann_formula hD hf hr_pos hclosed
  have hboundary :
      (∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ)) =
        ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := by
    -- Identify the Green boundary form pointwise with the radial derivative times `r`.
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hz : circleMap a r θ ∈ D := hclosed (circleMap_mem_closedBall a hr_pos.le θ)
    have hdiff : DifferentiableAt ℝ f (circleMap a r θ) :=
      (hf.contDiffAt (hD.mem_nhds hz)).differentiableAt (by norm_num)
    exact circle_boundary_form_eq_radial_deriv_mul_radius hdiff
  have harea :
      (∫ z in Metric.closedBall a r,
          (iteratedFDeriv ℝ 2 f z ![1, 1]) - (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I]))) =
        ∫ z in Metric.closedBall a r, (Δ[D] f) z := by
    -- Rewrite the Green area integrand to the within-Laplacian pointwise on the admissible disc.
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_closedBall] with z hz
    exact green_disc_integrand_eq_laplacianWithin hD hf (hclosed hz)
  calc
    ∫ z in Metric.closedBall a r, (Δ[D] f) z =
        ∫ z in Metric.closedBall a r,
          (iteratedFDeriv ℝ 2 f z ![1, 1]) -
            (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) := by
          symm
          exact harea
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
          symm
          exact hgreen
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := by
          exact hboundary
    _ = ∫ θ in 0..2 * Real.pi, deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := by
          rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
            MeasureTheory.restrict_Ioc_eq_restrict_Icc]


/-- Helper for Exercise 4: before replacing the radial derivative by the Laplacian density, the
circle average is the center value plus the radial-FTC/Fubini correction term. -/
lemma circleAverage_eq_center_add_integral_radial_fderiv {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 2 f D) {a : ℂ} {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hclosed : Metric.closedBall a ρ ⊆ D) :
    Real.circleAverage f a ρ = f a +
      ∫ r in 0..ρ, (2 * Real.pi)⁻¹ *
        ∫ θ in 0..2 * Real.pi,
          fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I)) := by
  let k : ℝ → ℝ → ℝ := fun r θ ↦
    fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I))
  have hfderiv_apply :
      ContinuousOn
        (fun p : ℂ × ℂ ↦ (fderiv ℝ f p.1 : ℂ →L[ℝ] ℝ) p.2)
        (D ×ˢ Set.univ) := by
    -- On the open domain, the within-derivative and the ordinary derivative coincide.
    refine
      (hf.continuousOn_fderivWithin_apply hD.uniqueDiffOn (by norm_num)).congr
        (fun p hp ↦ ?_)
    simp [fderivWithin_of_isOpen hD hp.1]
  have hk_hasDeriv (θ : ℝ) :
      ∀ r ∈ Set.uIcc 0 ρ,
        HasDerivAt (fun s : ℝ ↦ f (circleMap a s θ)) (k r θ) r := by
    intro r hr
    have hr' : r ∈ Set.Icc 0 ρ := by
      simpa [Set.uIcc_of_le hρ_pos.le] using hr
    have hz : circleMap a r θ ∈ D := by
      apply hclosed
      exact (Metric.closedBall_subset_closedBall hr'.2) (circleMap_mem_closedBall a hr'.1 θ)
    have hdiff : DifferentiableAt ℝ f (circleMap a r θ) :=
      (hf.contDiffAt (hD.mem_nhds hz)).differentiableAt (by norm_num)
    -- Differentiate the radial slice by the chain rule.
    simpa [k] using
      ((hdiff.hasFDerivAt.comp r (hasDerivAt_circleMap_radius a θ r).hasFDerivAt).hasDerivAt)
  have hk_intervalIntegrable (θ : ℝ) :
      IntervalIntegrable (fun r : ℝ ↦ k r θ) MeasureTheory.volume 0 ρ := by
    have hcircle_cont : ContinuousOn (fun r : ℝ ↦ circleMap a r θ) (Set.Icc 0 ρ) := by
      exact (by fun_prop : Continuous fun r : ℝ ↦ circleMap a r θ).continuousOn
    have hmaps : MapsTo (fun r : ℝ ↦ circleMap a r θ) (Set.Icc 0 ρ) D := by
      intro r hr
      exact hclosed <|
        (Metric.closedBall_subset_closedBall hr.2) (circleMap_mem_closedBall a hr.1 θ)
    have hderiv_cont :
        ContinuousOn (fun r : ℝ ↦ fderiv ℝ f (circleMap a r θ)) (Set.Icc 0 ρ) := by
      exact (hf.continuousOn_fderiv_of_isOpen hD (by norm_num)).comp hcircle_cont hmaps
    have hk_cont :
        ContinuousOn (fun r : ℝ ↦ k r θ) (Set.Icc 0 ρ) := by
      exact hderiv_cont.clm_apply continuous_const.continuousOn
    have hk_cont_u :
        ContinuousOn (fun r : ℝ ↦ k r θ) (Set.uIcc 0 ρ) := by
      simpa [Set.uIcc_of_le hρ_pos.le] using hk_cont
    exact hk_cont_u.intervalIntegrable
  have hslice_eq (θ : ℝ) :
      ∫ r in 0..ρ, k r θ = f (circleMap a ρ θ) - f a := by
    -- Fundamental theorem of calculus along each radial slice.
    simpa [k, circleMap_zero_radius] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (hk_hasDeriv θ) (hk_intervalIntegrable θ)
  have hprod :
      MeasureTheory.Integrable (fun p : ℝ × ℝ ↦ k p.1 p.2)
        ((MeasureTheory.volume.restrict (Set.uIoc 0 ρ)).prod
          (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi)))) := by
    let rect : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) ρ ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)
    have hrect_cont :
        ContinuousOn (fun p : ℝ × ℝ ↦ k p.1 p.2) rect := by
      have hphi_cont :
          ContinuousOn
            (fun p : ℝ × ℝ ↦
              (circleMap a p.1 p.2, Complex.exp (p.2 * Complex.I)))
            rect := by
        exact (by fun_prop : Continuous fun p : ℝ × ℝ ↦
          (circleMap a p.1 p.2, Complex.exp (p.2 * Complex.I))).continuousOn
      have hphi_maps :
          MapsTo
            (fun p : ℝ × ℝ ↦
              (circleMap a p.1 p.2, Complex.exp (p.2 * Complex.I)))
            rect (D ×ˢ Set.univ) := by
        intro p hp
        exact ⟨hclosed <|
          (Metric.closedBall_subset_closedBall hp.1.2) (circleMap_mem_closedBall a hp.1.1 p.2),
          trivial⟩
      exact hfderiv_apply.comp hphi_cont hphi_maps
    have hrect_int :
        MeasureTheory.IntegrableOn (fun p : ℝ × ℝ ↦ k p.1 p.2) rect
          (MeasureTheory.volume.prod MeasureTheory.volume) :=
      hrect_cont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hsubset :
        Set.uIoc 0 ρ ×ˢ Set.uIoc 0 (2 * Real.pi) ⊆ rect := by
      intro p hp
      have hp₁' : p.1 ∈ Set.Ioc (0 : ℝ) ρ := by
        simpa [Set.uIoc_of_le hρ_pos.le] using hp.1
      have hp₂' : p.2 ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
        simpa [Set.uIoc_of_le Real.two_pi_pos.le] using hp.2
      have hp₁ : p.1 ∈ Set.Icc (0 : ℝ) ρ := by
        exact ⟨le_of_lt hp₁'.1, hp₁'.2⟩
      have hp₂ : p.2 ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
        exact ⟨le_of_lt hp₂'.1, hp₂'.2⟩
      exact ⟨hp₁, hp₂⟩
    simpa [MeasureTheory.Measure.prod_restrict, MeasureTheory.IntegrableOn] using
      hrect_int.mono_set hsubset
  have houter_intervalIntegrable :
      IntervalIntegrable (fun θ : ℝ ↦ ∫ r in 0..ρ, k r θ) MeasureTheory.volume 0
        (2 * Real.pi) := by
    have houter_eq :
        (fun θ : ℝ ↦ ∫ r in 0..ρ, k r θ) =
          fun θ ↦ ∫ r, k r θ ∂ MeasureTheory.volume.restrict (Set.uIoc 0 ρ) := by
      funext θ
      rw [intervalIntegral.integral_of_le hρ_pos.le, Set.uIoc_of_le hρ_pos.le]
    rw [intervalIntegrable_iff]
    simpa [houter_eq, MeasureTheory.IntegrableOn] using hprod.integral_prod_right
  have hswap :
      ∫ θ in 0..2 * Real.pi, ∫ r in 0..ρ, k r θ =
        ∫ r in 0..ρ, ∫ θ in 0..2 * Real.pi, k r θ := by
    -- Swap the angle and radius integrals on the compact rectangle.
    simpa [intervalIntegral.integral_of_le hρ_pos.le,
      intervalIntegral.integral_of_le Real.two_pi_pos.le, Set.uIoc_of_le hρ_pos.le,
      Set.uIoc_of_le Real.two_pi_pos.le] using
      (MeasureTheory.integral_integral_swap
        (μ := MeasureTheory.volume.restrict (Set.uIoc 0 ρ))
        (ν := MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi)))
        (f := fun r θ ↦ k r θ) hprod).symm
  calc
    Real.circleAverage f a ρ = (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, f (circleMap a ρ θ) := by
      simp [Real.circleAverage_def, smul_eq_mul]
    _ = (2 * Real.pi)⁻¹ *
          ∫ θ in 0..2 * Real.pi, (f a + ∫ r in 0..ρ, k r θ) := by
          refine congrArg ((2 * Real.pi)⁻¹ * ·) ?_
          refine intervalIntegral.integral_congr_ae_restrict ?_
          refine Filter.Eventually.of_forall ?_
          intro θ
          simp [hslice_eq θ]
    _ = (2 * Real.pi)⁻¹ *
          ((∫ θ in 0..2 * Real.pi, f a) +
            ∫ θ in 0..2 * Real.pi, ∫ r in 0..ρ, k r θ) := by
          rw [intervalIntegral.integral_add intervalIntegrable_const houter_intervalIntegrable]
    _ = (2 * Real.pi)⁻¹ * ((2 * Real.pi) * f a) +
          (2 * Real.pi)⁻¹ * ∫ r in 0..ρ, ∫ θ in 0..2 * Real.pi, k r θ := by
          rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, hswap, mul_add]
    _ = f a + ∫ r in 0..ρ, (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, k r θ := by
          rw [← intervalIntegral.integral_const_mul]
          have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
          field_simp [h2pi_ne]

/-- Exercise 4 (9). For a `C²` real-valued function on an open set, the circle average over a
sufficiently small circle equals the center value plus the integral of the Laplacian term from the
textbook formula. -/
theorem circleAverage_eq_center_add_integral_laplacianWithin {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 2 f D) {a : ℂ} (ha : a ∈ D) :
    ∃ ε > 0, ∀ ⦃ρ : ℝ⦄, 0 < ρ → ρ < ε →
      Metric.closedBall a ρ ⊆ D ∧
        Real.circleAverage f a ρ = f a +
          ∫ r in 0..ρ, (2 * Real.pi * r)⁻¹ * ∫ z in Metric.closedBall a r, (Δ[D] f) z := by
  rcases integral_laplacianWithin_closedBall_eq_integral_deriv_circleMap hD hf ha with
    ⟨ε, hε_pos, hε⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro ρ hρ_pos hρ_lt
  rcases hε hρ_pos hρ_lt with ⟨hclosed, hdisc⟩
  refine ⟨hclosed, ?_⟩
  rw [circleAverage_eq_center_add_integral_radial_fderiv hD hf hρ_pos hclosed]
  refine congrArg (fun t : ℝ ↦ f a + t) ?_
  refine intervalIntegral.integral_congr_ae_restrict ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with r hr
  have hr' : r ∈ Set.Ioc (0 : ℝ) ρ := by
    simpa [Set.uIoc_of_le hρ_pos.le] using hr
  have hr_pos : 0 < r := hr'.1
  have hr_lt_ε : r < ε := lt_of_le_of_lt hr'.2 hρ_lt
  rcases hε hr_pos hr_lt_ε with ⟨hrclosed, hrdisc⟩
  have hradial :
      ∫ θ in 0..2 * Real.pi,
          fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I)) =
        ∫ θ in 0..2 * Real.pi, deriv (fun s : ℝ ↦ f (circleMap a s θ)) r := by
    -- Replace the Fréchet derivative by the one-dimensional radial derivative slice by slice.
    refine intervalIntegral.integral_congr_ae_restrict ?_
    refine Filter.Eventually.of_forall ?_
    intro θ
    have hz : circleMap a r θ ∈ D := hrclosed (circleMap_mem_closedBall a hr_pos.le θ)
    have hdiff : DifferentiableAt ℝ f (circleMap a r θ) :=
      (hf.contDiffAt (hD.mem_nhds hz)).differentiableAt (by norm_num)
    simpa using (deriv_circleMap_comp_eq_fderiv_exp (f := f) (a := a) (r := r) (θ := θ) hdiff).symm
  have hdiv :
      ∫ θ in 0..2 * Real.pi,
          fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I)) =
        (∫ z in Metric.closedBall a r, (Δ[D] f) z) / r := by
    have hr_ne : r ≠ 0 := hr_pos.ne'
    have hrdisc' :
        ∫ z in Metric.closedBall a r, (Δ[D] f) z =
          (∫ θ in 0..2 * Real.pi,
            fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I))) * r := by
      calc
        ∫ z in Metric.closedBall a r, (Δ[D] f) z =
            ∫ θ in 0..2 * Real.pi, deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := hrdisc
        _ = ∫ θ in 0..2 * Real.pi,
              fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I)) * r := by
              refine intervalIntegral.integral_congr_ae_restrict ?_
              refine Filter.Eventually.of_forall ?_
              intro θ
              have hz : circleMap a r θ ∈ D := hrclosed (circleMap_mem_closedBall a hr_pos.le θ)
              have hdiff : DifferentiableAt ℝ f (circleMap a r θ) :=
                (hf.contDiffAt (hD.mem_nhds hz)).differentiableAt (by norm_num)
              simpa using
                congrArg (fun t : ℝ ↦ t * r)
                  (deriv_circleMap_comp_eq_fderiv_exp
                    (f := f) (a := a) (r := r) (θ := θ) hdiff)
        _ = (∫ θ in 0..2 * Real.pi,
              fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I))) * r := by
              rw [intervalIntegral.integral_mul_const]
    rw [eq_div_iff hr_ne]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hrdisc'.symm
  calc
    (2 * Real.pi)⁻¹ *
        ∫ θ in 0..2 * Real.pi,
          fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I))
        = (2 * Real.pi)⁻¹ * ((∫ z in Metric.closedBall a r, (Δ[D] f) z) / r) := by
            rw [hdiv]
    _ = (2 * Real.pi * r)⁻¹ * ∫ z in Metric.closedBall a r, (Δ[D] f) z := by
          have hr_ne : r ≠ 0 := hr_pos.ne'
          have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
          field_simp [hr_ne, h2pi_ne]

/-- Helper for Exercise 4: on an open set, the within-Laplacian agrees with the ordinary
Laplacian. -/
lemma laplacianWithin_eq_laplacian_on_open {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {z : ℂ} (hz : z ∈ D) :
    (Δ[D] f) z = Δ f z := by
  -- Rewrite both Laplacians via second iterated derivatives on the complex plane.
  rw [InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_complexPlane f hD.uniqueDiffOn hz,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane f]
  -- On an open set, the within-iterated derivative matches the ordinary iterated derivative.
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hD.uniqueDiffOn
    (hf.contDiffAt (hD.mem_nhds hz)) hz]

/-- Helper for Exercise 4: the ordinary Laplacian of a `C²` real-valued function is continuous at
each point. -/
lemma continuousAt_laplacian_of_contDiffAt {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    ContinuousAt (Δ f) z := by
  -- Express the Laplacian as evaluation of the continuous second derivative on the two standard
  -- complex-plane basis directions.
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  have hiter : ContinuousAt (iteratedFDeriv ℝ 2 f) z :=
    hf.continuousAt_iteratedFDeriv le_rfl
  have h_one : ContinuousAt (fun w : ℂ ↦ iteratedFDeriv ℝ 2 f w ![1, 1]) z :=
    (continuous_eval_const (![1, 1] : Fin 2 → ℂ)).continuousAt.comp hiter
  have h_I : ContinuousAt (fun w : ℂ ↦ iteratedFDeriv ℝ 2 f w ![Complex.I, Complex.I]) z :=
    (continuous_eval_const (![Complex.I, Complex.I] : Fin 2 → ℂ)).continuousAt.comp hiter
  exact h_one.add h_I

/-- Helper for Exercise 4: theorem (9) turns pointwise nonnegativity of the within-Laplacian into
the sub-mean inequality. -/
lemma isSubharmonicOn_of_nonneg_laplacianWithin {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) (hΔ : ∀ z ∈ D, 0 ≤ (Δ[D] f) z) :
    IsSubharmonicOn f D := by
  constructor
  · -- A `C²` function is continuous on its domain.
    exact hf.continuousOn
  · intro a ha
    rcases circleAverage_eq_center_add_integral_laplacianWithin hD hf ha with ⟨ε, hε_pos, hε⟩
    refine ⟨ε, hε_pos, ?_⟩
    intro r hr_pos hr_lt
    rcases hε hr_pos hr_lt with ⟨hclosed, havg⟩
    refine ⟨hclosed, ?_⟩
    have hcorr_nonneg :
        0 ≤ ∫ s in 0..r, (2 * Real.pi * s)⁻¹ * ∫ z in Metric.closedBall a s, (Δ[D] f) z := by
      refine intervalIntegral.integral_nonneg hr_pos.le ?_
      intro s hs
      have hs_nonneg : 0 ≤ s := hs.1
      have hs_le_r : s ≤ r := hs.2
      have hs_closed : Metric.closedBall a s ⊆ D := by
        intro z hz
        exact hclosed (Metric.closedBall_subset_closedBall hs_le_r hz)
      have hinner_nonneg : 0 ≤ ∫ z in Metric.closedBall a s, (Δ[D] f) z := by
        refine MeasureTheory.integral_nonneg_of_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_closedBall] with z hz
        exact hΔ z (hs_closed hz)
      have hfactor_nonneg : 0 ≤ (2 * Real.pi * s)⁻¹ := by
        positivity
      exact mul_nonneg hfactor_nonneg hinner_nonneg
    -- The exact circle-average expansion turns the nonnegative correction term into the
    -- sub-mean inequality.
    rw [havg]
    linarith

/-- Helper for Exercise 4: a negative value of the within-Laplacian persists as a uniform
negative upper bound on some small closed ball. -/
lemma exists_closedBall_laplacianWithin_le_neg_const {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {a : ℂ} (ha : a ∈ D) (hneg : (Δ[D] f) a < 0) :
    ∃ c ε, c < 0 ∧ 0 < ε ∧ Metric.closedBall a ε ⊆ D ∧
      ∀ z ∈ Metric.closedBall a ε, (Δ[D] f) z ≤ c := by
  let c : ℝ := (Δ f a) / 2
  have hΔa : (Δ[D] f) a = Δ f a := laplacianWithin_eq_laplacian_on_open hD hf ha
  have hc_neg : c < 0 := by
    dsimp [c]
    rw [hΔa] at hneg
    linarith
  have hΔa_lt : Δ f a < c := by
    dsimp [c]
    linarith
  have hcont : ContinuousAt (Δ f) a :=
    continuousAt_laplacian_of_contDiffAt (hf.contDiffAt (hD.mem_nhds ha))
  have hballD : D ∈ 𝓝 a := hD.mem_nhds ha
  have hballΔ : {z : ℂ | Δ f z < c} ∈ 𝓝 a := by
    -- Continuity puts the ordinary Laplacian below the negative midpoint on a small neighborhood.
    exact hcont.preimage_mem_nhds (isOpen_Iio.mem_nhds hΔa_lt)
  rcases Metric.mem_nhds_iff.mp hballD with ⟨εD, hεD_pos, hεD⟩
  rcases Metric.mem_nhds_iff.mp hballΔ with ⟨εΔ, hεΔ_pos, hεΔ⟩
  let ε : ℝ := min (εD / 2) (εΔ / 2)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  have hε_lt_εD : ε < εD := by
    dsimp [ε]
    have hhalf : εD / 2 < εD := by linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have hε_lt_εΔ : ε < εΔ := by
    dsimp [ε]
    have hhalf : εΔ / 2 < εΔ := by linarith
    exact lt_of_le_of_lt (min_le_right _ _) hhalf
  refine ⟨c, ε, hc_neg, hε_pos, ?_, ?_⟩
  · -- The closed ball sits inside the open neighborhood supplied by openness of `D`.
    exact (Metric.closedBall_subset_ball hε_lt_εD).trans hεD
  · intro z hz
    have hz_ball : z ∈ Metric.ball a εΔ := by
      exact Metric.closedBall_subset_ball hε_lt_εΔ hz
    have hz_lt : Δ f z < c := hεΔ hz_ball
    have hzD : z ∈ D := by
      exact hεD (Metric.closedBall_subset_ball hε_lt_εD hz)
    -- On the controlling closed ball, the within-Laplacian matches the ordinary Laplacian.
    rw [laplacianWithin_eq_laplacian_on_open hD hf hzD]
    linarith

/-- Helper for Exercise 4: a uniform negative upper bound on the within-Laplacian forces the
theorem-(9) correction term to be bounded above by a negative quadratic. -/
lemma laplacianWithin_correction_le_neg_quadratic {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 2 f D) {a : ℂ} {c ε : ℝ}
    (_hc : c < 0) (hε_pos : 0 < ε) (hclosed : Metric.closedBall a ε ⊆ D)
    (hbound : ∀ z ∈ Metric.closedBall a ε, (Δ[D] f) z ≤ c) :
    ∃ η > 0, η ≤ ε ∧ ∀ {ρ : ℝ}, 0 < ρ → ρ < η →
      ∫ r in 0..ρ, (2 * Real.pi * r)⁻¹ * ∫ z in Metric.closedBall a r, (Δ[D] f) z ≤
        c * ρ ^ 2 / 4 := by
  have ha : a ∈ D := by
    -- The controlling closed ball contains its center, so the ball hypothesis puts `a` in `D`.
    have hself : a ∈ Metric.closedBall a ε := by
      simpa [Metric.mem_closedBall, dist_self] using hε_pos.le
    exact hclosed hself
  rcases integral_laplacianWithin_closedBall_eq_integral_deriv_circleMap hD hf ha with
    ⟨ε₀, hε₀_pos, hε₀⟩
  let η : ℝ := min ε ε₀
  refine ⟨η, ?_, min_le_left _ _, ?_⟩
  · -- The witness radius stays positive because both input radii are positive.
    dsimp [η]
    positivity
  · intro ρ hρ_pos hρ_lt
    let correction : ℝ → ℝ := fun r ↦
      (2 * Real.pi * r)⁻¹ * ∫ z in Metric.closedBall a r, (Δ[D] f) z
    let k : ℝ → ℝ → ℝ := fun r θ ↦
      fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I))
    let kernel : ℝ → ℝ := fun r ↦
      (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, k r θ
    have hρ_lt_ε : ρ < ε := lt_of_lt_of_le hρ_lt (min_le_left _ _)
    have hρ_lt_ε₀ : ρ < ε₀ := lt_of_lt_of_le hρ_lt (min_le_right _ _)
    have hfderiv_apply :
        ContinuousOn
          (fun p : ℂ × ℂ ↦ (fderiv ℝ f p.1 : ℂ →L[ℝ] ℝ) p.2)
          (D ×ˢ Set.univ) := by
      -- On the open domain, the within-derivative and ordinary derivative coincide.
      refine
        (hf.continuousOn_fderivWithin_apply hD.uniqueDiffOn (by norm_num)).congr
          (fun p hp ↦ ?_)
      simp [fderivWithin_of_isOpen hD hp.1]
    have hprod :
        MeasureTheory.Integrable (fun p : ℝ × ℝ ↦ k p.1 p.2)
          ((MeasureTheory.volume.restrict (Set.uIoc 0 ρ)).prod
            (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi)))) := by
      let rect : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) ρ ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)
      have hrect_cont :
          ContinuousOn (fun p : ℝ × ℝ ↦ k p.1 p.2) rect := by
        have hphi_cont :
            ContinuousOn
              (fun p : ℝ × ℝ ↦
                (circleMap a p.1 p.2, Complex.exp (p.2 * Complex.I)))
              rect := by
          exact (by
            fun_prop : Continuous fun p : ℝ × ℝ ↦
              (circleMap a p.1 p.2, Complex.exp (p.2 * Complex.I))).continuousOn
        have hphi_maps :
            MapsTo
              (fun p : ℝ × ℝ ↦
                (circleMap a p.1 p.2, Complex.exp (p.2 * Complex.I)))
              rect (D ×ˢ Set.univ) := by
          intro p hp
          refine ⟨hclosed ?_, trivial⟩
          exact
            (Metric.closedBall_subset_closedBall
              (le_trans hp.1.2 (le_of_lt hρ_lt_ε)))
              (circleMap_mem_closedBall a hp.1.1 p.2)
        have hk_cont :
            ContinuousOn
              (fun p : ℝ × ℝ ↦
                fderiv ℝ f (circleMap a p.1 p.2) (Complex.exp (p.2 * Complex.I)))
              rect :=
          hfderiv_apply.comp hphi_cont hphi_maps
        simpa [k] using hk_cont
      have hrect_int :
          MeasureTheory.IntegrableOn (fun p : ℝ × ℝ ↦ k p.1 p.2) rect
            (MeasureTheory.volume.prod MeasureTheory.volume) :=
        hrect_cont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      have hsubset :
          Set.uIoc 0 ρ ×ˢ Set.uIoc 0 (2 * Real.pi) ⊆ rect := by
        intro p hp
        have hp₁' : p.1 ∈ Set.Ioc (0 : ℝ) ρ := by
          simpa [Set.uIoc_of_le hρ_pos.le] using hp.1
        have hp₂' : p.2 ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
          simpa [Set.uIoc_of_le Real.two_pi_pos.le] using hp.2
        exact ⟨⟨le_of_lt hp₁'.1, hp₁'.2⟩, ⟨le_of_lt hp₂'.1, hp₂'.2⟩⟩
      simpa [MeasureTheory.Measure.prod_restrict, MeasureTheory.IntegrableOn] using
        hrect_int.mono_set hsubset
    have hkernel_int :
        IntervalIntegrable kernel MeasureTheory.volume 0 ρ := by
      have hbase :
          IntervalIntegrable (fun r : ℝ ↦ ∫ θ in 0..2 * Real.pi, k r θ)
            MeasureTheory.volume 0 ρ := by
        have houter_eq :
            (fun r : ℝ ↦ ∫ θ in 0..2 * Real.pi, k r θ) =
              fun r ↦ ∫ θ, k r θ ∂ MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi)) := by
          funext r
          rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, Set.uIoc_of_le Real.two_pi_pos.le]
        rw [intervalIntegrable_iff]
        simpa [houter_eq, MeasureTheory.IntegrableOn] using hprod.integral_prod_left
      simpa [kernel] using hbase.const_mul ((2 * Real.pi)⁻¹)
    have hcorr_eq : EqOn correction kernel (Set.uIoc 0 ρ) := by
      intro r hr
      have hr' : r ∈ Set.Ioc (0 : ℝ) ρ := by
        simpa [Set.uIoc_of_le hρ_pos.le] using hr
      have hr_pos : 0 < r := hr'.1
      have hr_lt_ε₀ : r < ε₀ := lt_of_le_of_lt hr'.2 hρ_lt_ε₀
      rcases hε₀ hr_pos hr_lt_ε₀ with ⟨hrclosed, hrdisc⟩
      have hdiv :
          ∫ θ in 0..2 * Real.pi, k r θ =
            (∫ z in Metric.closedBall a r, (Δ[D] f) z) / r := by
        have hr_ne : r ≠ 0 := hr_pos.ne'
        have hrdisc' :
            ∫ z in Metric.closedBall a r, (Δ[D] f) z =
              (∫ θ in 0..2 * Real.pi, k r θ) * r := by
          calc
            ∫ z in Metric.closedBall a r, (Δ[D] f) z =
                ∫ θ in 0..2 * Real.pi, deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := hrdisc
            _ = ∫ θ in 0..2 * Real.pi, k r θ * r := by
                  refine intervalIntegral.integral_congr_ae_restrict ?_
                  refine Filter.Eventually.of_forall ?_
                  intro θ
                  have hz : circleMap a r θ ∈ D := hrclosed (circleMap_mem_closedBall a hr_pos.le θ)
                  have hdiff : DifferentiableAt ℝ f (circleMap a r θ) :=
                    (hf.contDiffAt (hD.mem_nhds hz)).differentiableAt (by norm_num)
                  simpa using
                    congrArg (fun t : ℝ ↦ t * r)
                      (deriv_circleMap_comp_eq_fderiv_exp
                        (f := f) (a := a) (r := r) (θ := θ) hdiff)
            _ = (∫ θ in 0..2 * Real.pi, k r θ) * r := by rw [intervalIntegral.integral_mul_const]
        rw [eq_div_iff hr_ne]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hrdisc'.symm
      have hformula :
          kernel r = correction r := by
        have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
        have hr_ne : r ≠ 0 := hr_pos.ne'
        calc
          kernel r =
              (2 * Real.pi)⁻¹ * ((∫ z in Metric.closedBall a r, (Δ[D] f) z) / r) := by
                simp [kernel, hdiv]
          _ = correction r := by
                simp [correction]
                field_simp [h2pi_ne, hr_ne]
      exact hformula.symm
    have hcorr_int : IntervalIntegrable correction MeasureTheory.volume 0 ρ :=
      hkernel_int.congr hcorr_eq.symm
    have hlinear_int :
        IntervalIntegrable (fun r : ℝ ↦ c * r / 2) MeasureTheory.volume 0 ρ := by
      -- The comparison function is polynomial, so it is interval-integrable on every compact
      -- interval.
      exact Continuous.intervalIntegrable (by fun_prop) _ _
    have hpointwise : ∀ r ∈ Set.Ioo 0 ρ, correction r ≤ c * r / 2 := by
      intro r hr
      have hr_pos : 0 < r := hr.1
      have hr_lt_ε : r < ε := lt_trans hr.2 hρ_lt_ε
      have hr_closedε : Metric.closedBall a r ⊆ Metric.closedBall a ε :=
        Metric.closedBall_subset_closedBall (le_of_lt hr_lt_ε)
      have hr_closedD : Metric.closedBall a r ⊆ D := fun z hz => hclosed (hr_closedε hz)
      have hΔ_cont :
          ContinuousOn (Δ f) (Metric.closedBall a r) := by
        intro z hz
        exact
          (continuousAt_laplacian_of_contDiffAt
            (hf.contDiffAt (hD.mem_nhds (hr_closedD hz)))).continuousWithinAt
      have hwithin_cont :
          ContinuousOn (Δ[D] f) (Metric.closedBall a r) := by
        refine hΔ_cont.congr ?_
        intro z hz
        exact laplacianWithin_eq_laplacian_on_open hD hf (hr_closedD hz)
      have hinner_int :
          MeasureTheory.IntegrableOn (fun z : ℂ ↦ (Δ[D] f) z) (Metric.closedBall a r)
            MeasureTheory.volume :=
        hwithin_cont.integrableOn_compact (isCompact_closedBall a r)
      have hconst_int :
          MeasureTheory.IntegrableOn (fun _ : ℂ ↦ c) (Metric.closedBall a r) MeasureTheory.volume :=
        continuousOn_const.integrableOn_compact (isCompact_closedBall a r)
      have hinner_le :
          ∫ z in Metric.closedBall a r, (Δ[D] f) z ≤ ∫ z in Metric.closedBall a r, c := by
        refine MeasureTheory.integral_mono_ae hinner_int hconst_int ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_closedBall] with z hz
        exact hbound z (hr_closedε hz)
      have hconst_eval :
          ∫ z in Metric.closedBall a r, c = c * Real.pi * r ^ 2 := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
          Complex.volume_closedBall]
        simp [hr_pos.le, pow_two, mul_left_comm, mul_comm]
      have hfactor_nonneg : 0 ≤ (2 * Real.pi * r)⁻¹ := by
        positivity
      have hscaled :
          correction r ≤ (2 * Real.pi * r)⁻¹ * ∫ z in Metric.closedBall a r, c := by
        exact mul_le_mul_of_nonneg_left hinner_le hfactor_nonneg
      have hconst_correction :
          (2 * Real.pi * r)⁻¹ * ∫ z in Metric.closedBall a r, c = c * r / 2 := by
        have hr_ne : r ≠ 0 := hr_pos.ne'
        have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
        rw [hconst_eval]
        field_simp [hr_ne, h2pi_ne]
      exact hscaled.trans_eq hconst_correction
    have hcorr_bound :
        ∫ r in 0..ρ, correction r ≤ ∫ r in 0..ρ, c * r / 2 := by
      -- Compare the correction with the explicit linear majorant on `(0, ρ)`.
      exact
        intervalIntegral.integral_mono_on_of_le_Ioo hρ_pos.le hcorr_int hlinear_int hpointwise
    have hlinear_eval : ∫ r in 0..ρ, c * r / 2 = c * ρ ^ 2 / 4 := by
      -- The linear majorant integrates to the expected quadratic term.
      rw [show (fun r : ℝ ↦ c * r / 2) = fun r : ℝ ↦ (c / 2) * r by
        funext r
        ring]
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring
    exact hcorr_bound.trans_eq hlinear_eval

/-- Helper for Exercise 4: a negative value of the within-Laplacian makes the theorem-(9)
correction term strictly negative on all sufficiently small radii. -/
lemma laplacianWithin_correction_neg_of_neg_at_point {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {a : ℂ} (ha : a ∈ D) (hneg : (Δ[D] f) a < 0) :
    ∃ ε > 0, ∀ {ρ : ℝ}, 0 < ρ → ρ < ε →
      ∫ r in 0..ρ, (2 * Real.pi * r)⁻¹ * ∫ z in Metric.closedBall a r, (Δ[D] f) z < 0 := by
  rcases exists_closedBall_laplacianWithin_le_neg_const hD hf ha hneg with
    ⟨c, ε, hc, hε_pos, hclosed, hbound⟩
  rcases laplacianWithin_correction_le_neg_quadratic hD hf hc hε_pos hclosed hbound with
    ⟨η, hη_pos, hη_le, hη⟩
  refine ⟨η, hη_pos, ?_⟩
  intro ρ hρ_pos hρ_lt
  have hle : ∫ r in 0..ρ, (2 * Real.pi * r)⁻¹ * ∫ z in Metric.closedBall a r, (Δ[D] f) z ≤
      c * ρ ^ 2 / 4 := hη hρ_pos hρ_lt
  have hρsq_pos : 0 < ρ ^ 2 := by positivity
  have hrhs_neg : c * ρ ^ 2 / 4 < 0 := by
    nlinarith
  exact lt_of_le_of_lt hle hrhs_neg

/-- Cartan section17 0012_Exercise_4. Exercise 4 (10). A twice continuously differentiable
real-valued function on `D` is
subharmonic exactly when its Laplacian is pointwise nonnegative on `D`. -/
theorem isSubharmonicOn_iff_nonneg_laplacianWithin {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) :
    IsSubharmonicOn f D ↔ ∀ z ∈ D, 0 ≤ (Δ[D] f) z := by
  constructor
  · intro hsub z hz
    by_contra hneg_nonneg
    have hneg : (Δ[D] f) z < 0 := by linarith
    rcases circleAverage_eq_center_add_integral_laplacianWithin hD hf hz with ⟨ε₁, hε₁_pos, hε₁⟩
    rcases laplacianWithin_correction_neg_of_neg_at_point hD hf hz hneg with
      ⟨ε₂, hε₂_pos, hε₂⟩
    rcases hsub.2 hz with ⟨ε₃, hε₃_pos, hε₃⟩
    let ρ : ℝ := min (min (ε₁ / 2) (ε₂ / 2)) (ε₃ / 2)
    have hρ_pos : 0 < ρ := by
      dsimp [ρ]
      positivity
    have hρ_lt_ε₁ : ρ < ε₁ := by
      dsimp [ρ]
      have hhalf : ε₁ / 2 < ε₁ := by linarith
      exact lt_of_le_of_lt (min_le_left _ _) <| lt_of_le_of_lt (min_le_left _ _) hhalf
    have hρ_lt_ε₂ : ρ < ε₂ := by
      dsimp [ρ]
      have hhalf : ε₂ / 2 < ε₂ := by linarith
      exact lt_of_le_of_lt (min_le_left _ _) <| lt_of_le_of_lt (min_le_right _ _) hhalf
    have hρ_lt_ε₃ : ρ < ε₃ := by
      dsimp [ρ]
      have hhalf : ε₃ / 2 < ε₃ := by linarith
      exact lt_of_le_of_lt (min_le_right _ _) hhalf
    rcases hε₁ hρ_pos hρ_lt_ε₁ with ⟨hball, havg⟩
    rcases hε₃ hρ_pos hρ_lt_ε₃ with ⟨_, hsubmean⟩
    have hcorr_neg :
        ∫ r in 0..ρ, (2 * Real.pi * r)⁻¹ * ∫ z in Metric.closedBall z r, (Δ[D] f) z < 0 :=
      hε₂ hρ_pos hρ_lt_ε₂
    have havg_lt : Real.circleAverage f z ρ < f z := by
      -- Theorem (9) rewrites the circle average as the center value plus the negative correction.
      rw [havg]
      linarith
    exact not_lt_of_ge hsubmean havg_lt
  · intro hΔ
    exact isSubharmonicOn_of_nonneg_laplacianWithin hD hf hΔ
