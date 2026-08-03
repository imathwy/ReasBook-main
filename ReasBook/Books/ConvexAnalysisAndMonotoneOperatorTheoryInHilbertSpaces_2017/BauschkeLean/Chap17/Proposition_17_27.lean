import Mathlib
import BauschkeLean.Chap01.Text_1_0_6
import BauschkeLean.Chap17.Definition_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

universe u

namespace ERealFunction

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [IsTopologicalAddGroup H]
  [Module ℝ H] [ContinuousSMul ℝ H]

/-- Helper for Proposition 17.27: restricting lower semicontinuity to the affine parameter on
`]x₀,x₁]` gives a lower-semicontinuous scalar trace on `]0,1]`. -/
private lemma lowerSemicontinuousOn_lineMap_openClosedSegment
    (f : H → Set.Ioi (⊥ : EReal)) {x0 x1 : H}
    (hlsc : LowerSemicontinuousOn f.asEReal (openClosedSegment x0 x1)) :
    LowerSemicontinuousOn
      (fun t : ℝ ↦ f.asEReal (AffineMap.lineMap x0 x1 t))
      (Set.Ioc (0 : ℝ) 1) := by
  -- Compose the segment lower-semicontinuity with the affine parameterization of `]0,1]`.
  refine hlsc.comp AffineMap.lineMap_continuous.continuousOn ?_
  intro t ht
  exact mem_openClosedSegment_iff.mpr ⟨t, ht, rfl⟩

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17.27: shifting the scalar parameter on `lineMap` translates into
moving along the segment direction `x₁ - x₀`. -/
private lemma lineMap_add_eq_lineMap_add_smul
    (x0 x1 : H) (t α : ℝ) :
    AffineMap.lineMap x0 x1 (t + α) =
      AffineMap.lineMap x0 x1 t + α • (x1 - x0) := by
  -- Expand both affine combinations and regroup the common `t` and `α` terms.
  simp [AffineMap.lineMap_apply_module', add_smul, add_assoc, add_comm]

omit [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 17.27: a directional derivative along the chord direction becomes a
right derivative of the scalar trace. -/
private lemma hasRightDerivativeAt_lineMap_of_hasDirectionalDerivativeAt
    (f : H → Set.Ioi (⊥ : EReal)) {x0 x1 : H} {t : ℝ} {ξ : EReal}
    (hξ : HasDirectionalDerivativeAt f (AffineMap.lineMap x0 x1 t) (x1 - x0) ξ) :
    HasRightDerivativeAt
      (fun s : ℝ ↦ f (AffineMap.lineMap x0 x1 s))
      t ξ := by
  refine ⟨hξ.1, ?_⟩
  -- Rewrite the one-dimensional quotient into the given directional quotient.
  refine Filter.Tendsto.congr' ?_ hξ.2
  apply eventuallyEq_nhdsWithin_of_eqOn
  intro α hα
  simp [lineMap_add_eq_lineMap_add_smul, smul_eq_mul]

/-- Helper for Proposition 17.27: the epsilon barrier records the affine upper bound
`g(s) ≤ g(0) + ε s` up to the time `t`. -/
private def barrier
    (g : ℝ → Set.Ioi (⊥ : EReal)) (ε t : ℝ) : Prop :=
  t ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ s ∈ Set.Ioc (0 : ℝ) t,
      g.asEReal s ≤ g.asEReal 0 + (((ε * s : ℝ)) : EReal)

/-- Helper for Proposition 17.27: the barrier times form the `ε`-barrier set used in the
textbook `S_ε` argument. -/
private def barrierSet
    (g : ℝ → Set.Ioi (⊥ : EReal)) (ε : ℝ) : Set ℝ :=
  {t | barrier g ε t}

/-- Helper for Proposition 17.27: every time strictly below the supremum of the barrier set is
already a barrier time. -/
private lemma mem_barrier_of_lt_csSup
    (g : ℝ → Set.Ioi (⊥ : EReal)) {ε u : ℝ}
    (hS_nonempty : (barrierSet g ε).Nonempty)
    (hu : u ∈ Set.Ioo (0 : ℝ) (sSup (barrierSet g ε))) :
    barrier g ε u := by
  -- Choose a genuine barrier time strictly to the right of `u`, then restrict its estimate.
  rcases exists_lt_of_lt_csSup hS_nonempty hu.2 with ⟨v, hvS, huv⟩
  rcases hvS with ⟨hv_mem, hv_bound⟩
  refine ⟨⟨hu.1.le, le_trans huv.le hv_mem.2⟩, ?_⟩
  intro s hs
  exact hv_bound s ⟨hs.1, le_trans hs.2 huv.le⟩

/-- Helper for Proposition 17.27: lower semicontinuity on `]0,t₁]` closes an affine upper bound
known on the strict left-neighborhood `]0,t₁[`. -/
private lemma barrier_value_at_endpoint_of_lowerSemicontinuousOn
    (g : ℝ → Set.Ioi (⊥ : EReal)) {t1 : ℝ} {y : EReal}
    (ht1_pos : 0 < t1)
    (hlsc : LowerSemicontinuousOn g.asEReal (Set.Ioc (0 : ℝ) t1))
    (hbound : ∀ s ∈ Set.Ioo (0 : ℝ) t1, g.asEReal s ≤ y) :
    g.asEReal t1 ≤ y := by
  -- The left-open interval is frequent at the endpoint inside `]0,t₁]`, so lower
  -- semicontinuity turns the strict-left bound into the endpoint bound.
  have hfreq :
      ∃ᶠ s in 𝓝[Set.Ioc (0 : ℝ) t1] t1, g.asEReal s ≤ y := by
    have hclosure : t1 ∈ closure (Set.Ioo (0 : ℝ) t1) := by
      rw [closure_Ioo (show (0 : ℝ) ≠ t1 from ne_of_lt ht1_pos)]
      exact ⟨ht1_pos.le, le_rfl⟩
    have hfreq0 : ∃ᶠ s in 𝓝 t1, s ∈ Set.Ioo (0 : ℝ) t1 := by
      exact (mem_closure_iff_frequently (x := t1) (s := Set.Ioo (0 : ℝ) t1)).mp hclosure
    rw [frequently_nhdsWithin_iff]
    exact hfreq0.mono fun s hs ↦ ⟨hbound s hs, Set.Ioo_subset_Ioc_self hs⟩
  exact hlsc.frequently t1 ⟨ht1_pos, le_rfl⟩ y hfreq

/-- Helper for Proposition 17.27: a right derivative strictly below `ε` yields a short right
interval on which every secant slope is at most `ε`. -/
private lemma eventually_affine_upper_bound_of_hasRightDerivativeAt_lt
    (g : ℝ → Set.Ioi (⊥ : EReal)) {t : ℝ} {ξ : EReal} {ε : ℝ}
    (hξ : HasRightDerivativeAt g t ξ)
    (hξε : ξ < ((ε : ℝ) : EReal)) :
    ∃ δ > 0, ∀ s ∈ Set.Ioc t (min 1 (t + δ)),
      g.asEReal s ≤ g.asEReal t + (((ε * (s - t) : ℝ)) : EReal) := by
  let q : ℝ → EReal := fun α ↦ ((g (t + α) : EReal) - (g t : EReal)) / α
  have hq_tendsto : Filter.Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ξ) := by
    -- Unfold the one-dimensional derivative and rewrite `α • 1` as `α`.
    simpa [q, HasRightDerivativeAt, HasDirectionalDerivativeAt, one_smul] using hξ.2
  have hq_lt :
      ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), q α < ((ε : ℝ) : EReal) := by
    exact hq_tendsto.eventually (Iio_mem_nhds hξε)
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hq_lt with ⟨u, hu0, hu_subset⟩
  rcases Metric.mem_nhds_iff.mp hu0 with ⟨η, hη_pos, hη_subset⟩
  refine ⟨η / 2, half_pos hη_pos, ?_⟩
  intro s hs
  have hs_pos : 0 < s - t := sub_pos.mpr hs.1
  have hs_lt_eta : s - t < η := by
    have hs_le_half : s - t ≤ η / 2 := by
      have hs_upper : s ≤ t + η / 2 := le_trans hs.2 (min_le_right _ _)
      linarith
    linarith
  have hs_mem_u : s - t ∈ u := by
    apply hη_subset
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hs_pos] using hs_lt_eta
  have hq_s : q (s - t) < ((ε : ℝ) : EReal) := by
    exact hu_subset ⟨hs_mem_u, hs_pos⟩
  have hts : t + (s - t) = s := by ring
  have hquot :
      (g.asEReal s - g.asEReal t) / ((s - t : ℝ) : EReal) < ((ε : ℝ) : EReal) := by
    simpa [q, hts] using hq_s
  have hsub :
      g.asEReal s - g.asEReal t <
        ((ε : ℝ) : EReal) * ((s - t : ℝ) : EReal) := by
    exact (EReal.div_lt_iff (by exact_mod_cast hs_pos) (EReal.coe_ne_top (s - t))).1 hquot
  have hsub_le :
      g.asEReal s - g.asEReal t ≤ (((ε * (s - t) : ℝ)) : EReal) := by
    simpa [EReal.coe_mul] using hsub.le
  have hgt_bot : g.asEReal t ≠ ⊥ := ne_of_gt (g t).2
  have hgt_top : g.asEReal t ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hξ.1)
  have hle_add :
      g.asEReal s ≤ (((ε * (s - t) : ℝ)) : EReal) + g.asEReal t := by
    exact (EReal.sub_le_iff_le_add (Or.inl hgt_bot) (Or.inl hgt_top)).1 hsub_le
  simpa [add_comm, add_left_comm, add_assoc] using hle_add

/-- Helper for Proposition 17.27: once the barrier reaches `t₁`, any short right interval with
the same affine slope bound extends the barrier to the whole new endpoint. -/
private lemma barrier_push_right_of_local_affine_bound
    (g : ℝ → Set.Ioi (⊥ : EReal)) {ε t1 t2 : ℝ}
    (hbarrier : barrier g ε t1)
    (ht1_pos : 0 < t1)
    (ht1t2 : t1 < t2)
    (ht2_le_one : t2 ≤ 1)
    (hlocal : ∀ s ∈ Set.Ioc t1 t2,
      g.asEReal s ≤ g.asEReal t1 + (((ε * (s - t1) : ℝ)) : EReal)) :
    barrier g ε t2 := by
  rcases hbarrier with ⟨ht1_mem, ht1_bound⟩
  refine ⟨⟨le_trans ht1_pos.le ht1t2.le, ht2_le_one⟩, ?_⟩
  intro s hs
  by_cases hs_le : s ≤ t1
  · -- Points before `t₁` are already covered by the old barrier.
    exact ht1_bound s ⟨hs.1, hs_le⟩
  · -- Points after `t₁` use the local secant bound and the endpoint estimate at `t₁`.
    have hs_t1 : t1 < s := lt_of_not_ge hs_le
    have hs_local :
        g.asEReal s ≤ g.asEReal t1 + (((ε * (s - t1) : ℝ)) : EReal) :=
      hlocal s ⟨hs_t1, hs.2⟩
    have ht1_value :
        g.asEReal t1 ≤ g.asEReal 0 + (((ε * t1 : ℝ)) : EReal) :=
      ht1_bound t1 ⟨ht1_pos, le_rfl⟩
    have ht1_value' :
        g.asEReal t1 + (((ε * (s - t1) : ℝ)) : EReal) ≤
          (g.asEReal 0 + (((ε * t1 : ℝ)) : EReal)) +
            (((ε * (s - t1) : ℝ)) : EReal) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right ht1_value ((((ε * (s - t1) : ℝ)) : EReal))
    calc
      g.asEReal s ≤ g.asEReal t1 + (((ε * (s - t1) : ℝ)) : EReal) := hs_local
      _ ≤ (g.asEReal 0 + (((ε * t1 : ℝ)) : EReal)) +
            (((ε * (s - t1) : ℝ)) : EReal) := ht1_value'
      _ = g.asEReal 0 +
            ((((ε * t1 : ℝ) + (ε * (s - t1) : ℝ) : ℝ)) : EReal) := by
              rw [add_assoc, ← EReal.coe_add]
      _ = g.asEReal 0 + (((ε * s : ℝ)) : EReal) := by
              congr 2
              ring

/-- Helper for Proposition 17.27: for every positive `ε`, the textbook barrier argument proves
the affine endpoint bound `g(1) ≤ g(0) + ε`. -/
private theorem right_endpoint_le_affine_barrier_of_positive
    (g : ℝ → Set.Ioi (⊥ : EReal))
    (hlsc : LowerSemicontinuousOn g.asEReal (Set.Ioc (0 : ℝ) 1))
    (hderiv : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ∃ ξ : EReal, HasRightDerivativeAt g t ξ ∧ ξ ≤ 0) :
    ∀ ε > 0, g.asEReal 1 ≤ g.asEReal 0 + ((ε : ℝ) : EReal) := by
  intro ε hε
  -- Route correction: execute the source `S_ε`/`sSup` barrier proof on the scalar trace.
  obtain ⟨ξ0, hξ0, hξ0_nonpos⟩ := hderiv 0 ⟨le_rfl, zero_lt_one⟩
  have hξ0_lt : ξ0 < ((ε : ℝ) : EReal) := by
    exact lt_of_le_of_lt hξ0_nonpos (by exact_mod_cast hε)
  obtain ⟨δ0, hδ0_pos, hδ0_bound⟩ :=
    eventually_affine_upper_bound_of_hasRightDerivativeAt_lt g hξ0 hξ0_lt
  let t0 : ℝ := min (1 / 2 : ℝ) (δ0 / 2)
  have ht0_pos : 0 < t0 := by
    dsimp [t0]
    exact lt_min (by norm_num) (half_pos hδ0_pos)
  have ht0_le_one : t0 ≤ 1 := by
    dsimp [t0]
    exact le_trans (min_le_left _ _) (by norm_num)
  have ht0_le_min : t0 ≤ min 1 (0 + δ0) := by
    refine le_min ?_ ?_
    · exact ht0_le_one
    · dsimp [t0]
      have : min (1 / 2 : ℝ) (δ0 / 2) ≤ δ0 / 2 := min_le_right _ _
      linarith
  have ht0_barrier : barrier g ε t0 := by
    refine ⟨⟨ht0_pos.le, ht0_le_one⟩, ?_⟩
    intro s hs
    have hs_local : s ∈ Set.Ioc (0 : ℝ) (min 1 (0 + δ0)) := ⟨hs.1, le_trans hs.2 ht0_le_min⟩
    simpa using hδ0_bound s hs_local
  let Sε : Set ℝ := barrierSet g ε
  have hS_nonempty : Sε.Nonempty := ⟨t0, show t0 ∈ Sε from ht0_barrier⟩
  have hS_bdd : BddAbove Sε := ⟨1, fun t ht ↦ ht.1.2⟩
  let t1 : ℝ := sSup Sε
  have ht0_le_t1 : t0 ≤ t1 := by
    exact le_csSup hS_bdd (show t0 ∈ Sε from ht0_barrier)
  have ht1_pos : 0 < t1 := lt_of_lt_of_le ht0_pos ht0_le_t1
  have ht1_le_one : t1 ≤ 1 := by
    refine csSup_le hS_nonempty ?_
    intro t ht
    exact ht.1.2
  have hlt_barrier : ∀ u ∈ Set.Ioo (0 : ℝ) t1, barrier g ε u := by
    intro u hu
    simpa [Sε, t1] using mem_barrier_of_lt_csSup g hS_nonempty hu
  have hlsc_t1 : LowerSemicontinuousOn g.asEReal (Set.Ioc (0 : ℝ) t1) := by
    -- Restrict lower semicontinuity from `]0,1]` to `]0,t₁]`.
    refine hlsc.mono ?_
    intro s hs
    exact ⟨hs.1, le_trans hs.2 ht1_le_one⟩
  have ht1_value :
      g.asEReal t1 ≤ g.asEReal 0 + (((ε * t1 : ℝ)) : EReal) := by
    refine barrier_value_at_endpoint_of_lowerSemicontinuousOn g ht1_pos hlsc_t1 ?_
    intro s hs
    have hs_barrier : barrier g ε s := hlt_barrier s hs
    have hs_value : g.asEReal s ≤ g.asEReal 0 + (((ε * s : ℝ)) : EReal) :=
      hs_barrier.2 s ⟨hs.1, le_rfl⟩
    have hs_mul :
        (((ε * s : ℝ)) : EReal) ≤ (((ε * t1 : ℝ)) : EReal) := by
      exact_mod_cast mul_le_mul_of_nonneg_left hs.2.le hε.le
    have hs_value' :
        g.asEReal 0 + (((ε * s : ℝ)) : EReal) ≤
          g.asEReal 0 + (((ε * t1 : ℝ)) : EReal) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hs_mul (g.asEReal 0)
    exact le_trans hs_value hs_value'
  have ht1_barrier : barrier g ε t1 := by
    refine ⟨⟨ht1_pos.le, ht1_le_one⟩, ?_⟩
    intro s hs
    by_cases hs_lt : s < t1
    · have hs_barrier : barrier g ε s := hlt_barrier s ⟨hs.1, hs_lt⟩
      exact hs_barrier.2 s ⟨hs.1, le_rfl⟩
    · have hs_eq : s = t1 := le_antisymm hs.2 (le_of_not_gt hs_lt)
      simpa [hs_eq] using ht1_value
  have ht1_eq_one : t1 = 1 := by
    by_contra ht1_ne_one
    have ht1_lt_one : t1 < 1 := lt_of_le_of_ne ht1_le_one ht1_ne_one
    obtain ⟨ξ1, hξ1, hξ1_nonpos⟩ := hderiv t1 ⟨ht1_pos.le, ht1_lt_one⟩
    have hξ1_lt : ξ1 < ((ε : ℝ) : EReal) := by
      exact lt_of_le_of_lt hξ1_nonpos (by exact_mod_cast hε)
    obtain ⟨δ1, hδ1_pos, hδ1_bound⟩ :=
      eventually_affine_upper_bound_of_hasRightDerivativeAt_lt g hξ1 hξ1_lt
    let t2 : ℝ := min 1 (t1 + δ1 / 2)
    have ht1_lt_t2 : t1 < t2 := by
      dsimp [t2]
      rw [lt_min_iff]
      constructor
      · exact ht1_lt_one
      · linarith [half_pos hδ1_pos]
    have ht2_le_one : t2 ≤ 1 := by
      dsimp [t2]
      exact min_le_left _ _
    have ht2_le_min : t2 ≤ min 1 (t1 + δ1) := by
      dsimp [t2]
      refine le_min ?_ ?_
      · exact min_le_left _ _
      · have : min 1 (t1 + δ1 / 2) ≤ t1 + δ1 / 2 := min_le_right _ _
        linarith
    have ht2_local :
        ∀ s ∈ Set.Ioc t1 t2,
          g.asEReal s ≤ g.asEReal t1 + (((ε * (s - t1) : ℝ)) : EReal) := by
      intro s hs
      exact hδ1_bound s ⟨hs.1, le_trans hs.2 ht2_le_min⟩
    have ht2_barrier : barrier g ε t2 := by
      exact barrier_push_right_of_local_affine_bound
        g ht1_barrier ht1_pos ht1_lt_t2 ht2_le_one ht2_local
    have ht2_le_t1 : t2 ≤ t1 := by
      exact le_csSup hS_bdd (show t2 ∈ Sε by simpa [Sε] using ht2_barrier)
    exact (not_le_of_gt ht1_lt_t2) ht2_le_t1
  have h1_barrier : barrier g ε 1 := by
    simpa [Sε, t1, ht1_eq_one] using ht1_barrier
  -- Evaluate the barrier at the right endpoint.
  simpa using h1_barrier.2 1 ⟨zero_lt_one, le_rfl⟩

/-- Helper for Proposition 17.27: the scalar core statement on `]0,1]` obtained from the segment
trace. The source-faithful proof is the textbook `S_ε` barrier argument. -/
private theorem right_endpoint_le_left_endpoint_of_nonpos_rightDerivative_on_Ioc
    (g : ℝ → Set.Ioi (⊥ : EReal))
    (hg0 : 0 ∈ effectiveDomain g)
    (hlsc : LowerSemicontinuousOn g.asEReal (Set.Ioc (0 : ℝ) 1))
    (hderiv : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ∃ ξ : EReal, HasRightDerivativeAt g t ξ ∧ ξ ≤ 0) :
    g.asEReal 1 ≤ g.asEReal 0 := by
  have hg0_top : g.asEReal 0 ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hg0)
  have hg0_bot : g.asEReal 0 ≠ ⊥ := ne_of_gt (g 0).2
  have hε_bound :
      ∀ ε > 0, g.asEReal 1 ≤ g.asEReal 0 + ((ε : ℝ) : EReal) :=
    right_endpoint_le_affine_barrier_of_positive g hlsc hderiv
  have hg1_top : g.asEReal 1 ≠ ⊤ := by
    have h1_le : g.asEReal 1 ≤ g.asEReal 0 + ((1 : ℝ) : EReal) := hε_bound 1 zero_lt_one
    exact lt_top_iff_ne_top.mp <|
      lt_of_le_of_lt h1_le (EReal.add_lt_top hg0_top (EReal.coe_ne_top 1))
  have hg1_bot : g.asEReal 1 ≠ ⊥ := ne_of_gt (g 1).2
  have htoReal :
      (g.asEReal 1).toReal ≤ (g.asEReal 0).toReal := by
    by_contra hlt
    have hgap_pos : 0 < ((g.asEReal 1).toReal - (g.asEReal 0).toReal) := by
      exact sub_pos.mpr (lt_of_not_ge hlt)
    have hhalf :
        (g.asEReal 1).toReal ≤
          (g.asEReal 0).toReal + ((g.asEReal 1).toReal - (g.asEReal 0).toReal) / 2 := by
      have hhalf_pos :
          0 < ((g.asEReal 1).toReal - (g.asEReal 0).toReal) / 2 := by
        linarith
      have hε' :
          g.asEReal 1 ≤
            g.asEReal 0 +
              ((((g.asEReal 1).toReal - (g.asEReal 0).toReal) / 2 : ℝ)) := by
        simpa using
          hε_bound (((g.asEReal 1).toReal - (g.asEReal 0).toReal) / 2) hhalf_pos
      have hε'_real :
          (((g.asEReal 1).toReal : ℝ) : EReal) ≤
            (((g.asEReal 0).toReal +
              ((g.asEReal 1).toReal - (g.asEReal 0).toReal) / 2 : ℝ) : EReal) := by
        simpa [EReal.coe_toReal hg1_top hg1_bot, EReal.coe_toReal hg0_top hg0_bot,
          EReal.coe_add] using hε'
      exact_mod_cast hε'_real
    linarith
  -- Convert the real inequality back to `EReal` using finiteness of both endpoint values.
  rw [← EReal.coe_toReal hg1_top hg1_bot, ← EReal.coe_toReal hg0_top hg0_bot]
  exact_mod_cast htoReal

-- Semantic search tool unavailable in this runner; the statement below uses the local segment APIs
-- from `Text_1_0_6` and the directional-derivative owner from `Definition_17_1`.

/-- Proposition 17.27: let `f : H → ]-∞,+∞]`, let `x0 ∈ dom f`, and let `x1 ∈ H` satisfy
`[x0,x1[ ⊆ dom f`. If `f` is lower semicontinuous on `]x0,x1]` and every
`x ∈ [x0,x1[` admits a directional derivative `f'(x; x1 - x0)` with
`f'(x; x1 - x0) ≤ 0`, then `f x1 ≤ f x0`. -/
theorem right_value_le_left_value_of_nonpos_directional_derivative_on_half_open_segment
    (f : H → Set.Ioi (⊥ : EReal)) {x0 x1 : H}
    (hx0 : x0 ∈ effectiveDomain f)
    (hdom : closedOpenSegment x0 x1 ⊆ effectiveDomain f)
    (hlsc : LowerSemicontinuousOn f.asEReal (openClosedSegment x0 x1))
    (hderiv : ∀ x ∈ closedOpenSegment x0 x1,
      ∃ ξ : EReal, HasDirectionalDerivativeAt f x (x1 - x0) ξ ∧ ξ ≤ 0) :
    f.asEReal x1 ≤ f.asEReal x0 := by
  let g : ℝ → Set.Ioi (⊥ : EReal) := fun t ↦ f (AffineMap.lineMap x0 x1 t)
  have hg0 : 0 ∈ effectiveDomain g := by
    -- The left endpoint of the scalar trace is exactly `x₀`.
    simpa [g, mem_effectiveDomain_iff, AffineMap.lineMap_apply_zero] using
      (mem_effectiveDomain_iff.mp hx0)
  have hg_lsc : LowerSemicontinuousOn g.asEReal (Set.Ioc (0 : ℝ) 1) := by
    -- Restrict the ambient lower-semicontinuity to the line parameter.
    simpa [g] using lowerSemicontinuousOn_lineMap_openClosedSegment f hlsc
  have hg_deriv :
      ∀ t ∈ Set.Ico (0 : ℝ) 1,
        ∃ ξ : EReal, HasRightDerivativeAt g t ξ ∧ ξ ≤ 0 := by
    intro t ht
    have ht_seg : AffineMap.lineMap x0 x1 t ∈ closedOpenSegment x0 x1 := by
      -- Parameters in `[0,1[` are exactly the half-open segment points.
      exact mem_closedOpenSegment_iff.mpr ⟨t, ht, rfl⟩
    obtain ⟨ξ, hξ, hξ_nonpos⟩ := hderiv _ ht_seg
    refine ⟨ξ, ?_, hξ_nonpos⟩
    -- Transport the directional derivative on the segment to the scalar right derivative.
    simpa [g] using hasRightDerivativeAt_lineMap_of_hasDirectionalDerivativeAt f hξ
  -- Apply the scalar core theorem to the parameterized segment trace.
  simpa [g, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
    right_endpoint_le_left_endpoint_of_nonpos_rightDerivative_on_Ioc g hg0 hg_lsc hg_deriv

/-- Companion to Proposition 17.27: the same endpoint inequality follows from the stronger
closed-segment lower-semicontinuity hypothesis used by downstream files. -/
theorem apply_right_le_left_of_nonpos_directionalDerivativeOn_segment
    (f : H → Set.Ioi (⊥ : EReal)) {x0 x1 : H}
    (hlsc : LowerSemicontinuousOn f.asEReal (segment ℝ x0 x1))
    (hderiv : ∀ x ∈ closedOpenSegment x0 x1,
      ∃ ξ : EReal, HasDirectionalDerivativeAt f x (x1 - x0) ξ ∧ ξ ≤ 0) :
    f.asEReal x1 ≤ f.asEReal x0 := by
  have hx0_seg : x0 ∈ closedOpenSegment x0 x1 := by
    -- The left endpoint corresponds to the parameter value `0`.
    exact mem_closedOpenSegment_iff.mpr ⟨0, by simp, by simp⟩
  obtain ⟨ξ0, hξ0, -⟩ := hderiv x0 hx0_seg
  have hx0 : x0 ∈ effectiveDomain f := hξ0.1
  have hdom : closedOpenSegment x0 x1 ⊆ effectiveDomain f := by
    intro x hx
    obtain ⟨ξ, hξ, -⟩ := hderiv x hx
    exact hξ.1
  have hsubset : openClosedSegment x0 x1 ⊆ segment ℝ x0 x1 := by
    intro x hx
    rcases mem_openClosedSegment_iff.mp hx with ⟨t, ht, rfl⟩
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩
  have hlsc_half : LowerSemicontinuousOn f.asEReal (openClosedSegment x0 x1) :=
    hlsc.mono hsubset
  -- The stronger closed-segment hypothesis specializes to Proposition 17.27.
  exact right_value_le_left_value_of_nonpos_directional_derivative_on_half_open_segment
    f hx0 hdom hlsc_half hderiv

end ERealFunction
