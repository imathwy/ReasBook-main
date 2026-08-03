module

public import Topology_Munkres_2000.Book.Definition_17_4
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Basic

public section

open Filter Set Topology

/-- Helper for Example 17.8: a nonempty real open interval has its closed interval as
its derived set. -/
lemma derivedSet_Ioo_real {a b : ℝ} (hab : a < b) :
    derivedSet (Ioo a b) = Icc a b := by
  -- Two distinct trisection points make the interval nontrivial.
  have hnontrivial : (Ioo a b).Nontrivial := by
    refine ⟨(2 * a + b) / 3, ?_, (a + 2 * b) / 3, ?_, ?_⟩
    · constructor <;> linarith
    · constructor <;> linarith
    · linarith
  -- A nontrivial preconnected interval is preperfect, so its closure is perfect.
  have hperfect : Perfect (closure (Ioo a b)) :=
    (isPreconnected_Ioo.preperfect_of_nontrivial hnontrivial).perfect_closure
  have heq : closure (Ioo a b) = derivedSet (closure (Ioo a b)) :=
    perfect_iff_eq_derivedSet.mp hperfect
  -- Passing the derived set through closure leaves the closed interval.
  rw [derivedSet_closure] at heq
  rw [← heq, closure_Ioo hab.ne]

/-- Helper for Example 17.8: a dense subset of a T₁ space without isolated points has
the whole space as its derived set. -/
lemma Dense.derivedSet_eq_univ {X : Type*} [TopologicalSpace X] [T1Space X]
    [∀ x : X, NeBot (𝓝[≠] x)] {s : Set X} (hs : Dense s) :
    derivedSet s = univ := by
  -- Deleting the candidate point preserves density, hence its closure is universal.
  ext x
  simp only [mem_univ, iff_true, mem_derivedSet_iff_mem_closure_diff_singleton]
  rw [(hs.sdiff_singleton x).closure_eq]
  exact mem_univ x

/-- Helper for Example 17.8: a closed discrete subset of a T₁ space has no limit points. -/
lemma derivedSet_eq_empty_of_isClosed_isDiscrete {X : Type*} [TopologicalSpace X]
    [T1Space X] {s : Set X} (hs : IsClosed s) (hdisc : IsDiscrete s) :
    derivedSet s = ∅ := by
  -- At points of the set, use a discrete neighborhood; outside, use the open complement.
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [mem_derivedSet, accPt_iff_nhds] at hx
  by_cases hxs : x ∈ s
  · obtain ⟨U, hUopen, hU⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hdisc x hxs
    have hxU : x ∈ U := by
      have hxinter : x ∈ U ∩ s := by
        rw [hU]
        exact mem_singleton x
      exact hxinter.1
    obtain ⟨y, hy, hyx⟩ := hx U (hUopen.mem_nhds hxU)
    have hy_eq : y = x := by
      rw [hU] at hy
      exact hy
    exact hyx hy_eq
  · obtain ⟨y, hy, -⟩ := hx sᶜ (hs.isOpen_compl.mem_nhds hxs)
    exact hy.1 hy.2

/-- Helper for Example 17.8: every nonzero real has an open neighborhood meeting the
positive-reciprocal range only possibly at that real. -/
lemma exists_isOpen_inter_reciprocalRange_subset (x : ℝ) (hx : x ≠ 0) :
    ∃ U, IsOpen U ∧ x ∈ U ∧
      U ∩ range (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) ⊆ {x} := by
  classical
  let ε : ℝ := |x| / 2
  have htwo : (0 : ℝ) < 2 := by
    norm_num
  have hε : 0 < ε := div_pos (abs_pos.mpr hx) htwo
  have hdist : dist x 0 = ε + ε := by
    simp [ε, Real.dist_eq]
  -- Convergence places all sufficiently late reciprocal terms in the ball around zero.
  have htail_eventually : ∀ᶠ n : ℕ in atTop,
      1 / ((n : ℝ) + 1) ∈ Metric.ball 0 ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) (Metric.ball_mem_nhds 0 hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail_eventually
  let F : Set ℝ :=
    (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) '' (Finset.range N : Set ℕ) \ {x}
  have hFfinite : F.Finite := by
    exact ((Finset.finite_toSet (Finset.range N)).image _).sdiff
  -- Delete the finitely many early values other than the center from the ball around `x`.
  refine ⟨Metric.ball x ε \ F, Metric.isOpen_ball.sdiff hFfinite.isClosed, ?_, ?_⟩
  · refine ⟨Metric.mem_ball_self hε, ?_⟩
    simp [F]
  · rintro y ⟨⟨hyball, hyF⟩, ⟨n, rfl⟩⟩
    by_cases hn : n < N
    · by_contra hne
      apply hyF
      refine ⟨?_, hne⟩
      have hn_mem : n ∈ (Finset.range N : Set ℕ) := by
        simpa using hn
      exact ⟨n, hn_mem, rfl⟩
    · have htail : 1 / ((n : ℝ) + 1) ∈ Metric.ball 0 ε :=
        hN n (Nat.le_of_not_gt hn)
      have hdisj : Disjoint (Metric.ball x ε) (Metric.ball 0 ε) :=
        Metric.ball_disjoint_ball hdist.ge
      exact (hdisj.le_bot ⟨hyball, htail⟩).elim

/-- Example 17.8 (1): The limit points of `(0, 1]` are exactly the points of `[0, 1]`. -/
theorem derivedSet_Ioc_zero_one :
    derivedSet (Ioc (0 : ℝ) 1) = Icc 0 1 := by
  -- The derived set lies in the closure, while the contained open interval supplies
  -- every point of the closed interval as a limit point.
  have hzero_ne_one : (0 : ℝ) ≠ 1 := by
    norm_num
  have hzero_lt_one : (0 : ℝ) < 1 := by
    norm_num
  apply Set.Subset.antisymm
  · intro x hx
    have hxclosure := derivedSet_subset_closure (Ioc (0 : ℝ) 1) hx
    rwa [closure_Ioc hzero_ne_one] at hxclosure
  · rw [← derivedSet_Ioo_real hzero_lt_one]
    exact derivedSet_mono _ _ Ioo_subset_Ioc_self

/-- Companion for Example 17.8 (2): Zero is the unique limit point of the positive-reciprocal
sequence. -/
theorem derivedSet_one_div_posNat :
    derivedSet (range (fun n : ℕ ↦ 1 / ((n : ℝ) + 1))) = ({0} : Set ℝ) := by
  -- The isolation helper excludes every nonzero point from the derived set.
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hne
    obtain ⟨U, hUopen, hxU, hU⟩ :=
      exists_isOpen_inter_reciprocalRange_subset x hne
    rw [mem_derivedSet, accPt_iff_nhds] at hx
    obtain ⟨y, hy, hyx⟩ := hx U (hUopen.mem_nhds hxU)
    exact hyx (hU hy)
  · intro x hx
    rw [mem_singleton_iff] at hx
    subst x
    -- The convergent reciprocal sequence witnesses that zero is in the punctured closure.
    rw [mem_derivedSet_iff_mem_closure_diff_singleton]
    refine mem_closure_of_tendsto
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ?_
    filter_upwards with n
    refine ⟨⟨n, rfl⟩, ?_⟩
    have hdenom : (n : ℝ) + 1 ≠ 0 := by
      positivity
    exact one_div_ne_zero hdenom

/-- Companion for Example 17.8 (3): Away from zero, some open neighborhood meets the
positive-reciprocal sequence only possibly at its center. -/
theorem exists_isOpen_inter_one_div_posNat_subset (x : ℝ) (hx : x ≠ 0) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ∩ range (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) ⊆ {x} := by
  -- This is the source-facing specialization of the reciprocal isolation interface.
  exact exists_isOpen_inter_reciprocalRange_subset x hx

/-- Companion for Example 17.8 (4): The limit points of `{0} ∪ (1, 2)` are exactly the points
of `[1, 2]`. -/
theorem derivedSet_singleton_zero_union_Ioo_one_two :
    derivedSet (({0} : Set ℝ) ∪ Ioo 1 2) = Icc 1 2 := by
  -- Derived sets distribute over unions; the singleton contributes no limit points.
  have hone_lt_two : (1 : ℝ) < 2 := by
    norm_num
  rw [derivedSet_union]
  have hsingle : derivedSet ({0} : Set ℝ) = ∅ :=
    derivedSet_eq_empty_of_isClosed_isDiscrete
      isClosed_singleton (Set.toFinite {0}).isDiscrete
  rw [hsingle, empty_union, derivedSet_Ioo_real hone_lt_two]

/-- Companion for Example 17.8 (5): Every real number is a limit point of the rational numbers. -/
theorem derivedSet_ratCast :
    derivedSet (range (fun q : ℚ ↦ (q : ℝ))) = univ := by
  -- Rational density remains after deleting any candidate real point.
  exact Rat.denseRange_cast.derivedSet_eq_univ

/-- Companion for Example 17.8 (6): The positive integers have no limit points in `ℝ`. -/
theorem derivedSet_posNatCast :
    derivedSet (range (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ))) = ∅ := by
  let f : ℕ → ℝ := fun n ↦ ((n + 1 : ℕ) : ℝ)
  -- Distinct positive integers stay at least unit distance apart.
  have hpair : Pairwise fun m n : ℕ ↦ (1 : ℝ) ≤ dist (f m) (f n) := by
    intro m n hmn
    exact_mod_cast Nat.pairwise_one_le_dist (Nat.succ_ne_succ_iff.mpr hmn)
  have hemb : IsClosedEmbedding f :=
    Metric.isClosedEmbedding_of_pairwise_le_dist zero_lt_one hpair
  -- The uniformly separated range is both closed and discrete.
  exact derivedSet_eq_empty_of_isClosed_isDiscrete
    hemb.isClosed_range hemb.isInducing.isDiscrete_range

/-- Companion for Example 17.8 (7): Every nonnegative real number is a limit point of the
positive real numbers. -/
theorem Ici_zero_subset_derivedSet_Ioi_zero :
    Ici (0 : ℝ) ⊆ derivedSet (Ioi 0) := by
  -- The open ray is nontrivial and preconnected, so its closure is perfect.
  have hnontrivial : (Ioi (0 : ℝ)).Nontrivial := by
    refine ⟨1, ?_, 2, ?_, ?_⟩
    · norm_num
    · norm_num
    · norm_num
  have hperfect : Perfect (closure (Ioi (0 : ℝ))) :=
    (isPreconnected_Ioi.preperfect_of_nontrivial hnontrivial).perfect_closure
  have heq : closure (Ioi (0 : ℝ)) = derivedSet (closure (Ioi 0)) :=
    perfect_iff_eq_derivedSet.mp hperfect
  -- Derived sets are unchanged by closure, whose value is the nonnegative ray.
  rw [derivedSet_closure] at heq
  rw [← heq, closure_Ioi]
