module

public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Topology_Munkres_2000.Book.Theorem_19_2.Basis
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.WithTopology

public noncomputable section

open scoped Topology

/-- The map `f(t) = (t, 2t, 3t, ...)` into real sequence space. -/
def linearGrowthMap : ℝ → ℕ → ℝ :=
  fun t n ↦ (n + 1 : ℝ) * t

/-- The map `g(t) = (t, t, t, ...)` into real sequence space. -/
def constantSequenceMap : ℝ → ℕ → ℝ :=
  fun t _ ↦ t

/-- The map `h(t) = (t, t / 2, t / 3, ...)` into real sequence space. -/
def reciprocalDecayMap : ℝ → ℕ → ℝ :=
  fun t n ↦ t / (n + 1 : ℝ)

/-- The sequence `wₙ`, with `n` initial zeroes followed by the constant value `n + 1`. -/
def largeTailSequence : ℕ → ℕ → ℝ :=
  fun n i ↦ if i < n then 0 else (n + 1 : ℝ)

/-- The sequence `xₙ`, with `n` initial zeroes followed by the constant value `1 / (n + 1)`. -/
def smallTailSequence : ℕ → ℕ → ℝ :=
  fun n i ↦ if i < n then 0 else 1 / (n + 1 : ℝ)

/-- The sequence `yₙ`, equal to `1 / (n + 1)` through coordinate `n` and zero thereafter. -/
def growingSupportSequence : ℕ → ℕ → ℝ :=
  fun n i ↦ if i ≤ n then 1 / (n + 1 : ℝ) else 0

/-- The sequence `zₙ`, equal to `1 / (n + 1)` in its first two coordinates and zero elsewhere. -/
def fixedSupportSequence : ℕ → ℕ → ℝ :=
  fun n i ↦ if i < 2 then 1 / (n + 1 : ℝ) else 0

/-- Helper for Exercise 20.4: uniformly bounded scalar coefficients define a continuous map
into real sequence space with the uniform topology. -/
lemma continuous_uniform_scalarSequence_of_bound (a : ℕ → ℝ) (C : NNReal)
    (ha : ∀ n, |a n| ≤ C) :
    Continuous[_, UniformMetric.topology ℕ] (fun t n ↦ a n * t) := by
  -- The uniform distance is controlled coordinatewise by the common coefficient bound.
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  have hLipschitz : LipschitzWith C (fun t n ↦ a n * t) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [UniformMetric.dist_eq]
    refine ciSup_le fun n ↦ ?_
    calc
      min (dist (a n * x) (a n * y)) 1 ≤ dist (a n * x) (a n * y) := min_le_left _ _
      _ = |a n| * dist x y := by
        rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
      _ ≤ C * dist x y := mul_le_mul_of_nonneg_right (ha n) dist_nonneg
      _ = (C : ℝ) * dist x y := rfl
  exact hLipschitz.continuous

/-- Helper for Exercise 20.4: a common coordinatewise distance bound tending to zero implies
uniform convergence to the zero sequence. -/
lemma tendsto_uniform_of_pointwise_dist_le (u : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hb0 : ∀ n, 0 ≤ b n) (hb : Filter.Tendsto b Filter.atTop (nhds 0))
    (hu : ∀ n i, dist (u n i) 0 ≤ b n) :
    Filter.Tendsto (UniformRealSequence.ofSequence ∘ u) Filter.atTop
      (nhds (UniformRealSequence.ofSequence 0)) := by
  -- First prove convergence in the explicit uniform metric.
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  have hraw : Filter.Tendsto u Filter.atTop
      (@nhds (ℕ → ℝ) (UniformMetric.topology ℕ) 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hb' : ∀ᶠ n in Filter.atTop, dist (b n) 0 < ε :=
      (Metric.tendsto_nhds.mp hb) ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hb'
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [UniformMetric.dist_eq]
    have hsup : (⨆ i, min (dist (u n i) ((0 : ℕ → ℝ) i)) 1) ≤ b n := by
      refine ciSup_le fun i ↦ ?_
      simpa only [Pi.zero_apply] using
        (min_le_left (dist (u n i) 0) 1).trans (hu n i)
    exact hsup.trans_lt (by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (hb0 n)] using hN n hn)
  -- Transport the metric convergence through the topology wrapper.
  have htop := @Continuous.tendsto (ℕ → ℝ) UniformRealSequence
    (UniformMetric.topology ℕ) inferInstance
    (WithTopology.toTopology (UniformMetric.topology ℕ))
    (WithTopology.continuous_toTopology (UniformMetric.topology ℕ)) 0
  rw [show (UniformRealSequence.ofSequence ∘ u) =
    (WithTopology.toTopology (UniformMetric.topology ℕ) ∘ u) by
      funext n
      exact UniformRealSequence.ofSequence_eq_toTopology (u n)]
  rw [UniformRealSequence.ofSequence_eq_toTopology]
  exact htop.comp hraw

/-- Helper for Exercise 20.4: a sequence whose diagonal coordinates stay nonzero cannot
converge to zero in the box topology. -/
lemma not_tendsto_box_of_diagonal_ne_zero (u : ℕ → ℕ → ℝ)
    (hu : ∀ n, u n n ≠ 0) :
    ¬ Filter.Tendsto (BoxRealSequence.ofSequence ∘ u) Filter.atTop
      (nhds (BoxRealSequence.ofSequence 0)) := by
  -- Use a coordinate box whose `i`th radius is half the nonzero diagonal value.
  intro h
  let U : ℕ → Set ℝ := fun i ↦ Set.Ioo (-(|u i i| / 2)) (|u i i| / 2)
  have hUopen : ∀ i, IsOpen (U i) := fun i ↦ isOpen_Ioo
  have hzero : (0 : ℕ → ℝ) ∈ Set.pi Set.univ U := by
    intro i hi
    simp only [Pi.zero_apply, U, Set.mem_Ioo]
    have habs_pos : 0 < |u i i| := abs_pos.mpr (hu i)
    have hpos : 0 < |u i i| / 2 := div_pos habs_pos (by norm_num)
    exact ⟨neg_lt_zero.mpr hpos, hpos⟩
  letI : TopologicalSpace (ℕ → ℝ) := Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)
  have hbox : Set.pi Set.univ U ∈ nhds (0 : ℕ → ℝ) :=
    @IsOpen.mem_nhds (ℕ → ℝ) inferInstance (0 : ℕ → ℝ) (Set.pi Set.univ U)
      (Pi.isOpen_box U hUopen) hzero
  have heventual : ∀ᶠ n in Filter.atTop, u n ∈ Set.pi Set.univ U := by
    have hraw : Filter.Tendsto u Filter.atTop
        (@nhds (ℕ → ℝ) (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) 0) := by
      have hforget :=
        (@Continuous.tendsto BoxRealSequence (ℕ → ℝ) inferInstance
          (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))
          (WithTopology.ofTopology (t := Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)))
          (WithTopology.continuous_ofTopology
            (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)))
          (BoxRealSequence.ofSequence 0)).comp h
      rw [show (WithTopology.ofTopology ∘ BoxRealSequence.ofSequence ∘ u) = u by
        funext n
        rw [Function.comp_apply, Function.comp_apply,
          BoxRealSequence.ofSequence_eq_toTopology]
        ] at hforget
      rw [BoxRealSequence.ofSequence_eq_toTopology,
        WithTopology.ofTopology_toTopology] at hforget
      exact hforget
    exact hraw.eventually hbox
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventual
  have hdiag := hN N le_rfl N (Set.mem_univ N)
  simp only [U, Set.mem_Ioo] at hdiag
  have habs_lt : |u N N| < |u N N| / 2 := (abs_lt).2 hdiag
  have habs_pos : 0 < |u N N| := abs_pos.mpr (hu N)
  linarith

/-- Helper for Exercise 20.4: sequences with one fixed finite support converge in the box
topology when every supported coordinate converges to zero. -/
lemma tendsto_box_of_finite_support (u : ℕ → ℕ → ℝ) (s : Finset ℕ)
    (hsupport : ∀ n i, i ∉ s → u n i = 0)
    (hcoord : ∀ i ∈ s, Filter.Tendsto (fun n ↦ u n i) Filter.atTop (nhds 0)) :
    Filter.Tendsto (BoxRealSequence.ofSequence ∘ u) Filter.atTop
      (nhds (BoxRealSequence.ofSequence 0)) := by
  -- Prove convergence against a basic coordinate box, reducing to finitely many coordinates.
  letI : TopologicalSpace (ℕ → ℝ) := Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)
  have hraw : Filter.Tendsto u Filter.atTop
      (nhds (0 : ℕ → ℝ)) := by
    intro V hV
    let hbasis := Pi.isTopologicalBasis_box (X := fun _ : ℕ ↦ ℝ)
      (fun _ : ℕ ↦ TopologicalSpace.isTopologicalBasis_opens)
    obtain ⟨T, hTbasis, hzeroT, hTV⟩ := hbasis.mem_nhds_iff.mp hV
    obtain ⟨U, hUopen, hTU⟩ := hTbasis
    subst T
    have hcoord_eventual : ∀ i ∈ s, ∀ᶠ n in Filter.atTop, u n i ∈ U i := by
      intro i hi
      have hUi : U i ∈ nhds 0 :=
        @IsOpen.mem_nhds ℝ inferInstance 0 (U i) (hUopen i)
          (hzeroT i (Set.mem_univ i))
      exact (hcoord i hi).eventually hUi
    have hs_eventual : ∀ᶠ n in Filter.atTop, ∀ i ∈ s, u n i ∈ U i := by
      exact (Finset.eventually_all s).2 hcoord_eventual
    exact hs_eventual.mono fun n hn ↦ hTV fun i hi ↦ by
      by_cases his : i ∈ s
      · exact hn i his
      · rw [hsupport n i his]
        exact hzeroT i hi
  -- Transport the raw box convergence through the public wrapper computation rule.
  have hwrap :=
    (@Continuous.tendsto (ℕ → ℝ) BoxRealSequence
      (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) inferInstance
      (WithTopology.toTopology (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)))
      (WithTopology.continuous_toTopology
        (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))) 0).comp hraw
  rw [show (WithTopology.toTopology (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) ∘ u) =
      BoxRealSequence.ofSequence ∘ u by
    funext n
    exact (BoxRealSequence.ofSequence_eq_toTopology (u n)).symm] at hwrap
  rw [← BoxRealSequence.ofSequence_eq_toTopology] at hwrap
  exact hwrap

/-- Helper for Exercise 20.4: a path to zero with nonzero diagonal images obstructs
continuity into the box topology. -/
lemma notContinuous_box_of_diagonal_path (F : ℝ → ℕ → ℝ) (r : ℕ → ℝ)
    (hr : Filter.Tendsto r Filter.atTop (nhds 0)) (hzero : F 0 = 0)
    (hdiag : ∀ n, F (r n) n ≠ 0) :
    ¬ Continuous[_, Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)] F := by
  -- Continuity would send the scalar path to a box-convergent sequence family.
  intro hF
  have hraw := (@Continuous.tendsto ℝ (ℕ → ℝ) inferInstance
    (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) F hF 0).comp hr
  rw [hzero] at hraw
  have hwrap :=
    (@Continuous.tendsto (ℕ → ℝ) BoxRealSequence
      (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) inferInstance
      (WithTopology.toTopology (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)))
      (WithTopology.continuous_toTopology
        (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))) 0).comp hraw
  have hwrapped : Filter.Tendsto (BoxRealSequence.ofSequence ∘ fun n ↦ F (r n))
      Filter.atTop (nhds (BoxRealSequence.ofSequence 0)) := by
    rw [show WithTopology.toTopology (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) ∘ F ∘ r =
        BoxRealSequence.ofSequence ∘ fun n ↦ F (r n) by
      funext n
      exact (BoxRealSequence.ofSequence_eq_toTopology (F (r n))).symm] at hwrap
    rw [← BoxRealSequence.ofSequence_eq_toTopology] at hwrap
    exact hwrap
  exact not_tendsto_box_of_diagonal_ne_zero (fun n ↦ F (r n)) hdiag hwrapped

/-- Product-topology conclusion for Exercise 20.4 (1): `linearGrowthMap` is continuous. -/
theorem continuous_linearGrowthMap_product :
    Continuous linearGrowthMap := by
  -- Product continuity reduces to continuity of each scalar coordinate.
  apply continuous_pi
  intro n
  unfold linearGrowthMap
  fun_prop

/-- Uniform-topology conclusion for Exercise 20.4 (2): `linearGrowthMap` is not continuous. -/
theorem notContinuous_linearGrowthMap_uniform :
    ¬ Continuous[_, UniformMetric.topology ℕ] linearGrowthMap := by
  -- Along `tₙ = 1/(n+1)`, the diagonal output remains exactly one.
  intro h
  have hinput : Filter.Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hout := (@Continuous.tendsto ℝ (ℕ → ℝ) inferInstance (UniformMetric.topology ℕ)
    linearGrowthMap h 0).comp hinput
  have hzero : linearGrowthMap 0 = 0 := by
    funext i
    simp only [linearGrowthMap, mul_zero, Pi.zero_apply]
  rw [hzero] at hout
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  have hout' : Filter.Tendsto
      (fun n : ℕ ↦ linearGrowthMap (1 / (n + 1 : ℝ))) Filter.atTop
      (@nhds (ℕ → ℝ) (UniformMetric.topology ℕ) 0) := by
    exact hout
  rw [Metric.tendsto_atTop] at hout'
  obtain ⟨N, hN⟩ := hout' (1 / 2) (by norm_num)
  have hdist := hN N le_rfl
  rw [UniformMetric.dist_eq] at hdist
  have hle : (1 : ℝ) ≤ ⨆ i, min
      (dist (linearGrowthMap (1 / (N + 1 : ℝ)) i) ((0 : ℕ → ℝ) i)) 1 := by
    refine le_ciSup_of_le (bddAbove_def.2 ⟨1, fun z hz ↦ ?_⟩) N ?_
    · obtain ⟨i, rfl⟩ := hz
      exact min_le_right _ _
    · have hcoord : linearGrowthMap (1 / (N + 1 : ℝ)) N = 1 := by
        unfold linearGrowthMap
        field_simp
      rw [hcoord, Pi.zero_apply, dist_zero_right, Real.norm_eq_abs, abs_one, min_self]
  linarith

/-- Exercise 20.4 (3): `linearGrowthMap` is not continuous in the box topology. -/
theorem notContinuous_linearGrowthMap_box :
    ¬ Continuous[_, Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)]
      linearGrowthMap := by
  -- Along the reciprocal path, the diagonal coordinate is exactly one.
  apply notContinuous_box_of_diagonal_path linearGrowthMap
    (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) tendsto_one_div_add_atTop_nhds_zero_nat
  · funext i
    simp only [linearGrowthMap, mul_zero, Pi.zero_apply]
  · intro n
    have hcoord : linearGrowthMap (1 / (n + 1 : ℝ)) n = 1 := by
      unfold linearGrowthMap
      field_simp
    rw [hcoord]
    norm_num

/-- Product-topology conclusion for Exercise 20.4 (4): `constantSequenceMap` is continuous. -/
theorem continuous_constantSequenceMap_product :
    Continuous constantSequenceMap := by
  -- Every coordinate is the identity map.
  apply continuous_pi
  intro n
  unfold constantSequenceMap
  exact continuous_id

/-- Uniform-topology conclusion for Exercise 20.4 (5): `constantSequenceMap` is continuous. -/
theorem continuous_constantSequenceMap_uniform :
    Continuous[_, UniformMetric.topology ℕ] constantSequenceMap := by
  -- The constant coefficient family is uniformly bounded by one.
  unfold constantSequenceMap
  simpa only [one_mul] using
    continuous_uniform_scalarSequence_of_bound (fun _ : ℕ ↦ (1 : ℝ)) 1 (by simp)

/-- Box-topology conclusion for Exercise 20.4 (6): `constantSequenceMap` is not continuous. -/
theorem notContinuous_constantSequenceMap_box :
    ¬ Continuous[_, Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)]
      constantSequenceMap := by
  -- The reciprocal path has a positive diagonal coordinate under the constant map.
  apply notContinuous_box_of_diagonal_path constantSequenceMap
    (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) tendsto_one_div_add_atTop_nhds_zero_nat
  · funext i
    simp only [constantSequenceMap, Pi.zero_apply]
  · intro n
    simp only [constantSequenceMap]
    positivity

/-- Product-topology conclusion for Exercise 20.4 (7): `reciprocalDecayMap` is continuous. -/
theorem continuous_reciprocalDecayMap_product :
    Continuous reciprocalDecayMap := by
  -- Each coordinate is division by a fixed nonzero real number.
  apply continuous_pi
  intro n
  unfold reciprocalDecayMap
  fun_prop

/-- Uniform-topology conclusion for Exercise 20.4 (8): `reciprocalDecayMap` is continuous. -/
theorem continuous_reciprocalDecayMap_uniform :
    Continuous[_, UniformMetric.topology ℕ] reciprocalDecayMap := by
  -- Reciprocal coefficients are uniformly bounded by one.
  have hbound : ∀ n : ℕ, |(1 / (n + 1 : ℝ))| ≤ (1 : NNReal) := by
    intro n
    rw [abs_of_pos (by positivity)]
    exact (div_le_iff₀ (by positivity)).2 (by norm_num)
  unfold reciprocalDecayMap
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    continuous_uniform_scalarSequence_of_bound (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) 1 hbound

/-- Box-topology conclusion for Exercise 20.4 (9): `reciprocalDecayMap` is not continuous. -/
theorem notContinuous_reciprocalDecayMap_box :
    ¬ Continuous[_, Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)]
      reciprocalDecayMap := by
  -- The reciprocal path produces a positive square reciprocal on the diagonal.
  apply notContinuous_box_of_diagonal_path reciprocalDecayMap
    (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) tendsto_one_div_add_atTop_nhds_zero_nat
  · funext i
    simp only [reciprocalDecayMap, zero_div, Pi.zero_apply]
  · intro n
    simp only [reciprocalDecayMap]
    positivity

/-- Product-topology conclusion for Exercise 20.4 (10): `largeTailSequence` tends to zero. -/
theorem largeTailSequence_tendsto_product :
    Filter.Tendsto largeTailSequence Filter.atTop (nhds 0) := by
  -- Each fixed coordinate is eventually in the initial zero segment.
  rw [tendsto_pi_nhds]
  intro i
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop i] with n hn
  simp only [largeTailSequence, if_pos hn, Pi.zero_apply]

/-- Uniform-topology conclusion for Exercise 20.4 (11): `largeTailSequence` does not tend
to zero. -/
theorem largeTailSequence_not_tendsto_uniform :
    ¬ Filter.Tendsto
      (UniformRealSequence.ofSequence ∘ largeTailSequence)
      Filter.atTop (nhds (UniformRealSequence.ofSequence 0)) := by
  -- Forget the wrapper and contradict convergence using coordinate `n` at stage `n`.
  intro h
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  have hforget :=
    (@Continuous.tendsto UniformRealSequence (ℕ → ℝ) inferInstance
      (UniformMetric.topology ℕ)
      (WithTopology.ofTopology (t := UniformMetric.topology ℕ))
      (WithTopology.continuous_ofTopology (UniformMetric.topology ℕ))
      (UniformRealSequence.ofSequence 0)).comp h
  have hraw : Filter.Tendsto largeTailSequence Filter.atTop
      (@nhds (ℕ → ℝ) (UniformMetric.topology ℕ) 0) := by
    rw [show (WithTopology.ofTopology ∘ UniformRealSequence.ofSequence ∘
        largeTailSequence) = largeTailSequence by
      funext n
      rw [Function.comp_apply, Function.comp_apply,
        UniformRealSequence.ofSequence_eq_toTopology]] at hforget
    rw [UniformRealSequence.ofSequence_eq_toTopology,
      WithTopology.ofTopology_toTopology] at hforget
    exact hforget
  rw [Metric.tendsto_atTop] at hraw
  obtain ⟨N, hN⟩ := hraw (1 / 2) (by norm_num)
  have hdist := hN N le_rfl
  rw [UniformMetric.dist_eq] at hdist
  have hle : (1 : ℝ) ≤ ⨆ i, min
      (dist (largeTailSequence N i) ((0 : ℕ → ℝ) i)) 1 := by
    refine le_ciSup_of_le (bddAbove_def.2 ⟨1, fun z hz ↦ ?_⟩) N ?_
    · obtain ⟨i, rfl⟩ := hz
      exact min_le_right _ _
    · rw [largeTailSequence, if_neg (Nat.lt_irrefl N), Pi.zero_apply,
        dist_zero_right, Real.norm_eq_abs, min_eq_right]
      rw [abs_of_nonneg (by positivity)]
      norm_num
  linarith

/-- Box-topology conclusion for Exercise 20.4 (12): `largeTailSequence` does not tend to zero. -/
theorem largeTailSequence_not_tendsto_box :
    ¬ Filter.Tendsto
      (BoxRealSequence.ofSequence ∘ largeTailSequence)
      Filter.atTop (nhds (BoxRealSequence.ofSequence 0)) := by
  -- The diagonal coordinate is always positive.
  apply not_tendsto_box_of_diagonal_ne_zero largeTailSequence
  intro n
  simp only [largeTailSequence, lt_self_iff_false, if_false]
  positivity

/-- Product-topology conclusion for Exercise 20.4 (13): `smallTailSequence` tends to zero. -/
theorem smallTailSequence_tendsto_product :
    Filter.Tendsto smallTailSequence Filter.atTop (nhds 0) := by
  -- Each fixed coordinate is eventually in the initial zero segment.
  rw [tendsto_pi_nhds]
  intro i
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop i] with n hn
  simp only [smallTailSequence, if_pos hn, Pi.zero_apply]

/-- Uniform-topology conclusion for Exercise 20.4 (14): `smallTailSequence` tends to zero. -/
theorem smallTailSequence_tendsto_uniform :
    Filter.Tendsto
      (UniformRealSequence.ofSequence ∘ smallTailSequence)
      Filter.atTop (nhds (UniformRealSequence.ofSequence 0)) := by
  -- Every coordinate is bounded by the reciprocal scalar.
  apply tendsto_uniform_of_pointwise_dist_le smallTailSequence
    (fun n : ℕ ↦ 1 / (n + 1 : ℝ))
  · intro n
    positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n i
    by_cases h : i < n
    · simp only [smallTailSequence, if_pos h, dist_self]
      positivity
    · simp only [smallTailSequence, if_neg h, dist_zero_right, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]

/-- Box-topology conclusion for Exercise 20.4 (15): `smallTailSequence` does not tend to zero. -/
theorem smallTailSequence_not_tendsto_box :
    ¬ Filter.Tendsto
      (BoxRealSequence.ofSequence ∘ smallTailSequence)
      Filter.atTop (nhds (BoxRealSequence.ofSequence 0)) := by
  -- The diagonal reciprocal coordinate is always positive.
  apply not_tendsto_box_of_diagonal_ne_zero smallTailSequence
  intro n
  simp only [smallTailSequence, lt_self_iff_false, if_false]
  positivity

/-- Product-topology conclusion for Exercise 20.4 (16): `growingSupportSequence` tends to zero. -/
theorem growingSupportSequence_tendsto_product :
    Filter.Tendsto growingSupportSequence Filter.atTop (nhds 0) := by
  -- Each fixed coordinate eventually equals the reciprocal scalar.
  rw [tendsto_pi_nhds]
  intro i
  apply Filter.Tendsto.congr' _ tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [Filter.eventually_ge_atTop i] with n hn
  simp only [growingSupportSequence, if_pos hn]

/-- Uniform-topology conclusion for Exercise 20.4 (17): `growingSupportSequence` tends to zero. -/
theorem growingSupportSequence_tendsto_uniform :
    Filter.Tendsto
      (UniformRealSequence.ofSequence ∘ growingSupportSequence)
      Filter.atTop (nhds (UniformRealSequence.ofSequence 0)) := by
  -- Every coordinate is bounded by the reciprocal scalar.
  apply tendsto_uniform_of_pointwise_dist_le growingSupportSequence
    (fun n : ℕ ↦ 1 / (n + 1 : ℝ))
  · intro n
    positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n i
    by_cases h : i ≤ n
    · simp only [growingSupportSequence, if_pos h, dist_zero_right, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
    · simp only [growingSupportSequence, if_neg h, dist_self]
      positivity

/-- Box-topology conclusion for Exercise 20.4 (18): `growingSupportSequence` does not tend
to zero. -/
theorem growingSupportSequence_not_tendsto_box :
    ¬ Filter.Tendsto
      (BoxRealSequence.ofSequence ∘ growingSupportSequence)
      Filter.atTop (nhds (BoxRealSequence.ofSequence 0)) := by
  -- The diagonal reciprocal coordinate is always positive.
  apply not_tendsto_box_of_diagonal_ne_zero growingSupportSequence
  intro n
  simp only [growingSupportSequence, le_refl, if_true]
  positivity

/-- Product-topology conclusion for Exercise 20.4 (19): `fixedSupportSequence` tends to zero. -/
theorem fixedSupportSequence_tendsto_product :
    Filter.Tendsto fixedSupportSequence Filter.atTop (nhds 0) := by
  -- Supported coordinates follow the reciprocal limit; all other coordinates are zero.
  rw [tendsto_pi_nhds]
  intro i
  change Filter.Tendsto (fun n ↦ fixedSupportSequence n i) Filter.atTop (nhds 0)
  by_cases hi : i < 2
  · simpa only [fixedSupportSequence, if_pos hi] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0))
  · simpa only [fixedSupportSequence, if_neg hi] using tendsto_const_nhds

/-- Uniform-topology conclusion for Exercise 20.4 (20): `fixedSupportSequence` tends to zero. -/
theorem fixedSupportSequence_tendsto_uniform :
    Filter.Tendsto
      (UniformRealSequence.ofSequence ∘ fixedSupportSequence)
      Filter.atTop (nhds (UniformRealSequence.ofSequence 0)) := by
  -- Every coordinate is bounded by the reciprocal scalar.
  apply tendsto_uniform_of_pointwise_dist_le fixedSupportSequence
    (fun n : ℕ ↦ 1 / (n + 1 : ℝ))
  · intro n
    positivity
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n i
    by_cases h : i < 2
    · simp only [fixedSupportSequence, if_pos h, dist_zero_right, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
    · simp only [fixedSupportSequence, if_neg h, dist_self]
      positivity

/-- Box-topology conclusion for Exercise 20.4 (21): `fixedSupportSequence` tends to zero. -/
theorem fixedSupportSequence_tendsto_box :
    Filter.Tendsto
      (BoxRealSequence.ofSequence ∘ fixedSupportSequence)
      Filter.atTop (nhds (BoxRealSequence.ofSequence 0)) := by
  -- The support is fixed to the first two coordinates, both following the reciprocal limit.
  apply tendsto_box_of_finite_support fixedSupportSequence {0, 1}
  · intro n i hi
    have hilarge : ¬ i < 2 := by
      intro hsmall
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      omega
    simp only [fixedSupportSequence, if_neg hilarge]
  · intro i hi
    have hismall : i < 2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl <;> norm_num
    simpa only [fixedSupportSequence, if_pos hismall] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0))
