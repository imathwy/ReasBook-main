module

public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Topology_Munkres_2000.Book.Exercise_19_8.Coordinatewise
public import Mathlib.Topology.WithTopology

public section

open Filter

/-- Helper for Exercise 25.2: bounded coordinatewise difference is reflexive. -/
private theorem isBounded_range_self_sub (x : ℕ → ℝ) :
    Bornology.IsBounded (Set.range (x - x)) := by
  -- Pointwise subtraction reduces the range to the singleton `{0}`.
  simp

/-- Helper for Exercise 25.2: bounded coordinatewise difference is symmetric. -/
private theorem isBounded_range_sub_comm {x y : ℕ → ℝ}
    (hxy : Bornology.IsBounded (Set.range (x - y))) :
    Bornology.IsBounded (Set.range (y - x)) := by
  -- Negation carries the first difference range onto the reversed difference range.
  rw [isBounded_iff_forall_norm_le] at hxy ⊢
  obtain ⟨C, hC⟩ := hxy
  refine ⟨C, Set.forall_mem_range.mpr fun n ↦ ?_⟩
  simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm] using
    hC ((x - y) n) ⟨n, rfl⟩

/-- Helper for Exercise 25.2: bounded coordinatewise difference is transitive. -/
private theorem isBounded_range_sub_trans {x y z : ℕ → ℝ}
    (hxy : Bornology.IsBounded (Set.range (x - y)))
    (hyz : Bornology.IsBounded (Set.range (y - z))) :
    Bornology.IsBounded (Set.range (x - z)) := by
  -- Add numerical bounds and use the pointwise triangle inequality.
  rw [isBounded_iff_forall_norm_le] at hxy hyz ⊢
  obtain ⟨C, hC⟩ := hxy
  obtain ⟨D, hD⟩ := hyz
  refine ⟨C + D, Set.forall_mem_range.mpr fun n ↦ ?_⟩
  calc
    ‖(x - z) n‖ = ‖(x - y) n + (y - z) n‖ := by
      congr 1
      simp only [Pi.sub_apply]
      ring
    _ ≤ ‖(x - y) n‖ + ‖(y - z) n‖ := norm_add_le _ _
    _ ≤ C + D := add_le_add (hC _ ⟨n, rfl⟩) (hD _ ⟨n, rfl⟩)

/-- Helper for Exercise 25.2: uniform distance less than one gives bounded coordinatewise
difference. -/
private theorem isBounded_range_sub_of_uniformDistance_lt_one {x y : ℕ → ℝ}
    (hxy : (UniformMetric.metricSpace ℕ).dist x y < 1) :
    Bornology.IsBounded (Set.range (x - y)) := by
  -- Each truncated coordinate distance lies below the uniform supremum, hence below one.
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, Set.forall_mem_range.mpr fun n ↦ ?_⟩
  have hbounded : BddAbove (Set.range fun j ↦ min (dist (x j) (y j)) 1) := by
    refine ⟨1, Set.forall_mem_range.mpr fun j ↦ min_le_right _ _⟩
  have hcoord : min (dist (x n) (y n)) 1 < 1 := by
    calc
      min (dist (x n) (y n)) 1 ≤ ⨆ j, min (dist (x j) (y j)) 1 :=
        le_ciSup hbounded n
      _ = (UniformMetric.metricSpace ℕ).dist x y := (UniformMetric.dist_eq x y).symm
      _ < 1 := hxy
  have hdist : dist (x n) (y n) < 1 := by
    simpa only [min_lt_iff, lt_self_iff_false, or_false] using hcoord
  simpa only [Pi.sub_apply, Real.norm_eq_abs, Real.dist_eq] using hdist.le

/-- Helper for Exercise 25.2: balls for the explicit uniform metric are open in the named
uniform topology. -/
private theorem isOpen_uniformBall (x : ℕ → ℝ) (ε : ℝ) :
    (UniformMetric.topology ℕ).IsOpen
      {y | (UniformMetric.metricSpace ℕ).dist y x < ε} := by
  -- Install the named metric only while invoking the metric-ball theorem.
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  exact Metric.isOpen_ball

/-- Helper for Exercise 25.2: explicit uniform-metric balls are open after wrapping real
sequences in `UniformRealSequence`. -/
private theorem isOpen_uniformBall_wrapped (x : UniformRealSequence) (ε : ℝ) :
    IsOpen {y : UniformRealSequence |
      (UniformMetric.metricSpace ℕ).dist y.ofTopology x.ofTopology < ε} := by
  -- Pull the wrapped set back to the raw named uniform topology.
  rw [WithTopology.isOpen_iff]
  exact isOpen_uniformBall x.ofTopology ε

/-- Helper for Exercise 25.2: on natural-number sequences, finite support is equivalent to
eventual vanishing. -/
private theorem hasFiniteSupport_iff_eventually_zero (f : ℕ → ℝ) :
    f.HasFiniteSupport ↔ ∀ᶠ n in atTop, f n = 0 := by
  -- Replace `atTop` by the cofinite filter and unfold the support predicate.
  rw [← Nat.cofinite_eq_atTop]
  simp only [Filter.eventually_cofinite, Function.HasFiniteSupport, Function.support]

/-- Helper for Exercise 25.2: a uniformly bounded affine segment is continuous for the raw
uniform topology on real sequences. -/
private theorem continuous_uniformAffineSegment_raw_of_bounded (x y : ℕ → ℝ)
    (hxy : Bornology.IsBounded (Set.range (x - y))) :
    @Continuous ℝ (ℕ → ℝ) inferInstance (UniformMetric.topology ℕ)
      (fun t n ↦ x n + t * (y n - x n)) := by
  -- Route correction: perform the metric estimate before wrapping the codomain in `WithTopology`.
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  rw [isBounded_iff_forall_norm_le] at hxy
  obtain ⟨C, hC⟩ := hxy
  let K : NNReal := ⟨max C 0, le_max_right _ _⟩
  have hcoeff : ∀ n, |y n - x n| ≤ K := by
    intro n
    calc
      |y n - x n| = ‖(x - y) n‖ := by
        simp only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm]
      _ ≤ C := hC _ ⟨n, rfl⟩
      _ ≤ K := le_max_left _ _
  have hLipschitz : LipschitzWith K (fun t n ↦ x n + t * (y n - x n)) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [UniformMetric.dist_eq]
    refine ciSup_le fun n ↦ ?_
    calc
      min (dist (x n + s * (y n - x n)) (x n + t * (y n - x n))) 1 ≤
          dist (x n + s * (y n - x n)) (x n + t * (y n - x n)) := min_le_left _ _
      _ = |y n - x n| * dist s t := by
        rw [Real.dist_eq, Real.dist_eq, ← abs_mul]
        congr 1
        ring
      _ ≤ K * dist s t := mul_le_mul_of_nonneg_right (hcoeff n) dist_nonneg
      _ = (K : ℝ) * dist s t := rfl
  exact hLipschitz.continuous

/-- Helper for Exercise 25.2: the uniformly bounded affine segment remains continuous after
passing to `UniformRealSequence`. -/
private theorem continuous_uniformAffineSegment_of_bounded (x y : ℕ → ℝ)
    (hxy : Bornology.IsBounded (Set.range (x - y))) :
    Continuous (fun t ↦ UniformRealSequence.ofSequence (fun n ↦ x n + t * (y n - x n))) := by
  -- The wrapper carries exactly the named raw topology, so the raw proof transports directly.
  letI : TopologicalSpace (ℕ → ℝ) := UniformMetric.topology ℕ
  rw [show (fun t ↦ UniformRealSequence.ofSequence (fun n ↦ x n + t * (y n - x n))) =
      WithTopology.toTopology (UniformMetric.topology ℕ) ∘
        (fun t n ↦ x n + t * (y n - x n)) by
    funext t
    exact UniformRealSequence.ofSequence_eq_toTopology _]
  exact (WithTopology.continuous_toTopology (UniformMetric.topology ℕ)).comp
    (continuous_uniformAffineSegment_raw_of_bounded x y hxy)

/-- Helper for Exercise 25.2: every bounded-difference class in the uniform topology is path
connected. -/
private theorem isPathConnected_uniformBoundedDifferenceClass (x : UniformRealSequence) :
    IsPathConnected {y : UniformRealSequence |
      Bornology.IsBounded (Set.range (x.ofTopology - y.ofTopology))} := by
  -- Join arbitrary class members by their affine segment and bound it relative to the anchor.
  rw [isPathConnected_iff]
  refine ⟨⟨x, isBounded_range_self_sub x.ofTopology⟩, ?_⟩
  intro y hy z hz
  change Bornology.IsBounded (Set.range (x.ofTopology - y.ofTopology)) at hy
  change Bornology.IsBounded (Set.range (x.ofTopology - z.ofTopology)) at hz
  have hyz : Bornology.IsBounded (Set.range (y.ofTopology - z.ofTopology)) :=
    isBounded_range_sub_trans (isBounded_range_sub_comm hy) hz
  let f : ℝ → UniformRealSequence := fun t ↦
    UniformRealSequence.ofSequence
      (fun n ↦ y.ofTopology n + t * (z.ofTopology n - y.ofTopology n))
  have hf : Continuous f := continuous_uniformAffineSegment_of_bounded _ _ hyz
  refine JoinedIn.ofLine hf.continuousOn ?_ ?_ ?_
  · ext n
    dsimp only [f]
    simp only [UniformRealSequence.ofSequence_eq_toTopology,
      WithTopology.ofTopology_toTopology, zero_mul, add_zero]
  · ext n
    dsimp only [f]
    simp only [UniformRealSequence.ofSequence_eq_toTopology,
      WithTopology.ofTopology_toTopology, one_mul, add_sub_cancel]
  · rintro w ⟨t, ht, rfl⟩
    change Bornology.IsBounded (Set.range (x.ofTopology - (f t).ofTopology))
    rw [isBounded_iff_forall_norm_le] at hy hz ⊢
    obtain ⟨C, hC⟩ := hy
    obtain ⟨D, hD⟩ := hz
    refine ⟨C + D, Set.forall_mem_range.mpr fun n ↦ ?_⟩
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    calc
      ‖(x.ofTopology - (f t).ofTopology) n‖ =
          ‖(1 - t) * (x.ofTopology - y.ofTopology) n +
            t * (x.ofTopology - z.ofTopology) n‖ := by
        dsimp only [f]
        rw [UniformRealSequence.ofSequence_eq_toTopology,
          WithTopology.ofTopology_toTopology]
        simp only [Pi.sub_apply]
        congr 1
        ring
      _ ≤ ‖(1 - t) * (x.ofTopology - y.ofTopology) n‖ +
          ‖t * (x.ofTopology - z.ofTopology) n‖ := norm_add_le _ _
      _ = (1 - t) * ‖(x.ofTopology - y.ofTopology) n‖ +
          t * ‖(x.ofTopology - z.ofTopology) n‖ := by
        rw [norm_mul, norm_mul]
        simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0]
      _ ≤ (1 - t) * C + t * D :=
        add_le_add (mul_le_mul_of_nonneg_left (hC _ ⟨n, rfl⟩) (sub_nonneg.mpr ht1))
          (mul_le_mul_of_nonneg_left (hD _ ⟨n, rfl⟩) ht0)
      _ ≤ C + D := by
        have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ ⟨n, rfl⟩)
        have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD _ ⟨n, rfl⟩)
        nlinarith

/-- Helper for Exercise 25.2: every bounded-difference class in the uniform topology is clopen. -/
private theorem isClopen_uniformBoundedDifferenceClass (x : UniformRealSequence) :
    IsClopen {y : UniformRealSequence |
      Bornology.IsBounded (Set.range (x.ofTopology - y.ofTopology))} := by
  -- A radius-one uniform ball cannot cross between bounded-difference equivalence classes.
  have hopen : IsOpen {y : UniformRealSequence |
      Bornology.IsBounded (Set.range (x.ofTopology - y.ofTopology))} := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    change Bornology.IsBounded (Set.range (x.ofTopology - y.ofTopology)) at hy
    refine ⟨{z | (UniformMetric.metricSpace ℕ).dist z.ofTopology y.ofTopology < 1}, ?_, ?_, ?_⟩
    · intro z hz
      change Bornology.IsBounded (Set.range (x.ofTopology - z.ofTopology))
      exact isBounded_range_sub_trans hy
        (isBounded_range_sub_comm (isBounded_range_sub_of_uniformDistance_lt_one hz))
    · exact isOpen_uniformBall_wrapped y 1
    · simp
  have hopen_compl : IsOpen ({y : UniformRealSequence |
      Bornology.IsBounded (Set.range (x.ofTopology - y.ofTopology))}ᶜ) := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    refine ⟨{z | (UniformMetric.metricSpace ℕ).dist z.ofTopology y.ofTopology < 1}, ?_, ?_, ?_⟩
    · intro z hz hzclass
      apply hy
      change Bornology.IsBounded (Set.range (x.ofTopology - z.ofTopology)) at hzclass
      change Bornology.IsBounded (Set.range (x.ofTopology - y.ofTopology))
      exact isBounded_range_sub_trans hzclass
        (isBounded_range_sub_of_uniformDistance_lt_one hz)
    · exact isOpen_uniformBall_wrapped y 1
    · simp
  exact ⟨isOpen_compl_iff.mp hopen_compl, hopen⟩

/-- Helper for Exercise 25.2: an affine segment with finitely many varying coordinates is
continuous for the box topology. -/
private theorem continuous_boxAffineSegment_of_finiteSupport (x y : ℕ → ℝ)
    (hxy : (x - y).HasFiniteSupport) :
    Continuous (fun t ↦ BoxRealSequence.ofSequence (fun n ↦ x n + t * (y n - x n))) := by
  -- Expand the box topology once; every basic preimage is empty or a finite intersection.
  classical
  let support : Set ℕ := Function.support (x - y)
  have hsupport : support.Finite := hxy
  have hraw : @Continuous ℝ (ℕ → ℝ) inferInstance
      (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))
      (fun t n ↦ x n + t * (y n - x n)) := by
    rw [continuous_generateFrom_iff]
    intro V hV
    obtain ⟨U, hU, rfl⟩ := (Pi.mem_boxBasis _).mp hV
    by_cases houtside : ∀ n ∉ support, x n ∈ U n
    · have hpreimage :
          (fun t n ↦ x n + t * (y n - x n)) ⁻¹' Set.pi Set.univ U =
            ⋂ n ∈ support, (fun t : ℝ ↦ x n + t * (y n - x n)) ⁻¹' U n := by
        ext t
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
          Set.mem_iInter]
        constructor
        · intro ht n hn
          exact ht n
        · intro ht n
          by_cases hn : n ∈ support
          · exact ht n hn
          · have hzero : (x - y) n = 0 := Function.notMem_support.mp hn
            have hsame : y n = x n := by
              exact (sub_eq_zero.mp (by simpa only [Pi.sub_apply] using hzero)).symm
            simpa only [hsame, sub_self, mul_zero, add_zero] using houtside n hn
      rw [hpreimage]
      exact hsupport.isOpen_biInter fun n hn ↦
        (hU n).preimage (continuous_const.add (continuous_id.mul_const _))
    · push Not at houtside
      obtain ⟨n, hn, hxn⟩ := houtside
      have hzero : (x - y) n = 0 := Function.notMem_support.mp hn
      have hsame : y n = x n := by
        exact (sub_eq_zero.mp (by simpa only [Pi.sub_apply] using hzero)).symm
      have hpreimage :
          (fun t n ↦ x n + t * (y n - x n)) ⁻¹' Set.pi Set.univ U = ∅ := by
        ext t
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
          Set.mem_empty_iff_false, iff_false]
        intro ht
        exact hxn (by simpa only [hsame, sub_self, mul_zero, add_zero] using ht n)
      rw [hpreimage]
      exact isOpen_empty
  -- Wrap the raw box-continuous map exactly once.
  letI : TopologicalSpace (ℕ → ℝ) := Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)
  rw [show (fun t ↦ BoxRealSequence.ofSequence (fun n ↦ x n + t * (y n - x n))) =
      WithTopology.toTopology (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) ∘
        (fun t n ↦ x n + t * (y n - x n)) by
    funext t
    exact BoxRealSequence.ofSequence_eq_toTopology _]
  exact (WithTopology.continuous_toTopology
    (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))).comp hraw

/-- Helper for Exercise 25.2: every finite-difference class in the box topology is path
connected. -/
private theorem isPathConnected_boxFiniteDifferenceClass (x : BoxRealSequence) :
    IsPathConnected {y : BoxRealSequence |
      (x.ofTopology - y.ofTopology).HasFiniteSupport} := by
  -- Join each class member to the fixed anchor; two such paths concatenate through the anchor.
  rw [isPathConnected_iff]
  refine ⟨⟨x, ?_⟩, ?_⟩
  · simpa using (hasFiniteSupport_iff_eventually_zero (x.ofTopology - x.ofTopology)).mpr
      (Filter.Eventually.of_forall fun n ↦ sub_self (x.ofTopology n))
  · intro y hy z hz
    change (x.ofTopology - y.ofTopology).HasFiniteSupport at hy
    change (x.ofTopology - z.ofTopology).HasFiniteSupport at hz
    have joinAnchor (w : BoxRealSequence)
        (hw : (x.ofTopology - w.ofTopology).HasFiniteSupport) :
        JoinedIn {v : BoxRealSequence |
          (x.ofTopology - v.ofTopology).HasFiniteSupport} x w := by
      let f : ℝ → BoxRealSequence := fun t ↦
        BoxRealSequence.ofSequence
          (fun n ↦ x.ofTopology n + t * (w.ofTopology n - x.ofTopology n))
      have hf : Continuous f := continuous_boxAffineSegment_of_finiteSupport _ _ hw
      refine JoinedIn.ofLine hf.continuousOn ?_ ?_ ?_
      · ext n
        dsimp only [f]
        simp only [BoxRealSequence.ofSequence_eq_toTopology,
          WithTopology.ofTopology_toTopology, zero_mul, add_zero]
      · ext n
        dsimp only [f]
        simp only [BoxRealSequence.ofSequence_eq_toTopology,
          WithTopology.ofTopology_toTopology, one_mul, add_sub_cancel]
      · rintro v ⟨t, ht, rfl⟩
        change (x.ofTopology - (f t).ofTopology).HasFiniteSupport
        have hsubset : Function.support (x.ofTopology - (f t).ofTopology) ⊆
            Function.support (x.ofTopology - w.ofTopology) := by
          intro n hn
          contrapose! hn
          have hzero : (x.ofTopology - w.ofTopology) n = 0 :=
            Function.notMem_support.mp hn
          dsimp only [f]
          rw [BoxRealSequence.ofSequence_eq_toTopology,
            WithTopology.ofTopology_toTopology]
          simp only [Function.notMem_support, Pi.sub_apply] at hzero ⊢
          have hsame : w.ofTopology n = x.ofTopology n := (sub_eq_zero.mp hzero).symm
          simp only [hsame, sub_self, mul_zero, add_zero]
        exact hw.subset hsubset
    exact (joinAnchor y hy).symm.trans (joinAnchor z hz)

/-- Helper for Exercise 25.2: coordinatewise truncated bounds control the uniform distance. -/
private theorem uniformDist_le_of_coordinateDist_le (x y : ℕ → ℝ) (r : ℝ)
    (h : ∀ n, min (dist (x n) (y n)) 1 ≤ r) :
    (UniformMetric.metricSpace ℕ).dist x y ≤ r := by
  -- The uniform metric is the supremum of the truncated coordinate distances.
  rw [UniformMetric.dist_eq]
  exact ciSup_le h

/-- Helper for Exercise 25.2: a coordinate box of radius `ε / 2` lies in the uniform
`ε`-ball. -/
private theorem boxInterval_subset_uniformBall (x : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    Set.pi Set.univ (fun n ↦ Set.Ioo (x n - ε / 2) (x n + ε / 2)) ⊆
      @Metric.ball (ℕ → ℝ) (UniformMetric.metricSpace ℕ).toPseudoMetricSpace x ε := by
  -- Coordinate interval membership gives a common bound for every truncated distance.
  intro y hy
  have hdist : (UniformMetric.metricSpace ℕ).dist y x ≤ ε / 2 := by
    refine uniformDist_le_of_coordinateDist_le y x (ε / 2) ?_
    intro n
    have hn := (Set.mem_pi.mp hy) n (Set.mem_univ n)
    have habs : |y n - x n| < ε / 2 := by
      rw [abs_lt]
      constructor
      · linarith [hn.1]
      · linarith [hn.2]
    have hcoord : dist (y n) (x n) ≤ ε / 2 := by
      rw [Real.dist_eq]
      exact habs.le
    exact (min_le_left _ _).trans hcoord
  -- The half-radius estimate is strictly inside the requested ball.
  exact lt_of_le_of_lt hdist (by linarith)

/-- Helper for Exercise 25.2: the box topology on real sequences is finer than the uniform
topology. -/
private theorem boxTopology_le_uniformTopology :
    Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ) ≤ UniformMetric.topology ℕ := by
  -- Every uniform neighborhood contains the coordinate box supplied above.
  intro s hs
  have hs' : @IsOpen (ℕ → ℝ) (UniformMetric.topology ℕ) s := hs
  rw [@Metric.isOpen_iff _ (UniformMetric.metricSpace ℕ).toPseudoMetricSpace] at hs'
  rw [@isOpen_iff_mem_nhds _ (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))]
  intro x hx
  obtain ⟨ε, hε, hball⟩ := hs' x hx
  let U : ℕ → Set ℝ := fun n ↦ Set.Ioo (x n - ε / 2) (x n + ε / 2)
  have hxU : x ∈ Set.pi Set.univ U := by
    rw [Set.mem_pi]
    intro n hn
    dsimp [U]
    constructor <;> linarith
  have hUopen : @IsOpen (ℕ → ℝ) (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ))
      (Set.pi Set.univ U) := by
    exact @Pi.isOpen_box ℕ (fun _ ↦ ℝ) (fun _ ↦ inferInstance) U fun n ↦ isOpen_Ioo
  have hUsub : Set.pi Set.univ U ⊆ s := by
    exact (boxInterval_subset_uniformBall x hε).trans hball
  exact Filter.mem_of_superset
    (@IsOpen.mem_nhds _ (Pi.boxTopologicalSpace (fun _ : ℕ ↦ ℝ)) _ _ hUopen hxU) hUsub

/-- Helper for Exercise 25.2: forgetting from the box topology to the uniform topology is
continuous. -/
private theorem continuous_boxToUniformRealSequence :
    Continuous (fun z : BoxRealSequence ↦
      UniformRealSequence.ofSequence z.ofTopology) := by
  -- Pulling back a uniform-open set gives the same underlying set, now box-open.
  rw [continuous_def]
  intro s hs
  rw [WithTopology.isOpen_iff] at hs ⊢
  have hopen := boxTopology_le_uniformTopology _ hs
  convert hopen using 1
  ext z
  simp only [Set.mem_preimage, UniformRealSequence.ofSequence_eq_toTopology]

/-- Helper for Exercise 25.2: an infinite coordinate difference can be made unbounded by a
coordinatewise box homeomorphism. -/
private theorem exists_boxHomeomorph_unboundedDifference (x y : BoxRealSequence)
    (hxy : ¬ ∀ᶠ n in atTop, (x.ofTopology - y.ofTopology) n = 0) :
    ∃ h : BoxRealSequence ≃ₜ BoxRealSequence,
      h x = BoxRealSequence.ofSequence 0 ∧
        ¬ Bornology.IsBounded
          (Set.range ((h x).ofTopology - (h y).ofTopology)) := by
  -- Scale every nonzero coordinate difference to the growing value `n + 1`.
  classical
  let d : ℕ → ℝ := x.ofTopology - y.ofTopology
  let a : ℕ → ℝ := fun n ↦ if d n = 0 then 1 else (n + 1 : ℕ) / d n
  let b : ℕ → ℝ := fun n ↦ -a n * x.ofTopology n
  have ha : ∀ n, a n ≠ 0 := by
    intro n
    dsimp [a]
    split_ifs with hn
    · norm_num
    · exact div_ne_zero (by positivity) hn
  let f : BoxRealSequence → BoxRealSequence :=
    Pi.boxMap fun n z ↦ a n * z + b n
  have hf : IsHomeomorph f :=
    isHomeomorph_realSequenceAffineMap_box_of_ne_zero a b ha
  let h : BoxRealSequence ≃ₜ BoxRealSequence := IsHomeomorph.homeomorph f hf
  have hx : h x = BoxRealSequence.ofSequence 0 := by
    -- The translation term was chosen to send `x` to the zero sequence.
    ext n
    dsimp [h, f]
    simp only [IsHomeomorph.homeomorph_apply, Pi.boxMap_apply, Pi.map_apply,
      BoxRealSequence.ofSequence_eq_toTopology]
    dsimp [b]
    ring
  have hcoord : ∀ n, d n ≠ 0 →
      ((h x).ofTopology - (h y).ofTopology) n = (n + 1 : ℕ) := by
    -- On a nonzero-difference coordinate, the affine scale cancels that difference exactly.
    intro n hn
    dsimp [h, f]
    simp only [IsHomeomorph.homeomorph_apply, Pi.boxMap_apply, Pi.map_apply]
    dsimp [a, b]
    rw [if_neg hn]
    dsimp [d] at hn ⊢
    field_simp
    ring
  have hfrequent : ∀ N, ∃ n ≥ N, d n ≠ 0 := by
    -- Negated eventual vanishing supplies a nonzero difference beyond every threshold.
    intro N
    by_contra hN
    apply hxy
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn ↦ ?_⟩
    by_contra hne
    exact hN ⟨n, hn, hne⟩
  refine ⟨h, hx, ?_⟩
  -- Any claimed norm bound is exceeded at a sufficiently late nonzero coordinate.
  rw [isBounded_iff_forall_norm_le]
  rintro ⟨C, hC⟩
  obtain ⟨N, hNC⟩ := exists_nat_gt C
  obtain ⟨n, hnN, hn⟩ := hfrequent N
  have hbound := hC _ ⟨n, rfl⟩
  rw [hcoord n hn, Real.norm_natCast] at hbound
  norm_num at hbound
  have hNn1 : N ≤ n + 1 := hnN.trans (Nat.le_add_right n 1)
  exact (not_lt_of_ge hbound) (lt_of_lt_of_le hNC (by exact_mod_cast hNn1))

/-- Product-topology component characterization for Exercise 25.2: every real sequence lies
in the same connected component. -/
theorem productRealSequencesConnectedComponent (x : ℕ → ℝ) :
    connectedComponent x = (Set.univ : Set (ℕ → ℝ)) := by
  -- The universal set is connected, so maximality puts every point in the component of `x`.
  apply Set.eq_univ_of_univ_subset
  exact isConnected_univ.subset_connectedComponent (Set.mem_univ x)

/-- Product-topology path-component characterization for Exercise 25.2: every real sequence
lies in the same path component. -/
theorem productRealSequencesPathComponent (x : ℕ → ℝ) :
    pathComponent x = (Set.univ : Set (ℕ → ℝ)) := by
  -- The Pi-space path-connected instance joins `x` to every real sequence.
  apply Set.eq_univ_of_univ_subset
  exact isPathConnected_univ.subset_pathComponent (Set.mem_univ x)

/-- Uniform-topology component characterization for Exercise 25.2: two real sequences lie in
the same connected component exactly when their difference has bounded range. -/
theorem uniformRealSequences_sameConnectedComponent_iff (x y : UniformRealSequence) :
    y ∈ connectedComponent x ↔
      Bornology.IsBounded (Set.range (x.ofTopology - y.ofTopology)) := by
  -- The bounded-difference class is simultaneously connected and clopen around `x`.
  constructor
  · intro hy
    exact (isClopen_uniformBoundedDifferenceClass x).connectedComponent_subset
      (isBounded_range_self_sub x.ofTopology) hy
  · intro hxy
    exact (isPathConnected_uniformBoundedDifferenceClass x).isConnected.subset_connectedComponent
      (isBounded_range_self_sub x.ofTopology) hxy

/-- Exercise 25.2: Two real sequences lie in the same connected component for the box
topology exactly when their difference is eventually zero. -/
theorem boxRealSequences_sameConnectedComponent_iff (x y : BoxRealSequence) :
    y ∈ connectedComponent x ↔
      ∀ᶠ n in atTop, (x.ofTopology - y.ofTopology) n = 0 := by
  -- Finite coordinate variation gives a box-continuous straight-line path; the converse is
  -- reduced to the uniform theorem by a coordinatewise affine box homeomorphism.
  constructor
  · intro hy
    by_contra hxy
    obtain ⟨h, hx, hunbounded⟩ := exists_boxHomeomorph_unboundedDifference x y hxy
    -- First carry component membership through the box homeomorphism.
    have hbox : h y ∈ connectedComponent (h x) :=
      h.continuous.mapsTo_connectedComponent x hy
    let forget : BoxRealSequence → UniformRealSequence := fun z ↦
      UniformRealSequence.ofSequence z.ofTopology
    have huniform : forget (h y) ∈ connectedComponent (forget (h x)) :=
      continuous_boxToUniformRealSequence.mapsTo_connectedComponent (h x) hbox
    have hbounded : Bornology.IsBounded
        (Set.range ((h x).ofTopology - (h y).ofTopology)) := by
      -- The uniform component characterization turns the transported membership into a bound.
      have hboundWrapped := (uniformRealSequences_sameConnectedComponent_iff (forget (h x))
        (forget (h y))).mp huniform
      simpa only [forget, UniformRealSequence.ofSequence_eq_toTopology,
        WithTopology.ofTopology_toTopology] using hboundWrapped
    exact hunbounded hbounded
  · intro hxy
    have hsupport : (x.ofTopology - y.ofTopology).HasFiniteSupport :=
      (hasFiniteSupport_iff_eventually_zero _).mpr hxy
    exact (isPathConnected_boxFiniteDifferenceClass x).isConnected.subset_connectedComponent
      (by
        apply (hasFiniteSupport_iff_eventually_zero _).mpr
        exact Filter.Eventually.of_forall fun n ↦ sub_self (x.ofTopology n)) hsupport

/-- A finite-support formulation of `boxRealSequences_sameConnectedComponent_iff`. -/
theorem boxRealSequences_sameConnectedComponent_iff_hasFiniteSupport
    (x y : BoxRealSequence) :
    y ∈ connectedComponent x ↔
      (x.ofTopology - y.ofTopology).HasFiniteSupport := by
  -- On `ℕ`, eventual vanishing at `atTop` is exactly finiteness of the support.
  rw [boxRealSequences_sameConnectedComponent_iff, hasFiniteSupport_iff_eventually_zero]
