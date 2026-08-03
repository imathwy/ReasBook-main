module

public import Mathlib.Topology.MetricSpace.Basic

public section

open Set

universe u

namespace Pi

/-- The weighted supremum of the coordinate distances truncated at `1`, with the
coordinate indexed by `n` weighted by `1 / (n + 1)`. -/
@[expose]
noncomputable def weightedSupDist {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
    (x y : ∀ n, X n) : ℝ :=
  sSup (range (fun n : ℕ ↦ min (dist (x n) (y n)) 1 / (n + 1 : ℕ)))

/-- The defining formula for `weightedSupDist`. -/
theorem weightedSupDist_def {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
    (x y : ∀ n, X n) :
    weightedSupDist x y =
      sSup (range (fun n : ℕ ↦ min (dist (x n) (y n)) 1 / (n + 1 : ℕ))) := rfl

/-- Helper for Theorem 20.5: every weighted coordinate distance lies between `0` and `1`. -/
private lemma weightedCoordinate_mem_unitInterval {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
    (x y : ∀ n, X n) (n : ℕ) :
    0 ≤ min (dist (x n) (y n)) 1 / (n + 1 : ℕ) ∧
      min (dist (x n) (y n)) 1 / (n + 1 : ℕ) ≤ 1 := by
  -- Positivity of the denominator transfers the elementary bounds on the truncated distance.
  constructor
  · positivity
  · calc
      min (dist (x n) (y n)) 1 / (n + 1 : ℕ) ≤ 1 / (n + 1 : ℕ) := by
        gcongr
        exact min_le_right _ _
      _ ≤ 1 := by
        exact (div_le_one (by positivity)).mpr (by norm_num)

/-- Helper for Theorem 20.5: every defining coordinate is bounded by the supremum. -/
private lemma weightedCoordinate_le_weightedSupDist {X : ℕ → Type u}
    [∀ n, MetricSpace (X n)] (x y : ∀ n, X n) (n : ℕ) :
    min (dist (x n) (y n)) 1 / (n + 1 : ℕ) ≤ weightedSupDist x y := by
  -- The unit upper bound makes the defining range bounded above, so `le_csSup` applies.
  rw [weightedSupDist_def]
  refine le_csSup ?_ ⟨n, rfl⟩
  refine ⟨1, ?_⟩
  rintro _ ⟨m, rfl⟩
  exact (weightedCoordinate_mem_unitInterval x y m).2

/-- The weighted supremum distance vanishes on the diagonal. -/
theorem weightedSupDist_self {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
    (x : ∀ n, X n) : weightedSupDist x x = 0 := by
  -- Every coordinate term is zero, so the supremum is squeezed to zero.
  apply le_antisymm
  · rw [weightedSupDist_def]
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨n, rfl⟩
    simp
  · exact (weightedCoordinate_mem_unitInterval x x 0).1.trans
      (weightedCoordinate_le_weightedSupDist x x 0)

/-- The weighted supremum distance is symmetric. -/
theorem weightedSupDist_comm {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
    (x y : ∀ n, X n) : weightedSupDist x y = weightedSupDist y x := by
  -- Symmetry holds pointwise in the two ranges defining the suprema.
  simp only [weightedSupDist_def, dist_comm]

/-- Helper for Theorem 20.5: truncating a metric at `1` preserves the triangle inequality. -/
private lemma minDist_triangle {α : Type u} [MetricSpace α] (a b c : α) :
    min (dist a c) 1 ≤ min (dist a b) 1 + min (dist b c) 1 := by
  -- Split according to whether the right side has already reached the truncation threshold.
  by_cases h : 1 ≤ min (dist a b) 1 + min (dist b c) 1
  · exact (min_le_right _ _).trans h
  · rw [not_le] at h
    have hab : dist a b < 1 := by
      by_contra hab
      have hab' : 1 ≤ dist a b := le_of_not_gt hab
      rw [min_eq_right hab'] at h
      have hmin_nonneg : 0 ≤ min (dist b c) 1 := le_min dist_nonneg zero_le_one
      linarith
    have hbc : dist b c < 1 := by
      by_contra hbc
      have hbc' : 1 ≤ dist b c := le_of_not_gt hbc
      rw [min_eq_right hbc'] at h
      have hmin_nonneg : 0 ≤ min (dist a b) 1 := le_min dist_nonneg zero_le_one
      linarith
    rw [min_eq_left hab.le, min_eq_left hbc.le]
    exact (min_le_left _ _).trans (dist_triangle _ _ _)

/-- The weighted supremum distance satisfies the triangle inequality. -/
theorem weightedSupDist_triangle {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
    (x y z : ∀ n, X n) :
    weightedSupDist x z ≤ weightedSupDist x y + weightedSupDist y z := by
  -- Bound each coordinate by the sum of the two global suprema, then take the supremum.
  rw [weightedSupDist_def]
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨n, rfl⟩
  calc
    min (dist (x n) (z n)) 1 / (n + 1 : ℕ) ≤
        (min (dist (x n) (y n)) 1 + min (dist (y n) (z n)) 1) / (n + 1 : ℕ) := by
      gcongr
      exact minDist_triangle _ _ _
    _ = min (dist (x n) (y n)) 1 / (n + 1 : ℕ) +
        min (dist (y n) (z n)) 1 / (n + 1 : ℕ) := by ring
    _ ≤ weightedSupDist x y + weightedSupDist y z :=
      add_le_add (weightedCoordinate_le_weightedSupDist x y n)
        (weightedCoordinate_le_weightedSupDist y z n)

/-- Helper for Theorem 20.5: finitely many positive real numbers have a positive
common lower bound. -/
private lemma exists_pos_le_on_finset (I : Finset ℕ) (r : ℕ → ℝ)
    (hr : ∀ i ∈ I, 0 < r i) : ∃ ε > 0, ∀ i ∈ I, ε ≤ r i := by
  -- Induction adjoins one coordinate by replacing the old radius with a minimum.
  classical
  induction I using Finset.induction_on with
  | empty =>
      exact ⟨1, zero_lt_one, by simp⟩
  | @insert i I hi ih =>
      obtain ⟨ε, hε, hεI⟩ := ih (fun j hj ↦ hr j (Finset.mem_insert_of_mem hj))
      refine ⟨min ε (r i), lt_min hε (hr i (Finset.mem_insert_self i I)), ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hεI j hj)

/-- Helper for Theorem 20.5: a small weighted distance forces membership in a chosen
coordinate ball. -/
private lemma mem_ball_of_weightedSupDist_lt {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
    (x y : ∀ n, X n) (n : ℕ) (δ ε : ℝ) (hδ1 : δ ≤ 1)
    (hε : ε ≤ δ / (n + 1 : ℕ)) (hxy : weightedSupDist x y < ε) :
    y n ∈ Metric.ball (x n) δ := by
  -- Compare the coordinate term with the supremum, then remove truncation and the positive weight.
  have hcoord : min (dist (x n) (y n)) 1 / (n + 1 : ℕ) < δ / (n + 1 : ℕ) :=
    lt_of_le_of_lt (weightedCoordinate_le_weightedSupDist x y n) (hxy.trans_le hε)
  have hmin : min (dist (x n) (y n)) 1 < δ := by
    have hdenom : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    exact (div_lt_div_iff_of_pos_right hdenom).mp hcoord
  have hdist : dist (x n) (y n) < δ := by
    by_contra h
    have hδdist : δ ≤ dist (x n) (y n) := le_of_not_gt h
    have : δ ≤ min (dist (x n) (y n)) 1 := le_min hδdist hδ1
    exact (not_le_of_gt hmin) this
  exact Metric.mem_ball'.mpr hdist

/-- A set is open in the product topology exactly when it contains a positive
weighted-supremum-distance ball around each of its points. -/
theorem isOpen_iff_weightedSupDist {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
    (s : Set (∀ n, X n)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, weightedSupDist x y < ε → y ∈ s := by
  classical
  constructor
  · intro hs x hx
    -- Refine a product neighborhood to finitely many coordinate balls and take one common radius.
    obtain ⟨I, u, hu, huis⟩ := isOpen_pi_iff.mp hs x hx
    have hball_exists (i : ℕ) (hi : i ∈ I) :
        ∃ δ > 0, δ ≤ 1 ∧ Metric.ball (x i) δ ⊆ u i := by
      obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp (hu i hi).1 (x i) (hu i hi).2
      refine ⟨min r 1, lt_min hr zero_lt_one, min_le_right r 1, ?_⟩
      intro z hz
      apply hrs
      exact Metric.mem_ball'.mpr
        ((Metric.mem_ball'.mp hz).trans_le (min_le_left r 1))
    let δ : ℕ → ℝ := fun i ↦
      if hi : i ∈ I then (hball_exists i hi).choose else 1
    have hδpos (i : ℕ) (hi : i ∈ I) : 0 < δ i := by
      simp only [δ, dif_pos hi]
      exact (hball_exists i hi).choose_spec.1
    have hδrest (i : ℕ) (hi : i ∈ I) :
        δ i ≤ 1 ∧ Metric.ball (x i) (δ i) ⊆ u i := by
      simp only [δ, dif_pos hi]
      exact (hball_exists i hi).choose_spec.2
    obtain ⟨ε, hε, hεI⟩ := exists_pos_le_on_finset I
      (fun i ↦ δ i / (i + 1 : ℕ)) (fun i hi ↦ div_pos (hδpos i hi) (by positivity))
    refine ⟨ε, hε, fun y hy ↦ huis ?_⟩
    intro i hi
    exact (hδrest i hi).2 (mem_ball_of_weightedSupDist_lt x y i (δ i) ε
      (hδrest i hi).1 (hεI i hi) hy)
  · intro hs
    -- A weighted ball contains a cylinder restricting only an initial finite block of coordinates.
    rw [isOpen_pi_iff]
    intro x hx
    obtain ⟨ε, hε, hεs⟩ := hs x hx
    have hεhalf : 0 < ε / 2 := by linarith
    have hhalf_lt : ε / 2 < ε := by linarith
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hεhalf
    let u : ∀ n, Set (X n) := fun n ↦ Metric.ball (x n) ((ε / 2) * (n + 1 : ℕ))
    refine ⟨Finset.range (N + 1), u, ?_, ?_⟩
    · intro n hn
      constructor
      · exact Metric.isOpen_ball
      · exact Metric.mem_ball_self (mul_pos hεhalf (by positivity))
    · intro y hy
      apply hεs y
      rw [weightedSupDist_def]
      refine lt_of_le_of_lt (csSup_le (Set.range_nonempty _) ?_) hhalf_lt
      rintro _ ⟨n, rfl⟩
      by_cases hn : n ∈ Finset.range (N + 1)
      · have hball := hy n hn
        have hdist : dist (x n) (y n) < (ε / 2) * (n + 1 : ℕ) :=
          Metric.mem_ball'.mp hball
        calc
          min (dist (x n) (y n)) 1 / (n + 1 : ℕ) ≤ dist (x n) (y n) / (n + 1 : ℕ) := by
            gcongr
            exact min_le_left _ _
          _ ≤ ε / 2 := by
            have hdenom : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
            exact ((div_lt_iff₀ hdenom).mpr hdist).le
      · have hNn : N ≤ n := by
          rw [Finset.mem_range, not_lt] at hn
          omega
        calc
          min (dist (x n) (y n)) 1 / (n + 1 : ℕ) ≤ 1 / (n + 1 : ℕ) := by
            gcongr
            exact min_le_right _ _
          _ ≤ 1 / (N + 1 : ℝ) := by
            rw [one_div_le_one_div (by positivity) (by positivity)]
            exact_mod_cast Nat.add_le_add_right hNn 1
          _ ≤ ε / 2 := hN.le

/-- Points at weighted supremum distance zero are equal. -/
theorem eq_of_weightedSupDist_eq_zero {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
    (x y : ∀ n, X n) (h : weightedSupDist x y = 0) : x = y := by
  -- Every nonnegative coordinate term is squeezed to zero, forcing coordinatewise equality.
  funext n
  have hcoord : min (dist (x n) (y n)) 1 / (n + 1 : ℕ) = 0 := by
    apply le_antisymm
    · simpa [h] using weightedCoordinate_le_weightedSupDist x y n
    · exact (weightedCoordinate_mem_unitInterval x y n).1
  have hmin : min (dist (x n) (y n)) 1 = 0 := by
    exact (div_eq_zero_iff).mp hcoord |>.resolve_right (by positivity)
  have hdist : dist (x n) (y n) = 0 := by
    have hdist_nonneg : 0 ≤ dist (x n) (y n) := dist_nonneg
    by_cases hdist1 : dist (x n) (y n) ≤ 1
    · simpa [min_eq_left hdist1] using hmin
    · rw [min_eq_right (le_of_not_ge hdist1)] at hmin
      norm_num at hmin
  exact dist_eq_zero.mp hdist

/-- The explicit metric structure whose distance is `weightedSupDist` and whose
topology is the existing product topology. -/
@[implicit_reducible]
noncomputable def weightedSupMetricSpace {X : ℕ → Type u} [∀ n, MetricSpace (X n)] :
    MetricSpace (∀ n, X n) :=
  MetricSpace.ofDistTopology weightedSupDist weightedSupDist_self weightedSupDist_comm
    weightedSupDist_triangle isOpen_iff_weightedSupDist eq_of_weightedSupDist_eq_zero

/-- The distance field of `weightedSupMetricSpace` is `weightedSupDist`. -/
theorem weightedSupMetricSpace_dist {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
    (x y : ∀ n, X n) :
    weightedSupMetricSpace.toDist.dist x y = weightedSupDist x y := by
  -- The construction stores the supplied distance definitionally.
  rfl

/-- The topology underlying `weightedSupMetricSpace` is the product topology. -/
theorem weightedSupMetricSpace_topology (X : ℕ → Type u) [∀ n, MetricSpace (X n)] :
    (weightedSupMetricSpace : MetricSpace (∀ n, X n)).toUniformSpace.toTopologicalSpace =
      Pi.topologicalSpace := by
  -- `MetricSpace.ofDistTopology` preserves the pre-existing product topology definitionally.
  rfl

/- Theorem 20.5. The metric `weightedSupMetricSpace` on real sequences induces
the product topology. Its index `n + 1` reindexes the textbook's positive integer
coordinate `i`. -/
#check (weightedSupMetricSpace : MetricSpace (ℕ → ℝ))

/-- The metric in Theorem 20.5 induces the product topology on real sequences. -/
theorem realWeightedSupMetricSpace_topology :
    (weightedSupMetricSpace : MetricSpace (ℕ → ℝ)).toUniformSpace.toTopologicalSpace =
      Pi.topologicalSpace :=
  weightedSupMetricSpace_topology (fun _ : ℕ ↦ ℝ)

/-- The distance in Theorem 20.5 is the textbook's weighted supremum formula. -/
theorem realWeightedSupMetricSpace_dist (x y : ℕ → ℝ) :
    (weightedSupMetricSpace : MetricSpace (ℕ → ℝ)).toDist.dist x y =
      sSup (Set.range (fun n : ℕ ↦ min (dist (x n) (y n)) 1 / (n + 1 : ℕ))) := by
  -- Expose the metric projection and then the defining supremum formula.
  rw [weightedSupMetricSpace_dist, weightedSupDist_def]

end Pi
