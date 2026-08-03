module

public import Topology_Munkres_2000.Book.Definition_20_9.UniformMetric
public import Topology_Munkres_2000.Book.Exercise_19_7.EventuallyZero

public section

open scoped Topology

/-- Helper for Exercise 20.5: `truncateSequence x N` agrees with `x` before `N` and
vanishes from `N` onward. -/
def truncateSequence (x : ℕ → ℝ) (N : ℕ) : ℕ → ℝ :=
  fun n ↦ if n < N then x n else 0

/-- Helper for Exercise 20.5: every finite-prefix truncation has finite support. -/
lemma truncateSequence_hasFiniteSupport (x : ℕ → ℝ) (N : ℕ) :
    (truncateSequence x N).HasFiniteSupport := by
  -- The support is contained in the finite initial interval `Set.Iio N`.
  rw [Function.HasFiniteSupport]
  refine Set.finite_Iio N |>.subset ?_
  intro n hn
  by_contra hnN
  have hNn : N ≤ n := Nat.le_of_not_gt hnN
  simp [Function.mem_support, truncateSequence, Nat.not_lt_of_ge hNn] at hn

/-- Helper for Exercise 20.5: a finitely supported sequence is zero after one index. -/
lemma exists_zero_tail_of_hasFiniteSupport {y : ℕ → ℝ} (hy : y.HasFiniteSupport) :
    ∃ N, ∀ n ≥ N, y n = 0 := by
  -- A finite subset of `ℕ` has an upper bound; its successor misses the support.
  rw [Function.HasFiniteSupport] at hy
  obtain ⟨N, hN⟩ := hy.bddAbove
  refine ⟨N + 1, fun n hn ↦ ?_⟩
  by_contra hyn
  have hnSupport : n ∈ Function.support y := by
    simpa [Function.mem_support] using hyn
  have hnLe : n ≤ N := hN hnSupport
  omega

/-- Helper for Exercise 20.5: below distance `1`, uniform distance bounds every
coordinate distance. -/
lemma coordinateDistance_le_uniformDistance_of_lt_one {x y : ℕ → ℝ}
    (hxy : (UniformMetric.metricSpace ℕ).dist x y < 1) (n : ℕ) :
    dist (x n) (y n) ≤ (UniformMetric.metricSpace ℕ).dist x y := by
  -- First compare the truncated coordinate distance with its supremum.
  have hb : BddAbove (Set.range fun j ↦ min (dist (x j) (y j)) 1) := by
    refine ⟨1, ?_⟩
    rintro z ⟨j, rfl⟩
    exact min_le_right _ _
  have hnSup : min (dist (x n) (y n)) 1 ≤
      ⨆ j, min (dist (x j) (y j)) 1 := le_ciSup hb n
  have hnLtOne : dist (x n) (y n) < 1 := by
    by_contra hn
    have hone : 1 ≤ dist (x n) (y n) := le_of_not_gt hn
    rw [min_eq_right hone, ← UniformMetric.dist_eq] at hnSup
    exact (not_lt_of_ge hnSup) hxy
  -- Since this coordinate distance is below `1`, the truncation is inactive.
  rw [min_eq_left hnLtOne.le, ← UniformMetric.dist_eq] at hnSup
  exact hnSup

/-- Helper for Exercise 20.5: a uniformly small tail makes a finite-prefix truncation
uniformly close to the original sequence. -/
lemma uniformDistance_truncateSequence_le {x : ℕ → ℝ} {N : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hx : ∀ n ≥ N, dist (x n) 0 ≤ δ) :
    (UniformMetric.metricSpace ℕ).dist x (truncateSequence x N) ≤ δ := by
  -- Bound each coordinate of the supremum, splitting before and after the cutoff.
  rw [UniformMetric.dist_eq]
  refine ciSup_le fun n ↦ ?_
  by_cases hn : n < N
  · simp [truncateSequence, hn, hδ]
  · have hNn : N ≤ n := Nat.le_of_not_gt hn
    calc
      min (dist (x n) (truncateSequence x N n)) 1 ≤
          dist (x n) (truncateSequence x N n) := min_le_left _ _
      _ = dist (x n) 0 := by simp [truncateSequence, hn]
      _ ≤ δ := hx n hNn

/-- Exercise 20.5: In the uniform topology, the closure of the eventually zero real
sequences is the set of real sequences converging to zero. -/
theorem uniformClosure_eventuallyZeroRealSequences :
    closure[UniformMetric.topology ℕ] eventuallyZeroRealSequences =
      {x | Filter.Tendsto x Filter.atTop (nhds 0)} := by
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    -- Approximate the closure point by a finitely supported sequence at a radius below `1`.
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < min (ε / 2) (1 / 2) := by positivity
    have hδε : min (ε / 2) (1 / 2) < ε := by
      exact (min_le_left _ _).trans_lt (half_lt_self hε)
    have hδone : min (ε / 2) (1 / 2) < 1 := by
      exact (min_le_right _ _).trans_lt (by norm_num)
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ hδ
    rw [mem_eventuallyZeroRealSequences] at hy
    obtain ⟨N, hyN⟩ := exists_zero_tail_of_hasFiniteSupport hy
    refine ⟨N, fun n hn ↦ ?_⟩
    have hxyOne : dist x y < 1 := hxy.trans hδone
    have hnLe : dist (x n) (y n) ≤ dist x y :=
      coordinateDistance_le_uniformDistance_of_lt_one hxyOne n
    -- Beyond the support of `y`, coordinate control gives convergence of `x` to zero.
    calc
      dist (x n) 0 = dist (x n) (y n) := by rw [hyN n hn]
      _ ≤ dist x y := hnLe
      _ < min (ε / 2) (1 / 2) := hxy
      _ < ε := hδε
  · intro hx
    -- Truncate a sufficiently small tail to obtain a finitely supported approximant.
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hδ : 0 < min (ε / 2) (1 / 2) := by positivity
    have hδε : min (ε / 2) (1 / 2) < ε := by
      exact (min_le_left _ _).trans_lt (half_lt_self hε)
    obtain ⟨N, hxN⟩ := Metric.tendsto_atTop.1 hx _ hδ
    refine ⟨truncateSequence x N, ?_, ?_⟩
    · rw [mem_eventuallyZeroRealSequences]
      exact truncateSequence_hasFiniteSupport x N
    · have hdist : dist x (truncateSequence x N) ≤ min (ε / 2) (1 / 2) :=
        uniformDistance_truncateSequence_le hδ.le fun n hn ↦ (hxN n hn).le
      exact hdist.trans_lt hδε

/-- A real sequence lies in the uniform closure of the eventually zero sequences
exactly when it converges to zero. -/
theorem mem_uniformClosure_eventuallyZeroRealSequences (x : ℕ → ℝ) :
    x ∈ closure[UniformMetric.topology ℕ] eventuallyZeroRealSequences ↔
      Filter.Tendsto x Filter.atTop (nhds 0) := by
  rw [uniformClosure_eventuallyZeroRealSequences]
  rfl
