module

public import Topology_Munkres_2000.Book.Definition_20_9

public section

open scoped Topology

/-- The infinite coordinate box of radius `ε` about a real sequence. -/
def uniformCoordinateBox (x : ℕ → ℝ) (ε : ℝ) : Set (ℕ → ℝ) :=
  Set.univ.pi fun n ↦ Set.Ioo (x n - ε) (x n + ε)

/-- Membership in `uniformCoordinateBox` is coordinatewise membership in the corresponding
open intervals. -/
theorem mem_uniformCoordinateBox {x y : ℕ → ℝ} {ε : ℝ} :
    y ∈ uniformCoordinateBox x ε ↔ ∀ n, y n ∈ Set.Ioo (x n - ε) (x n + ε) := by
  -- Unpack membership in the dependent product over all coordinates.
  simp only [uniformCoordinateBox, Set.mem_pi, Set.mem_univ, true_implies]

/-- Helper for Exercise 20.6: coordinate-box membership is a strict coordinatewise distance
bound. -/
lemma mem_uniformCoordinateBox_iff_dist_lt {x y : ℕ → ℝ} {ε : ℝ} :
    y ∈ uniformCoordinateBox x ε ↔ ∀ n, dist (y n) (x n) < ε := by
  -- Convert the two interval inequalities into the absolute-value formula for real distance.
  rw [mem_uniformCoordinateBox]
  constructor
  · intro hy n
    rw [Real.dist_eq]
    exact abs_lt.2 ⟨by linarith [hy n |>.1], by linarith [hy n |>.2]⟩
  · intro hy n
    have hn := hy n
    rw [Real.dist_eq] at hn
    exact ⟨by linarith [abs_lt.1 hn |>.1], by linarith [abs_lt.1 hn |>.2]⟩

/-- Helper for Exercise 20.6: every pair lies at uniform distance below any radius greater
than one. -/
lemma uniformMetric_dist_lt_of_one_lt (x y : ℕ → ℝ) {ε : ℝ} (hε : 1 < ε) :
    (UniformMetric.metricSpace ℕ).dist x y < ε := by
  -- Combine the global diameter bound with the strict radius inequality.
  exact lt_of_le_of_lt (UniformMetric.dist_le_one x y) hε

/-- Helper for Exercise 20.6: every truncated coordinate distance is bounded by the uniform
distance. -/
lemma coordinateTruncatedDist_le_uniformDist (x y : ℕ → ℝ) (n : ℕ) :
    min (dist (y n) (x n)) 1 ≤ (UniformMetric.metricSpace ℕ).dist y x := by
  -- Rewrite the uniform distance as its supremum, then select the given coordinate.
  rw [UniformMetric.dist_eq]
  refine le_ciSup (f := fun i : ℕ ↦ min (dist (y i) (x i)) 1) ?_ n
  refine ⟨1, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact min_le_right _ _

/-- Helper for Exercise 20.6: changing one coordinate has uniform distance equal to its
truncated coordinate displacement. -/
lemma uniformDist_update_eq (y : ℕ → ℝ) (n : ℕ) (a : ℝ) :
    (UniformMetric.metricSpace ℕ).dist (Function.update y n a) y = min (dist a (y n)) 1 := by
  -- Bound the supremum by the updated coordinate's displacement.
  apply le_antisymm
  · rw [UniformMetric.dist_eq]
    refine ciSup_le fun i ↦ ?_
    by_cases hin : i = n
    · subst i
      rw [Function.update_self]
    · rw [Function.update_of_ne hin]
      simp
  · -- The selected-coordinate lower bound gives the reverse inequality.
    simpa only [Function.update_self] using
      coordinateTruncatedDist_le_uniformDist y (Function.update y n a) n

/-- Helper for Exercise 20.6: a sequence whose coordinates approach the upper face of the
coordinate box. -/
noncomputable def approachingUpperFace (x : ℕ → ℝ) (ε : ℝ) : ℕ → ℝ :=
  fun n ↦ x n + ε - ε / (n + 1 : ℝ)

/-- Helper for Exercise 20.6: the gap from `approachingUpperFace x ε` to the upper face at
coordinate `n` is `ε / (n + 1)`. -/
lemma approachingUpperFace_gap (x : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    x n + ε - approachingUpperFace x ε n = ε / (n + 1 : ℝ) := by
  -- Expand the witness and normalize the coordinate gap.
  unfold approachingUpperFace
  ring

/-- Helper for Exercise 20.6: for positive radius, `approachingUpperFace x ε` lies in the
coordinate box of radius `ε`. -/
lemma approachingUpperFace_mem (x : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    approachingUpperFace x ε ∈ uniformCoordinateBox x ε := by
  -- Each positive reciprocal gap keeps the coordinate strictly below the upper face.
  rw [mem_uniformCoordinateBox]
  intro n
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hgap : 0 < ε / (n + 1 : ℝ) := div_pos hε hn
  constructor
  · unfold approachingUpperFace
    have hdiv : ε / (n + 1 : ℝ) ≤ ε := by
      exact (div_le_iff₀ hn).2 (by nlinarith)
    linarith
  · rw [← sub_pos, approachingUpperFace_gap]
    exact hgap

/-- Part (a) of Exercise 20.6: The infinite coordinate box of radius `ε` is not the
`ε`-ball for the uniform metric. -/
theorem uniformCoordinateBox_ne_ball (x : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    uniformCoordinateBox x ε ≠ UniformMetric.ball x ε := by
  -- Separate the sets by a boundary-approaching sequence when `ε ≤ 1`.
  intro heq
  by_cases hεone : ε ≤ 1
  · have hwitness : approachingUpperFace x ε ∈ UniformMetric.ball x ε := by
      rw [← heq]
      exact approachingUpperFace_mem x hε
    have hdist : (UniformMetric.metricSpace ℕ).dist (approachingUpperFace x ε) x < ε := by
      exact UniformMetric.mem_ball.1 hwitness
    have hremaining : 0 < (ε - (UniformMetric.metricSpace ℕ).dist
        (approachingUpperFace x ε) x) / ε := div_pos (sub_pos.2 hdist) hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hremaining
    have hnpos : 0 < (n + 1 : ℝ) := by positivity
    have hcoord : dist (approachingUpperFace x ε n) (x n) =
        ε - ε / (n + 1 : ℝ) := by
      rw [Real.dist_eq]
      unfold approachingUpperFace
      have hdiv : ε / (n + 1 : ℝ) ≤ ε := by
        exact (div_le_iff₀ hnpos).2 (by nlinarith)
      rw [abs_of_nonneg]
      · ring
      · linarith
    have hcoordlt : dist (approachingUpperFace x ε n) (x n) < 1 := by
      rw [hcoord]
      have hdivpos : 0 < ε / (n + 1 : ℝ) := div_pos hε hnpos
      linarith
    have hglobal := coordinateTruncatedDist_le_uniformDist x (approachingUpperFace x ε) n
    rw [min_eq_left hcoordlt.le, hcoord] at hglobal
    have hscaled : ε / (n + 1 : ℝ) <
        ε - (UniformMetric.metricSpace ℕ).dist (approachingUpperFace x ε) x := by
      calc
        ε / (n + 1 : ℝ) = ε * (1 / (n + 1 : ℝ)) := by ring
        _ < ε * ((ε - (UniformMetric.metricSpace ℕ).dist
            (approachingUpperFace x ε) x) / ε) := mul_lt_mul_of_pos_left hn hε
        _ = ε - (UniformMetric.metricSpace ℕ).dist (approachingUpperFace x ε) x := by
          field_simp [ne_of_gt hε]
    linarith
  · -- For `ε > 1`, the uniform ball is universal, while the coordinate box is not.
    have hεgt : 1 < ε := lt_of_not_ge hεone
    let y : ℕ → ℝ := Function.update x 0 (x 0 + ε)
    have hyball : y ∈ UniformMetric.ball x ε := by
      exact UniformMetric.mem_ball.2 (uniformMetric_dist_lt_of_one_lt y x hεgt)
    have hynot : y ∉ uniformCoordinateBox x ε := by
      rw [mem_uniformCoordinateBox]
      intro hy
      have := (hy 0).2
      simp only [y, Function.update_self] at this
      exact (lt_irrefl (x 0 + ε)) this
    exact hynot (heq ▸ hyball)

/-- Part (b) of Exercise 20.6: The infinite coordinate box of radius `ε` is not open in the
uniform topology. -/
theorem uniformCoordinateBox_not_isOpen (x : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ¬ IsOpen[UniformMetric.topology ℕ] (uniformCoordinateBox x ε) := by
  -- An open neighborhood of the boundary-approaching point would permit one boundary hit.
  intro hopen
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  have hmetricOpen : @IsOpen (ℕ → ℝ) (UniformMetric.topology ℕ)
      (uniformCoordinateBox x ε) := hopen
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hmetricOpen
    (approachingUpperFace x ε) (approachingUpperFace_mem x hε)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hr hε)
  have hnpos : 0 < (n + 1 : ℝ) := by positivity
  let y := Function.update (approachingUpperFace x ε) n (x n + ε)
  have hydist : (UniformMetric.metricSpace ℕ).dist y (approachingUpperFace x ε) < r := by
    rw [uniformDist_update_eq]
    have hgap : dist (x n + ε) (approachingUpperFace x ε n) = ε / (n + 1 : ℝ) := by
      rw [Real.dist_eq, abs_of_nonneg]
      · exact approachingUpperFace_gap x ε n
      · rw [approachingUpperFace_gap]
        exact (div_pos hε hnpos).le
    rw [hgap]
    refine lt_of_le_of_lt (min_le_left _ _) ?_
    calc
      ε / (n + 1 : ℝ) = ε * (1 / (n + 1 : ℝ)) := by ring
      _ < ε * (r / ε) := mul_lt_mul_of_pos_left hn hε
      _ = r := by field_simp [ne_of_gt hε]
  have hymem : y ∈ uniformCoordinateBox x ε := hball hydist
  rw [mem_uniformCoordinateBox] at hymem
  have := (hymem n).2
  simp only [y, Function.update_self] at this
  exact (lt_irrefl (x n + ε)) this

/-- Part (c) of Exercise 20.6: The `ε`-ball for the uniform metric is the union of all
infinite coordinate boxes of radii strictly less than `ε`. -/
theorem uniformMetric_ball_eq_iUnion_coordinateBox (x : ℕ → ℝ) {ε : ℝ} (hε₁ : ε < 1) :
    UniformMetric.ball x ε = ⋃ δ ∈ Set.Iio ε, uniformCoordinateBox x δ := by
  -- Use the midpoint between the uniform distance and `ε` as a common coordinate radius.
  ext y
  constructor
  · intro hy
    have hdist : (UniformMetric.metricSpace ℕ).dist y x < ε := by
      exact UniformMetric.mem_ball.1 hy
    let δ := ((UniformMetric.metricSpace ℕ).dist y x + ε) / 2
    have hdistδ : (UniformMetric.metricSpace ℕ).dist y x < δ := by
      dsimp only [δ]
      linarith
    have hδε : δ < ε := by
      dsimp only [δ]
      linarith
    rw [Set.mem_iUnion]
    refine ⟨δ, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨hδε, ?_⟩
    rw [mem_uniformCoordinateBox_iff_dist_lt]
    intro n
    have hcoord := coordinateTruncatedDist_le_uniformDist x y n
    have hδone : δ < 1 := lt_trans hδε hε₁
    by_contra hnot
    have hone : 1 ≤ dist (y n) (x n) := by
      by_contra honeNot
      have hcoordlt : dist (y n) (x n) < 1 := lt_of_not_ge honeNot
      rw [min_eq_left hcoordlt.le] at hcoord
      exact hnot (lt_of_le_of_lt hcoord hdistδ)
    rw [min_eq_right hone] at hcoord
    linarith
  · -- A common strict coordinate radius bounds the entire coordinate supremum.
    intro hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨δ, hy⟩ := hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨hδε, hybox⟩ := hy
    have hcoord : ∀ n, dist (y n) (x n) < δ :=
      mem_uniformCoordinateBox_iff_dist_lt.1 hybox
    have hδpos : 0 < δ := by
      have hzero := hcoord 0
      exact lt_of_le_of_lt dist_nonneg hzero
    have huniform : (UniformMetric.metricSpace ℕ).dist y x ≤ δ := by
      rw [UniformMetric.dist_eq]
      refine ciSup_le fun n ↦ ?_
      exact le_trans (min_le_left _ _) (hcoord n).le
    exact UniformMetric.mem_ball.2 (lt_of_le_of_lt huniform hδε)

/-- Exercise 20.6: A positive coordinate box is neither its uniform-metric ball nor open,
and for radius below one the ball is the union of all smaller coordinate boxes. -/
theorem uniformCoordinateBox_exerciseProperties (x : ℕ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε₁ : ε < 1) :
    uniformCoordinateBox x ε ≠ UniformMetric.ball x ε ∧
      ¬ IsOpen[UniformMetric.topology ℕ] (uniformCoordinateBox x ε) ∧
      UniformMetric.ball x ε = ⋃ δ ∈ Set.Iio ε, uniformCoordinateBox x δ := by
  -- Assemble the three parts from their source-facing component theorems.
  exact ⟨uniformCoordinateBox_ne_ball x hε, uniformCoordinateBox_not_isOpen x hε,
    uniformMetric_ball_eq_iUnion_coordinateBox x hε₁⟩
