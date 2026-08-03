module

public import Mathlib.Topology.MetricSpace.Thickening

public section

/- Exercise 27.2 (a): For a nonempty subset of a metric space, the distance from a point
to the set is zero exactly when the point belongs to its closure. -/
#check Metric.mem_closure_iff_infDist_zero

/- Exercise 27.2 (b): A nonempty compact subset of a metric space contains a point realizing
the distance from any given point to the set. -/
#check IsCompact.exists_infDist_eq_dist

/- Exercise 27.2 (c), definition: The `ε`-neighborhood of a set is its open thickening. -/
#check Metric.thickening
#check Metric.mem_thickening_iff_infDist_lt

/- Exercise 27.2 (c), conclusion: The `ε`-neighborhood of a set is the union of the open balls
of radius `ε` centered at its points. -/
#check Metric.thickening_eq_biUnion_ball

/- Exercise 27.2 (d): Every open set containing a compact set contains a positive-radius
neighborhood of that compact set. -/
#check IsCompact.exists_thickening_subset_open

namespace ShrinkingBallCounterexample

/-- The closed discrete set used for the counterexample in Exercise 27.2 (e). -/
def points : Set (ℝ × ℝ) :=
  {p | ∃ n : ℕ, p = ((n : ℝ), 0)}

/-- The open union of shrinking balls used for the counterexample in Exercise 27.2 (e). -/
def openSet : Set (ℝ × ℝ) :=
  ⋃ n : ℕ, Metric.ball ((n : ℝ), 0) ((n : ℝ) + 1)⁻¹

/-- The counterexample set is nonempty. -/
theorem points_nonempty : points.Nonempty := by
  -- The point indexed by zero supplies an explicit member.
  have hzero : (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ) = (((0 : ℕ) : ℝ), (0 : ℝ)) := by
    norm_num
  exact ⟨((0 : ℝ), (0 : ℝ)), 0, hzero⟩

/-- Helper for Exercise 27.2: the counterexample set is the product of the natural-number
range in `ℝ` with the singleton `{0}`. -/
lemma points_eq_range_prod_singleton :
    points = Set.range ((↑) : ℕ → ℝ) ×ˢ ({0} : Set ℝ) := by
  -- Extensionality separates the index witness from the fixed second coordinate.
  ext p
  constructor
  · rintro ⟨n, hn⟩
    have hfirst : p.1 = (n : ℝ) := congrArg Prod.fst hn
    have hsecond : p.2 = 0 := congrArg Prod.snd hn
    exact ⟨⟨n, hfirst.symm⟩, hsecond⟩
  · rintro ⟨⟨n, hn⟩, hsecond⟩
    have hp : p = ((n : ℝ), 0) := Prod.ext hn.symm hsecond
    exact ⟨n, hp⟩

/-- Helper for Exercise 27.2: distinct natural-number points in `ℝ` are at least unit
distance apart. -/
lemma one_le_dist_natCast_of_ne {m n : ℕ} (hmn : m ≠ n) :
    1 ≤ dist (m : ℝ) (n : ℝ) := by
  -- Transport the standard separation bound on `ℕ` through its real embedding.
  rw [Nat.dist_cast_real]
  exact Nat.pairwise_one_le_dist hmn

/-- The counterexample set is closed. -/
theorem isClosed_points : IsClosed points := by
  -- Rewrite the set into a product of two closed canonical sets.
  rw [points_eq_range_prod_singleton]
  exact Nat.isClosedEmbedding_coe_real.isClosed_range.prod isClosed_singleton

/-- The counterexample set is not compact. -/
theorem not_isCompact_points : ¬ IsCompact points := by
  -- Compactness would place all natural-number points in one bounded ball.
  intro hcompact
  obtain ⟨r, hr⟩ := hcompact.isBounded.subset_ball (0, 0)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hpoint : ((n : ℝ), 0) ∈ points := ⟨n, rfl⟩
  have hball := hr hpoint
  -- The chosen point has distance `n` from the origin, contradicting `r < n`.
  have hnr : (n : ℝ) < r := by
    simpa [Metric.mem_ball, Prod.dist_eq, Real.dist_eq] using hball
  exact (not_lt_of_ge hn.le) hnr

/-- The union of shrinking balls is open. -/
theorem isOpen_openSet : IsOpen openSet := by
  -- An indexed union of open metric balls is open.
  exact isOpen_iUnion fun n ↦ Metric.isOpen_ball

/-- The union of shrinking balls contains the counterexample set. -/
theorem points_subset_openSet : points ⊆ openSet := by
  -- Each point lies in the ball carrying the same natural-number index.
  rintro p ⟨n, rfl⟩
  refine Set.mem_iUnion.2 ⟨n, ?_⟩
  rw [Metric.mem_ball]
  simp only [dist_self]
  positivity

/-- No positive-radius neighborhood of the counterexample set is contained in the union of
shrinking balls. -/
theorem not_thickening_subset_openSet (ε : ℝ) (hε : 0 < ε) :
    ¬ Metric.thickening ε points ⊆ openSet := by
  -- Choose a late index whose reciprocal scale is smaller than `ε`.
  obtain ⟨n, hnpos, hninv⟩ := Real.exists_nat_pos_inv_lt hε
  let radius : ℝ := ((n : ℝ) + 1)⁻¹
  let witness : ℝ × ℝ := ((n : ℝ), radius)
  have hradius_pos : 0 < radius := by
    dsimp [radius]
    positivity
  have hradius_lt : radius < ε := by
    have hncast_pos : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hradius_le_inv : radius ≤ (n : ℝ)⁻¹ := by
      dsimp [radius]
      exact inv_anti₀ hncast_pos (le_add_of_nonneg_right zero_le_one)
    exact hradius_le_inv.trans_lt hninv
  have hwitness_thickening : witness ∈ Metric.thickening ε points := by
    -- The witness is vertically `radius` away from the point with index `n`.
    rw [Metric.mem_thickening_iff]
    refine ⟨((n : ℝ), 0), ⟨n, rfl⟩, ?_⟩
    simpa [witness, Prod.dist_eq, Real.dist_eq, abs_of_pos hradius_pos] using
      And.intro hε hradius_lt
  intro hsubset
  have hwitness_open := hsubset hwitness_thickening
  obtain ⟨m, hball⟩ := Set.mem_iUnion.1 hwitness_open
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hball
  by_cases hmn : m = n
  · -- At the matching index, the witness lies exactly on the ball boundary.
    subst m
    have : radius < radius := by
      simpa [witness, radius, Real.dist_eq, abs_of_pos hradius_pos] using hball.2
    exact (lt_irrefl radius) this
  · -- At every other index, horizontal separation is at least one, exceeding its radius.
    have hsep : 1 ≤ dist (n : ℝ) (m : ℝ) := one_le_dist_natCast_of_ne (Ne.symm hmn)
    have hballRadius_le : ((m : ℝ) + 1)⁻¹ ≤ 1 := by
      apply (inv_le_one₀ (by positivity)).2
      exact le_add_of_nonneg_left (Nat.cast_nonneg m)
    have hhorizontal : dist (n : ℝ) (m : ℝ) < ((m : ℝ) + 1)⁻¹ := by
      simpa [witness] using hball.1
    exact (not_lt_of_ge (hballRadius_le.trans hsep)) hhorizontal

/-- Exercise 27.2 (e): The conclusion of part (d) can fail for a closed noncompact set. -/
theorem exists_closed_noncompact_not_thickening_subset :
    ∃ A U : Set (ℝ × ℝ), IsClosed A ∧ ¬ IsCompact A ∧ IsOpen U ∧ A ⊆ U ∧
      ∀ ε > 0, ¬ Metric.thickening ε A ⊆ U := by
  exact ⟨points, openSet, isClosed_points, not_isCompact_points, isOpen_openSet,
    points_subset_openSet, not_thickening_subset_openSet⟩

end ShrinkingBallCounterexample
