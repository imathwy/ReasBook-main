module

public import Mathlib.Topology.MetricSpace.Defs

public section

universe u

namespace MetricSpace

variable {α : Type u}

private theorem standardBounded_dist_self (m : MetricSpace α) (x : α) :
    min (m.dist x x) 1 = 0 := by
  -- Expose `m` so the ordinary distance laws rewrite the truncated distance.
  letI : MetricSpace α := m
  simp only [dist_self, min_eq_left, zero_le_one]

private theorem standardBounded_dist_comm (m : MetricSpace α) (x y : α) :
    min (m.dist x y) 1 = min (m.dist y x) 1 := by
  -- Symmetry is preserved by applying the same truncation to both sides.
  letI : MetricSpace α := m
  rw [dist_comm x y]

private theorem standardBounded_dist_triangle (m : MetricSpace α) (x y z : α) :
    min (m.dist x z) 1 ≤ min (m.dist x y) 1 + min (m.dist y z) 1 := by
  -- If an adjacent distance reaches `1`, its truncated value bounds the left side.
  letI : MetricSpace α := m
  by_cases hxy : 1 ≤ dist x y
  · calc
      min (dist x z) 1 ≤ 1 := min_le_right _ _
      _ ≤ 1 + min (dist y z) 1 :=
        le_add_of_nonneg_right (le_min dist_nonneg zero_le_one)
      _ = min (dist x y) 1 + min (dist y z) 1 := by
        rw [min_eq_right hxy]
  · by_cases hyz : 1 ≤ dist y z
    · calc
        min (dist x z) 1 ≤ 1 := min_le_right _ _
        _ ≤ min (dist x y) 1 + 1 :=
          le_add_of_nonneg_left (le_min dist_nonneg zero_le_one)
        _ = min (dist x y) 1 + min (dist y z) 1 := by
          rw [min_eq_right hyz]
    · -- Below the cutoff, truncation disappears and the original triangle law applies.
      have hxy' : dist x y ≤ 1 := le_of_lt (lt_of_not_ge hxy)
      have hyz' : dist y z ≤ 1 := le_of_lt (lt_of_not_ge hyz)
      calc
        min (dist x z) 1 ≤ dist x z := min_le_left _ _
        _ ≤ dist x y + dist y z := dist_triangle _ _ _
        _ = min (dist x y) 1 + min (dist y z) 1 := by
          rw [min_eq_left hxy', min_eq_left hyz']

private theorem standardBounded_isOpen (m : MetricSpace α) (s : Set α) :
    @IsOpen α m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace s ↔
      ∀ x ∈ s, ∃ ε > 0, ∀ y, min (m.dist x y) 1 < ε → y ∈ s := by
  -- Compare the two metric bases using radii below the truncation threshold.
  letI : MetricSpace α := m
  rw [Metric.isOpen_iff]
  constructor
  · intro hs x hx
    obtain ⟨ε, hε, hball⟩ := hs x hx
    refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
    intro y hy
    apply hball
    rw [Metric.mem_ball']
    have htruncated_lt_one : min (dist x y) 1 < 1 :=
      lt_of_lt_of_le hy (min_le_right ε 1)
    have hdist_lt_one : dist x y < 1 :=
      (min_lt_iff.mp htruncated_lt_one).resolve_right (lt_irrefl 1)
    rw [min_eq_left (le_of_lt hdist_lt_one)] at hy
    exact lt_of_lt_of_le hy (min_le_left ε 1)
  · intro hs x hx
    obtain ⟨ε, hε, htruncated⟩ := hs x hx
    refine ⟨ε, hε, ?_⟩
    intro y hy
    apply htruncated y
    exact lt_of_le_of_lt (min_le_left (dist x y) 1) (Metric.mem_ball'.mp hy)

private theorem standardBounded_eq_of_dist_eq_zero (m : MetricSpace α) (x y : α) :
    min (m.dist x y) 1 = 0 → x = y := by
  -- Nonnegativity makes the minimum equal the original distance at zero.
  letI : MetricSpace α := m
  intro h
  rcases min_eq_iff.mp h with hdist | hone
  · exact eq_of_dist_eq_zero hdist.1
  · exact False.elim (one_ne_zero hone.1)

/-- Theorem 20.1. The standard bounded metric corresponding to `m`, whose distance is
`min (m.dist x y) 1` and whose topology is the topology induced by `m`. -/
@[implicit_reducible]
def standardBounded (m : MetricSpace α) : MetricSpace α :=
  @MetricSpace.ofDistTopology α m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (fun x y ↦ min (m.dist x y) 1) (standardBounded_dist_self m)
    (standardBounded_dist_comm m) (standardBounded_dist_triangle m) (standardBounded_isOpen m)
    (standardBounded_eq_of_dist_eq_zero m)

/-- The distance of the standard bounded metric is the original distance truncated at `1`. -/
theorem standardBounded_dist (m : MetricSpace α) (x y : α) :
    m.standardBounded.dist x y = min (m.dist x y) 1 := by
  -- The constructor stores the truncated distance definitionally.
  rfl

/-- Every distance in the standard bounded metric is at most `1`. -/
theorem standardBounded_dist_le_one (m : MetricSpace α) (x y : α) :
    m.standardBounded.dist x y ≤ 1 := by
  -- Rewrite to the truncated formula and use the defining upper bound.
  rw [standardBounded_dist]
  exact min_le_right _ _

/-- The standard bounded metric induces the same topology as the original metric. -/
theorem standardBounded_toTopologicalSpace (m : MetricSpace α) :
    m.standardBounded.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  -- `ofDistTopology` preserves the supplied topology definitionally.
  rfl

end MetricSpace

end
