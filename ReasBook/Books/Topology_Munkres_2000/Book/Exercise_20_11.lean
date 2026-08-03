module

public import Topology_Munkres_2000.Book.Definition_20_1

public section

universe u

namespace MetricSpace

variable {X : Type u}

/-- The fractional transform `d / (1 + d)` of the distance of a metric structure. -/
noncomputable def fractionalDist (m : MetricSpace X) (x y : X) : ℝ :=
  m.dist x y / (1 + m.dist x y)

/-- Helper for Exercise 20.11: the fractional transform strictly preserves order on
nonnegative real numbers. -/
private lemma fractionalTransform_lt_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a / (1 + a) < b / (1 + b) ↔ a < b := by
  -- Positive denominators permit cross multiplication, where the common product cancels.
  have haDen : 0 < 1 + a := by linarith
  have hbDen : 0 < 1 + b := by linarith
  rw [div_lt_div_iff₀ haDen hbDen]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- Helper for Exercise 20.11: the fractional transform is subadditive on
nonnegative real numbers. -/
private lemma fractionalTransform_subadd {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / (1 + (a + b)) ≤ a / (1 + a) + b / (1 + b) := by
  -- Clear the positive denominators and reduce the inequality to nonnegative products.
  have haDen : 0 < 1 + a := by linarith
  have hbDen : 0 < 1 + b := by linarith
  have habDen : 0 < 1 + (a + b) := by linarith
  rw [div_le_iff₀ habDen]
  field_simp [haDen.ne', hbDen.ne']
  nlinarith [mul_nonneg ha hb]

private theorem fractionalDist_self (m : MetricSpace X) (x : X) :
    fractionalDist m x x = 0 := by
  -- The original self-distance vanishes, so its fractional transform vanishes too.
  letI : MetricSpace X := m
  simp only [fractionalDist, dist_self, zero_div]

private theorem fractionalDist_comm (m : MetricSpace X) (x y : X) :
    fractionalDist m x y = fractionalDist m y x := by
  -- Symmetry is preserved because both sides apply the same scalar transform.
  letI : MetricSpace X := m
  rw [fractionalDist, fractionalDist, dist_comm x y]

private theorem fractionalDist_triangle (m : MetricSpace X) (x y z : X) :
    fractionalDist m x z ≤ fractionalDist m x y + fractionalDist m y z := by
  -- Monotonicity transfers the original triangle inequality, then subadditivity splits it.
  letI : MetricSpace X := m
  have hmono :
      dist x z / (1 + dist x z) ≤
        (dist x y + dist y z) / (1 + (dist x y + dist y z)) := by
    have hxzDen : 0 < 1 + dist x z := by positivity
    have hsumDen : 0 < 1 + (dist x y + dist y z) := by positivity
    rw [div_le_div_iff₀ hxzDen hsumDen]
    nlinarith [dist_triangle x y z]
  calc
    fractionalDist m x z = dist x z / (1 + dist x z) := rfl
    _ ≤ (dist x y + dist y z) / (1 + (dist x y + dist y z)) := hmono
    _ ≤ dist x y / (1 + dist x y) + dist y z / (1 + dist y z) :=
      fractionalTransform_subadd dist_nonneg dist_nonneg
    _ = fractionalDist m x y + fractionalDist m y z := rfl

private theorem fractionalDist_isOpen (m : MetricSpace X) (s : Set X) :
    @IsOpen X m.toUniformSpace.toTopologicalSpace s ↔
      ∀ x ∈ s, ∃ ε > 0, ∀ y, fractionalDist m x y < ε → y ∈ s := by
  -- Compare the original and fractional metric bases using transformed radii.
  letI : MetricSpace X := m
  rw [Metric.isOpen_iff]
  constructor
  · intro hs x hx
    obtain ⟨ε, hε, hball⟩ := hs x hx
    have hεDen : 0 < 1 + ε := by linarith
    refine ⟨ε / (1 + ε), div_pos hε hεDen, ?_⟩
    intro y hy
    apply hball
    rw [Metric.mem_ball']
    exact (fractionalTransform_lt_iff dist_nonneg (le_of_lt hε)).mp hy
  · intro hs x hx
    obtain ⟨ε, hε, hfractional⟩ := hs x hx
    refine ⟨ε, hε, ?_⟩
    intro y hy
    apply hfractional y
    have hdist : dist x y < ε := Metric.mem_ball'.mp hy
    have hdistNonneg : 0 ≤ dist x y := dist_nonneg
    have hden : 1 ≤ 1 + dist x y := by linarith
    have htransform_le : dist x y / (1 + dist x y) ≤ dist x y := by
      exact div_le_self hdistNonneg hden
    exact lt_of_le_of_lt htransform_le hdist

private theorem fractionalDist_eq_zero (m : MetricSpace X) (x y : X)
    (h : fractionalDist m x y = 0) : x = y := by
  -- The positive denominator forces the original distance, hence the points, to coincide.
  letI : MetricSpace X := m
  have hden : 1 + dist x y ≠ 0 := by positivity
  have hdist : dist x y = 0 := (div_eq_zero_iff.mp h).resolve_right hden
  exact eq_of_dist_eq_zero hdist

@[implicit_reducible]
private noncomputable def fractionalMetric (m : MetricSpace X) : MetricSpace X :=
  @MetricSpace.ofDistTopology X m.toUniformSpace.toTopologicalSpace
    (fractionalDist m) (fractionalDist_self m)
    (fractionalDist_comm m) (fractionalDist_triangle m) (fractionalDist_isOpen m)
    (fractionalDist_eq_zero m)

/-- Exercise 20.11 (1): The distance `d'(x, y) = d(x, y) / (1 + d(x, y))`
defines a metric whenever `d` does. -/
@[implicit_reducible]
noncomputable def fractional (m : MetricSpace X) : MetricSpace X :=
  fractionalMetric m

/-- The distance field of the fractional metric is the stated fractional transform. -/
theorem fractional_dist (m : MetricSpace X) (x y : X) :
    m.fractional.dist x y = m.dist x y / (1 + m.dist x y) := by
  -- The metric constructor stores the fractional distance definitionally.
  rfl

/-- Exercise 20.11 (2): Every distance in the fractional metric is strictly less than `1`. -/
theorem fractional_dist_lt_one (m : MetricSpace X) (x y : X) :
    m.fractional.dist x y < 1 := by
  -- Rewrite the distance and compare its numerator with its positive denominator.
  letI : MetricSpace X := m
  rw [fractional_dist]
  apply (div_lt_one (by positivity)).mpr
  have hdistNonneg : 0 ≤ dist x y := dist_nonneg
  linarith

/-- Exercise 20.11 (3): The fractional metric induces the topology of the original metric. -/
theorem fractional_toTopologicalSpace (m : MetricSpace X) :
    (m.fractional).toUniformSpace.toTopologicalSpace = m.toUniformSpace.toTopologicalSpace := by
  -- `ofDistTopology` preserves the supplied topology definitionally.
  rfl

end MetricSpace


end
