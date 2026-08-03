module

public import Topology_Munkres_2000.Book.Theorem_20_1.BoundedMetric
public import Mathlib.Topology.UniformSpace.Cauchy

public section

universe u

namespace MetricSpace

variable {X : Type u}

/-- A sequence is Cauchy with respect to the explicitly specified metric. -/
abbrev IsCauchySeq (m : MetricSpace X) (u : ℕ → X) : Prop :=
  @CauchySeq X ℕ m.toUniformSpace inferInstance u

/-- A sequence converges to `x` with respect to the explicitly specified metric. -/
abbrev ConvergesTo (m : MetricSpace X) (u : ℕ → X) (x : X) : Prop :=
  Filter.Tendsto u Filter.atTop (@nhds X m.toUniformSpace.toTopologicalSpace x)

/-- A set is totally bounded with respect to the uniform space induced by the explicitly
specified metric. -/
abbrev IsTotallyBounded (m : MetricSpace X) (s : Set X) : Prop :=
  @TotallyBounded X m.toUniformSpace s

/-- A metric is complete when its induced uniform space is complete. -/
abbrev IsComplete (m : MetricSpace X) : Prop :=
  @CompleteSpace X m.toUniformSpace

namespace standardBounded

/-- The standard bounded metric induces the same uniform space as the original metric. -/
theorem toUniformSpace_eq (m : MetricSpace X) :
    m.standardBounded.toUniformSpace = m.toUniformSpace := by
  -- Compare the distance-entourage bases, shrinking the reverse radius below the cutoff `1`.
  apply UniformSpace.ext
  letI : MetricSpace X := m.standardBounded
  have boundedBasis := @Metric.uniformity_basis_dist X m.standardBounded.toPseudoMetricSpace
  letI : MetricSpace X := m
  have originalBasis := @Metric.uniformity_basis_dist X m.toPseudoMetricSpace
  refine boundedBasis.ext originalBasis ?_ ?_
  · intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro p hp
    change m.dist p.1 p.2 < ε at hp
    change m.standardBounded.dist p.1 p.2 < ε
    rw [MetricSpace.standardBounded_dist]
    exact lt_of_le_of_lt (min_le_left _ _) hp
  · intro ε hε
    refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
    intro p hp
    change m.standardBounded.dist p.1 p.2 < min ε 1 at hp
    change m.dist p.1 p.2 < ε
    rw [MetricSpace.standardBounded_dist] at hp
    have hdist_one : m.dist p.1 p.2 < 1 := by
      -- The bounded distance being below `min ε 1` forces the original distance below `1`.
      apply (min_lt_iff.mp (lt_of_lt_of_le hp (min_le_right ε 1))).resolve_right
      exact lt_irrefl 1
    rw [min_eq_left (le_of_lt hdist_one)] at hp
    exact lt_of_lt_of_le hp (min_le_left ε 1)

/-- A sequence is Cauchy for the standard bounded metric exactly when it is Cauchy for the
original metric. -/
theorem cauchySeq_iff (m : MetricSpace X) (u : ℕ → X) :
    m.standardBounded.IsCauchySeq u ↔ m.IsCauchySeq u := by
  change @CauchySeq X ℕ m.standardBounded.toUniformSpace inferInstance u ↔
    @CauchySeq X ℕ m.toUniformSpace inferInstance u
  rw [toUniformSpace_eq]

/-- A sequence converges to the same point for the standard bounded metric and the original
metric. -/
theorem convergesTo_iff (m : MetricSpace X) (u : ℕ → X) (x : X) :
    m.standardBounded.ConvergesTo u x ↔ m.ConvergesTo u x := by
  change Filter.Tendsto u Filter.atTop
      (@nhds X m.standardBounded.toUniformSpace.toTopologicalSpace x) ↔
    Filter.Tendsto u Filter.atTop (@nhds X m.toUniformSpace.toTopologicalSpace x)
  rw [toUniformSpace_eq]

/-- A set is totally bounded for the standard bounded metric exactly when it is totally bounded
for the original metric. -/
theorem totallyBounded_iff (m : MetricSpace X) (s : Set X) :
    m.standardBounded.IsTotallyBounded s ↔ m.IsTotallyBounded s := by
  change @TotallyBounded X m.standardBounded.toUniformSpace s ↔
    @TotallyBounded X m.toUniformSpace s
  rw [toUniformSpace_eq]

/-- A type is complete for the standard bounded metric exactly when it is complete for the
original metric. -/
theorem completeSpace_iff (m : MetricSpace X) :
    m.standardBounded.IsComplete ↔ m.IsComplete := by
  change @CompleteSpace X m.standardBounded.toUniformSpace ↔
    @CompleteSpace X m.toUniformSpace
  rw [toUniformSpace_eq]

end standardBounded

end MetricSpace

end
