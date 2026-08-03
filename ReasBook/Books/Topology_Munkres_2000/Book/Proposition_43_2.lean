module

public import Topology_Munkres_2000.Book.Theorem_20_1.BoundedMetric
public import Mathlib.Topology.UniformSpace.Cauchy

public section

universe u

namespace MetricSpace

variable {X : Type u}

/-- Helper for Proposition 43.2: a sequence is Cauchy with respect to an explicitly specified
metric. -/
abbrev IsCauchySeq (m : MetricSpace X) (u : ℕ → X) : Prop :=
  @CauchySeq X ℕ m.toUniformSpace inferInstance u

/-- Helper for Proposition 43.2: a sequence converges to `x` with respect to an explicitly
specified metric. -/
abbrev ConvergesTo (m : MetricSpace X) (u : ℕ → X) (x : X) : Prop :=
  Filter.Tendsto u Filter.atTop (@nhds X m.toUniformSpace.toTopologicalSpace x)

/-- Helper for Proposition 43.2: a metric is complete when its induced uniform space is
complete. -/
abbrev IsComplete (m : MetricSpace X) : Prop :=
  @CompleteSpace X m.toUniformSpace

namespace standardBounded

/-- Proposition 43.2: the standard bounded metric induces the same uniform space as the
original metric. -/
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
    have hdist_one : m.dist p.1 p.2 < 1 :=
      (min_lt_iff.mp (lt_of_lt_of_le hp (min_le_right ε 1))).resolve_right (lt_irrefl 1)
    rw [min_eq_left (le_of_lt hdist_one)] at hp
    exact lt_of_lt_of_le hp (min_le_left ε 1)

/-- Helper for Proposition 43.2: the standard bounded and original metrics have the same
Cauchy sequences. -/
theorem cauchySeq_iff (m : MetricSpace X) (u : ℕ → X) :
    m.standardBounded.IsCauchySeq u ↔ m.IsCauchySeq u := by
  change @CauchySeq X ℕ m.standardBounded.toUniformSpace inferInstance u ↔
    @CauchySeq X ℕ m.toUniformSpace inferInstance u
  rw [toUniformSpace_eq]

/-- Helper for Proposition 43.2: the standard bounded and original metrics have the same
convergent sequences and limits. -/
theorem convergesTo_iff (m : MetricSpace X) (u : ℕ → X) (x : X) :
    m.standardBounded.ConvergesTo u x ↔ m.ConvergesTo u x := by
  change Filter.Tendsto u Filter.atTop
      (@nhds X m.standardBounded.toUniformSpace.toTopologicalSpace x) ↔
    Filter.Tendsto u Filter.atTop (@nhds X m.toUniformSpace.toTopologicalSpace x)
  rw [toUniformSpace_eq]

/-- Helper for Proposition 43.2: completeness is unchanged by passing to the standard bounded
metric. -/
theorem completeSpace_iff (m : MetricSpace X) :
    m.standardBounded.IsComplete ↔ m.IsComplete := by
  change @CompleteSpace X m.standardBounded.toUniformSpace ↔
    @CompleteSpace X m.toUniformSpace
  rw [toUniformSpace_eq]

end standardBounded

end MetricSpace

end
