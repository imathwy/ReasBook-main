module

public import Topology_Munkres_2000.Book.Proposition_43_2.Convergence
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.UniformSpace.Cauchy

public section

open scoped Uniformity

universe u

namespace MetricSpace

variable {X : Type u}

/-- Two metrics on the same type are metrically equivalent when the identity map is uniformly
continuous in both directions. -/
def Equivalent (m m' : MetricSpace X) : Prop :=
  UniformContinuous[m.toUniformSpace, m'.toUniformSpace] id ∧
    UniformContinuous[m'.toUniformSpace, m.toUniformSpace] id

/-- Metric equivalence is exactly uniform continuity of the identity map in both directions. -/
theorem equivalent_iff (m m' : MetricSpace X) :
    m.Equivalent m' ↔
      UniformContinuous[m.toUniformSpace, m'.toUniformSpace] id ∧
        UniformContinuous[m'.toUniformSpace, m.toUniformSpace] id := Iff.rfl

/-- Two metrics are equivalent exactly when they induce the same uniform space. -/
theorem equivalent_iff_toUniformSpace_eq (m m' : MetricSpace X) :
    m.Equivalent m' ↔ m.toUniformSpace = m'.toUniformSpace := by
  rw [Equivalent, ← le_iff_uniformContinuous_id, ← le_iff_uniformContinuous_id]
  constructor
  · exact fun h ↦ le_antisymm h.1 h.2
  · exact fun h ↦ ⟨h.le, h.ge⟩

namespace Equivalent

/-- Every metric is equivalent to itself. -/
theorem refl (m : MetricSpace X) : m.Equivalent m := ⟨uniformContinuous_id, uniformContinuous_id⟩

/-- Metric equivalence is symmetric. -/
theorem symm {m m' : MetricSpace X} (h : m.Equivalent m') : m'.Equivalent m := ⟨h.2, h.1⟩

/-- Metric equivalence is transitive. -/
theorem trans {m m' m'' : MetricSpace X} (h : m.Equivalent m')
    (h' : m'.Equivalent m'') : m.Equivalent m'' := by
  rw [equivalent_iff_toUniformSpace_eq] at h h' ⊢
  exact h.trans h'

/-- Completeness is invariant under metric equivalence. -/
theorem completeSpace_iff {m m' : MetricSpace X} (h : m.Equivalent m') :
    m.IsComplete ↔ m'.IsComplete := by
  rw [equivalent_iff_toUniformSpace_eq] at h
  unfold IsComplete
  rw [h]

end Equivalent

end MetricSpace

end
