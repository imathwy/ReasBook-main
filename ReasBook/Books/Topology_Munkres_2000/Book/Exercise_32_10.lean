module

import Topology_Munkres_2000.Book.Exercise_32_9
public import Topology_Munkres_2000.Book.Exercise_32_10.Separation
import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-- The additive topological group `ℝ → ℝ`, written multiplicatively, is not normal. -/
theorem multiplicativeRealPower_notNormal :
    ¬ NormalSpace (Multiplicative (ℝ → ℝ)) := by
  exact (realPower_notNormal : ¬ NormalSpace (ℝ → ℝ))

/-- Exercise 32.10: Not every topological group is normal. The group
`Multiplicative (ℝ → ℝ)` is a `T₁` topological group that is not normal. -/
theorem multiplicativeRealPower_counterexample :
    IsTopologicalGroup (Multiplicative (ℝ → ℝ)) ∧
      T1Space (Multiplicative (ℝ → ℝ)) ∧
      ¬ NormalSpace (Multiplicative (ℝ → ℝ)) := by
  exact ⟨inferInstance, inferInstance, multiplicativeRealPower_notNormal⟩

/-- The counterexample to Exercise 32.10 is not normal in the book's `T4Space` convention. -/
theorem multiplicativeRealPower_notT4 :
    ¬ T4Space (Multiplicative (ℝ → ℝ)) := by
  intro h
  exact multiplicativeRealPower_notNormal h.toNormalSpace
