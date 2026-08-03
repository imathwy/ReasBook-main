module

public import Topology_Munkres_2000.Book.Definition_28_6.ShrinkingMap
public import Mathlib.Topology.MetricSpace.Contracting

public section

universe u

open scoped NNReal

/-- A self-map of a metric space is a contraction if it is contracting with some constant. -/
def IsContraction {X : Type u} [MetricSpace X] (f : X → X) : Prop :=
  ∃ K : ℝ≥0, ContractingWith K f

namespace ContractingWith

/-- A map contracting with a specified constant is a contraction. -/
theorem isContraction {X : Type u} [MetricSpace X] {K : ℝ≥0} {f : X → X}
    (hf : ContractingWith K f) : IsContraction f :=
  ⟨K, hf⟩

end ContractingWith

namespace IsContraction

/-- A contraction admits a contraction constant. -/
theorem exists_contractingWith {X : Type u} [MetricSpace X] {f : X → X}
    (hf : IsContraction f) : ∃ K : ℝ≥0, ContractingWith K f :=
  hf

/-- Every contraction is a shrinking map. -/
theorem isShrinkingMap {X : Type u} [MetricSpace X] {f : X → X}
    (hf : IsContraction f) : IsShrinkingMap f := by
  obtain ⟨K, hK, hf⟩ := hf
  rw [isShrinkingMap_iff]
  intro x y hxy
  refine lt_of_le_of_lt (hf.dist_le_mul x y) ?_
  simpa only [NNReal.smul_def, one_mul] using
    mul_lt_mul_of_pos_right (NNReal.coe_lt_one.2 hK) (dist_pos.2 hxy)

end IsContraction

/-- A self-map is a contraction exactly when it satisfies the textbook distance inequality for
some constant less than one. -/
theorem isContraction_iff {X : Type u} [MetricSpace X] (f : X → X) :
    IsContraction f ↔ ∃ K : ℝ≥0, K < 1 ∧ ∀ x y, dist (f x) (f y) ≤ K * dist x y := by
  simp only [IsContraction, ContractingWith, lipschitzWith_iff_dist_le_mul]
