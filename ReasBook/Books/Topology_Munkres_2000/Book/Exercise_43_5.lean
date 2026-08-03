module

public import Topology_Munkres_2000.Book.Definition_28_7.Contraction

public section

universe u

open scoped NNReal

/-- A map contracting with a specified constant on a nonempty complete metric space has a unique
fixed point. -/
theorem ContractingWith.existsUnique_fixedPoint {X : Type u} [MetricSpace X] [Nonempty X]
    [CompleteSpace X] {K : ℝ≥0} {f : X → X} (hf : ContractingWith K f) :
    ∃! x, Function.IsFixedPt f x := by
  refine ⟨hf.fixedPoint f, hf.fixedPoint_isFixedPt, ?_⟩
  intro x hx
  exact hf.fixedPoint_unique hx

/-- Exercise 43.5: a contraction of a nonempty complete metric space has a unique fixed point. -/
theorem IsContraction.existsUnique_fixedPoint {X : Type u} [MetricSpace X] [Nonempty X]
    [CompleteSpace X] {f : X → X} (hf : IsContraction f) :
    ∃! x, Function.IsFixedPt f x := by
  obtain ⟨K, hK⟩ := hf.exists_contractingWith
  exact hK.existsUnique_fixedPoint
