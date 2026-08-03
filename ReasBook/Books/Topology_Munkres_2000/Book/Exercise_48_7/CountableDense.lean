module

public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Baire.CompleteMetrizable

public section

/-- A countable dense subset of `ℝ` is not a `Gδ` set. -/
theorem Set.Countable.not_isGδ_of_dense {D : Set ℝ} (hD_countable : D.Countable)
    (hD_dense : Dense D) : ¬ IsGδ D := by
  intro hD_gdelta
  -- A dense `Gδ` subset of the Baire space `ℝ` cannot be meagre.
  apply not_isMeagre_of_isGδ_of_dense hD_gdelta hD_dense
  rw [isMeagre_iff_countable_union_isNowhereDense]
  -- Cover the countable set by its singleton subsets, each of which is nowhere dense.
  refine ⟨(fun x : ℝ => {x}) '' D, ?_, hD_countable.image _, ?_⟩
  · rintro s ⟨x, -, rfl⟩
    simp only [IsNowhereDense, closure_singleton, interior_singleton]
  · rw [Set.sUnion_image, Set.biUnion_of_singleton]
