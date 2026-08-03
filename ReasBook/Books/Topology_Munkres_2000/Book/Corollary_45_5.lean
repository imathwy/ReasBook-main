module

public import Topology_Munkres_2000.Book.Corollary_45_5.ProperTarget
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

universe u

/-- Corollary 45.5 (1). For the square metric on finite-dimensional real space, a
family of continuous maps from a compact space is compact in the uniform topology
exactly when it is closed, bounded in the supremum metric, and equicontinuous. -/
theorem isCompact_iff_closed_bounded_equicontinuous_sup
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {n : ℕ}
    (𝓕 : Set (BoundedContinuousFunction X (Fin n → ℝ))) :
    IsCompact 𝓕 ↔ IsClosed 𝓕 ∧ Bornology.IsBounded 𝓕 ∧
      Equicontinuous (fun f : 𝓕 ↦ (f : X → Fin n → ℝ)) :=
  BoundedContinuousFunction.isCompact_iff_isClosed_isBounded_equicontinuous 𝓕

/-- Corollary 45.5 (2). For the Euclidean metric on finite-dimensional real space, a
family of continuous maps from a compact space is compact in the uniform topology
exactly when it is closed, bounded in the supremum metric, and equicontinuous. -/
theorem isCompact_iff_closed_bounded_equicontinuous_euclidean
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {n : ℕ}
    (𝓕 : Set (BoundedContinuousFunction X (EuclideanSpace ℝ (Fin n)))) :
    IsCompact 𝓕 ↔ IsClosed 𝓕 ∧ Bornology.IsBounded 𝓕 ∧
      Equicontinuous (fun f : 𝓕 ↦ (f : X → EuclideanSpace ℝ (Fin n))) :=
  BoundedContinuousFunction.isCompact_iff_isClosed_isBounded_equicontinuous 𝓕

end
