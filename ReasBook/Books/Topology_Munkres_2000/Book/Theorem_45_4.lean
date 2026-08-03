module

public import Topology_Munkres_2000.Book.Theorem_45_4.ProperTarget
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

universe u

/-- Theorem 45.4 (1). For the square metric on finite-dimensional real space, a family
of continuous maps from a compact space, modeled in the uniform topology by
`BoundedContinuousFunction`, has compact closure exactly when it is equicontinuous and
pointwise bounded. -/
theorem isCompact_closure_iff_equicontinuous_and_pointwiseBounded_sup
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {n : ℕ}
    (𝓕 : Set (BoundedContinuousFunction X (Fin n → ℝ))) :
    IsCompact (closure 𝓕) ↔
      Equicontinuous (fun f : 𝓕 ↦ (f : X → Fin n → ℝ)) ∧
        PointwiseBounded (fun f : 𝓕 ↦ (f : X → Fin n → ℝ)) :=
  BoundedContinuousFunction.isCompact_closure_iff_equicontinuous_and_pointwiseBounded 𝓕

/-- Theorem 45.4 (2). For the Euclidean metric on finite-dimensional real space, a
family of continuous maps from a compact space, modeled in the uniform topology by
`BoundedContinuousFunction`, has compact closure exactly when it is equicontinuous and
pointwise bounded. -/
theorem isCompact_closure_iff_equicontinuous_and_pointwiseBounded_euclidean
    {X : Type u} [TopologicalSpace X] [CompactSpace X] {n : ℕ}
    (𝓕 : Set (BoundedContinuousFunction X (EuclideanSpace ℝ (Fin n)))) :
    IsCompact (closure 𝓕) ↔
      Equicontinuous (fun f : 𝓕 ↦ (f : X → EuclideanSpace ℝ (Fin n))) ∧
        PointwiseBounded (fun f : 𝓕 ↦ (f : X → EuclideanSpace ℝ (Fin n))) :=
  BoundedContinuousFunction.isCompact_closure_iff_equicontinuous_and_pointwiseBounded 𝓕
