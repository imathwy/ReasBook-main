module

public import Topology_Munkres_2000.Book.Exercise_47_2.ProperTarget
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

universe u

namespace ContinuousMap

/-- Exercise 47.2 (square metric). For a locally compact Hausdorff space `X`, a family of
continuous maps `X → Fin n → ℝ` has compact closure in the topology of compact convergence
if and only if it is equicontinuous and pointwise bounded. -/
theorem isCompact_closure_iff_equicontinuous_and_pointwiseBounded_sup
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {n : ℕ} (𝓕 : Set C(X, Fin n → ℝ)) :
    IsCompact (closure 𝓕) ↔
      Equicontinuous (fun f : 𝓕 ↦ (f : X → Fin n → ℝ)) ∧
        PointwiseBounded (fun f : 𝓕 ↦ (f : X → Fin n → ℝ)) :=
  ContinuousMap.isCompact_closure_iff_equicontinuous_and_pointwiseBounded 𝓕

/-- Exercise 47.2 (Euclidean metric). For a locally compact Hausdorff space `X`, a family of
continuous maps `X → EuclideanSpace ℝ (Fin n)` has compact closure in the topology of compact
convergence if and only if it is equicontinuous and pointwise bounded. -/
theorem isCompact_closure_iff_equicontinuous_and_pointwiseBounded_euclidean
    {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {n : ℕ} (𝓕 : Set C(X, EuclideanSpace ℝ (Fin n))) :
    IsCompact (closure 𝓕) ↔
      Equicontinuous (fun f : 𝓕 ↦ (f : X → EuclideanSpace ℝ (Fin n))) ∧
        PointwiseBounded (fun f : 𝓕 ↦ (f : X → EuclideanSpace ℝ (Fin n))) :=
  ContinuousMap.isCompact_closure_iff_equicontinuous_and_pointwiseBounded 𝓕

end ContinuousMap
