module

public import Topology_Munkres_2000.Book.Definition_45_3.PointwiseBounded
public import Topology_Munkres_2000.Book.Theorem_47_1
public import Mathlib.Topology.MetricSpace.ProperSpace

import Mathlib.Topology.MetricSpace.Bounded

public section

universe u v

namespace ContinuousMap

/-- For a proper metric target, a family of continuous maps from a locally compact Hausdorff
space has compact closure in the compact-open topology exactly when it is equicontinuous and
pointwise bounded. -/
theorem isCompact_closure_iff_equicontinuous_and_pointwiseBounded
    {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MetricSpace Y] [ProperSpace Y] (𝓕 : Set C(X, Y)) :
    IsCompact (closure 𝓕) ↔
      Equicontinuous (fun f : 𝓕 ↦ (f : X → Y)) ∧
        PointwiseBounded (fun f : 𝓕 ↦ (f : X → Y)) := by
  constructor
  · intro h_compact
    obtain ⟨h_equicontinuous, h_pointwise⟩ :=
      (isCompact_closure_iff_equicontinuous_and_pointwiseCompact 𝓕).1 h_compact
    refine ⟨h_equicontinuous, pointwiseBounded_iff.2 fun x ↦ ?_⟩
    have hrange : Set.range (fun f : 𝓕 ↦ (f : X → Y) x) =
        (fun f : C(X, Y) ↦ f x) '' 𝓕 :=
      (Set.image_eq_range (fun f : C(X, Y) ↦ f x) 𝓕).symm
    rw [hrange]
    exact (h_pointwise x).isBounded.subset subset_closure
  · rintro ⟨h_equicontinuous, h_pointwise⟩
    apply (isCompact_closure_iff_equicontinuous_and_pointwiseCompact 𝓕).2
    refine ⟨h_equicontinuous, fun x ↦ ?_⟩
    have hrange : (fun f : C(X, Y) ↦ f x) '' 𝓕 =
        Set.range (fun f : 𝓕 ↦ (f : X → Y) x) :=
      Set.image_eq_range (fun f : C(X, Y) ↦ f x) 𝓕
    rw [hrange]
    exact (pointwiseBounded_iff.1 h_pointwise x).isCompact_closure

end ContinuousMap
