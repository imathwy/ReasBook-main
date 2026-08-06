import Mathlib.Topology.Separation.Hausdorff

universe u v w

open Topology

-- Analogy: `WeaklyLocallyCompactSpace` and `CompactlyGeneratedSpace`
-- use topological property classes.
/-- Definition 5.1.4. A topological space `X` is weak Hausdorff if `Set.range g` is closed in `X`
for every continuous map `g : K → X` from a compact Hausdorff space `K`. -/
@[mk_iff weaklyHausdorffSpace_iff]
class WeaklyHausdorffSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- The image of a continuous map from a compact Hausdorff space is closed. -/
  isClosed_range {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K] (g : K → X)
      (hg : Continuous g) : IsClosed (Set.range g)

/-- Every Hausdorff space is weak Hausdorff. -/
instance T2Space.toWeaklyHausdorffSpace (X : Type u) [TopologicalSpace X] [T2Space X] :
    WeaklyHausdorffSpace.{u, v} X where
  isClosed_range g hg := by
    simpa using (hg.isClosedMap.isClosed_range : IsClosed (Set.range g))

/-- In a weak Hausdorff space, the range of a continuous map from a compact Hausdorff space is
closed. -/
theorem Continuous.isClosed_range {X : Type u} [TopologicalSpace X]
    [hX : WeaklyHausdorffSpace.{u, v} X]
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K] {g : K → X}
    (hg : Continuous g) : IsClosed (Set.range g) :=
  hX.isClosed_range g hg

/-- If the codomain of a topological embedding is weak Hausdorff, then so is its domain. -/
protected theorem Topology.IsEmbedding.weaklyHausdorffSpace
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [hY : WeaklyHausdorffSpace.{v, w} Y] {f : X → Y} (hf : Topology.IsEmbedding f) :
    WeaklyHausdorffSpace.{u, w} X where
  isClosed_range := by
    intro K _ _ _ g hg
    have hclosed : IsClosed (Set.range (f ∘ g)) :=
      hY.isClosed_range (f ∘ g) (hf.continuous.comp hg)
    simpa [Set.range_comp, hf.injective.preimage_image] using
      hf.isClosed_preimage (Set.range (f ∘ g)) hclosed

/-- Every subspace of a weak Hausdorff space is weak Hausdorff. -/
instance Subtype.weaklyHausdorffSpace {X : Type u} [TopologicalSpace X]
    [WeaklyHausdorffSpace.{u, v} X] {p : X → Prop} : WeaklyHausdorffSpace.{u, v} (Subtype p) :=
  IsEmbedding.subtypeVal.weaklyHausdorffSpace
