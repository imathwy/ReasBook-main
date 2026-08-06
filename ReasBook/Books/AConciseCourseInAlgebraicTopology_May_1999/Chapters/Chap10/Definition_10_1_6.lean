import Mathlib.Topology.CWComplex.Classical.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.SpacePair

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

namespace Topology.RelCWComplex

variable {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable {C D : Set X} {E F : Set Y}
variable [RelCWComplex C D] [RelCWComplex E F]

-- Semantic recall via `lean_leansearch`: `Topology.RelCWComplex.skeleton` is the canonical
-- mathlib owner for relative CW skeleta, and Chapter 13 provides the repo's `SpacePair.Hom` API
-- for actual maps of pairs. This item records the source-facing relative cellularity predicate on
-- genuine pair maps by the explicit base-plus-cells skeleta, and exposes the canonical skeleton
-- bridge under Hausdorff hypotheses.

/-- The space pair `(A, B)` attached to an ambient subset `A` with distinguished base subspace
`B`. Its ambient space is the subtype `A`, and its distinguished subspace is `B ∩ A` inside that
subtype. -/
abbrev relativeSpacePair {Z : Type u} [TopologicalSpace Z] (A B : Set Z) : SpacePair where
  space := TopCat.of A
  subspace := { x | (x : Z) ∈ B }

/-- The relative `n`-skeleton of `(C, D)` viewed as a subset of the subtype space `C`. -/
abbrev relativeSkeletonSubspace (C : Set X) {D : Set X} [RelCWComplex C D] (n : ℕ∞) : Set C :=
  { x | (x : X) ∈ D ∪ ⋃ (m : ℕ) (_ : m < n + 1) (j : cell C m), openCell m j }

/-- The source-facing explicit relative `n`-skeleton inside the subtype `C` agrees with the
canonical relative skeleton `skeleton C n`. -/
theorem mem_relativeSkeletonSubspace_iff
    [T2Space X] (C : Set X) {D : Set X} [RelCWComplex C D] {n : ℕ∞} {x : C} :
    x ∈ relativeSkeletonSubspace C n ↔ (x : X) ∈ skeleton C n := by
  simp [relativeSkeletonSubspace, RelCWComplex.iUnion_openCell_eq_skeleton]

/-- Definition 10.1.6: a map of relative CW complexes is cellular when it is a map of pairs
`(C, D) ⟶ (E, F)` and sends each relative `n`-skeleton into the corresponding relative
`n`-skeleton. -/
class IsCellularMap (f : SpacePair.Hom (relativeSpacePair C D) (relativeSpacePair E F)) : Prop where
  /-- A relative cellular map sends each relative `n`-skeleton into the corresponding relative
  `n`-skeleton. -/
  mapsToSkeleton :
    ∀ n : ℕ, MapsTo f.hom (relativeSkeletonSubspace C n) (relativeSkeletonSubspace E n)

/-- The identity map of a relative CW pair is cellular. -/
instance isCellularMapId :
    IsCellularMap (SpacePair.id (relativeSpacePair C D)) where
  mapsToSkeleton n := by
    intro x hx
    simpa using hx

/-- When the ambient spaces are Hausdorff, a relative cellular map sends each canonical
`n`-skeleton into the corresponding canonical `n`-skeleton. -/
theorem IsCellularMap.mapsTo_skeleton [T2Space X] [T2Space Y]
    {f : SpacePair.Hom (relativeSpacePair C D) (relativeSpacePair E F)}
    (hf : IsCellularMap f) (n : ℕ) :
    MapsTo f.hom
      { x : C | (x : X) ∈ skeleton C n }
      { y : E | (y : Y) ∈ skeleton E n } := by
  intro x hx
  exact (mem_relativeSkeletonSubspace_iff E).1
    (hf.mapsToSkeleton n ((mem_relativeSkeletonSubspace_iff C).2 hx))

end Topology.RelCWComplex
