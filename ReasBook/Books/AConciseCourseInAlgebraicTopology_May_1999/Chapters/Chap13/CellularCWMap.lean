import Mathlib.Topology.Category.TopCat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_3

noncomputable section

open CategoryTheory
open Topology
open Topology.CWComplex
open Topology.RelCWComplex

/-- The absolute pair map `(X, ∅) ⟶ (Y, ∅)` induced by a `TopCat` morphism `f : X ⟶ Y`. This
local bridge keeps the Chapter 13 cellular-map API independent of Chapter 10's later homotopy
corollaries. -/
private abbrev topCatAbsolutePairHom
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) :
    SpacePair.Hom
      (relativeSpacePair (Set.univ : Set X) (∅ : Set X))
      (relativeSpacePair (Set.univ : Set Y) (∅ : Set Y)) where
  hom :=
    TopCat.ofHom
      ⟨fun x ↦ ⟨f x.1, Set.mem_univ _⟩,
        ((map_continuous f.hom).comp continuous_subtype_val).subtype_mk
          fun _ ↦ Set.mem_univ _⟩
  map_subspace' := fun {_} hx ↦ False.elim hx

/-- A morphism of `TopCat` between CW complexes is cellular when its underlying continuous map is
cellular in the Chapter 10 sense. This is the Chapter 13 bridge from the continuous-map owner
`ContinuousMap.IsCellular` to the `TopCat` morphism language used in cellular chain constructions.
-/
abbrev IsCellularCWMap
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) : Prop :=
  Topology.RelCWComplex.IsCellularMap (topCatAbsolutePairHom f)

namespace IsCellularCWMap

/-- A cellular `TopCat` morphism sends each chosen CW skeleton into the corresponding chosen
CW skeleton. -/
theorem mapsToSkeleton
    {X Y : TopCat} [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    {f : X ⟶ Y} (hf : IsCellularCWMap f) (n : ℕ) :
    Set.MapsTo f (cellularSkeleton X n) (cellularSkeleton Y n) := by
  -- Reinterpret the `TopCat` morphism as an absolute pair map so the relative-cellular skeleton
  -- API can be applied directly.
  intro x hx
  let x' : (Set.univ : Set X) := ⟨x, Set.mem_univ x⟩
  have hx' :
      x' ∈ { x : (Set.univ : Set X) | (x : X) ∈ cellularSkeleton X n } := by
    simpa using hx
  have hpair : IsCellularMap (topCatAbsolutePairHom f) := hf
  have hy := hpair.mapsTo_skeleton n hx'
  simpa [cellularSkeleton] using hy

end IsCellularCWMap
