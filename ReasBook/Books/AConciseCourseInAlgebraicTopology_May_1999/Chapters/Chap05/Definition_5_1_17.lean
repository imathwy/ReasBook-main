import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

universe u v

open scoped Topology

-- Semantic search hit: `TopologicalSpace.compactlyGenerated`; local Chapter 5 precedent uses this
-- as the canonical owner for k-ification, so this item is formalized as source-facing product
-- topology abbreviations on `X × Y`.

/-- The textbook notation `X ×_c Y` for the usual product topology on `X × Y`. -/
abbrev ordinaryProductTopology (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] : TopologicalSpace (X × Y) :=
  instTopologicalSpaceProd

scoped[Topology] notation X " ×_c " Y => ordinaryProductTopology X Y

/-- Definition 5.1.17. The compactly generated product topology on `X × Y` is the
k-ification of the ordinary product topology `X ×_c Y`. -/
abbrev compactlyGeneratedProductTopology (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] : TopologicalSpace (X × Y) :=
  let _ : TopologicalSpace (X × Y) := X ×_c Y
  TopologicalSpace.compactlyGenerated.{max u v} (X × Y)

/-- `compactlyGeneratedProductTopology X Y` is the k-ification of the ordinary product topology on
`X × Y`, namely `TopologicalSpace.compactlyGenerated (X × Y)` for the usual product topology. -/
@[simp]
theorem compactlyGeneratedProductTopology_def (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] :
    compactlyGeneratedProductTopology X Y =
      TopologicalSpace.compactlyGenerated.{max u v} (X × Y) := rfl
