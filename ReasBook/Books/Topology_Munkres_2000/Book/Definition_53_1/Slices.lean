module

public import Mathlib.Order.Partition.Basic
public import Mathlib.Topology.Homeomorph.Defs

public section

universe u v

namespace EvenlyCovered

/-- An open set `V` is a slice over `U` for `p` when the restriction of `p` to `V` is a
homeomorphism onto `U`. -/
def IsSlice {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (U : Set B) (V : Set E) : Prop :=
  IsOpen V ∧ ∃ hV : V ⊆ p ⁻¹' U, IsHomeomorph (Set.MapsTo.restrict p V U hV)

end EvenlyCovered

/-- A partition of `p ⁻¹' U` into slices over `U`. -/
def IsSlicePartition {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] (p : E → B) (U : Set B) (P : Partition (p ⁻¹' U)) : Prop :=
  ∀ V ∈ P, EvenlyCovered.IsSlice p U V

namespace IsSlicePartition

/-- Every part of a slice partition is a slice. -/
theorem isSlice {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} {U : Set B} {P : Partition (p ⁻¹' U)} (hP : IsSlicePartition p U P)
    {V : Set E} (hV : V ∈ P) : EvenlyCovered.IsSlice p U V :=
  hP V hV

/-- Every part of a slice partition is open. -/
theorem isOpen {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} {U : Set B} {P : Partition (p ⁻¹' U)} (hP : IsSlicePartition p U P)
    {V : Set E} (hV : V ∈ P) : IsOpen V :=
  (hP.isSlice hV).1

/-- The restriction of `p` to each part of a slice partition is a homeomorphism onto `U`. -/
theorem isHomeomorph {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} {U : Set B} {P : Partition (p ⁻¹' U)}
    (hP : IsSlicePartition p U P) {V : Set E} (hV : V ∈ P) :
    IsHomeomorph (Set.MapsTo.restrict p V U fun _ hx ↦ P.le_of_mem hV hx) := by
  obtain ⟨hVU, hp⟩ := (hP.isSlice hV).2
  simpa only [Subsingleton.elim hVU] using hp

end IsSlicePartition
