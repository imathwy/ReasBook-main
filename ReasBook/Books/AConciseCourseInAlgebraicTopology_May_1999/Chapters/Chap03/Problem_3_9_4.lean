import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

namespace IsLocalHomeomorph

/-- A compact-domain Hausdorff local homeomorphism to a Hausdorff target is a covering map. -/
-- Proof sketch: apply `IsCoveringMapOn.of_openPartialHomeomorph` over `Set.univ`; a local
-- homeomorphism already supplies the required local `OpenPartialHomeomorph` charts at each source
-- point.
theorem isCoveringMap_of_compact [CompactSpace X] [T2Space X] [T2Space Y] {f : X → Y}
    (hf : IsLocalHomeomorph f) : IsCoveringMap f := by
  refine isCoveringMap_iff_isCoveringMapOn_univ.mpr ?_
  refine IsCoveringMapOn.of_openPartialHomeomorph hf.continuous ?_
  intro e _
  obtain ⟨φ, heφ, hφ⟩ := hf e
  exact ⟨φ, heφ, hφ.symm⟩

/-- Problem 3.9.4: a compact-domain local homeomorphism from a nonempty Hausdorff space to a
preconnected locally path-connected Hausdorff target is a path-connected covering map. -/
-- Proof sketch: first apply `isCoveringMap_of_compact` to obtain the canonical covering-map
-- owner. The image of a compact-domain local homeomorphism is compact and therefore closed in a
-- Hausdorff codomain, while local homeomorphisms are open; connectedness of the target then
-- forces the image to be all of `Y`, giving surjectivity. Only preconnectedness is needed here:
-- nonemptiness comes from the nonempty compact domain. Finally invoke
-- `IsCoveringMap.isPathConnectedCoveringMap`.
theorem isPathConnectedCoveringMap_of_compact [CompactSpace X] [Nonempty X] [T2Space X]
    [PreconnectedSpace Y] [LocPathConnectedSpace Y] [T2Space Y] {f : X → Y}
    (hf : IsLocalHomeomorph f) : IsPathConnectedCoveringMap f := by
  have hRangeClosed : IsClosed (Set.range f) := (isCompact_range hf.continuous).isClosed
  have hRangeOpen : IsOpen (Set.range f) := hf.isOpenMap.isOpen_range
  have hRangeNonempty : (Set.range f).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨f x, ⟨x, rfl⟩⟩
  have hsurj : Function.Surjective f := by
    rw [← Set.range_eq_univ]
    exact IsClopen.eq_univ ⟨hRangeClosed, hRangeOpen⟩ hRangeNonempty
  exact (hf.isCoveringMap_of_compact).isPathConnectedCoveringMap hsurj

end IsLocalHomeomorph
