module

public import Mathlib.Topology.Constructions
public section

/-- Exercise 22.5: Restricting an open map to an open subset of its domain and
corestricting it to the image of that subset yields an open map. -/
theorem IsOpenMap.restrictImage {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {p : X → Y} (hp : IsOpenMap p) {A : Set X} (hA : IsOpen A) :
    IsOpenMap (Set.MapsTo.restrict p A (p '' A) (Set.mapsTo_image p A)) :=
  hp.mapsToRestrict hA (Set.mapsTo_image p A)
