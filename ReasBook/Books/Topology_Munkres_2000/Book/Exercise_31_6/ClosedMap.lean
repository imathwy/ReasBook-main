module

public import Mathlib.Topology.Separation.Regular

public section

universe u v

namespace IsClosedMap

/-- Helper for Exercise 31.6: disjoint sets have disjoint kernel images under a surjection. -/
private lemma disjoint_kernImage_of_surjective {X : Type u} {Y : Type v} {p : X → Y}
    (hp_surjective : Function.Surjective p) {u v : Set X} (huv : Disjoint u v) :
    Disjoint (Set.kernImage p u) (Set.kernImage p v) := by
  -- Pull any alleged common target point back to a common source point.
  rw [Set.disjoint_left]
  intro y hyu hyv
  obtain ⟨x, rfl⟩ := hp_surjective y
  -- Membership in both kernel images contradicts the source disjointness.
  exact Set.disjoint_left.mp huv (hyu rfl) (hyv rfl)

/-- A closed continuous surjection carries normality from its domain to its codomain. -/
theorem normalSpace {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [NormalSpace X] {p : X → Y} (hp_closed : IsClosedMap p)
    (hp_continuous : Continuous p) (hp_surjective : Function.Surjective p) :
    NormalSpace Y := by
  -- Separate the closed preimages in the normal domain.
  constructor
  intro s t hs ht hst
  obtain ⟨u, v, hu_open, hv_open, hsu, htv, huv⟩ :=
    normal_separation (hs.preimage hp_continuous) (ht.preimage hp_continuous)
      (hst.preimage p)
  -- Push the separating neighborhoods to the codomain using kernel images.
  refine ⟨Set.kernImage p u, Set.kernImage p v, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isClosedMap_iff_kernImage.mp hp_closed) hu_open
  · exact (isClosedMap_iff_kernImage.mp hp_closed) hv_open
  · exact Set.subset_kernImage_iff.mpr hsu
  · exact Set.subset_kernImage_iff.mpr htv
  · exact disjoint_kernImage_of_surjective hp_surjective huv

/-- A closed surjection carries the `T₁` separation property from its domain to its codomain. -/
theorem t1Space {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] {p : X → Y} (hp_closed : IsClosedMap p)
    (hp_surjective : Function.Surjective p) : T1Space Y := by
  -- Represent each target singleton as the image of a source singleton.
  constructor
  intro y
  obtain ⟨x, rfl⟩ := hp_surjective y
  -- Closedness is preserved by the closed map.
  simpa only [Set.image_singleton] using hp_closed {x} isClosed_singleton

/-- A closed continuous surjection carries the `T₄` separation property from its domain to its
codomain. -/
theorem t4Space {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T4Space X] {p : X → Y} (hp_closed : IsClosedMap p)
    (hp_continuous : Continuous p) (hp_surjective : Function.Surjective p) : T4Space Y where
  toT1Space := hp_closed.t1Space hp_surjective
  toNormalSpace := hp_closed.normalSpace hp_continuous hp_surjective

end IsClosedMap
