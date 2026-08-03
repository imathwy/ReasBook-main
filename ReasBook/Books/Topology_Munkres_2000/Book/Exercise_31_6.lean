module

public import Mathlib.Topology.Separation.Regular

public section

universe u v

namespace IsClosedMap

/-- Helper for Exercise 31.6: disjoint sets have disjoint kernel images under a surjection. -/
private lemma disjoint_kernImage_of_surjective {X : Type u} {Y : Type v} {p : X → Y}
    (hp_surjective : Function.Surjective p) {s t : Set X} (hst : Disjoint s t) :
    Disjoint (Set.kernImage p s) (Set.kernImage p t) := by
  -- Pull any alleged common target point back to a common source point.
  rw [Set.disjoint_left]
  intro y hys hyt
  obtain ⟨x, rfl⟩ := hp_surjective y
  -- Membership in both kernel images contradicts source disjointness.
  exact Set.disjoint_left.mp hst (hys rfl) (hyt rfl)

/-- Helper for Exercise 31.6: a closed continuous surjection carries normality to its codomain. -/
private lemma normalSpace_of_surjective {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [NormalSpace X] {p : X → Y}
    (hp_closed : IsClosedMap p) (hp_continuous : Continuous p)
    (hp_surjective : Function.Surjective p) : NormalSpace Y := by
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

/-- Helper for Exercise 31.6: a closed surjection carries the `T₁` property to its codomain. -/
private lemma t1Space_of_surjective {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [T1Space X] {p : X → Y}
    (hp_closed : IsClosedMap p) (hp_surjective : Function.Surjective p) : T1Space Y := by
  -- Represent each target singleton as the image of a source singleton.
  constructor
  intro y
  obtain ⟨x, rfl⟩ := hp_surjective y
  -- Closedness is preserved by the closed map.
  simpa only [Set.image_singleton] using hp_closed {x} isClosed_singleton

/-- Exercise 31.6: A closed continuous surjection carries the `T₄` separation property from its
domain to its codomain. -/
theorem t4Space {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T4Space X] {p : X → Y} (hp_closed : IsClosedMap p)
    (hp_continuous : Continuous p) (hp_surjective : Function.Surjective p) : T4Space Y where
  toT1Space := t1Space_of_surjective hp_closed hp_surjective
  toNormalSpace := normalSpace_of_surjective hp_closed hp_continuous hp_surjective

end IsClosedMap
