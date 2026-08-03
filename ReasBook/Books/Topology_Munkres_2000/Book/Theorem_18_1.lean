module

public import Mathlib.Topology.Continuous

public section

open Filter Set

universe u v

/- Theorem 18.1 (1). Conditions (1) and (2): continuity is equivalent to mapping
the closure of every set into the closure of its image. -/
#check continuous_iff_image_closure_subset_closure_image

/- Theorem 18.1 (2). Conditions (1) and (3): continuity is equivalent to the
preimage of every closed set being closed. -/
#check continuous_iff_isClosed

/-- A map is continuous at `x` exactly when each open set containing `f x` contains
the image of some open set containing `x`. -/
theorem continuousAt_iff_open_neighborhood_image_subset {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (x : X) :
    ContinuousAt f x ↔
      ∀ (V : Set Y) (_ : IsOpen V) (_ : f x ∈ V),
        ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ f '' U ⊆ V := by
  rw [continuousAt_def]
  constructor
  · intro hf V hV hxV
    obtain ⟨U, hU, hU_open, hxU⟩ := mem_nhds_iff.mp (hf V (hV.mem_nhds hxV))
    exact ⟨U, hU_open, hxU, image_subset_iff.mpr hU⟩
  · intro hf V hV
    obtain ⟨W, hWV, hW_open, hfxW⟩ := mem_nhds_iff.mp hV
    obtain ⟨U, hU_open, hxU, hUW⟩ := hf W hW_open hfxW
    exact mem_of_superset (hU_open.mem_nhds hxU) (image_subset_iff.mp (hUW.trans hWV))

/-- Theorem 18.1 (3). Conditions (1) and (4): continuity is equivalent to every
open set containing `f x` containing the image of an open set containing `x`. -/
theorem continuous_iff_open_neighborhood_image_subset {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔
      ∀ (x : X) (V : Set Y) (_ : IsOpen V) (_ : f x ∈ V),
        ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ f '' U ⊆ V := by
  rw [continuous_iff_continuousAt]
  exact forall_congr' (continuousAt_iff_open_neighborhood_image_subset f)
