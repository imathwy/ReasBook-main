module

public import Topology_Munkres_2000.Book.Definition_18_3

public section

universe u v

/-- Definition 18.4: A function between topological spaces is a homeomorphism if and
only if it is bijective and its direct image preserves and reflects openness. -/
theorem isHomeomorph_iff_bijective_isOpen_image {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    IsHomeomorph f ↔ Function.Bijective f ∧
      ∀ U : Set X, IsOpen (f '' U) ↔ IsOpen U := by
  constructor
  · intro hf
    refine ⟨hf.bijective, fun U ↦ ⟨fun hU ↦ ?_, hf.isOpenMap U⟩⟩
    rw [← hf.injective.preimage_image U]
    exact hf.continuous.isOpen_preimage _ hU
  · rintro ⟨hf, h_open⟩
    refine ⟨?_, fun U hU ↦ (h_open U).2 hU, hf⟩
    rw [continuous_def]
    intro V hV
    apply (h_open (f ⁻¹' V)).1
    rwa [hf.surjective.image_preimage V]
