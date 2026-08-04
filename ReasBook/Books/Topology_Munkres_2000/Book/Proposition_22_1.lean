module

public import Topology_Munkres_2000.Book.Definition_22_2
public import Mathlib.Topology.Maps.Basic

public section

universe u v

namespace Topology

/-- Proposition 22.1 (open-set form): A surjective map is a quotient map
exactly when it is continuous and maps saturated open sets to open sets. -/
theorem isQuotientMap_iff_isOpen_image_of_saturated {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hp : Function.Surjective p) :
    IsQuotientMap p ↔
      Continuous p ∧
        ∀ U : Set X, Set.IsSaturated p U → IsOpen U → IsOpen (p '' U) := by
  constructor
  · intro hq
    refine ⟨hq.continuous, ?_⟩
    intro U hU_sat hU
    -- Coinducing reflects openness, and saturation identifies the relevant preimage with `U`.
    apply hq.isCoinducing.isOpen_preimage.mp
    rwa [Set.isSaturated_iff_preimage_image.mp hU_sat]
  · rintro ⟨hcont, himage⟩
    refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen ?_, hp⟩
    intro V
    constructor
    · intro hpre
      -- A preimage is saturated, so its open image is `V` by surjectivity.
      have hopenImage : IsOpen (p '' (p ⁻¹' V)) :=
        himage (p ⁻¹' V) (Set.isSaturated_preimage p V) hpre
      simpa only [hp.image_preimage V] using hopenImage
    · intro hV
      -- Continuity supplies the converse implication in the coinducing criterion.
      exact hV.preimage hcont

/-- Proposition 22.1 (closed-set form): A surjective map is a quotient map
exactly when it is continuous and maps saturated closed sets to closed sets. -/
theorem isQuotientMap_iff_isClosed_image_of_saturated {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hp : Function.Surjective p) :
    IsQuotientMap p ↔
      Continuous p ∧
        ∀ C : Set X, Set.IsSaturated p C → IsClosed C → IsClosed (p '' C) := by
  constructor
  · intro hq
    refine ⟨hq.continuous, ?_⟩
    intro C hC_sat hC
    -- Coinducing reflects closedness, and saturation reduces its preimage test to `C`.
    apply hq.isCoinducing.isClosed_preimage.mp
    rwa [Set.isSaturated_iff_preimage_image.mp hC_sat]
  · rintro ⟨hcont, himage⟩
    rw [isQuotientMap_iff_isClosed]
    refine ⟨hp, fun V ↦ ⟨?_, ?_⟩⟩
    · intro hV
      -- Continuity sends closed codomain sets to closed preimages.
      exact hV.preimage hcont
    · intro hpre
      -- The saturated preimage has closed image, which surjectivity identifies with `V`.
      have hclosedImage : IsClosed (p '' (p ⁻¹' V)) :=
        himage (p ⁻¹' V) (Set.isSaturated_preimage p V) hpre
      simpa only [hp.image_preimage V] using hclosedImage

/-- Combined form of Proposition 22.1: A surjective map is a quotient map exactly when it is
continuous and maps saturated open sets to open sets, or saturated closed sets to closed sets. -/
theorem isQuotientMap_iff_continuous_maps_saturated_open_or_closed
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (hp : Function.Surjective p) :
    IsQuotientMap p ↔
      Continuous p ∧
        ((∀ U : Set X, Set.IsSaturated p U → IsOpen U → IsOpen (p '' U)) ∨
          ∀ C : Set X, Set.IsSaturated p C → IsClosed C → IsClosed (p '' C)) := by
  constructor
  · intro hq
    -- The open-set criterion supplies one of the two equivalent alternatives.
    refine ⟨hq.continuous, Or.inl ?_⟩
    exact (isQuotientMap_iff_isOpen_image_of_saturated p hp).mp hq |>.2
  · rintro ⟨hcont, hopen | hclosed⟩
    · exact (isQuotientMap_iff_isOpen_image_of_saturated p hp).mpr ⟨hcont, hopen⟩
    · exact (isQuotientMap_iff_isClosed_image_of_saturated p hp).mpr ⟨hcont, hclosed⟩

namespace IsQuotientMap

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A quotient map sends every saturated open set to an open set. -/
theorem isOpen_image_of_isSaturated {p : X → Y} (hp : IsQuotientMap p) {U : Set X}
    (hU_sat : Set.IsSaturated p U) (hU : IsOpen U) :
    IsOpen (p '' U) :=
  (isQuotientMap_iff_isOpen_image_of_saturated p hp.surjective).mp hp |>.2 U hU_sat hU

/-- A quotient map sends every saturated closed set to a closed set. -/
theorem isClosed_image_of_isSaturated {p : X → Y} (hp : IsQuotientMap p) {C : Set X}
    (hC_sat : Set.IsSaturated p C) (hC : IsClosed C) :
    IsClosed (p '' C) :=
  (isQuotientMap_iff_isClosed_image_of_saturated p hp.surjective).mp hp |>.2 C hC_sat hC

end IsQuotientMap

end Topology

end
