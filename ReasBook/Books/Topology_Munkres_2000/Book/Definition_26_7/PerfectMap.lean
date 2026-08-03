module

public import Mathlib.Topology.Maps.Proper.Basic

public section

open Function Set Topology

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A perfect map is a surjective proper map. -/
structure IsPerfectMap (f : X → Y) : Prop extends IsProperMap f where
  /-- A perfect map is surjective. -/
  surjective : Surjective f

/-- A map is perfect exactly when it is continuous, closed, surjective, and has compact fibers. -/
theorem isPerfectMap_iff {f : X → Y} :
    IsPerfectMap f ↔
      Continuous f ∧ IsClosedMap f ∧ Surjective f ∧ ∀ y, IsCompact (f ⁻¹' {y}) := by
  constructor
  · intro hf
    have h_proper := hf.toIsProperMap
    rw [isProperMap_iff_isClosedMap_and_compact_fibers] at h_proper
    exact ⟨h_proper.1, h_proper.2.1, hf.surjective, h_proper.2.2⟩
  · rintro ⟨hf, h_closed, h_surjective, h_fiber⟩
    exact ⟨isProperMap_iff_isClosedMap_and_compact_fibers.2 ⟨hf, h_closed, h_fiber⟩,
      h_surjective⟩

namespace IsPerfectMap

/-- A perfect map is closed. -/
lemma isClosedMap {f : X → Y} (hf : IsPerfectMap f) : IsClosedMap f :=
  hf.toIsProperMap.isClosedMap

/-- Every fiber of a perfect map is compact. -/
lemma isCompact_fiber {f : X → Y} (hf : IsPerfectMap f) (y : Y) :
    IsCompact (f ⁻¹' {y}) :=
  hf.toIsProperMap.isCompact_preimage isCompact_singleton

/-- A perfect map is a quotient map. -/
lemma isQuotientMap {f : X → Y} (hf : IsPerfectMap f) : IsQuotientMap f :=
  hf.isClosedMap.isQuotientMap hf.toIsProperMap.continuous hf.surjective

/-- The composition of perfect maps is perfect. -/
lemma comp {f : X → Y} {g : Y → Z} (hg : IsPerfectMap g) (hf : IsPerfectMap f) :
    IsPerfectMap (g ∘ f) :=
  ⟨hg.toIsProperMap.comp hf.toIsProperMap, hg.surjective.comp hf.surjective⟩

end IsPerfectMap
