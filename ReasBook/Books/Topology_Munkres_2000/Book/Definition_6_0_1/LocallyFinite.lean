module

public import Mathlib.Topology.LocallyFinite

public section

open Filter Set Topology

universe u

namespace Set

/-- A collection of subsets of a topological space is locally finite when its
inclusion family is locally finite. -/
abbrev LocallyFinite {X : Type u} [TopologicalSpace X] (𝒜 : Set (Set X)) : Prop :=
  _root_.LocallyFinite (Subtype.val : 𝒜 → Set X)

/-- A collection is locally finite exactly when every point has a neighborhood
meeting only finitely many members of the collection. -/
theorem locallyFinite_iff {X : Type u} [TopologicalSpace X] {𝒜 : Set (Set X)} :
    𝒜.LocallyFinite ↔
      ∀ x, ∃ U ∈ 𝓝 x, {A | A ∈ 𝒜 ∧ (A ∩ U).Nonempty}.Finite := by
  change _root_.LocallyFinite (Subtype.val : 𝒜 → Set X) ↔ _
  constructor <;> intro h x
  · rcases h x with ⟨U, hU, hfin⟩
    refine ⟨U, hU, ?_⟩
    exact (hfin.image Subtype.val).subset fun A hA ↦
      ⟨⟨A, hA.1⟩, hA.2, rfl⟩
  · rcases h x with ⟨U, hU, hfin⟩
    refine ⟨U, hU, ?_⟩
    have hpreimage := hfin.preimage
      (Subtype.val_injective : Function.Injective (Subtype.val : 𝒜 → Set X)).injOn
    exact hpreimage.subset fun i hi ↦ ⟨i.property, hi⟩

end Set
