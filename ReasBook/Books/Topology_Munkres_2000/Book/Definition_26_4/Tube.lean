module

public import Mathlib.Data.Set.Prod
public import Mathlib.Topology.Defs.Basic

universe u v

public section

namespace Set

/-- A subset of `X × Y` is a tube about the slice through `x₀` if it is the
product of an open neighborhood of `x₀` with all of `Y`. -/
def IsTubeAbout {X : Type u} {Y : Type v} [TopologicalSpace X]
    (x₀ : X) (T : Set (X × Y)) : Prop :=
  ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ T = W ×ˢ (univ : Set Y)

/-- A set is a tube about the slice through `x₀` exactly when it is the product
of an open neighborhood of `x₀` with all of `Y`. -/
theorem isTubeAbout_iff {X : Type u} {Y : Type v} [TopologicalSpace X]
    {x₀ : X} {T : Set (X × Y)} :
    IsTubeAbout x₀ T ↔ ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ T = W ×ˢ (univ : Set Y) :=
  Iff.rfl

namespace IsTubeAbout

/-- The product of an open neighborhood of `x₀` with all of `Y` is a tube
about the slice through `x₀`. -/
theorem prod_univ {X : Type u} {Y : Type v} [TopologicalSpace X]
    {x₀ : X} {W : Set X} (hW_open : IsOpen W) (hx₀ : x₀ ∈ W) :
    IsTubeAbout x₀ (W ×ˢ (univ : Set Y)) :=
  ⟨W, hW_open, hx₀, rfl⟩

/-- A tube about the slice through `x₀` contains that slice. -/
theorem slice_subset {X : Type u} {Y : Type v}
    [TopologicalSpace X] {x₀ : X} {T : Set (X × Y)} (hT : IsTubeAbout x₀ T) :
    ({x₀} : Set X) ×ˢ (univ : Set Y) ⊆ T := by
  obtain ⟨W, _, hx₀, rfl⟩ := isTubeAbout_iff.mp hT
  exact prod_mono (singleton_subset_iff.mpr hx₀) (Subset.refl _)

end IsTubeAbout

end Set
