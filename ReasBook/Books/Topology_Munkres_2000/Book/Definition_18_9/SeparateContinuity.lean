module

public import Mathlib.Topology.Continuous

public section

/-- A map on a product is separately continuous if each partial map is continuous. -/
structure SeparatelyContinuous {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (F : X × Y → Z) : Prop where
  /-- Every partial map varying the first coordinate is continuous. -/
  continuous_fst (y₀ : Y) : Continuous fun x ↦ F (x, y₀)
  /-- Every partial map varying the second coordinate is continuous. -/
  continuous_snd (x₀ : X) : Continuous fun y ↦ F (x₀, y)

/-- Separate continuity is equivalent to continuity of all partial maps. -/
theorem separatelyContinuous_iff {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {F : X × Y → Z} :
    SeparatelyContinuous F ↔
      (∀ y₀, Continuous fun x ↦ F (x, y₀)) ∧ ∀ x₀, Continuous fun y ↦ F (x₀, y) :=
  ⟨fun h ↦ ⟨h.continuous_fst, h.continuous_snd⟩, fun h ↦ ⟨h.1, h.2⟩⟩
