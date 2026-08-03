module

public import Mathlib.Topology.Connected.Clopen

public section

open Set

universe u

/-- The quasicomponent of `x`, consisting of the points in every clopen neighborhood of `x`. -/
def quasicomponent {X : Type u} [TopologicalSpace X] (x : X) : Set X :=
  ⋂ s : {s : Set X // IsClopen s ∧ x ∈ s}, (s : Set X)

/-- Membership in a quasicomponent means membership in every clopen neighborhood of its base
point. -/
theorem mem_quasicomponent_iff {X : Type u} [TopologicalSpace X] {x y : X} :
    y ∈ quasicomponent x ↔ ∀ U : Set X, IsClopen U → x ∈ U → y ∈ U := by
  -- Unpack the intersection indexed by all clopen neighborhoods of `x`.
  rw [quasicomponent]
  constructor
  · intro hy U hU hx
    exact Set.mem_iInter.mp hy ⟨U, hU, hx⟩
  · intro hy
    rw [Set.mem_iInter]
    intro U
    exact hy U U.property.1 U.property.2

/-- Two points are in the same quasicomponent exactly when no clopen set separates them. -/
theorem mem_quasicomponent_iff_no_clopen_separation {X : Type u} [TopologicalSpace X]
    {x y : X} :
    y ∈ quasicomponent x ↔ ¬ ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ y ∉ U := by
  -- Negating universal membership gives exactly a separating clopen neighborhood.
  rw [mem_quasicomponent_iff]
  constructor
  · intro hmem hsep
    obtain ⟨U, hU, hx, hy⟩ := hsep
    exact hy (hmem U hU hx)
  · intro hsep U hU hx
    by_contra hy
    exact hsep ⟨U, hU, hx, hy⟩

/-- Belonging to the quasicomponent of another point is a symmetric relation. -/
theorem mem_quasicomponent_comm {X : Type u} [TopologicalSpace X] {x y : X} :
    y ∈ quasicomponent x ↔ x ∈ quasicomponent y := by
  -- A clopen set separating the points in one direction has a clopen complement
  -- separating them in the other direction.
  rw [mem_quasicomponent_iff, mem_quasicomponent_iff]
  constructor
  · intro hxy U hU hy
    by_contra hx
    have hxCompl : x ∈ Uᶜ := hx
    have hyCompl : y ∈ Uᶜ := hxy Uᶜ hU.compl hxCompl
    exact hyCompl hy
  · intro hyx U hU hx
    by_contra hy
    have hyCompl : y ∈ Uᶜ := hy
    have hxCompl : x ∈ Uᶜ := hyx Uᶜ hU.compl hyCompl
    exact hxCompl hx
