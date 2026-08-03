module

public import Topology_Munkres_2000.Book.Definition_15_1

public section

universe u v

open Set TopologicalSpace

/-- The open rectangles in the product of two topological spaces. -/
def openRectangles (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] : Set (Set (X × Y)) :=
  {s | ∃ U V, IsOpen U ∧ IsOpen V ∧ s = U ×ˢ V}

/-- Membership in `openRectangles X Y` is witnessed by two open factors. -/
@[simp] theorem mem_openRectangles {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (s : Set (X × Y)) :
    s ∈ openRectangles X Y ↔ ∃ U V, IsOpen U ∧ IsOpen V ∧ s = U ×ˢ V :=
  Iff.rfl

/-- Proposition 15.1: The open rectangles `U ×ˢ V`, with `U` open in `X` and
`V` open in `Y`, form a basis for the canonical product topology on `X × Y`.
Their intersections are computed componentwise. -/
theorem isTopologicalBasis_open_prod {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] :
    IsTopologicalBasis (openRectangles X Y) := by
  convert (isTopologicalBasis_opens : IsTopologicalBasis {U : Set X | IsOpen U}).prod
    (isTopologicalBasis_opens : IsTopologicalBasis {V : Set Y | IsOpen V}) using 1
  ext s
  simp only [mem_openRectangles, Set.mem_image2]
  constructor
  · rintro ⟨U, V, hU, hV, rfl⟩
    exact ⟨U, hU, V, hV, rfl⟩
  · rintro ⟨U, hU, V, hV, rfl⟩
    exact ⟨U, V, hU, hV, rfl⟩

#check Set.prod_inter_prod
