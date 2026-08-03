module

public import Topology_Munkres_2000.Book.Definition_53_4.Torus

public section

noncomputable section

namespace FigureEight

/-- The union of the two coordinate circles in the torus, meeting at `(1, 1)`. -/
def carrier : Set Torus :=
  {z | z.2 = 1 ∨ z.1 = 1}

/-- A pair lies in the figure eight exactly when one coordinate is the circle basepoint. -/
theorem mem_iff (z : Torus) :
    z ∈ carrier ↔ z.2 = 1 ∨ z.1 = 1 := Iff.rfl

/-- The common point `(1, 1)` as the standard basepoint of the figure eight. -/
def basepoint : carrier :=
  ⟨(1, 1), Or.inl rfl⟩

end FigureEight

/-- The figure-eight subspace of the torus. -/
abbrev FigureEight := FigureEight.carrier
