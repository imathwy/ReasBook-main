module

public import Topology_Munkres_2000.Book.Example_58_2.PlanarFigureEight

public section

noncomputable section

namespace DoublyPuncturedPlane

/-- The puncture `-1 / 2` in the left bounded component of the complement of the planar
theta carrier, chosen as part of the normalized model. -/
def leftPuncture : ℂ := -1 / 2

/-- The puncture `1 / 2` in the right bounded component of the complement of the planar
theta carrier, chosen as part of the normalized model. -/
def rightPuncture : ℂ := 1 / 2

end DoublyPuncturedPlane

/-- The normalized doubly punctured plane. -/
abbrev DoublyPuncturedPlane :=
  TwoPuncturePlane DoublyPuncturedPlane.leftPuncture DoublyPuncturedPlane.rightPuncture

namespace PlanarTheta

/-- The planar theta carrier `S¹ ∪ ({0} × Set.Icc (-1) 1)` in complex coordinates. -/
def carrier : Set ℂ :=
  {z | ‖z‖ = 1 ∨ (z.re = 0 ∧ z.im ∈ Set.Icc (-1 : ℝ) 1)}

/-- Membership in the planar theta carrier. -/
theorem mem_iff (z : ℂ) :
    z ∈ carrier ↔ ‖z‖ = 1 ∨ (z.re = 0 ∧ z.im ∈ Set.Icc (-1 : ℝ) 1) := Iff.rfl

/-- The planar theta carrier regarded as a subset of the normalized doubly punctured plane. -/
def inDoublyPuncturedPlane : Set DoublyPuncturedPlane :=
  {z | (z : ℂ) ∈ carrier}

/-- The point `1` as a basepoint of the planar theta space. -/
def basepoint : carrier :=
  ⟨1, Or.inl norm_one⟩

end PlanarTheta

/-- The planar theta space. -/
abbrev PlanarTheta := PlanarTheta.carrier
