import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Definition 3.1.6: for a cover `p : E → B`, the space `E` is the total space, `B` is the base
space, the set-theoretic fiber over `b` is `p ⁻¹' {b}`, and a set `V ⊆ B` is a fundamental
neighborhood of `b` when it is a path-connected evenly covered neighborhood for `p`. -/
def IsFundamentalNeighborhood (p : E → B) (b : B) (V : Set B) : Prop :=
  DiscreteTopology (p ⁻¹' {b}) ∧
    b ∈ V ∧ IsOpen V ∧ IsPathConnected V ∧ IsOpen (p ⁻¹' V) ∧
    ∃ H : p ⁻¹' V ≃ₜ V × (p ⁻¹' {b}), ∀ e, (H e).1.1 = p e

namespace IsFundamentalNeighborhood

variable {p : E → B} {b : B} {V : Set B}

/-- A fundamental neighborhood records the discrete topology on the fiber over the basepoint. -/
theorem discreteTopology_fiber (hV : IsFundamentalNeighborhood p b V) :
    DiscreteTopology (p ⁻¹' {b}) :=
  hV.1

/-- A fundamental neighborhood contains the chosen basepoint. -/
theorem mem (hV : IsFundamentalNeighborhood p b V) : b ∈ V :=
  hV.2.1

/-- A fundamental neighborhood is open. -/
theorem isOpen (hV : IsFundamentalNeighborhood p b V) : IsOpen V :=
  hV.2.2.1

/-- A fundamental neighborhood is path connected. -/
theorem isPathConnected (hV : IsFundamentalNeighborhood p b V) : IsPathConnected V :=
  hV.2.2.2.1

/-- The full preimage of a fundamental neighborhood is open. -/
theorem isOpen_preimage (hV : IsFundamentalNeighborhood p b V) : IsOpen (p ⁻¹' V) :=
  hV.2.2.2.2.1

/-- A fundamental neighborhood comes with a chosen trivializing homeomorphism over `V`. -/
theorem exists_preimageHomeomorph (hV : IsFundamentalNeighborhood p b V) :
    ∃ H : p ⁻¹' V ≃ₜ V × (p ⁻¹' {b}), ∀ e, (H e).1.1 = p e :=
  hV.2.2.2.2.2

/-- A fundamental neighborhood supplies the chosen witness for
`IsPathConnectedEvenlyCovered p b`. -/
theorem isPathConnectedEvenlyCovered (hV : IsFundamentalNeighborhood p b V) :
    IsPathConnectedEvenlyCovered p b := by
  rcases hV.exists_preimageHomeomorph with ⟨H, hH⟩
  exact
    ⟨hV.discreteTopology_fiber, V, hV.mem, hV.isOpen, hV.isPathConnected,
      hV.isOpen_preimage, H, hH⟩

/-- A fundamental neighborhood is, in particular, an evenly covered neighborhood with fiber
`p ⁻¹' {b}`. -/
theorem isEvenlyCovered (hV : IsFundamentalNeighborhood p b V) :
    IsEvenlyCovered p b (p ⁻¹' {b}) :=
  hV.isPathConnectedEvenlyCovered.isEvenlyCovered

/-- A point has a path-connected evenly covered neighborhood exactly when it admits some
fundamental neighborhood. -/
theorem exists_iff : IsPathConnectedEvenlyCovered p b ↔ ∃ V, IsFundamentalNeighborhood p b V := by
  constructor
  · rintro ⟨hdiscrete, V, hbV, hVOpen, hVPathConnected, hpVOpen, H, hH⟩
    exact ⟨V, hdiscrete, hbV, hVOpen, hVPathConnected, hpVOpen, H, hH⟩
  · rintro ⟨V, hV⟩
    exact hV.isPathConnectedEvenlyCovered

end IsFundamentalNeighborhood
