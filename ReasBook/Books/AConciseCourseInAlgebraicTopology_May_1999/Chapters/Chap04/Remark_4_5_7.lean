import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Construction_4_5_5.ConeAdjunction

-- Semantic recall via `lean_leansearch`: the visible `homotopyCofiber` hits are for homological
-- complexes, so this item names the local topological cone-adjunction-space construction instead.

universe u

noncomputable section

section

variable {E : Type u} [TopologicalSpace E]
variable {B : Type u} [TopologicalSpace B]

/-- Remark 4.5.7. The space constructed from a map `p : E ⟶ B` in
Construction 4.5.5 is called the homotopy cofiber of `p`. -/
abbrev unbasedHomotopyCofiber (p : C(E, B)) : TopCat :=
  coneAdjunctionSpace p

/-- The homotopy cofiber of `p` is the cone adjunction space `B ∪ₚ CE`
introduced in Construction 4.5.5. -/
@[simp]
theorem unbasedHomotopyCofiber_def (p : C(E, B)) :
    unbasedHomotopyCofiber p = coneAdjunctionSpace p :=
  rfl

end
