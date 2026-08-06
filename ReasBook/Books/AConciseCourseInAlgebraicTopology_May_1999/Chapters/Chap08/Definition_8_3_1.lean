import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_5_1

open CategoryTheory
open scoped unitInterval

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced only model-category cofibration APIs; the relevant
-- project owner for the textbook HEP notion is Chapter 6's topological `IsCofibration`, so this
-- file records its based analogue on `Under (⊤_ TopCat)`.

/-- Definition 8.3.1. A based map `i : A ⟶ X` is a based cofibration if every basepoint-preserving
homotopy on `A` whose time-`0` map is induced from a based map `X ⟶ Y` extends to a
basepoint-preserving homotopy on `X`. -/
def IsBasedCofibration {A X : BasedSpace} (i : A ⟶ X) : Prop :=
  ∀ ⦃Y : BasedSpace⦄ (f₀ : X ⟶ Y) (g : A ⟶ Y)
    (H : ((i ≫ f₀).right.hom) HRel[A] g.right.hom),
      ∃ G : X ⟶ Y,
        ∃ F : f₀.right.hom HRel[X] G.right.hom,
          ∀ z : I × A.right, F (z.1, i.right.hom z.2) = H z

/-- A based cofibration extends every basepoint-preserving homotopy on `A` that is compatible
with a chosen initial based map on `X`. -/
theorem IsBasedCofibration.exists_homotopy_extension {A X : BasedSpace} {i : A ⟶ X}
    (hi : IsBasedCofibration i) {Y : BasedSpace} (f₀ : X ⟶ Y) (g : A ⟶ Y)
    (H : ((i ≫ f₀).right.hom) HRel[A] g.right.hom) :
    ∃ G : X ⟶ Y,
      ∃ F : f₀.right.hom HRel[X] G.right.hom,
        ∀ z : I × A.right, F (z.1, i.right.hom z.2) = H z :=
  hi f₀ g H
