import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_3_4

open CategoryTheory

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced covering-space and model-category lifting APIs, but
-- the current project owners for this item are Chapter 7's `IsFibration` on unbased maps and
-- Chapter 8's `IsBasedFibration` on `Under (⊤_ TopCat)`, with well pointedness expressed by
-- `IsCofibration (basedSpaceBasepointInclusion A)`.

namespace IsBasedFibration

variable {E B : BasedSpace} {p : E ⟶ B}

/-- Lemma 8.5.2 (1). Every based fibration is an unbased fibration. -/
instance instIsFibration [hp : IsBasedFibration p] : IsFibration p.right.hom := sorry

end IsBasedFibration

namespace IsFibration

variable {E B : BasedSpace} {p : E ⟶ B}

/-- Lemma 8.5.2 (2). Conversely, if the underlying map `p.right.hom` is an unbased fibration,
then `p` satisfies the based covering homotopy property for every test space `A` whose basepoint
inclusion `basedSpaceBasepointInclusion A` is an unbased cofibration. -/
theorem exists_based_homotopyLift_of_wellPointed [hp : IsFibration p.right.hom] {A : BasedSpace}
    (hA : IsCofibration (basedSpaceBasepointInclusion A)) {f₀ f₁ : A ⟶ B}
    (H : f₀.right.hom HRel[A] f₁.right.hom) {g₀ : A ⟶ E}
    (hg₀ : g₀ ≫ p = f₀) :
    ∃ g₁ : A ⟶ E,
      ∃ G : g₀.right.hom HRel[A] g₁.right.hom,
        ContinuousMap.comp p.right.hom G.toContinuousMap = H.toContinuousMap := sorry

/-- If the test space `A` is well pointed, an unbased fibration `p.right.hom` admits the based
covering homotopy lift asserted in Lemma 8.5.2 (2). -/
theorem exists_based_homotopyLift [hp : IsFibration p.right.hom] {A : BasedSpace}
    [hA : WellPointedBasedSpace A] {f₀ f₁ : A ⟶ B}
    (H : f₀.right.hom HRel[A] f₁.right.hom) {g₀ : A ⟶ E}
    (hg₀ : g₀ ≫ p = f₀) :
    ∃ g₁ : A ⟶ E,
      ∃ G : g₀.right.hom HRel[A] g₁.right.hom,
        ContinuousMap.comp p.right.hom G.toContinuousMap = H.toContinuousMap :=
  exists_based_homotopyLift_of_wellPointed hA.isCofibration H hg₀

end IsFibration
