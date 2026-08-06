import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Lemma_6_1_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_4_1

open CategoryTheory CategoryTheory.Limits

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall: `lean_leansearch` surfaced only model-categorical cofibration results. The
-- verified local owners for this source statement are Chapter 6's topological `IsCofibration`,
-- Chapter 8's bridge `IsCofibration.isBasedCofibration`, and the pushout presentation
-- `homotopyCofiber f = pushout f (basedConeBaseInclusion X)` from Definition 8.4.1.

/-- Lemma 8.4.3. The inclusion `i : Y ⟶ C_f`, formalized as
`homotopyCofiberTargetInclusion f : Y ⟶ homotopyCofiber f`, has underlying unbased map a
cofibration. Equivalently, it is the left pushout map for the pushout presentation
`C_f = Y ∪_f CX`. -/
theorem homotopyCofiberTargetInclusion_isCofibration {X Y : BasedSpace} (f : X ⟶ Y) :
    IsCofibration (homotopyCofiberTargetInclusion f).right.hom := sorry

/-- The canonical target inclusion `Y ⟶ C_f` is also a based cofibration. -/
theorem homotopyCofiberTargetInclusion_isBasedCofibration {X Y : BasedSpace} (f : X ⟶ Y) :
    IsBasedCofibration (homotopyCofiberTargetInclusion f) :=
  IsCofibration.isBasedCofibration (homotopyCofiberTargetInclusion_isCofibration f)
