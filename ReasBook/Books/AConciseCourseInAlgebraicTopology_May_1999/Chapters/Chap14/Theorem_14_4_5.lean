import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Definition_14_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Definition_14_4_4

open CategoryTheory
open CategoryTheory.ObjectProperty
open HomotopicalAlgebra

noncomputable section

-- Semantic recall via `lean_leansearch` did not surface a canonical library owner for this
-- determination theorem. This file therefore follows the local Chapter 19 dual precedent and
-- formalizes the source as injectivity of restriction along the inclusion of based CW complexes
-- into nondegenerately based spaces.

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "NBasedSpace" => nondegeneratelyBasedSpace

/-- Restrict a graded reduced homology functor on nondegenerately based spaces to based CW
complexes along the inclusion induced by `hCWtoN`. -/
abbrev restrictGradedHomologyToBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    (hCWtoN :
      IsBasedCWComplex ≤
        (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace))
    (E : ℤ → NBasedSpace ⥤ AddCommGrpCat) :
    ℤ → BasedCWComplex ⥤ AddCommGrpCat :=
  fun q ↦ ιOfLE hCWtoN ⋙ E q

namespace ReducedSuspensionCofiberSetup

/-- A bridge from the ambient reduced suspension/cofiber setup on nondegenerately based spaces to
chosen based-CW suspension/cofiber data along `hCWtoN`. This records that the based-CW
suspension and cofiber are the ones used to restrict `setup`, rather than arbitrary endofunctors
on `BasedCWComplex`. -/
structure RestrictsToBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    (setup : ReducedSuspensionCofiberSetup)
    (hCWtoN :
      IsBasedCWComplex ≤
        (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace))
    (basedCWSetup : BasedCWReducedSuspensionCofiberSetup) where
  /-- The based-CW suspension agrees with the ambient suspension after inclusion into
  nondegenerately based spaces. -/
  suspensionIso :
    basedCWSetup.suspension ⋙ ιOfLE hCWtoN ≅
      ιOfLE hCWtoN ⋙ setup.suspension
  /-- For each cofibration of based CW complexes, the chosen based-CW cofiber agrees with the
  ambient cofiber after inclusion into nondegenerately based spaces. -/
  cofiberIso {A X : BasedCWComplex} (i : A ⟶ X) :
    (ιOfLE hCWtoN).obj (basedCWSetup.cofiber.obj (Arrow.mk i)) ≅
      setup.cofiber.obj (Arrow.mk ((ιOfLE hCWtoN).map i))
  /-- The based-CW quotient map agrees with the ambient quotient map under the chosen cofiber
  comparison. -/
  cofiberMap_comm {A X : BasedCWComplex} (i : A ⟶ X) :
    CommSq
      ((ιOfLE hCWtoN).map (basedCWSetup.cofiberMap i))
      (setup.cofiberMap ((ιOfLE hCWtoN).map i))
      (cofiberIso i).hom
      (𝟙 _)

end ReducedSuspensionCofiberSetup

/-- Restrict a reduced homology theory on nondegenerately based spaces to a reduced homology
theory on based CW complexes, using based-CW suspension/cofiber data that is explicitly linked to
the ambient `setup` along `hCWtoN`. -/
theorem restrictReducedHomologyTheoryToBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    (setup : ReducedSuspensionCofiberSetup)
    (basedCWSetup : BasedCWReducedSuspensionCofiberSetup)
    (hCWtoN :
      IsBasedCWComplex ≤
        (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace))
    (hrestrictSetup :
      setup.RestrictsToBasedCWComplexes hCWtoN basedCWSetup)
    (E : ℤ → NBasedSpace ⥤ AddCommGrpCat)
    [ReducedHomologyTheory setup E] :
    ReducedHomologyTheoryOnBasedCWComplexes
      basedCWSetup.suspension basedCWSetup.cofiber basedCWSetup.cofiberMap
      (restrictGradedHomologyToBasedCWComplexes hCWtoN E) := by
  sorry

/-- Theorem 14.4.5: reduced homology theories on nondegenerately based spaces are determined by
their restrictions to based CW complexes. Concretely, once based CW complexes are viewed as
nondegenerately based spaces via `hCWtoN`, equality of the restricted graded functors forces
equality of the original graded reduced homology theories. -/
theorem reducedHomologyTheory_eq_of_restrictToBasedCWComplexes_eq
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (hCWtoN :
      IsBasedCWComplex ≤
        (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace))
    (E F : ℤ → NBasedSpace ⥤ AddCommGrpCat)
    [ReducedHomologyTheory setup E]
    [ReducedHomologyTheory setup F]
    (hrestrict :
      restrictGradedHomologyToBasedCWComplexes hCWtoN E =
        restrictGradedHomologyToBasedCWComplexes hCWtoN F) :
    E = F := sorry
