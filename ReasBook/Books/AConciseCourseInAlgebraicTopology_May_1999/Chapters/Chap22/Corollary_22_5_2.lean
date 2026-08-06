import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Topology.Category.TopCat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Lemma_22_2_3

open CategoryTheory Opposite
open scoped HomotopyClasses

noncomputable section

universe u

-- Chapter 22 uses the canonical Chapter 7 owner `continuousMapHomotopyClasses` for `Ho[Z, Z']`.
-- This file supplies the companion quotient-category bridge needed for Corollary 22.5.2.

/-- Corollary 22.5.2. In the homotopy category of topological spaces, natural transformations
`[−, Z] ⟶ [−, Z′]` between the representable presheaves correspond to homotopy classes
`Ho[Z, Z′]`. -/
abbrev homotopyClassesNatTransEquiv (Z Z' : Type u) [TopologicalSpace Z] [TopologicalSpace Z'] :
    ((yoneda.obj (topCatHomotopyCategoryObj Z)) ⟶
      (yoneda.obj (topCatHomotopyCategoryObj Z'))) ≃
        Ho[Z, Z'] :=
  (yonedaEquiv :
    ((yoneda.obj (topCatHomotopyCategoryObj Z)) ⟶
      (yoneda.obj (topCatHomotopyCategoryObj Z'))) ≃
        (topCatHomotopyCategoryObj Z ⟶ topCatHomotopyCategoryObj Z')).trans
    (topCatHomotopyCategoryHomEquiv Z Z')

/-- `homotopyClassesNatTransEquiv` evaluates a natural transformation at the identity homotopy
class of `Z`. -/
theorem homotopyClassesNatTransEquiv_apply {Z Z' : Type u} [TopologicalSpace Z]
    [TopologicalSpace Z']
    (η : (yoneda.obj (topCatHomotopyCategoryObj Z)) ⟶
      (yoneda.obj (topCatHomotopyCategoryObj Z'))) :
    homotopyClassesNatTransEquiv Z Z' η =
      topCatHomotopyCategoryHomEquiv Z Z'
        (η.app (op (topCatHomotopyCategoryObj Z))
          (𝟙 (topCatHomotopyCategoryObj Z))) := by
  simpa [homotopyClassesNatTransEquiv] using
    congrArg (topCatHomotopyCategoryHomEquiv Z Z') (yonedaEquiv_apply η)
