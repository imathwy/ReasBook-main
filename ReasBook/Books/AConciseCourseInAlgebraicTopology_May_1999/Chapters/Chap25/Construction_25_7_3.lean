import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_7_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_7_2

open CategoryTheory

universe u w

/-- The category of spectra, bundled as the full subcategory of `Prespectrum` cut out by
`Spectrum`. -/
abbrev Spectra :=
  ObjectProperty.FullSubcategory (Spectrum : ObjectProperty Prespectrum.{u, w})

/-- Construction 25.7.3: a morphism of spectra is a weak (stable) equivalence when it induces an
isomorphism on every integer-graded stable homotopy group. This is exactly the class inverted in
May's stable category. -/
def spectraStableEquivalences : MorphismProperty (Spectra.{u, w}) :=
  fun _ _ f ↦ Prespectrum.IsStableEquivalence f.hom

/-- Unfolding `spectraStableEquivalences` says that the induced map on `π_n` is an isomorphism
for every integer `n`. -/
theorem spectraStableEquivalences_iff
    {T U : Spectra.{u, w}} (f : T ⟶ U) :
    spectraStableEquivalences f ↔
      ∀ n : ℤ, IsIso (Prespectrum.stableHomotopyGroupMap f.hom n) :=
  Iff.rfl

/-- Construction 25.7.3: the stable category is the localization of spectra at the stable
equivalences. -/
abbrev StableCategory : Type (w + 1) :=
  (spectraStableEquivalences : MorphismProperty (Spectra.{u, w})).Localization

/-- The localization functor from spectra to the stable category. -/
abbrev spectraToStableCategory : Spectra.{u, w} ⥤ StableCategory :=
  spectraStableEquivalences.Q

/-- The localization functor inverts every stable equivalence of spectra. -/
theorem spectraToStableCategory_inverts_stableEquivalences :
    spectraStableEquivalences.IsInvertedBy spectraToStableCategory :=
  spectraStableEquivalences.Q_inverts

/- Construction 25.7.3 packages the stable category as the localization of the category `Spectra`
at the morphism property `spectraStableEquivalences`, together with the canonical localization
functor `spectraToStableCategory : Spectra ⥤ StableCategory`. -/
#check Spectra
#check spectraStableEquivalences
#check StableCategory
#check spectraToStableCategory
