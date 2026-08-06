import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_2_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_2_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_7_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Construction_25_7_3

/- Remark 25.7.4. This item is organizational rather than a new theorem: Definition 25.7.1
provides the stable-object owner `Spectrum`, Theorem 22.2.6 packages generalized cohomology
theories represented by Ω-prespectra, Definition 25.6.1 supplies the cobordism-side example
`MO`, and Construction 25.7.3 bundles the category of spectra `Spectra`, the stable category
`StableCategory`, and the localization functor
`spectraToStableCategory : Spectra ⥤ StableCategory`. On the Chapter 24 side,
Definition 24.2.5 already exposes the prespectrum-level owner `ComplexKTheoryPrespectrum`,
whose instances package the Ω-prespectrum and reduced-theory comparison data representing complex
`K`-theory. Accordingly, this source remark is formalized as a labeled recall block around those
existing Chapter 22/24/25 owners. -/
#check Spectrum
#check Spectra
#check StableCategory
#check spectraToStableCategory
#check omegaPrespectrumRepresentsReducedCohomologyTheory
#check MO
#check ComplexKTheoryPrespectrum
