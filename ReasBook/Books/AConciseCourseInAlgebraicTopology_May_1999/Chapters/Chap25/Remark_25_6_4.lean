import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_2_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_6_1

-- Semantic recall: Remark 25.6.4 points from the associated Thom spectrum `MO` to the Chapter 22
-- generalized homology and cohomology constructions. In the current repository those owners are
-- the explicit connective-prespectrum presentation-level homology API
-- `connectivePrespectrumReducedHomology`,
-- `connectivePrespectrumReducedHomologyTheoryOfPresentation`,
-- `connectivePrespectrumDefinesReducedHomologyTheory`, together with the Ω-prespectrum
-- cohomology owners `omegaPrespectrumReducedCohomology`,
-- `omegaPrespectrumReducedCohomologyAdditive`, and
-- `omegaPrespectrumRepresentsReducedCohomologyTheory` with its degreewise comparison
-- `omegaPrespectrumRepresentsReducedCohomologyTheory_comparison`. Since
-- Definition 25.6.1 already exposes the associated Thom spectrum `MO TO model`, and the same
-- file supplies the canonical instance
-- `omegaPrespectrum_MO : OmegaPrespectrum (MO TO model)`, this remark is best recorded as a
-- labeled recall block around the corresponding `MO`-specialized Chapter 22 surfaces rather than
-- as a new local wrapper declaration.

universe u

/- Remark 25.6.4. This item is interpretive rather than a new theorem: Definition 25.6.1 names
the associated Thom spectrum `MO`, and the same file provides the canonical Ω-prespectrum
instance `omegaPrespectrum_MO`. The reduced cohomology side attached to `MO` is therefore the
canonical Chapter 22 Ω-prespectrum represented-functor construction together with its additive
and bundled reduced-cohomology-theory packaging, while the generalized homology side is
expressed in the repository through the Chapter 22 connective-prespectrum presentation API,
together with the accompanying existence theorem for the resulting reduced homology theory.
Accordingly, this item is formalized as a labeled recall block around those existing
constructions after specializing them to the associated Thom spectrum `MO TO model`, rather than
as a duplicate wrapper theorem. -/
variable {TO : Prespectrum.{u, 0}} (model : OmegaSpectrumModel TO)
variable [HomotopicalAlgebra.CategoryWithCofibrations BasedSpace]
variable [HomotopicalAlgebra.CategoryWithCofibrations BasedCWComplex]
variable [HomotopicalAlgebra.CategoryWithWeakEquivalences BasedCWComplex]
variable (setup : BasedCWReducedSuspensionCofiberSetup)
variable (presentation : ConnectivePrespectrumReducedHomologyPresentation (MO TO model)) (q : ℤ)

#check MO
#check omegaPrespectrum_MO
#check connectivePrespectrumReducedHomology (MO TO model) presentation
#check connectivePrespectrumReducedHomologyTheoryOfPresentation setup (MO TO model) presentation
#check connectivePrespectrumDefinesReducedHomologyTheory (MO TO model)
#check omegaPrespectrumReducedCohomology (MO TO model) q
#check omegaPrespectrumReducedCohomologyAdditive (MO TO model)
#check omegaPrespectrumRepresentsReducedCohomologyTheory setup (MO TO model)
#check omegaPrespectrumRepresentsReducedCohomologyTheory_comparison setup (MO TO model) q
