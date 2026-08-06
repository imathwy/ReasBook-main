import Mathlib.Topology.Homeomorph.Lemmas
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Remark_9_6_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_2_5

universe u w

-- Semantic recall: `lean_leansearch` timed out for the spectrum query in this environment, so
-- this item follows the verified local Chapter 22 precedent: a Prop-valued class on the existing
-- `Prespectrum` owner, phrased in terms of the explicit adjoint structure maps.

/-- Definition 25.7.1: a spectrum is a prespectrum whose adjoint structure maps
`E n ⟶ Ω E (n + 1)` are homeomorphisms. -/
@[mk_iff spectrum_iff]
class Spectrum (E : Prespectrum.{u, w}) : Prop where
  /-- Each adjoint structure map `E n ⟶ Ω E (n + 1)` is a homeomorphism. -/
  isHomeomorph : ∀ n : ℕ, IsHomeomorph (adjointStructureMapContinuousMap E n)

/-- In a spectrum, each adjoint structure map is a homeomorphism. -/
instance isHomeomorph_adjointStructureMap
    (E : Prespectrum.{u, w}) [h : Spectrum E] (n : ℕ) :
    IsHomeomorph (adjointStructureMapContinuousMap E n) :=
  h.isHomeomorph n

/-- Every spectrum is an Omega-prespectrum. -/
instance omegaPrespectrum_of_spectrum
    (E : Prespectrum.{u, w}) [Spectrum E] :
    OmegaPrespectrum E where
  isWeakEquivalence n := by
    let h :
        IsHomeomorph (adjointStructureMapContinuousMap E n) :=
      (show Spectrum E from inferInstance).isHomeomorph n
    simpa using
      ContinuousMap.HomotopyEquiv.isWeakEquivalence
        ((h.homeomorph (adjointStructureMapContinuousMap E n)).toHomotopyEquiv)
