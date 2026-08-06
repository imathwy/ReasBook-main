import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Definition_25_6_1

-- Semantic recall: `Definition_25_6_1` already exposes the canonical owner
-- `omegaPrespectrum_MO : OmegaPrespectrum (MO TO model)`. The source statement that each adjoint
-- structure map of `MO TO model` is a weak equivalence is therefore the inherited Chapter 22
-- `OmegaPrespectrum` surface, not a separate local theorem.

/- Construction 25.6.2. The associated spectrum `MO TO model` is already formalized as an
`OmegaPrespectrum` by `omegaPrespectrum_MO`; hence each adjoint structure map
`MO TO model n ⟶ Ω (MO TO model (n + 1))` is a weak equivalence by the generic Chapter 22
instance `isWeakEquivalence_adjointStructureMap`. This construction is therefore recorded as a
labeled recall of the canonical owner-level API rather than as a duplicate wrapper theorem. -/
#check omegaPrespectrum_MO
#check isWeakEquivalence_adjointStructureMap
