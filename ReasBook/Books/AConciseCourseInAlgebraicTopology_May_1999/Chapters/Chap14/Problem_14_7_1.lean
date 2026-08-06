import Mathlib.Algebra.Homology.HomologySequenceLemmas

-- Declarations for this item will be appended below by the statement pipeline.

-- The source-facing Mayer-Vietoris exactness package for this chapter is the trio
-- `pairHomologyMayerVietorisExact₁/₂/₃`, proved elsewhere from the canonical Mathlib five-arrow
-- exactness owner `HomologicalComplex.HomologySequence.composableArrows₅_exact`. Local exactness
-- at a chosen consecutive pair is extracted by `CategoryTheory.ComposableArrows.Exact.exact'`.

/- Problem 14.7.1. The underlying canonical owner for Mayer-Vietoris exactness is the exact
five-arrow window in the long exact homology sequence attached to a short exact sequence of
homological complexes. This file records that core owner and the standard extractor for exactness
at any consecutive pair. -/
#check HomologicalComplex.HomologySequence.composableArrows₅_exact
#check CategoryTheory.ComposableArrows.Exact.exact'
