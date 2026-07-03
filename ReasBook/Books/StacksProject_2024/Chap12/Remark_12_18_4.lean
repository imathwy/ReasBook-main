import Mathlib.Algebra.Homology.BifunctorAssociator
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open ComplexShape

/- Domain-style sampling for Remark 12.18.4:
- primary domain: associativity of totalization for triple cochain complexes;
- sampled core/canonical declarations:
  `ComplexShape.Associative`,
  `HomologicalComplex.mapBifunctorAssociator`,
  `GradedObject.mapBifunctorAssociator`;
- best owner abstraction: the pair consisting of the shape-level associativity datum
  `ComplexShape.Associative` and the induced homological-complex isomorphism
  `HomologicalComplex.mapBifunctorAssociator`;
- primitive data: three cochain-complex shapes, the two intermediate total-complex shapes, the
  final total shape, and the canonical associativity witness between the two ways of summing the
  three indices;
- derived API: the resulting canonical `≅` between the two iterated totalizations, obtained from
  the upstream bifunctor-associator construction rather than from any local wrapper;
- source/core/bridge triage:
  `source-facing`: the textbook remark that the two iterated totalizations of a triple cochain
    complex are canonically isomorphic;
  `core/canonical`: `ComplexShape.Associative` and
    `HomologicalComplex.mapBifunctorAssociator`;
  `bridge/view`: the graded precursor `GradedObject.mapBifunctorAssociator`.

This file should therefore stay at direct canonical recall/use, not introduce a parallel local
`IsIsomorphic` API around the upstream isomorphism. -/
recall ComplexShape.Associative

/- For cochain complexes, the needed associativity datum is the canonical `add_assoc`-based
instance already provided by mathlib. -/
#check (inferInstance : ComplexShape.Associative (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ) (up ℤ))

/- The owner `≅`-level construction for associativity of totalized homological-complex
constructions is `HomologicalComplex.mapBifunctorAssociator`; Remark 12.18.4 is the
triple-totalization specialization of this upstream API. -/
recall HomologicalComplex.mapBifunctorAssociator
