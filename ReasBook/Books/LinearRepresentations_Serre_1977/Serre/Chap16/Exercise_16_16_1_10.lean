import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 16-16.1-10: the large-field surjectivity statement for Serre's decomposition
homomorphism is the existing theorem `Representation.decompositionHom_surjective`.

Domain-style sampling for this item:
* primary domain: Serre's decomposition homomorphism on Grothendieck groups of finite-dimensional
  representations over a fraction field and its residue field.
* relevant owner declarations inspected in the same domain:
  `stableLatticeReduction_grothendieckClass_eq`,
  `decompositionHom`,
  `decompositionHom_finiteRepClass_eq`,
  `decompositionHom_surjective`.

Primitive data vs derived API:
* the owner data are already carried by `Representation.decompositionHom`;
* the large-field surjectivity assertion is already carried by the canonical theorem
  `Representation.decompositionHom_surjective`;
* this exercise adds no new source-facing object, only the proof-note observation that the
  surjectivity statement does not require any completeness hypothesis on the fraction field.

Source/core/bridge triage:
* source-facing: Exercise `16-16.1-10` is a proof note about the existing Chapter `16`
  surjectivity statement;
* core/canonical: the owner theorem is `Representation.decompositionHom_surjective`;
* bridge/view: there is no additional bridge construction here, so the refined surface should stay
  a direct recall of the canonical theorem rather than a duplicate wrapper. -/
recall Representation.decompositionHom_surjective
