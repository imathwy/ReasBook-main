import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicTopology

/- Domain-style sampling for Lemma 14.23.4:
- primary domain: simplicial objects in an abelian category and the canonical comparison between
  their normalized Moore and alternating face map complexes;
- sampled same-kind declarations:
  `normalizedMooreComplex`,
  `alternatingFaceMapComplex`,
  `inclusionOfMooreComplexMap`,
  `inclusionOfMooreComplex`;
- best owner abstraction: the objectwise comparison morphism `inclusionOfMooreComplexMap`;
- primitive data: only the simplicial object `U`; the degreewise inclusions are derived from the
  normalized Moore subobjects and do not belong in a separate local wrapper;
- derived API: the natural transformation `inclusionOfMooreComplex`, together with the component
  formula `inclusionOfMooreComplexMap_f`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that the canonical inclusions `N(U)_n ⟶ U_n` assemble to
  a morphism of chain complexes;
- `core/canonical`: `inclusionOfMooreComplexMap`;
- `bridge/view`: the natural transformation `inclusionOfMooreComplex` whose component at `U` is
  that chain map.

This item carries no additional source-defined data beyond that canonical component, so the right
refinement is direct recall of the owner map. -/

/- Lemma 14.23.4: for a simplicial object `U` in an abelian category `A`, the canonical inclusions
`N(U)_n ⟶ U_n` assemble to the canonical morphism of chain complexes
`inclusionOfMooreComplexMap U : N(U) ⟶ s(U)`, where `N(U)` is the normalized
Moore complex and `s(U)` is the alternating face map complex. -/
recall inclusionOfMooreComplexMap
