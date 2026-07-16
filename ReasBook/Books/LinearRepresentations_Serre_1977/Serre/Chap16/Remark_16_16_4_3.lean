import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Proposition_16_16_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open Representation

/- Domain-style sampling for this item:
- primary domain: stable-lattice reduction and decomposition classes in modular representation
  theory for defect-zero irreducible representations;
- relevant owner declarations inspected before refining:
  `Representation.HasDefectZero`,
  `StableLattice.reductionRepresentation`,
  `StableLattice.reduction_irreducible_of_defect_zero`,
  `decompositionHom_finiteRepClass_eq`;
- best owner abstraction: the source-facing defect-zero owner
  `Representation.HasDefectZero`, together with the canonical reduction owner
  `StableLattice.reductionRepresentation`; this remark itself is purely derived theorem-level API.

Primitive data vs derived API:
- primitive data live upstream in `Representation.HasDefectZero`, `StableLattice`, and the
  canonical reduction construction `StableLattice.reductionRepresentation`;
- derived API here is only the theorem-level consequences already owned by the two recalled
  declarations, so this remark should stay recall-only.

Source/core/bridge triage:
- source-facing: Remark `16-16.4-3` is an explanatory block-theory remark saying that
  Proposition `16-16.4-1` sits in the defect-zero block-theoretic situation;
- core/canonical: the actual owners already present in the chapter/project API are
  `StableLattice.reduction_irreducible_of_defect_zero` and
  `decompositionHom_finiteRepClass_eq`;
- bridge/view: since this project does not formalize blocks as a separate owner here, the remark
  should remain a recall of those existing declarations rather than a new theorem phrased in
  unformalized block language or bundling stable-lattice data and decomposition equalities into a
  parallel wrapper. -/

/- Remark 16-16.4-3 rephrases Proposition `16-16.4-1` in defect-zero block-theoretic language.
Since blocks are not introduced as a separate owner in this chapter API, the relevant recalled
owner here is the irreducibility statement for the reduction of a stable lattice in a defect-zero
irreducible representation. -/
recall StableLattice.reduction_irreducible_of_defect_zero

/- Theorem `15-15.2-2` supplies the decomposition-homomorphism computation on the same reduced
stable lattice. Together with the previous recalled theorem, this is the project-level content of
the remark's defect-zero interpretation. -/
recall decompositionHom_finiteRepClass_eq
