import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Chap12.Corollary_12_12_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Representation

namespace Representation

/- Domain-style sampling for Theorem 19-19.1-1:
* primary domain: finite-group characters and realizability of finite-dimensional representations
  over smaller coefficient fields.
* inspected owner declarations in this domain:
  `IsRealizableOver`,
  `isRealizableOver_of_hasEnoughRootsOfUnity`,
  `exists_character_eq_of_isRealizableOver`,
  `groupFunctionPairingOverField_character_eq_finrank_intertwiningMap`.
* best owner abstractions:
  `IsRealizableOver K ρ` for the realizability clause, and
  `groupFunctionPairingOverField_character_eq_finrank_intertwiningMap` for the character-pairing
  clause.
* source/core/bridge triage:
  source-facing: LinearRepresentations_Serre_1977 applies these theorems to the Artin character;
  core/canonical: the Chapter `12` owners above;
  bridge/view: a chosen complex Artin realization `ArtinRep : FDRep ℂ G` would only be an
    auxiliary view used to specialize those owners.

Primitive data versus derived API:
in the minimal API closure of this file, the project does not yet provide a source-facing owner
for "LinearRepresentations_Serre_1977's Artin class function" itself. A theorem quantified over an arbitrary `ArtinRep :
FDRep ℂ G` therefore changes the source semantics: it no longer says anything specifically about
the Artin character. The faithful refinement is recall-only. The Chapter `12` owners are the real
mathematical statements, and the Artin application is obtained by specializing them to whichever
complex realization of the Artin character is available upstream. -/

/- Theorem 19-19.1-1, realizability clause: LinearRepresentations_Serre_1977's Artin character application is a direct
specialization of the Chapter `12` owner theorem saying that every finite-dimensional complex
representation of a finite group is realizable over any field with enough roots of unity. The
textbook equality of characters over `K` is the bridge companion
`exists_character_eq_of_isRealizableOver`, not a separate owner in this file. -/
recall isRealizableOver_of_hasEnoughRootsOfUnity

/- Theorem 19-19.1-1, pairing clause: the integrality of the Artin-character pairing is the
specialization to the chosen Artin realization of the canonical character-pairing owner theorem,
which identifies the normalized pairing with the natural-number-valued dimension of the
intertwining space. -/
recall groupFunctionPairingOverField_character_eq_finrank_intertwiningMap

end Representation
