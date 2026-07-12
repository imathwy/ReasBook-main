import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldRestriction

/-!
This file now reuses the canonical restriction API from
`Serre.Chap12.CharacterRingOverFieldRestriction`.

Route correction: `characterRingOverFieldRestrictionOfLe`, its notation `↾R[...]`, and the
evaluation lemma `characterRingOverFieldRestrictionOfLe_apply` are already owned there. Keeping a
second local copy here created duplicate declarations during single-file imports, so the
`Lemma_12_12_7_5` support layer re-exports the canonical owner instead of redefining it.

The restriction API was moved out of `Proposition_12_12_6_4` (which imports
`Theorem_12_12_6_2`) into the upstream file `CharacterRingOverFieldRestriction` to break the
import cycle that blocked `Theorem_12_12_6_2` from reusing the §12.7 cyclic-descent infrastructure.
-/
