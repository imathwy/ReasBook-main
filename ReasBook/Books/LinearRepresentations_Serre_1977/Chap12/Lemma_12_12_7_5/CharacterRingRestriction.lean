import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_6_4

/-!
This file now reuses the canonical restriction API from
`LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_6_4`.

Route correction: `characterRingOverFieldRestrictionOfLe`, its notation `↾R[...]`, and the
evaluation lemma `characterRingOverFieldRestrictionOfLe_apply` are already owned there. Keeping a
second local copy here created duplicate declarations during single-file imports, so the
`Lemma_12_12_7_5` support layer now re-exports the canonical owner instead of redefining it.
-/
