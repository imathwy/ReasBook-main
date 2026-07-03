import LinearRepresentations_Serre_1977.Chap08.Definition_8_8_4_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 8-8.4-2 (1): in canonical mathlib form, the existence of a Sylow `p`-subgroup is the
more general theorem `Sylow.nonempty`; the source finite-group/prime case is an immediate
specialization. -/
recall Sylow.nonempty

/- Theorem 8-8.4-2 (2): in canonical mathlib form, Sylow conjugacy is the pretransitivity of the
conjugation action of `G` on `Sylow p G`; the source finite-group case is an immediate
specialization, and `MulAction.exists_smul_eq G P Q` recovers the usual existential statement. -/
recall Sylow.isPretransitive_of_finite

/- Theorem 8-8.4-2 (3): in canonical mathlib form, every `p`-subgroup is contained in a Sylow
`p`-subgroup via `IsPGroup.exists_le_sylow`; the source finite-group/prime case is an immediate
specialization. -/
recall IsPGroup.exists_le_sylow
