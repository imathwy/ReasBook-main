import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace Representation

section

variable {G : Type} [Group G] [Finite G]

/- Source/core/bridge triage:
* `source-facing`: the remark-level restatement that Brauer induction reduces characters to the
  span of degree-`1` subgroup characters, together with the standard consequence that the image of
  a degree-`1` character is cyclic.
* `core/canonical`: `IsMonomialCharacter`, `character_mem_monomialCharacterSpan`,
  `MonoidHom.finite_iff_finite_ker_range`, and mathlib's canonical cyclicity owner for finite
  subgroups of units in an integral domain.
* `bridge/view`: `degree_one_character_range_isCyclic`, which specializes that owner to the range
  of a degree-`1` complex character `χ : G →* ℂˣ`.

Sampled owner declarations in this domain:
* `Representation.IsMonomialCharacter`
* `Representation.character_mem_monomialCharacterSpan`
* `MonoidHom.finite_iff_finite_ker_range`
* `RingTheory.IntegralDomain.isCyclic_subgroup_units`

Primitive data versus derived API:
the source-facing content of this remark is already owned upstream by the chapter-level monomial
character declarations. The cyclic-image statement for a degree-`1` character is derived API: its
primitive data is only the homomorphism `χ`; finite image is derived canonically from the
homomorphism owner `MonoidHom.finite_iff_finite_ker_range`, and cyclicity is then supplied by the
existing finite-subgroup-of-`ℂˣ` owner, not by new local structure. -/

/- Remark 10-10.5-4: the chapter's source-facing reduction to degree-`1` characters is already
owned by `IsMonomialCharacter`, whose defining data is induction from a one-dimensional complex
representation of a subgroup. The further reduction to cyclic groups, and the application to
Artin `L`-functions mentioned by Serre, are expository consequences of this canonical owner rather
than new declaration-level mathematics in this file. -/
recall IsMonomialCharacter

/- The actual Brauer-induction reduction theorem used by the remark is the canonical chapter-level
statement that every character of `G` belongs to the monomial-character span. -/
recall character_mem_monomialCharacterSpan

/-- Remark 10-10.5-4: the image of a degree-`1` complex character of a finite group is cyclic. -/
theorem degree_one_character_range_isCyclic (χ : G →* ℂˣ) : IsCyclic χ.range := by
  haveI : Finite χ.range := ((MonoidHom.finite_iff_finite_ker_range χ).1 inferInstance).2
  infer_instance

end

/- In this cyclic form, Brauer's induction theorem gives the classical application to Artin
`L`-functions. -/

end Representation
