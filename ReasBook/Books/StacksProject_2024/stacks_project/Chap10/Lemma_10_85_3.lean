import StacksProject_2024.Chap10.Lemma_10_85_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {P : Type v}
variable [CommRing R] [IsLocalRing R]
variable [AddCommGroup P] [Module R P] [Module.Projective R P]

/- Domain triage: this file lies in commutative algebra of projective modules over local rings
and free direct summands.
Sampled declarations in this domain:
* `Module.Projective.iff_split`
* `Module.Projective.of_split`
* `Complementeds (Submodule R P)`
* `Module.HasFiniteFreeComplementSummandProperty R P`
The numbered item is `source-facing`: it says a given element lies in a free direct summand.
The best downstream owner abstraction is `Module.HasFiniteFreeComplementSummandProperty R P` from
Lemma `10.85.2`.
Primitive data are only the ambient projective module `P`; the complemented free submodule
containing a chosen element is derived output. -/

-- Proof sketch: realize `P` as a direct summand of a free module using
-- `Module.Projective.iff_split`, choose a minimal finite support expression for `x` in a basis of
-- the ambient free module, project the supporting basis vectors to `P`, and use the local-ring
-- determinant argument from the textbook to show these projected vectors span a free complemented
-- submodule containing `x`.
/-- Lemma 10.85.3: if `P` is a projective module over a local ring `R`, then every element of `P`
is contained in a free direct summand of `P`. -/
theorem exists_free_directSummand_submodule_containing
    (x : P) :
    ∃ N : Complementeds (Submodule R P), x ∈ (N : Submodule R P) ∧
      Module.Free R (N : Submodule R P) := sorry

namespace Module

-- Proof sketch: given a decomposition `P = N ⊕ N'` with `N'` finite free, the summand `N` is
-- projective by `Module.Projective.of_split`; apply Lemma `10.85.3` to each `x : N`.
/-- Canonical owner-form companion to Lemma 10.85.3 for the chapter abstraction used in
Lemma `10.85.2`. -/
theorem hasFiniteFreeComplementSummandProperty_of_projective_of_isLocalRing :
    HasFiniteFreeComplementSummandProperty R P := sorry

end Module

end
