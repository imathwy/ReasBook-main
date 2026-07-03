import stacks_project.Chap15.Lemma_15_16_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain triage:
- primary domain: commutative algebra of quotient-flatness over quotient rings in the Artinian
  ideal lattice;
- sampled owner declarations of the same kind:
  `Ideal.IsFlatQuotient`,
  `Module.Flat`,
  `Ideal.IsFlatQuotient.inf`,
  `exists_minimal_of_wellFoundedLT`;
- best owner abstraction: the ideal-level predicate recording that `M / JM` is flat over `R / J`;
- primitive data: the ring `R`, the module `M`, and an ideal `J : Ideal R`;
- derived API: the canonical `sInf` least ideal and the source-facing existence corollary.

Layering:
- `source-facing`: the existence of a smallest ideal cutting out a flat quotient of `M`;
- `core/canonical`: `Ideal.IsFlatQuotient` with `Module.Flat` on the canonical quotient ring and
  quotient module, together with the lattice infimum `sInf`;
- `bridge/view`: the existence theorem derived from the canonical `sInf` leastness statement.
-/

variable [IsArtinianRing R]

-- Proof sketch: consider the set of ideals `J` such that `M / JM` is flat over `R ⧸ J`. By
-- Lemma `15.16.1`, this set is closed under finite intersections, and since `R` is Artinian every
-- nonempty collection of ideals has a minimal element. Taking the intersection of all such ideals
-- then gives the smallest one.
/-- The infimum of all flat-quotient ideals is itself the smallest flat-quotient ideal. -/
theorem isLeast_sInf_flat_quotient_ideal :
    IsLeast
      {J : Ideal R | J.IsFlatQuotient M}
      (sInf {J : Ideal R | J.IsFlatQuotient M}) := sorry

/-- Lemma 15.17.1: over an Artinian ring `R`, there exists a smallest ideal `I` such that
`M / IM` is flat over `R ⧸ I`. -/
theorem exists_isLeast_flat_quotient_ideal :
    ∃ I : Ideal R,
      IsLeast {J : Ideal R | J.IsFlatQuotient M} I :=
  ⟨_, isLeast_sInf_flat_quotient_ideal⟩

end
