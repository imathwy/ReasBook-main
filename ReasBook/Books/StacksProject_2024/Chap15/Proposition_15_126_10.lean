import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11
import StacksProject_2024.Chap10.Lemma_10_105_2
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/- Domain-style sampling:
- primary domain: local commutative algebra over Noetherian catenary normal local rings, with the
  normality and catenary hypotheses carried by the chapter ring-level owners;
- sampled owner declarations:
  `IsNormalRing`,
  `IsCatenaryRing`,
  `principalIdeal`,
  `Ideal.IsRadical`;
- best owner abstraction: the ambient ring hypotheses should be expressed through the existing
  chapter owners `IsNormalRing R` and `IsCatenaryRing R`, while principal quotients use the
  Chapter 15 owner `principalIdeal`;
- primitive data vs. derived API:
  primitive data is the radical ideal `J` together with `hJrad : J.IsRadical` and `hJne : J ≠ ⊥`;
  derived API is the existence of a nonzero element of `J` whose principal quotient is reduced.

Source/core/bridge triage:
- `source-facing`: the existence statement for a nonzero element of the given radical ideal;
- `core/canonical`: `IsNormalRing`, `IsCatenaryRing`, `Ideal.IsRadical`, and `principalIdeal`;
- `bridge/view`: none. The local redeclaration of `IsCatenaryRing` would be a duplicate owner and
  should be removed in favor of the chapter owner. -/

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsNormalRing R]
  [IsCatenaryRing R]

-- Proof sketch: imitate Lemma `15.126.5` using the catenary version of the perturbation argument.
-- Start with a nonzero element of the nonzero radical ideal `J`, use the stable perturbation
-- family from Lemma `15.126.9`, and bound the number of minimal primes of the perturbed principal
-- quotients via Lemma `15.126.8`. Choosing a perturbation with maximal number of minimal primes
-- forces every height-one valuation multiplicity to become `1`, which is equivalent to the
-- reducedness of the principal quotient.
/-- Proposition 15.126.10: if `J` is a nonzero radical ideal in a catenary Noetherian local normal
domain, then `J` contains a nonzero element whose principal quotient is reduced. -/
theorem exists_nonzero_mem_radicalIdeal_with_reduced_principal_quotient
    (J : Ideal R) (hJrad : J.IsRadical) (hJne : J ≠ ⊥) :
    ∃ f : R, f ≠ 0 ∧ f ∈ J ∧ IsReduced (R ⧸ principalIdeal f) := sorry

end
