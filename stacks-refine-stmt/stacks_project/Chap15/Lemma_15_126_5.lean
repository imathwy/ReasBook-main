import stacks_project.Chap10.Definition_10_37_11
import stacks_project.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsNormalRing R]

/-
Domain-style sampling:
- primary domain: two-dimensional local commutative algebra, with height-one prime ideals and
  principal quotients;
- sampled owner declarations:
  `IsNormalRing`,
  `principalIdeal`,
  `PrimeSpectrum R`,
  `IsReduced`,
  `Ideal.height`,
  `chinese_remainder_prod_eq_iInf`,
  `exists_power_sum_ne_zero`;
- best owner abstraction: the source-facing input is a finite distinct collection of height-one
  prime ideals, so the right owner surface here is a
  `Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 }` rather than an indexed family plus a
  separate injectivity witness;
  mathlib's `IsDedekindDomain.HeightOneSpectrum` is too specific for this normal local setting,
  while the quotient by the chosen element should use the chapter owner `principalIdeal` rather
  than restating `Ideal.span ({f} : Set R)`;
- primitive data vs. derived API:
  primitive data is the finite set `ps : Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 }`;
  derived API is the existence of a common nonzero element whose principal quotient is reduced.

Source/core/bridge triage:
- `source-facing`: the common-element existence statement for a finite family of pairwise distinct
  height-one primes;
- `core/canonical`: `IsNormalRing`, `principalIdeal`, `IsReduced`, and the height API on ideals;
- `bridge/view`: none beyond the canonical direct subtype
  `{ p : PrimeSpectrum R // p.asIdeal.height = 1 }`.
-/

-- Proof sketch: start with any nonzero element in the finite intersection of the given height-one
-- primes and apply the stable-perturbation lemma from the previous item to vary it by a deep
-- maximal-ideal element. Interpreting the resulting principal divisor through the discrete
-- valuation rings at the height-one primes, choose the perturbation so that the number of minimal
-- primes of the quotient is maximal; then all valuation multiplicities become `1`, which is
-- equivalent to the quotient by the principal ideal being reduced.
/-- Lemma 15.126.5: in a two-dimensional Noetherian local normal ring, any finite family of
pairwise distinct height-one prime ideals has a common nonzero element whose principal quotient is
reduced. -/
theorem exists_mem_heightOnePrimes_with_reduced_principal_quotient
    (hdim : ringKrullDim R = 2)
    (ps : Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    ∃ f : R, f ≠ 0 ∧ (∀ p ∈ ps, f ∈ p.1.asIdeal) ∧ IsReduced (R ⧸ principalIdeal f) := sorry

end
