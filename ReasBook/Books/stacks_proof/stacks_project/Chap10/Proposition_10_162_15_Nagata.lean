import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Definition_10_162_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
- primary domain: commutative algebra of the source-facing Nagata and universally Japanese
  conditions on commutative rings;
- sampled owner declarations of the same kind in the chapter/project:
  `IsN1Ring`,
  `IsN2Ring`,
  `UniversallyJapaneseRing`,
  `NagataRing`.
- best owner abstraction:
  `NagataRing` and `UniversallyJapaneseRing` are the source-facing owners;
  the theorem below is therefore a `bridge/view` TFAE comparing the owner `NagataRing` with its
  finite-type stability clause and the canonical `UniversallyJapaneseRing ∧ IsNoetherianRing`
  description.
- primitive data vs. derived API:
  the public clauses of the proposition are the source-facing content;
  extracted consequences such as `NagataRing R → UniversallyJapaneseRing R` are derived owner API
  and should be named once here, then reused downstream instead of re-extracting `List.TFAE` data.

Source/core/bridge triage:
- `source-facing`: the `List.TFAE` proposition itself;
- `core/canonical`: the owner classes `NagataRing`, `UniversallyJapaneseRing`, `IsN2Ring`,
  and the canonical Noetherian owner `IsNoetherianRing`;
- `bridge/view`: the named bridge theorem and instance extracted from the TFAE below.
-/

-- Proof sketch: `(1) → (2)` is the finite-type stability of Nagata rings proved by reducing to
-- the one-generator case and then to the domain case. `(2) → (3)` follows by applying clause
-- `(2)` to the identity algebra `R` to get Noetherianity, and then to finite type domain
-- `R`-algebras to obtain the universally Japanese property. `(3) → (1)` combines the Noetherian
-- hypothesis with the universally Japanese condition applied to the quotient domains `R ⧸ p`.
/-- Proposition 10.162.15 (Nagata): for a commutative ring `R`, the following are equivalent:
`R` is a Nagata ring, every finite type `R`-algebra is a Nagata ring, and `R` is universally
Japanese and Noetherian. -/
@[stacks 0334]
theorem nagataRing_tfae_finiteType_algebra_nagata_universallyJapanese_noetherian :
    List.TFAE
      [ NagataRing R,
        ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S], NagataRing S,
        UniversallyJapaneseRing R ∧ IsNoetherianRing R ] := sorry

/-- The Nagata condition is equivalent to being universally Japanese and Noetherian. -/
theorem nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing :
    NagataRing R ↔ UniversallyJapaneseRing.{u, v} R ∧ IsNoetherianRing R := by
  have htfae :
      List.TFAE
        [ NagataRing R,
          ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S], NagataRing S,
          UniversallyJapaneseRing.{u, v} R ∧ IsNoetherianRing R ] :=
    nagataRing_tfae_finiteType_algebra_nagata_universallyJapanese_noetherian
  exact htfae.out 0 2

end

section

variable (R : Type u) [CommRing R] [NagataRing R]

/-- Every Nagata ring is universally Japanese. -/
instance nagataRing_toUniversallyJapaneseRing : UniversallyJapaneseRing.{u, v} R :=
  (nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing.1 inferInstance).1

end
