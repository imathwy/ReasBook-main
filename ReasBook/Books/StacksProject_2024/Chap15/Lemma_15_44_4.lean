import Mathlib
import StacksProject_2024.Chap10.Lemma_10_37_16
import StacksProject_2024.Chap10.Lemma_10_120_17
import StacksProject_2024.Chap15.Lemma_15_44_2
import StacksProject_2024.Chap15.Lemma_15_44_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling for Lemma 15.44.4:
- primary domain: étale commutative algebra over Dedekind domains, together with the canonical
  Dedekind-ring and localization owners for one-dimensional normal rings;
- sampled owner declarations of the same kind:
  `IsDedekindRing`,
  `IsDedekindDomain`,
  `normalRing_tfae_isIntegrallyClosed_isFiniteProductOfNormalDomains`,
  `isDedekindDomainByFactorization_iff_isDedekindDomainDvr`,
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`;
- owner abstraction: the canonical `IsDedekindRing` owner on `B`, the Dedekind-domain owner on
  each product factor, and the localization-at-a-prime owner for the DVR conclusion;
- primitive data: the rings `A`, `B`, the algebra `A → B`, and the étale structure;
- derived API: the finite-product decomposition, the `IsDedekindRing B` bridge, and the
  discrete-valuation-ring conclusion for a nonzero maximal localization.

Layer triage:
- `source-facing`: `exists_finite_product_dedekindDomain_of_etale`;
- `core/canonical`: `IsDedekindRing`, `IsDedekindDomain`, and
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`;
- `bridge/view`: the local discrete-valuation statement is a source-facing consequence for the
  canonical localization `Localization.AtPrime q.asIdeal`, rather than for an arbitrary chosen
  localization model.

Primitive-vs-derived refinement:
- a Dedekind-domain factor already carries its domain structure, so an extra public witness
  `∀ i, IsDomain (R i)` is redundant;
- the product decomposition is existential source content, so the theorem should keep only the
  Prop-level witness `Nonempty (B ≃+* Π i, R i)` rather than duplicating any extra wrapper API;
- `IsDedekindRing B` is the canonical owner-level conclusion for `B`, so it should be exposed
  directly instead of only through downstream consequences;
- the domain structure on a nonzero maximal localization of `B` is derived local data, so it
  should be internalized as an auxiliary instance rather than exposed in the public statement of
  the DVR theorem.
-/
section

variable {A : Type u} {B : Type v} [CommRing A] [IsDedekindDomain A]
variable [CommRing B] [Algebra A B] [Algebra.Etale A B]

-- Proof sketch: by Lemmas `15.44.2` and `15.44.3`, every localization `B_q` at a maximal ideal
-- has the same dimension and regularity as the corresponding localization of the Dedekind domain
-- `A`, hence is a discrete valuation ring via Algebra, Lemma `10.119.7`. Therefore `B` is a
-- Noetherian normal ring of dimension `1`, and Algebra, Lemmas `10.37.16` and `10.120.17` split
-- it as a finite product of Dedekind domains.
/-- Lemma 15.44.4: if `A → B` is an étale ring map and `A` is a Dedekind domain, then `B` is a
finite product of Dedekind domains. -/
theorem exists_finite_product_dedekindDomain_of_etale :
    ∃ (ι : Type (max u v)) (_ : Finite ι) (R : ι → Type (max u v))
      (_ : ∀ i, CommRing (R i)) (_ : ∀ i, IsDedekindDomain (R i)),
      Nonempty (B ≃+* Π i, R i) := sorry

-- Proof sketch: combine the local dimension comparison of Lemma `15.44.2` and the local
-- regularity equivalence of Lemma `15.44.3` to see that every nonzero maximal localization of `B`
-- is a discrete valuation ring. The canonical owner API then upgrades `B` to an
-- `IsDedekindRing`.
/-- An étale algebra over a Dedekind domain is a Dedekind ring. -/
theorem isDedekindRing_of_etale : IsDedekindRing B := by
  sorry

private instance localizationAtMaximal_isDomain_of_etale
    (q : MaximalSpectrum B) : IsDomain (Localization.AtPrime q.asIdeal) := by
  sorry

-- Proof sketch: combine the previous theorem with the fact that localizing a finite product at a
-- maximal ideal picks out one factor. That factor is a Dedekind domain, and the localization of a
-- Dedekind domain at a nonzero prime is a discrete valuation ring by the standard mathlib theorem
-- `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`.
/-- The localization of an étale algebra over a Dedekind domain at a nonzero maximal ideal is a
discrete valuation ring. -/
theorem localizationAtMaximal_isDiscreteValuationRing_of_etale
    (q : MaximalSpectrum B) (hq : q.asIdeal ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := by
  sorry

end
