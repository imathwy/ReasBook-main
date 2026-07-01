import Mathlib
import stacks_project.Chap10.Definition_10_151_1
import stacks_project.Chap15.Definition_15_107_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

/-
Domain-style sampling for Lemma 15.108.2:
- primary domain: local commutative algebra at a prime, with localized maps and local étaleness;
- sampled owner declarations:
  `Algebra.UnramifiedAt`,
  `Algebra.unramifiedAt_iff_isUnramifiedAt`,
  `Localization.localRingHom`,
  `IsGeometricallyUnibranch`,
  `Algebra.Etale`;
- best owner abstraction: the source prime should be carried by `q : PrimeSpectrum B`, and the
  base prime is then canonically its contraction `q.asIdeal.under A`; keeping a separate
  parameter `p` together with `[q.asIdeal.LiesOver p]` is redundant public data.

Primitive data vs. derived API:
- primitive data: the prime `q`, geometric unibranchness of `Localization.AtPrime (q ∩ A)`, the
  source-facing unramified-at-prime hypothesis `Algebra.UnramifiedAt A B q`, and injectivity of
  the canonical localized map `A_(q ∩ A) → B_q`;
- derived API: an étale basic-open neighbourhood of `q`.

Source/core/bridge triage:
- `source-facing`: the existence of an étale basic-open neighbourhood of `q`;
- `core/canonical`: `Algebra.UnramifiedAt`, `Localization.localRingHom`, and
  `IsGeometricallyUnibranch`;
- `bridge/view`: the contraction `q.asIdeal.under A`, which replaces the redundant explicit
  parameter `p`.
-/
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A]

-- Proof sketch: use the local unramified hypothesis at `q` to shrink `B` to a standard étale
-- neighborhood of `q`, localize further to isolate the unique branch coming from the
-- geometrically unibranch local ring `A_p`, and then apply Lemma `15.108.1` to the kernel of the
-- resulting surjection to prove that the map is injective after shrinking. The localized target is
-- then étale over `A`.
/-- Lemma 15.108.2: if `q` lies over `p`, `A` is a domain, `A_p` is geometrically unibranch,
`A → B` is unramified at `q`, and the induced local map `A_p → B_q` is injective, then there
exists `g ∈ B \ q` such that `B_g` is étale over `A`. -/
theorem exists_etale_localizationAway_of_geometricallyUnibranch_of_unramifiedAtPrime_of_injective_localRingHom
    (q : PrimeSpectrum B)
    [IsGeometricallyUnibranch (Localization.AtPrime (q.asIdeal.under A))]
    (hunram : Algebra.UnramifiedAt A B q)
    (hinj : Function.Injective
      (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)) :
    ∃ g : B, g ∉ q.asIdeal ∧ Algebra.Etale A (Localization.Away g) := sorry

end
