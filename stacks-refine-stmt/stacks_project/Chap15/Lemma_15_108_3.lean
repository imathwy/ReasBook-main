import Mathlib
import stacks_project.Chap15.Definition_15_107_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

/-
Domain-style sampling:
- primary domain: local commutative algebra of geometrically unibranch local domains, essential
  finite type local maps, and étale localization criteria;
- sampled owner declarations of the same kind:
  `IsLocalization`,
  `Algebra.Etale`,
  `exists_etale_localizationAway_of_geometricallyUnibranch_of_unramifiedAtPrime_of_injective_localRingHom`,
  `ideal_comap_ne_bot_of_cases`;
- best owner abstraction: the source-facing conclusion is an intermediate étale `A`-algebra `C`
  together with a localization witness `IsLocalization M B`; collapsing this to
  `Algebra.Etale A B` is too strong here, because a local ring obtained by localizing an étale
  `A`-algebra need not itself be finite presented over `A`;
- primitive data: the local domain `A`, the local `A`-algebra `B`, the injective local map,
  the maximal-ideal equality, the separable residue-field extension, and the essential finite type
  hypothesis;
- derived API: an étale `A`-algebra whose localization is `B`.

Source/core/bridge triage:
- `source-facing`: the theorem below, expressing Stacks Lemma `15.108.3` as a localization
  existence result;
- `core/canonical`: the owner predicate `Algebra.Etale A C` on an intermediate algebra `C` and
  the localization owner `IsLocalization M B`;
- `bridge/view`: the essential finite type presentation of `B` and the étale-localization
  neighborhood produced by Lemma `15.108.2`.
-/
variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsLocalRing A] [IsGeometricallyUnibranch A]
variable [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [Algebra.EssFiniteType A B]

-- Proof sketch: write `B` as a localization of a finite type `A`-algebra `C` at a prime over the
-- maximal ideal of `A`. Lemma `10.151.7` gives that `A → C` is unramified at that prime from the
-- maximal-ideal and separable-residue-field hypotheses, and Lemma `15.108.2` then produces an
-- étale `A`-algebra after shrinking around that prime. The geometric-unibranch hypotheses and
-- Lemmas `15.107.7`, `15.107.8`, and `15.108.1` show that the resulting local map into `B` is
-- injective, yielding an intermediate étale `A`-algebra whose localization identifies with `B`.
/-- Lemma 15.108.3: if `(A, 𝔪)` is a geometrically unibranch local domain and `A → B` is an
injective local homomorphism of local rings that is essentially of finite type, such that
`𝔪 B = maximalIdeal B` and the induced residue-field extension is separable, then `B` is the
localization of an étale `A`-algebra. -/
theorem exists_etale_localization_of_isGeometricallyUnibranch_of_injective_localHom
    (hinj : Function.Injective (algebraMap A B))
    (hmax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (hsep : Algebra.IsSeparable (ResidueField A) (ResidueField B)) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (M : Submonoid C), Algebra.Etale A C ∧ IsLocalization M B := sorry

end
