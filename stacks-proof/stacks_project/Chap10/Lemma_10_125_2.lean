import Mathlib
import stacks_project.Chap10.Definition_10_125_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Domain-style sampling:
- primary domain: relative fiber dimension and quasi-finite polynomial presentations of
  localizations of finite-type algebras;
- sampled owner declarations:
  `relativeDimensionAt`,
  `fiberLocalRingAt`,
  `RingHom.QuasiFinite`,
  `Algebra.QuasiFiniteAt`;
- best owner abstraction: the local fiber-dimension owner `relativeDimensionAt`, together with the
  canonical morphism-level quasi-finite predicate on the witnessing polynomial map.

Source/core/bridge triage:
- `source-facing`: the existence of a localization `S_g` and a quasi-finite map
  `R[t₁, ..., tₙ] → S_g`;
- `core/canonical`: `relativeDimensionAt`, `fiberLocalRingAt`, and `RingHom.QuasiFinite`;
- `bridge/view`: passing from the fiber-local dimension statement to a polynomial presentation of
  a localization away from an element `g ∉ q`.

Primitive data are only the prime `q`, the integer `n`, and the relative-dimension equality. The
map `MvPolynomial (Fin n) R →ₐ[R] Localization.Away g` is the source-facing witness itself, while
its quasi-finiteness should be expressed by the canonical owner predicate on the morphism, not via
an explicit `toRingHom` projection in the public theorem surface.
-/

-- Proof sketch: let `p = q.asIdeal.under R` and identify the fiber through `q` with
-- `Spec ((q.asIdeal.under R).Fiber S)`. The hypothesis `relativeDimensionAt R S q = n` says that
-- this fiber has local dimension `n` at the corresponding point. Shrink to a basic open
-- neighbourhood of that fiber point of dimension `n`, apply the finite-type-over-a-field
-- Noether-normalization statement to the fiber ring to obtain `n` algebraically independent
-- coordinates, and then use openness of the quasi-finite locus to lift the resulting
-- quasi-finite-at-`q` polynomial presentation to a localization `S_g`.
/-- Lemma 10.125.2: let `R → S` be a finite type ring map, let `q : Spec(S)` be a prime, and
assume the relative dimension `dim_q(S/R)`, formalized as `relativeDimensionAt R S q`, is `n`.
Then there exists `g ∈ S` with `g ∉ q` such that `S_g`, formalized as `Localization.Away g`, is
quasi-finite over the polynomial algebra `R[t₁, …, tₙ]`, formalized as `MvPolynomial (Fin n) R`. -/
theorem exists_quasiFinite_polynomial_localizationAway_of_relativeDimensionAt_eq
    (n : ℕ) (q : PrimeSpectrum S) (hq : relativeDimensionAt R S q = (n : WithBot ℕ∞)) :
    ∃ g : S, g ∉ q.asIdeal ∧
      ∃ φ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g,
        φ.QuasiFinite := sorry

end
