import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain R] [Algebra.FiniteType R S]

/-
Source/core/bridge triage:
* primary domain: Noether normalization over a domain together with localization-away descent;
* sampled owner API:
  `exists_finite_inj_algHom_of_fg` from mathlib's Noether-normalization file,
  `exists_noether_normalization_polynomials_quotient_mvPolynomial` from Lemma `10.115.4`,
  `Localization.awayMapₐ` for the canonical localization-away algebra map,
  `Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ` for the localization-away owner
  interface used later in the chapter;
* source-facing: an intermediate `R`-algebra `S'` sitting between `R[y₁, …, y_d]` and `S`, with
  both structure maps injective, `S'` finite over the polynomial algebra, and `S'_f ≃ S_f` for
  some nonzero `f ∈ R`;
* core/canonical: injective `AlgHom`s, `AlgHom.Finite`, and the localization-away algebra
  `Localization.Away`;
* bridge/view: describing the polynomial algebra by a chosen family `y : Fin d → T` inside a
  subalgebra `T ⊆ S`, together with algebraic-independence or module-finiteness consequences.

Primitive data here are the intermediate algebra, the two injective maps, the finite polynomial
map, the nonzero localization element, and bijectivity of the canonical localized map. The earlier
subalgebra-and-generators presentation is derived API from this factorization and should not remain
the main public owner.
-/

/-- The image subalgebra of `S` cut out by a polynomial factorization, together with the finite
injective polynomial map and the away-localization comparison being an isomorphism-on-underlying
sets. -/
structure IsInjectivePolynomialFactorizationAway
    (d : ℕ) (S' : Subalgebra R S)
    (polynomialToIntermediate : MvPolynomial (Fin d) R →ₐ[R] S') (f : R) : Prop where
  polynomialToIntermediate_injective : Function.Injective polynomialToIntermediate
  polynomialToIntermediate_finite : AlgHom.Finite polynomialToIntermediate
  localizationElement_ne_zero : f ≠ 0
  awayMap_bijective :
    Function.Bijective (Localization.awayMapₐ S'.val (algebraMap R S' f))

-- Proof sketch: pass from the injective finite type `R`-algebra `S` to its generic fiber over the
-- fraction field of the domain `R`, apply the field case of Noether normalization there, and then
-- clear denominators to descend the normalization data back to a localization of `R`. This
-- produces an injective polynomial subalgebra, a finite intermediate algebra, and a nonzero
-- element `f ∈ R` away from which the canonical localized map from the intermediate algebra to `S`
-- is bijective.
/-- Lemma 10.115.7: let `R → S` be an injective finite type ring map with `R` a domain. Then
there exist an integer `d` and a factorization `R → R[y₁, …, y_d] → S' → S` by injective maps
such that `S'` is finite over `R[y₁, …, y_d]` and such that `S'_f ≃ S_f` for some nonzero
`f ∈ R`. -/
theorem exists_injective_polynomial_factorization_of_injective_finiteType
    (hinj : Function.Injective (algebraMap R S)) :
    ∃ (d : ℕ) (S' : Subalgebra R S)
      (polynomialToIntermediate : MvPolynomial (Fin d) R →ₐ[R] S') (f : R),
      IsInjectivePolynomialFactorizationAway d S' polynomialToIntermediate f := sorry

end
