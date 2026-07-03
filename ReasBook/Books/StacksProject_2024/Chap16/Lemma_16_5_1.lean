import Mathlib
import StacksProject_2024.Chap10.Lemma_10_147_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Algebra

section

variable {R : Type u} {A : Type u} {Λ : Type u}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

/- Domain-style sampling for smooth quotient factorizations over a square-zero ideal:
* primary domain: commutative algebra of smooth `R`-algebras, quotient algebras, and finite
  presentation factorization through filtered colimits of smooth quotients;
* sampled owner declarations:
  `Smooth R B`,
  `RingHom.IsFilteredColimitOfSmooth`,
  `exists_smooth_factorization_of_singularIdeal_map_eq_top`,
  `exists_smooth_lift_of_quotient_smooth`;
* best owner abstraction: this item is not a new packaged object; its canonical public surface is
  the direct existence of a smooth `R`-algebra `B`, an ideal `J : Ideal B`, and the quotient
  factorization `A →ₐ[R] B ⧸ J →ₐ[R] Λ`.

Source/core/bridge triage:
* `source-facing`: the existence theorem below, matching Lemma `16.5.1`;
* `core/canonical`: `Smooth`, `Ideal`, quotient algebras `B ⧸ J`, and
  `RingHom.IsFilteredColimitOfSmooth`;
* `bridge/view`: the explicit quotient-stage factorization maps into and out of `B ⧸ J`.

Primitive output data are exactly `B`, `J`, the canonical owner hypotheses on `B` and `J`, and
the two algebra maps exhibiting the factorization. A separate wrapper structure would only
repackage those primitives without adding mathematical content, so the theorem exposes the direct
existential data instead.
-/

-- Proof sketch: factor the induced map `A ⧸ IA → Λ ⧸ IΛ` through a smooth `(R ⧸ I)`-algebra using
-- the filtered-colimit hypothesis and finite presentation. Lift that smooth quotient algebra to a
-- smooth `R`-algebra, then use formal smoothness across the square-zero extension `I² = 0` to map
-- the lift into a polynomial enlargement of `Λ`. Finally, rewrite the resulting surjection as a
-- quotient `B ⧸ J` with `J ⊆ IB` finitely generated via Nakayama and finite presentation.
/-- Lemma 16.5.1: if `I ⊂ R` is square-zero, if the quotient map
`R ⧸ I → Λ ⧸ IΛ` is a filtered colimit of smooth `(R ⧸ I)`-algebras, and if `φ : A → Λ` is an
`R`-algebra map with `A` of finite presentation over `R`, then `φ` factors as
`A → B ⧸ J → Λ` with `B` smooth over `R` and `J ⊆ IB` finitely generated. -/
theorem exists_smooth_quotient_factorization_of_square_zero
    (I : Ideal R) [FinitePresentation R A] (hSq : I ^ 2 = ⊥)
    (hcolim : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (φ : A →ₐ[R] Λ) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B) (_ : Smooth R B)
      (J : Ideal B) (_ : J ≤ I.map (algebraMap R B)) (_ : J.FG)
      (f : A →ₐ[R] B ⧸ J) (g : B ⧸ J →ₐ[R] Λ),
      g.comp f = φ := sorry

end

end Algebra
