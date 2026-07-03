import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_16_5_1 (from Chap16) -/
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

/-! ### Lemma_16_5_2 (from Chap16) -/
universe u v

namespace Algebra

section

variable {R : Type u} {B : Type v} {Λ : Type u}
variable [CommRing R] [CommRing B] [CommRing Λ]
variable [Algebra R B] [Algebra R Λ]

/- Domain-style sampling for smooth factorizations killing a finitely generated ideal:
* primary domain: commutative algebra of smooth `R`-algebras, square-zero ideals, and filtered
  colimits of smooth quotient algebras;
* sampled owner declarations:
  `Smooth R B`,
  `(algebraMap (R ⧸ I) _).IsFilteredColimitOfSmooth`,
  `exists_smooth_quotient_factorization_of_square_zero`,
  `exists_smooth_factorization_of_singularIdeal_map_eq_top`;
* best owner abstraction: this item is a source-facing bridge theorem, not a new packaged owner.
  Its canonical surface is the direct existence of a smooth factorization `B ─α→ B' ─β→ Λ`
  subject to the intrinsic ideal-theoretic conditions on `J`.

Source/core/bridge triage:
* `source-facing`: the factorization statement killing a finitely generated ideal `J ⊆ IB`;
* `core/canonical`: `Smooth`, `Ideal`, quotient algebras, and
  `RingHom.IsFilteredColimitOfSmooth`;
* `bridge/view`: the comparison maps `α` and `β` exhibiting the refined factorization.

Primitive input data are exactly `J`, the inclusion `J ≤ I.map (algebraMap R B)`, finite
generation of `J`, and the annihilation condition `J ≤ RingHom.ker φ`. The factorization
maps are derived output data, so a wrapper structure would only duplicate the owner declarations
already present upstream in Chapter 16.
-/

-- Proof sketch: argue by induction on the number of generators of `J`, reducing to the principal
-- case. For a generator `h = ∑ εᵢ bᵢ` with `εᵢ ∈ I`, apply the equational criterion of flatness to
-- the relation `∑ εᵢ φ(bᵢ) = 0` in the flat `R`-algebra `Λ`, build the auxiliary algebra
-- `C = B[x₁, …, xₘ]/(bᵢ - ∑ aᵢⱼ xⱼ)`, factor `C → Λ` through Lemma `16.5.1`, and then lift
-- `B → C → B' ⧸ J'` to `α : B → B'` by smoothness of `B` over `R`. The imposed relations and the
-- square-zero hypothesis `I² = 0` force `α` to kill `J`.
/-- Lemma 16.5.2: let `R → Λ` be a flat ring map, let `I ⊂ R` be a square-zero ideal, and assume
`Λ ⧸ IΛ` is a filtered colimit of smooth `(R ⧸ I)`-algebras. If `φ : B → Λ` is an `R`-algebra map
with `B` smooth over `R`, and if `J ⊆ IB` is a finitely generated ideal killed by `φ`, then `φ`
factors as `B ─α→ B' ─β→ Λ` with `B'` smooth over `R` and with `α` killing `J`. -/
theorem exists_smooth_factorization_killing_ideal_of_square_zero
    (I : Ideal R) [Module.Flat R Λ] [Smooth R B] (hSq : I ^ 2 = ⊥)
    (hcolim : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (φ : B →ₐ[R] Λ) (J : Ideal B)
    (hJ : J ≤ I.map (algebraMap R B)) (hJfg : J.FG)
    (hφJ : J ≤ RingHom.ker φ) :
    ∃ (B' : Type (max u v)) (_ : CommRing B') (_ : Algebra R B') (_ : Smooth R B')
      (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ),
      J ≤ RingHom.ker α ∧ β.comp α = φ := sorry

end

end Algebra

/-! ### Proposition_16_5_3 (from Chap16) -/
universe u

namespace Algebra

section

variable {R : Type u} {Λ : Type u}
variable [CommRing R] [CommRing Λ] [Algebra R Λ]
variable [Module.Flat R Λ]

/- Domain-style sampling for PT across nilpotent thickenings:
* primary domain: commutative algebra of filtered colimits of smooth algebras and nilpotent
  thickenings;
* sampled owner declarations:
  `RingHom.IsFilteredColimitOfSmooth`,
  `exists_smooth_quotient_factorization_of_square_zero`,
  `exists_smooth_factorization_killing_ideal_of_square_zero`,
  `Ideal.IsNilpotent`;
* best owner abstraction: `(algebraMap R Λ).IsFilteredColimitOfSmooth`;
* primitive data: the nilpotent ideal `I`, flatness of `R → Λ`, and the PT hypothesis on the
  quotient map;
* derived API: any chosen filtered diagram presenting PT and the square-zero induction step used
  in the proof.

Source/core/bridge triage:
* `source-facing`: the nilpotent-thickening lifting statement of Proposition `16.5.3`;
* `core/canonical`: `RingHom.IsFilteredColimitOfSmooth`;
* `bridge/view`: the square-zero factorization results from Lemmas `16.5.1` and `16.5.2`.

This item stays source-facing, but its public statement should be phrased directly in the canonical
owner `RingHom.IsFilteredColimitOfSmooth` rather than through any auxiliary presentation data.
-/

-- Proof sketch: choose `n` with `I ^ n = ⊥` and argue by induction on `n`, reducing to the
-- square-zero case. To apply the factorization criterion for filtered colimits of smooth
-- algebras, start from a finitely presented `R`-algebra mapping to `Λ`, use Lemma `16.5.1` to
-- write it as a quotient `B ⧸ J` of a smooth `R`-algebra with `J ⊆ IB` finitely generated, and
-- then apply Lemma `16.5.2` to kill `J` after passing to another smooth `R`-algebra. The map
-- from the finitely presented algebra then factors through a smooth `R`-algebra, which is the
-- desired factorization criterion.
/-- Proposition 16.5.3: let `R → Λ` be a flat ring map and `I ⊂ R` a nilpotent ideal. If
`Λ ⧸ IΛ` is a filtered colimit of smooth `(R ⧸ I)`-algebras, then `Λ` is a filtered colimit of
smooth `R`-algebras. -/
theorem isFilteredColimitOfSmooth_of_nilpotent_quotient
    (I : Ideal R) (hI : IsNilpotent I)
    (hquot : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth) :
    (algebraMap R Λ).IsFilteredColimitOfSmooth := sorry

end

end Algebra
