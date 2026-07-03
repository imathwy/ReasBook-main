import Mathlib
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Quotient

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_10_1 (from Chap15) -/
universe u

section

variable (A : Type u) [CommRing A]
variable (I : Ideal A)

/- Domain-style sampling for Zariski pairs and Jacobson-radical containment:
- primary domain: commutative-ring ideals and the Jacobson radical;
- sampled declarations: `Ideal.jacobson`, `Ideal.le_jacobson`, `Ideal.jacobson_bot`,
  `Ring.jacobson`;
- best owner abstraction: the canonical ideal-level owner `Ideal.jacobson`, exposed on a ring by
  the shorter surface `Ring.jacobson A`.

Layer triage:
- `source-facing`: the textbook condition that the ideal `I` lies in the Jacobson radical of `A`;
- `core/canonical`: the ideal-level owner `Ideal.jacobson`;
- `bridge/view`: `Ideal.jacobson_bot`, which identifies `⊥.jacobson` with `Ring.jacobson A`.

Primitive data is only the ideal `I`. The containment proposition `I ≤ Ring.jacobson A` is the
whole source-facing notion, and consequences such as the special case `I = ⊥` are derived API via
`Ideal.le_jacobson`. Therefore this file should recall the canonical containment proposition
directly rather than introduce a parallel `ZariskiPair` wrapper.
-/

/- Definition 15.10.1: a Zariski pair `(A, I)` means exactly that `I` is contained in the
Jacobson radical of `A`, expressed canonically as `I ≤ Ring.jacobson A`. -/
#check (I ≤ Ring.jacobson A)

end

/-! ### Lemma_15_10_2 (from Chap15) -/
universe u

open IsLocalRing
open LocalizedModule (AtPrime mkLinearMap)

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: commutative-ring idempotents under quotient maps, controlled by the Jacobson
  radical and tested on maximal localizations;
- sampled owner declarations: `RingHom.idempotentMap`, `element_zero_localization_tfae`,
  `Localization.AtPrime.map_eq_maximalIdeal`, `Ring.jacobson_le_of_isMaximal`,
  `IsIdempotentElem.iff_eq_one_of_isUnit`;
- best owner abstraction: the induced map on the canonical idempotent subtype, with maximal
  localization and local-ring unit dichotomy supplying the proof core, and Chapter 10's
  local-to-global owner theorem closing the argument;
- primitive data: the ring homomorphism on elements and the Jacobson-radical containment `I ≤
  Ring.jacobson A`;
- derived API: injectivity of the quotient-induced idempotent map.

Layer triage:
- `source-facing`: injectivity for the quotient map `A → A ⧸ I`;
- `core/canonical`: maximal localization and local-ring Jacobson APIs;
- `bridge/view`: the owner-level map `RingHom.idempotentMap` on the idempotent subtype. -/

private theorem eq_zero_or_one_of_isIdempotentElem
    {R : Type*} [CommRing R] [IsLocalRing R] {x : R} (hx : IsIdempotentElem x) :
    x = 0 ∨ x = 1 := by
  rcases isUnit_or_isUnit_one_sub_self x with hx_unit | hx_unit
  · exact Or.inr <| (IsIdempotentElem.iff_eq_one_of_isUnit hx_unit).mp hx
  · exact Or.inl <| sub_eq_self.mp <|
      (IsIdempotentElem.iff_eq_one_of_isUnit hx_unit).mp hx.one_sub

private theorem eq_of_sub_mem_jacobson_of_isIdempotentElem
    {e₁ e₂ : A} (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (hd : e₁ - e₂ ∈ Ring.jacobson A) : e₁ = e₂ := by
  sorry

-- Proof sketch: if two idempotents of `A` have the same image in `A ⧸ I`, then their difference
-- lies in `I`, hence in the Jacobson radical by hypothesis. By Lemma
-- `10.23.1`, an idempotent is determined by the maximal ideals where it vanishes, so two
-- idempotents differing by a Jacobson-radical element must coincide.
/-- Lemma 15.10.2: if `(A, I)` is a Zariski pair, then the canonical map `A → A ⧸ I` induces an
injective map from idempotents of `A` to idempotents of `A ⧸ I`. -/
theorem quotientMk_injective_on_idempotents_of_le_jacobson (I : Ideal A)
    (hI : I ≤ Ring.jacobson A) :
    Function.Injective (Ideal.Quotient.mk I).idempotentMap := by
  intro e₁ e₂ h
  apply Subtype.ext
  apply eq_of_sub_mem_jacobson_of_isIdempotentElem e₁.2 e₂.2
  exact hI <| by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [map_sub] using sub_eq_zero.mpr (congrArg Subtype.val h)

end

/-! ### Lemma_15_10_3 (from Chap15) -/
universe u v

namespace Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A)
variable [Module.Flat A B] [Algebra.IsIntegral A B] [Algebra.FinitePresentation A B]

open LinearMap

local notation "IB" => I.map (algebraMap A B)

/- Domain-style sampling:
- primary domain: flat integral finitely presented algebras over a Jacobson pair, quotient algebra
  equivalences, and finite projective comparison modulo the Jacobson radical;
- sampled owner declarations of the same kind:
  `Algebra.finite_iff_isIntegral_and_finiteType`,
  `Module.FinitePresentation.iff_of_finite_finitePresentation`,
  `Module.Flat.projective_of_finitePresentation`,
  `bijective_of_bijective_mod_jacobson_of_finite_projective`,
  `LinearMap.quotientMapByIdeal`;
- best owner abstraction: the source-facing quotient hypothesis should live on the canonical owner
  `(A ⧸ I) ≃ₐ[A ⧸ I] (B ⧸ I B)`, while the module-theoretic core owner remains
  `Module.Projective`;
- primitive data: the flat integral finitely presented `A`-algebra `B`, the ideal `I`, and the
  quotient algebra equivalence modulo `I`;
- derived API: finiteness of `B` over `A`, finite presentation of `B` as an `A`-module,
  projectivity of `B`, and finally bijectivity of `algebraMap A B`; the raw quotient-map
  bijectivity is only an internal bridge extracted from the quotient algebra equivalence.

Layer classification:
- `source-facing`: the present Jacobson-pair lemma for algebras;
- `core/canonical`: `Module.Projective`;
- `bridge/view`: the quotient linear equivalence induced by `hquot`, together with the chapter
  comparison lemma `bijective_of_bijective_mod_jacobson_of_finite_projective`.
-/

-- Proof sketch: the quotient algebra equivalence identifies `B ⧸ I B` with `A ⧸ I`, so
-- `B ⧸ I B` is projective over `A ⧸ I`. Since `B` is integral and finitely presented over `A`, it
-- is finite over `A`, hence finitely presented as an `A`-module via the canonical finite/finitely
-- presented change-of-scalars bridge. Flatness then upgrades `B` to a projective `A`-module, and
-- Lemma `15.3.5` applies to the linear map underlying `A → B` after identifying its quotient
-- `LinearMap.quotientMapByIdeal` with the given quotient algebra equivalence.
/-- Lemma 15.10.3: for a Zariski pair `(A, I)`, a flat integral finitely presented
`A`-algebra `B` whose reduction modulo the extended ideal `I.map (algebraMap A B)` is identified
with `A ⧸ I` by an `(A ⧸ I)`-algebra equivalence already satisfies that the canonical map
`A → B` is bijective. -/
theorem bijective_algebraMap_of_zariskiPair_of_flat_integral_finitePresentation
    (hI : I ≤ Ring.jacobson A)
    (hquot : (A ⧸ I) ≃ₐ[A ⧸ I] (B ⧸ IB)) :
    Function.Bijective (algebraMap A B) := by
  sorry

end

end Algebra

/-! ### Lemma_15_10_4 (from Chap15) -/
open scoped Polynomial
open Polynomial

universe u v w w'

section

variable {A : Type u} {B : Type v} {B₁ : Type w} {B₂ : Type w'}
variable [CommRing A] [CommRing B] [CommRing B₁] [CommRing B₂]
variable [Algebra A B] [Module.Finite A B]
variable (I : Ideal A)
variable [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]

/- Domain-style sampling:
- primary domain: finite commutative `A`-algebras, quotient product decompositions over `A ⧸ I`,
  and polynomial relations detected modulo `I`;
- sampled owner declarations:
  `Algebra.exists_monic_polynomial_of_isIdempotentElem_mod_map`,
  `aeval`,
  `Ideal.Quotient.mk`;
- best owner abstraction: the source-facing polynomial witness should use the direct existential
  owner style already established by `Algebra.exists_monic_polynomial_of_isIdempotentElem_mod_map`,
  with `f.Monic`, `aeval b f = 0`, and the quotient polynomial identity as derived witness data;
- primitive data: the product decomposition of `B ⧸ I B`, the surjectivity of `A ⧸ I → B₁`, and
  the element `b` mapping to `(1, 0)`;
- derived API: the existence of a monic annihilating polynomial with the specified image in
  `(A ⧸ I)[X]`.

Source/core/bridge triage:
- `source-facing`: the theorem below, which produces the polynomial relation attached to the chosen
  component `(1, 0)`;
- `core/canonical`: the chapter owner theorem
  `Algebra.exists_monic_polynomial_of_isIdempotentElem_mod_map` for the idempotent-lifting
  polynomial witness;
- `bridge/view`: the product decomposition hypothesis, which identifies the image of `b` with the
  distinguished idempotent `(1, 0)` and upgrades the generic idempotent witness to the sharper
  factor `(X - 1) * X ^ d`.

The previous local class only repackaged this witness data for a single theorem, so the public
surface should expose the direct existential statement instead of a parallel wrapper owner.
-/

-- Proof sketch: use Lemma `15.9.10` to lift the idempotent `(1, 0)` after an étale base change,
-- split the base change of `b` into the two factors, kill the second factor by a monic polynomial
-- with coefficients in `I`, and then descend the resulting relation from the faithfully flat étale
-- cover back to `B`.
/-- Lemma 15.10.4: for a finite `A`-algebra `B` over a Zariski pair `(A, I)`, if `B ⧸ I B`
identifies with a product `B₁ × B₂` of `A ⧸ I`-algebras, the map `A ⧸ I → B₁` is surjective, and
`b : B` maps to `(1, 0)`, then `b` satisfies a monic polynomial whose reduction modulo `I` is of
the form `(X - 1) * X^d` with `d ≥ 1`. -/
theorem exists_monic_polynomial_of_product_decomposition_mod_ideal
    (hI : I ≤ Ring.jacobson A)
    (hprod : (B ⧸ Ideal.map (algebraMap A B) I) ≃ₐ[A ⧸ I] (B₁ × B₂))
    (hsurj : Function.Surjective (algebraMap (A ⧸ I) B₁))
    (b : B)
    (hb : hprod (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) b) = ((1 : B₁), (0 : B₂))) :
    ∃ d : ℕ, 0 < d ∧ ∃ f : A[X],
      f.Monic ∧
        aeval b f = 0 ∧
          f.map (Ideal.Quotient.mk I) = ((X - 1) * X ^ d : (A ⧸ I)[X]) := by
  sorry

end

/-! ### Lemma_15_10_5 (from Chap15) -/
universe u v

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: Jacobson rings, Jacobson-radical membership, and away-localization in
  commutative algebra;
- sampled owner declarations of the same kind:
  `Ring.jacobson`,
  `Definition_15_10_1`'s canonical Zariski-pair surface `I ≤ Ring.jacobson A`,
  `isJacobsonRing_localization`,
  `isJacobsonRing_of_isNoetherianRing_of_primeIdeal_isMaximal_or_infinite_primesOver`;
- best owner abstraction: an arbitrary away-localization target `S` with `[Algebra A S]` and
  `[IsLocalization.Away f S]`, of which `Localization.Away f` is the canonical model;
- primitive data: `f : A`, the Jacobson-radical membership `hf : f ∈ Ring.jacobson A`, and the
  ambient away-localization owner structure on `S`;
- derived API: the Zariski-pair formulation obtained from `I ≤ Ring.jacobson A` and `f ∈ I`; the
  concrete ring `Localization.Away f` is only a specialization of the owner-level statement.

Layer triage:
- `source-facing`: `isJacobsonRing_of_isLocalizationAway_of_mem_of_le_jacobson`;
- `core/canonical`: `isJacobsonRing_of_isLocalizationAway_of_mem_jacobson`, proved from the
  chapter Jacobson criterion
  `isJacobsonRing_of_isNoetherianRing_of_primeIdeal_isMaximal_or_infinite_primesOver` together
  with mathlib's away-localization infrastructure;
- `bridge/view`: the specialization `S = Localization.Away f`, supplied automatically by the
  canonical `IsLocalization.Away` instance.
-/

-- Proof sketch: apply the Noetherian Jacobson criterion to an arbitrary away-localization target
-- `S`. For a nonmaximal prime of `S`, contract to a prime of `A` and use `f ∈ Ring.jacobson A`
-- to show the corresponding quotient has dimension at least `1`; the local domain criterion from
-- Chapter 10 then gives infinitely many primes above it, so Lemma `10.61.4` makes `S` Jacobson.
variable [IsNoetherianRing A]

/-- Lemma 15.10.5 in canonical owner form: if `A` is Noetherian and `f ∈ Ring.jacobson A`, then
any away localization of `A` at `f` is a Jacobson ring. The textbook ring `Localization.Away f`
is the special case `S = Localization.Away f`. -/
theorem isJacobsonRing_of_isLocalizationAway_of_mem_jacobson
    {S : Type v} [CommRing S] [Algebra A S] (f : A) [IsLocalization.Away f S]
    (hf : f ∈ Ring.jacobson A) :
    IsJacobsonRing S := by
  sorry

/-- Lemma 15.10.5 in the textbook Zariski-pair form: if `(A, I)` is a Zariski pair with `A`
Noetherian and `f ∈ I`, then any away localization of `A` at `f` is a Jacobson ring. The
textbook ring `Localization.Away f` is the special case `S = Localization.Away f`. -/
theorem isJacobsonRing_of_isLocalizationAway_of_mem_of_le_jacobson
    {S : Type v} [CommRing S] [Algebra A S] (I : Ideal A) (hI : I ≤ Ring.jacobson A)
    (f : A) [IsLocalization.Away f S] (hf : f ∈ I) :
    IsJacobsonRing S :=
  isJacobsonRing_of_isLocalizationAway_of_mem_jacobson f (hI hf)

end
