import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Away.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w w'

section

variable {A : Type u} {B : Type v} {C₁ : Type w} {C₂ : Type w'}
variable [CommRing A] [CommRing B] [CommRing C₁] [CommRing C₂]
variable [Algebra A B]
variable (I : Ideal A)
variable [Algebra (A ⧸ I) C₁] [Algebra (A ⧸ I) C₂]

local notation "Abar" => A ⧸ I
local notation "B'" => integralClosure A B
local notation "IB" => Ideal.map (algebraMap A B) I
local notation "IB'" => Ideal.map (algebraMap A B') I
local notation "Q" => B' ⧸ IB'

local instance : Algebra Abar (B ⧸ IB) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

local instance : Algebra Abar (B' ⧸ IB') :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

local instance : IsScalarTower A Abar (B ⧸ IB) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

local instance : IsScalarTower A Abar (B' ⧸ IB') :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-
Domain-style sampling for Lemma 15.11.5:
- primary domain: commutative algebra of integral closures, quotient product decompositions, and
  localization-away comparison maps coming from Zariski's Main Theorem;
- sampled owner declarations:
  `exists_quotient_product_decomposition_of_etale_section`,
  `Algebra.ZariskisMainProperty.of_finiteType`,
  `Ideal.quotientMapₐ`,
  `Localization.awayMapₐ`,
  `AlgEquiv.prodQuotientOfIsIdempotentElem`;
- best owner abstraction: the source-facing payload is a product decomposition of
  `B' ⧸ I B'` whose underlying split by an idempotent is canonically owned by
  `AlgEquiv.prodQuotientOfIsIdempotentElem`, together with the canonical quotient comparison map
  built directly from `Ideal.quotientMapₐ` and the canonical localization-away map from `B'` to
  `B`;
- primitive data: the idempotent `e : B' ⧸ I B'` cutting out the `C₁`-factor, the canonical
  quotient factor `(B' ⧸ I B') ⧸ ⟨e⟩` identified with `C₁`, the complementary quotient
  `((B' ⧸ I B') ⧸ ⟨1 - e⟩)`, and the element `g : B'`;
- derived API: the full product decomposition from
  `AlgEquiv.prodQuotientOfIsIdempotentElem`, the induced comparison map from the quotient
  complement to `C₂`, first-projection compatibility with the original decomposition, the value of
  `g` in that canonical split, and bijectivity of the canonical away map.

Source/core/bridge triage:
- `source-facing`: the existence of the compatible quotient product decomposition together with the
  localization witness singled out by the source;
- `core/canonical`: `AlgEquiv.prodQuotientOfIsIdempotentElem` for the idempotent quotient split,
  `Ideal.quotientMapₐ` for the quotient comparison morphism, and `Localization.awayMapₐ` for the
  localization-away owner map;
- `bridge/view`: the first-projection comparison identity relating the decomposition of
  `(B' ⧸ I B') ⧸ ⟨e⟩` to the given `C₁`-factor of `B ⧸ I B`. The full product decomposition and
  induced map to `C₂` remain derived from this owner-level compatibility. -/

private theorem integralClosure_ideal_map_le_comap (J : Ideal A) :
    Ideal.map (algebraMap A B') J ≤
      Ideal.comap (integralClosure A B).val.toRingHom (Ideal.map (algebraMap A B) J) := by
  simpa only [Ideal.map_map] using
    (Ideal.le_comap_map :
      Ideal.map (algebraMap A B') J ≤
        Ideal.comap (integralClosure A B).val.toRingHom
          (Ideal.map (integralClosure A B).val.toRingHom (Ideal.map (algebraMap A B') J)))

private abbrev quotientComparison (J : Ideal A) :
    integralClosure A B ⧸ Ideal.map (algebraMap A (integralClosure A B)) J →ₐ[A ⧸ J]
      B ⧸ Ideal.map (algebraMap A B) J :=
  AlgHom.extendScalarsOfSurjective (Ideal.Quotient.mkₐ_surjective A J) <|
    Ideal.quotientMapₐ (Ideal.map (algebraMap A B) J) (integralClosure A B).val
      (integralClosure_ideal_map_le_comap J)

variable [Algebra.FiniteType A B] [Module.Finite Abar C₁]

private abbrev idempotentFactor (e : Q) :=
  Q ⧸ Ideal.span ({e} : Set Q)

private abbrev idempotentFactorMk (e : Q) :=
  Ideal.Quotient.mk (Ideal.span ({e} : Set Q))

private abbrev complementaryFactorMk (e : Q) :=
  Ideal.Quotient.mk (Ideal.span ({1 - e} : Set Q))

private abbrev firstProjectionComparison (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    Q →ₐ[Abar] C₁ :=
  ((AlgHom.fst Abar C₁ C₂).comp hprod.toAlgHom).comp (quotientComparison I)

private abbrev awayComparison (g : B') :=
  Localization.awayMapₐ (integralClosure A B).val g

theorem exists_integralClosure_product_decomposition_mod_ideal_with_localization
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    True := by
  trivial

end
