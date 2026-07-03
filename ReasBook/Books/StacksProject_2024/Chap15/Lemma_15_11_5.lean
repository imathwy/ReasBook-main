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
  `Ideal.quotientMapₐ`,
  `AlgHom.prodMap`,
  `Localization.awayMapₐ`,
  `AlgEquiv.prodQuotientOfIsIdempotentElem`;
- best owner abstraction: the source-facing payload is a product decomposition of
  `B' ⧸ I B'` together with the factor-preserving comparison to the given product
  `B ⧸ I B ≃ C₁ × C₂`; canonically, the second factor is the quotient by `⟨1 - e⟩` cut out by an
  idempotent `e`, and the comparison map is the canonical quotient map from `Ideal.quotientMapₐ`;
- primitive data: the idempotent `e : B' ⧸ I B'`, the canonical product decomposition
  `B' ⧸ I B' ≃ C₁ × ((B' ⧸ I B') ⧸ ⟨1 - e⟩)`, the induced second-factor map to `C₂`, and the
  element `g : B'`;
- derived API: first-projection compatibility with the original decomposition, the value of `g`
  in the canonical split, and bijectivity of the canonical away map.

Source/core/bridge triage:
- `source-facing`: the existence of the compatible quotient product decomposition together with the
  localization witness singled out by the source;
- `core/canonical`: `AlgEquiv.prodQuotientOfIsIdempotentElem` for the idempotent quotient split,
  `Ideal.quotientMapₐ` for the quotient comparison morphism, `AlgHom.prodMap` for the
  factor-preserving map between the two product decompositions, and `Localization.awayMapₐ` for
  the localization-away owner map;
- `bridge/view`: the equality asserting that the quotient comparison map respects the two product
  decompositions. -/

private theorem integralClosure_ideal_map_le_comap (J : Ideal A) :
    Ideal.map (algebraMap A B') J ≤
      Ideal.comap (integralClosure A B).val.toRingHom (Ideal.map (algebraMap A B) J) := by
  simpa only [Ideal.map_map] using
    (Ideal.le_comap_map :
      Ideal.map (algebraMap A B') J ≤
        Ideal.comap (integralClosure A B).val.toRingHom
          (Ideal.map (integralClosure A B).val.toRingHom (Ideal.map (algebraMap A B') J)))

-- Proof sketch: apply Zariski's Main Theorem to the clopen subset of `Spec(B / I B)` cut out by
-- the factor `C₁`, then descend that clopen subset to `Spec(B' / I B')` for `B' = integralClosure
-- A B`. The resulting idempotent yields a canonical split of `B' / I B'`; keep the full product
-- decomposition and the induced comparison map to `C₂`, and choose `g ∈ B'` whose image has
-- coordinates `(1, 0)` so that the away map `B'[1/g] → B[1/g]` is bijective.
/- Lemma 15.11.5: let `B' = integralClosure A B`. If `A → B` is finite type, if
`B ⧸ I B ≃ C₁ × C₂`, and if `C₁` is finite over `A ⧸ I`, then there is a product decomposition
`B' ⧸ I B'` cut out by an idempotent `e`, together with a map from the complementary quotient
factor to `C₂` so that the canonical quotient map `B' ⧸ I B' → B ⧸ I B` preserves the two product
decompositions. The source-facing payload also includes an element `g ∈ B'` mapping to `(1, 0)`
in this split and making the away map `B'[1/g] → B[1/g]` bijective. -/
theorem exists_integralClosure_product_decomposition_mod_ideal_with_localization
    [Algebra.FiniteType A B] [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    ∃ (e : Q) (he : IsIdempotentElem e)
      (productDecomposition :
        Q ≃ₐ[Abar] (C₁ × (Q ⧸ Ideal.span ({1 - e} : Set Q))))
      (toSecondFactor : (Q ⧸ Ideal.span ({1 - e} : Set Q)) →ₐ[Abar] C₂) (g : B'),
        let quotientToB : Q →ₐ[Abar] (B ⧸ IB) :=
          AlgHom.extendScalarsOfSurjective (Ideal.Quotient.mkₐ_surjective A I) <|
            Ideal.quotientMapₐ (Ideal.map (algebraMap A B) I) (integralClosure A B).val
              (integralClosure_ideal_map_le_comap I)
        hprod.toAlgHom.comp quotientToB =
            (AlgHom.prodMap (AlgHom.id Abar C₁) toSecondFactor).comp
              productDecomposition.toAlgHom ∧
          productDecomposition (Ideal.Quotient.mk IB' g) = (1, 0) ∧
          Function.Bijective (Localization.awayMapₐ (integralClosure A B).val g) := by
  sorry

end
