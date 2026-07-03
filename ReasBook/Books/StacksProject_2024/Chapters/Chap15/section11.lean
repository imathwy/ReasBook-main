import Mathlib
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Colimit.Ring
import Mathlib.Data.List.TFAE
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_11_1 (from Chap15) -/
universe u

section

open scoped Polynomial

variable {A : Type u} [CommRing A]

namespace Ideal

/- Domain-style sampling for henselian pairs:
- primary domain: henselian pairs and Hensel lifting for ideals in commutative rings
- primitive owner object: `HenselianRing A I`
- primitive owner fields: `HenselianRing.jac`, `HenselianRing.is_henselian`
- same-domain declarations inspected: `HenselianRing`, `HenselianRing.jac`,
  `HenselianRing.is_henselian`, `RingPairCat.henselianPairProperty`

Layer triage:
- `source-facing`: the Jacobson-radical clause and the coprime-factorization lifting clause from
  the textbook definition of a henselian pair
- `core/canonical`: the mathlib owner `HenselianRing A I`
- `bridge/view`: the factorization-lifting theorem below, which is derived from the owner field
  `HenselianRing.is_henselian`, together with the Jacobson-radical bridge to the chapter surface
  `I ≤ Ring.jacobson A`

Primitive data is exactly the Jacobson-radical field and the simple-root lifting field of
`HenselianRing A I`. The coprime-factorization statement is derived API: mathlib records the
canonical owner in simple-root form, while this file keeps the textbook factorization clause as a
source-facing bridge theorem instead of introducing a second wrapper notion. Likewise, the
Jacobson clause is exposed below on the chapter-level surface `I ≤ Ring.jacobson A` rather than
the lower-level field type `I ≤ Ideal.jacobson ⊥`.
-/

/- Definition 15.11.1: the canonical mathlib notion of a henselian ideal `I` in a commutative
ring `A` is `HenselianRing A I`. The companion declarations below record the Jacobson-radical and
factorization-lifting consequences appearing in the textbook formulation. -/
recall HenselianRing

/- The Jacobson-radical clause of Definition 15.11.1, on the chapter surface
`I ≤ Ring.jacobson A`, is the owner field `HenselianRing.jac` transported along
`Ideal.jacobson_bot`. -/
theorem le_ring_jacobson_of_henselianRing (I : Ideal A) [HenselianRing A I] :
    I ≤ Ring.jacobson A := by
  simpa [Ideal.jacobson_bot] using
    (show I ≤ Ideal.jacobson (⊥ : Ideal A) from HenselianRing.jac)

/- The primitive lifting clause of Definition 15.11.1 is the owner field
`HenselianRing.is_henselian`. -/
recall HenselianRing.is_henselian (I : Ideal A) [HenselianRing A I]
    (f : A[X]) (hf : f.Monic) (a₀ : A)
    (ha₀ : f.eval a₀ ∈ I)
    (hderiv : IsUnit ((Ideal.Quotient.mk I) (f.derivative.eval a₀))) :
    ∃ a : A, f.IsRoot a ∧ a - a₀ ∈ I

-- Proof sketch: translate the coprime residue factorization into the simple-root formulation used
-- by `HenselianRing`, lift the corresponding simple root, and reconstruct the lifted monic factors
-- with the prescribed reductions from that lifted root.
/-- A henselian ideal lifts monic coprime factorizations modulo the ideal. -/
theorem exists_monic_coprime_factorization_lift (I : Ideal A) [HenselianRing A I]
    (f : A[X]) (hf : f.Monic) (g₀ h₀ : (A ⧸ I)[X]) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcoprime : IsCoprime g₀ h₀)
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    ∃ g h : A[X],
      g.Monic ∧ h.Monic ∧
        f = g * h ∧
          g.map (Ideal.Quotient.mk I) = g₀ ∧
            h.map (Ideal.Quotient.mk I) = h₀ := sorry

end Ideal

end

/-! ### Lemma_15_11_2 (from Chap15) -/
open CategoryTheory
open CommRingCat

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: étale `A`-algebras and reduction modulo an ideal;
- sampled owner declarations:
  `CommAlgCat`,
  `commAlgCatEquivUnder`,
  `CommRingCat.etale`,
  `ObjectProperty.lift`;
- best owner abstraction: the ambient category of `A`-algebras is canonically `CommAlgCat A`,
  equivalent to `Under (CommRingCat.of A)` via `commAlgCatEquivUnder`; the étale condition is
  therefore best expressed as an object property on `CommAlgCat A`, while the reduction functor is
  the base-change bridge to `CommAlgCat (A ⧸ I)`;
- primitive data: an object `B : CommAlgCat A`, equivalently an `A`-algebra with its structure
  morphism `A ⟶ B`;
- derived API: the étale object property on `CommAlgCat A`, the quotient/base-change functor
  `CommAlgCat A ⥤ CommAlgCat (A ⧸ I)`, its restriction to the étale full subcategory, its
  equivalence under a locally nilpotent ideal, and the induced henselian-ring instance.

Source/core/bridge triage:
- `source-facing`: reduction modulo `I` on the full subcategory of étale objects in
  `CommAlgCat A`;
- `core/canonical`: `CommAlgCat A`, `commAlgCatEquivUnder`, and `CommRingCat.etale`;
- `bridge/view`: the quotient/base-change functor on `CommAlgCat A`, obtained from the ordinary
  under-category base-change functor through `commAlgCatEquivUnder`.
-/

/-- The object property on `CommAlgCat A` selecting the étale `A`-algebras. -/
abbrev etaleAlgebraProperty (A : Type u) [CommRing A] : ObjectProperty (CommAlgCat A) :=
  fun B : CommAlgCat A ↦
    CommRingCat.etale (((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj B).hom)

variable (I : Ideal A)

/-- Base change along `A → A ⧸ I`, formalizing the functor `B ↦ B / IB` on `A`-algebras, viewed
in the canonical owner category `CommAlgCat`. -/
abbrev quotientCommAlgFunctor : CommAlgCat A ⥤ CommAlgCat (A ⧸ I) :=
  (commAlgCatEquivUnder (CommRingCat.of A)).functor ⋙
    (CommRingCat.of A).tensorProd (CommRingCat.of (A ⧸ I)) ⋙
      (commAlgCatEquivUnder (CommRingCat.of (A ⧸ I))).inverse

-- Proof sketch: an étale algebra stays étale after any base change, so applying the quotient
-- functor to an étale object of `CommAlgCat A` again lands in the étale full subcategory of
-- `CommAlgCat (A ⧸ I)`.
private theorem quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty :
    ∀ B : (etaleAlgebraProperty A).FullSubcategory,
      etaleAlgebraProperty (A ⧸ I) ((quotientCommAlgFunctor I).obj B.obj) := sorry

-- Proof sketch: essential surjectivity comes from lifting étale `A ⧸ I`-algebras across the
-- locally nilpotent quotient. Fullness comes from lifting morphisms by formal smoothness of étale
-- algebras. Faithfulness follows from the idempotent criterion for unramified morphisms together
-- with the fact that locally nilpotent ideals contain no nonzero idempotents.
/-- Lemma 15.11.2 (1): if `I` is locally nilpotent, then reduction modulo `I`, formalized by base
change along `A → A ⧸ I`, induces an equivalence between the full subcategories of étale objects
in `CommAlgCat A` and `CommAlgCat (A ⧸ I)`. -/
theorem quotientCommAlgFunctor_isEquivalence_on_etale_of_isLocallyNilpotent
    (hI : I.IsLocallyNilpotent) :
    Functor.IsEquivalence
      (ObjectProperty.lift
        (etaleAlgebraProperty (A ⧸ I))
        ((etaleAlgebraProperty A).ι ⋙ quotientCommAlgFunctor I)
        (quotientCommAlgFunctor_obj_mem_etaleAlgebraProperty I)) := sorry

-- Proof sketch: locally nilpotent ideals lie in the Jacobson radical, giving the Jacobson part of
-- henselianity. The factorization-lifting criterion is obtained by applying the étale
-- factorization lift of Lemma `15.9.5` and then using the equivalence from part `(1)` to descend
-- the resulting étale extension back to `A`.
/-- Lemma 15.11.2 (2): if `I` is locally nilpotent, then the pair `(A, I)` is henselian, i.e.
`A` is henselian at the ideal `I`. -/
instance henselianRing_of_isLocallyNilpotent
    (hI : I.IsLocallyNilpotent) : HenselianRing A I := sorry

end

/-! ### Lemma_15_11_3 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open CommRingCat

universe u

section

variable (F : SequentialInverseSystem CommRingCat.{u})

/- Domain-style sampling:
- primary domain: henselian pairs on inverse limits of commutative rings;
- sampled owner declarations of the same kind:
  `SequentialInverseSystem.stepMap`,
  `HenselianRing`,
  `henselianRing_of_isLocallyNilpotent`,
  `inverseSystem_limit_henselianRing`,
  `IsAdicComplete.henselianRing`;
- best owner abstraction: the sequential source-facing owner is `SequentialInverseSystem`, with
  `SequentialInverseSystem.stepMap` as the canonical stage-to-stage transition API; the core owner
  for the conclusion is `HenselianRing`, while the chapter-level inverse-limit owner is
  `inverseSystem_limit_henselianRing`; the locally nilpotent-kernel criterion from
  `henselianRing_of_isLocallyNilpotent` supplies the stagewise henselian ideals used in that
  inverse-limit owner;
- primitive data: the inverse system `F`, a stage `n`, and the stepwise transition hypotheses on
  `F.stepMap r`;
- derived API: henselianity of the kernel ideal of the projection `limit F → F.obj (op n)`.

Source/core/bridge triage:
- `source-facing`: the specialization to the projection-kernel ideal at a fixed stage `n`;
- `core/canonical`: `HenselianRing`;
- `bridge/view`: the sequential transition API `SequentialInverseSystem.stepMap` and the chapter
  owner `inverseSystem_limit_henselianRing`, fed by the stagewise locally nilpotent-kernel
  instances from `henselianRing_of_isLocallyNilpotent`.
-/

-- Proof sketch: fix `n`. Starting from the stepwise hypotheses on `A_{r + 1} → A_r`, derive the
-- corresponding surjectivity and locally nilpotent-kernel facts for the longer transition maps
-- `A_m → A_n` with `n ≤ m`. Repeated applications of `henselianRing_of_isLocallyNilpotent` then
-- make the stagewise kernel ideals henselian. Apply the inverse-limit owner
-- `inverseSystem_limit_henselianRing` to that compatible inverse system of ideals to obtain
-- henselianity of the limit ideal, which is the kernel of the projection `limit F → A_n`.
/-- Lemma 15.11.3: if `F : SequentialInverseSystem CommRingCat` is an inverse system of rings
whose stepwise transition maps `A_{r + 1} → A_r` are surjective and have locally nilpotent
kernels, then for each `n` the pair consisting of the inverse limit `limit F` and the kernel of
the projection `limit F → F.obj (op n)` is henselian. -/
instance henselianRing_limitProjection_ker_of_surjective_of_isLocallyNilpotent
    (n : ℕ)
    (h_surj : ∀ r : ℕ, Function.Surjective (F.stepMap r).hom)
    (h_locnil : ∀ r : ℕ, RingHom.ker (F.stepMap r).hom ≤ nilradical _) :
    HenselianRing ((limit F : CommRingCat.{u}) : Type u)
      (RingHom.ker (limit.π F (Opposite.op n)).hom) :=
    sorry

end

/-! ### Lemma_15_11_4 (from Chap15) -/
universe u

section

variable (A : Type u) [CommRing A] (I : Ideal A) [IsAdicComplete I A]

/- Domain-style sampling for adically complete henselian pairs:
- primary domain: commutative algebra of adic completeness and henselian ideals
- sampled same-domain owner declarations:
  `HenselianRing`,
  `HenselianRing.is_henselian`,
  `IsAdicComplete.henselianRing`,
  `localRing_henselian_of_isCompleteLocalRing`
- best owner abstraction: the canonical owner for the target conclusion is `HenselianRing A I`,
  and the canonical bridge from the source hypothesis is the mathlib instance
  `IsAdicComplete.henselianRing`
- primitive data: a commutative ring `A`, an ideal `I`, and the owner hypothesis
  `[IsAdicComplete I A]`
- derived API: the induced henselian structure on `(A, I)`

Layer triage:
- `source-facing`: the Stacks statement that an `I`-adically complete pair `(A, I)` is henselian
- `core/canonical`: the owner `HenselianRing A I`
- `bridge/view`: the instance `IsAdicComplete.henselianRing`

This item adds no new mathematical content beyond that canonical bridge, so the correct refined
surface is a direct `recall` of the owner-level instance rather than a local wrapper theorem or
alias.
-/
/- Lemma 15.11.4: if `A` is `I`-adically complete, then the pair `(A, I)` is henselian. This is
exactly the canonical mathlib instance `IsAdicComplete.henselianRing`. -/
recall IsAdicComplete.henselianRing

end

/-! ### Lemma_15_11_5 (from Chap15) -/
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

/-! ### Lemma_15_11_6 (from Chap15) -/
open scoped Polynomial
open Polynomial

universe u

section

variable {A : Type u} [CommRing A]

namespace Ideal

/-
Domain-style sampling:
- primary domain: henselian pairs in commutative algebra, expressed through the canonical owner
  `HenselianRing A I`, étale quotient sections, and quotient-induced maps on idempotents;
- sampled owner declarations:
  `HenselianRing`,
  `Ideal.HasFiniteAlgebraIdempotentLifting`,
  `Ideal.HasIntegralAlgebraIdempotentLifting`,
  `RingHom.idempotentMap`,
  `Algebra.FormallyEtale.iff_comp_bijective`;
- best owner abstraction: the main owner remains `HenselianRing A I`; among the auxiliary clauses,
  the idempotent conditions are already canonically owned upstream in Chapter 15, while the
  étale-section and Gabber polynomial conditions are genuinely source-facing here and should be
  phrased through canonical comparison maps rather than parallel wrapper data;
- primitive data: the ideal `I`, the owner predicate `HenselianRing A I`, the canonical quotient
  composition map `τ ↦ (Ideal.Quotient.mkₐ A I).comp τ`, and the quotient polynomial identity
  defining Gabber's test polynomials;
- derived API: the TFAE packaging and the uniqueness of a root in `1 + I`.

Source/core/bridge triage:
- `source-facing`: `HasEtaleLiftProperty`, `IsGabberHenselPolynomial`,
  `SatisfiesGabberRootCriterion`, and the chapter TFAE theorem;
- `core/canonical`: `HenselianRing A I`, the Chapter 15 idempotent-lifting owners, and the
  canonical map `RingHom.idempotentMap`;
- `bridge/view`: the unique-root consequence extracted from Gabber's criterion.
-/

/-- The étale lifting formulation of the henselian pair condition modulo `I`. -/
def HasEtaleLiftProperty (I : Ideal A) : Prop :=
  ∀ ⦃A' : Type u⦄ [CommRing A'] [Algebra A A'] [Algebra.Etale A A'],
    Function.Surjective fun τ : A' →ₐ[A] A ↦ (Ideal.Quotient.mkₐ A I).comp τ

/-- A Gabber test polynomial for the henselian criterion modulo `I`. -/
def IsGabberHenselPolynomial (I : Ideal A) (f : A[X]) : Prop :=
  ∃ n : ℕ, 0 < n ∧ f.Monic ∧
    f.map (Ideal.Quotient.mk I) = X ^ n * (X - 1)

/-- Gabber's Jacobson-plus-root criterion for the pair `(A, I)`. -/
def SatisfiesGabberRootCriterion (I : Ideal A) : Prop :=
  I ≤ Ring.jacobson A ∧
    ∀ ⦃f : A[X]⦄, I.IsGabberHenselPolynomial f → ∃ i : I, f.IsRoot (1 + ↑i)

end Ideal

-- Proof sketch: use the Stacks chain of implications `(2) → (4) → (3) → (1) → (5) → (2)`.
-- The Jacobson-radical condition enters via the henselian definition and the idempotent
-- injectivity lemma, finite and integral cases are related by integrality of finite algebras, and
-- Gabber's polynomial criterion supplies the final lifting step for étale sections.
/-- Lemma 15.11.6: for a commutative ring `A` and an ideal `I`, the following are equivalent: the
pair `(A, I)` is henselian; every section modulo `I` of an étale `A`-algebra lifts to `A`; for
all finite `A`-algebras the reduction map induces a bijection on idempotents; for all integral
`A`-algebras the reduction map induces a bijection on idempotents; and Gabber's Jacobson-plus-root
criterion holds for `I`. -/
theorem henselianRing_tfae_etaleLift_idempotents_gabberCriterion (I : Ideal A) :
    List.TFAE
      [ HenselianRing A I
      , I.HasEtaleLiftProperty
      , I.HasFiniteAlgebraIdempotentLifting
      , I.HasIntegralAlgebraIdempotentLifting
      , I.SatisfiesGabberRootCriterion
      ] := sorry

namespace Ideal

-- Proof sketch: this is the `(5) → (1)` implication in Lemma `15.11.6`.
/-- Gabber's Jacobson-plus-root criterion implies that `(A, I)` is henselian. -/
theorem henselianRing_of_satisfiesGabberRootCriterion (I : Ideal A)
    (hI : I.SatisfiesGabberRootCriterion) :
    HenselianRing A I := sorry

-- Proof sketch: this is the `(1) → (3)` implication in Lemma `15.11.6`, specialized to the
-- identity `A`-algebra.
/-- If `(A, I)` is henselian, then reduction modulo `I` induces a bijection on idempotents of
`A`. -/
theorem quotientMk_bijective_idempotentMap_of_henselianRing (I : Ideal A) [HenselianRing A I] :
    Function.Bijective (Ideal.Quotient.mk I).idempotentMap := sorry

end Ideal

-- Proof sketch: for a Gabber test polynomial, the derivative at any root in `1 + I` is a unit
-- modulo `I`; comparing two such roots modulo the square of their difference shows that the
-- difference is annihilated by a unit, hence the roots coincide.
/-- Under Gabber's criterion, a henselian test polynomial has a unique root in `1 + I`. -/
theorem existsUnique_gabber_root_of_satisfiesGabberRootCriterion (I : Ideal A)
    (hI : I.SatisfiesGabberRootCriterion) {f : A[X]} (hf : I.IsGabberHenselPolynomial f) :
    ∃! i : I, f.IsRoot (1 + ↑i) := sorry

end

/-! ### Lemma_15_11_7 (from Chap15) -/
universe u v

section

open PrimeSpectrum

variable {A : Type u} [CommRing A]

namespace Ideal

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra, viewed through the prime-spectrum closed
  subset `V(I)` and the Chapter 15 idempotent-lifting criterion;
- sampled owner declarations:
  `HenselianRing`,
  `Ideal.HasIntegralAlgebraIdempotentLifting`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`,
  `PrimeSpectrum.zeroLocus_eq_iff`;
- best owner abstraction: the public statement should stay on the canonical owner
  `HenselianRing A I`; the integral-idempotent lifting predicate is derived bridge API from
  Lemma `15.11.6`, and radical equality is the canonical owner-level form of the spectral
  hypothesis `V(I) = V(J)`;
- primitive data: the ideals `I`, `J`, the closed-subset equality `zeroLocus I = zeroLocus J`,
  and for auxiliary integral `A`-algebras `B`, the mapped ideals `Ideal.map (algebraMap A B) I`
  and `Ideal.map (algebraMap A B) J`;
- derived API: the quotient-induced maps on idempotents and the passage from an ideal to its
  radical quotient, which is internal proof infrastructure rather than public owner data.

Source/core/bridge triage:
- `source-facing`: the invariance of henselianity under replacing `I` by an ideal with the same
  closed subset in `Spec A`;
- `core/canonical`: `HenselianRing A I`, `Ideal.HasIntegralAlgebraIdempotentLifting`, and
  `PrimeSpectrum.zeroLocus_eq_iff`;
- `bridge/view`: the zero-locus invariance equivalence for the Chapter 15 integral-idempotent
  lifting owner, proved by passing to the common radical / reduced quotient.
-/

-- If two ideals define the same closed subset of `Spec A`, then the Chapter 15 integral
-- idempotent-lifting criterion is the same for both.
private theorem hasIntegralAlgebraIdempotentLifting_iff_of_zeroLocus_eq (I J : Ideal A)
    (hV : zeroLocus (I : Set A) = zeroLocus (J : Set A)) :
    I.HasIntegralAlgebraIdempotentLifting ↔ J.HasIntegralAlgebraIdempotentLifting := by
  -- For every integral `A`-algebra `B`, the mapped ideals `IB` and `JB` have the same zero locus,
  -- hence the same radical by `PrimeSpectrum.zeroLocus_eq_iff`. Passing from `B / IB` and
  -- `B / JB` to the common reduced quotient by that radical does not change idempotents, because
  -- quotienting by a nilradical extension preserves idempotents. Thus the Chapter 15 owner
  -- `HasIntegralAlgebraIdempotentLifting` depends only on the closed subset `V(I)`.
  sorry

end Ideal

-- Proof sketch: by Lemma `15.11.6`, henselianity of `(A, I)` is equivalent to bijectivity on
-- idempotents after quotienting every integral `A`-algebra `B` by `IB`. If `V(I) = V(J)` in
-- `Spec A`, then for every integral `A`-algebra `B` the extended ideals `IB` and `JB` have the
-- same zero locus, so Lemma `10.21.3` identifies the idempotents of `B/IB` and `B/JB`. Hence the
-- idempotent-lifting criterion is the same for `I` and `J`, and the conclusion follows again from
-- Lemma `15.11.6`.
/-- Lemma 15.11.7: if two ideals `I` and `J` of a commutative ring `A` define the same closed
subset of `Spec A`, then the pair `(A, I)` is henselian if and only if the pair `(A, J)` is
henselian. -/
theorem henselianRing_iff_of_zeroLocus_eq (I J : Ideal A)
    (hV : zeroLocus (I : Set A) = zeroLocus (J : Set A)) :
    HenselianRing A I ↔ HenselianRing A J := by
  let Q : Ideal A → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{u, u}
  let P : Ideal A → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{u, u}
  let T (K : Ideal A) : List Prop :=
    [HenselianRing A K, K.HasEtaleLiftProperty, Q K, P K, K.SatisfiesGabberRootCriterion]
  have hTfaeI : List.TFAE (T I) := by
    simpa [T, Q, P] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion I
  have hI : HenselianRing A I ↔ P I := by
    simpa [T] using hTfaeI.out 0 3
  have hIJ : P I ↔ P J :=
    Ideal.hasIntegralAlgebraIdempotentLifting_iff_of_zeroLocus_eq I J hV
  have hTfaeJ : List.TFAE (T J) := by
    simpa [T, Q, P] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion J
  have hJ : HenselianRing A J ↔ P J := by
    simpa [T] using hTfaeJ.out 0 3
  exact (hI.trans hIJ).trans hJ.symm

end

/-! ### Lemma_15_11_8 (from Chap15) -/
universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) [hH : HenselianRing A I] [Algebra.IsIntegral A B]

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra under integral base change;
- sampled owner declarations:
  `HenselianRing`,
  `Ideal.HasIntegralAlgebraIdempotentLifting`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`;
- best owner abstraction: the public conclusion is still the canonical owner
  `HenselianRing B (Ideal.map (algebraMap A B) I)`, while the idempotent-lifting clause from
  Lemma `15.11.6` is derived API used only to bridge from `(A, I)` to `(B, I B)`;
- primitive data: the ideal `I`, the owner instance `HenselianRing A I`, the integral `A`-algebra
  `B`, and the mapped ideal `Ideal.map (algebraMap A B) I`;
- derived API: integral-idempotent lifting over `A`, its transport to integral `B`-algebras by
  transitivity of integrality, and the `3 → 0` implication of the chapter TFAE.

Source/core/bridge triage:
- `source-facing`: the henselianity of the mapped pair `(B, I B)`;
- `core/canonical`: `HenselianRing` and `Ideal.HasIntegralAlgebraIdempotentLifting`;
- `bridge/view`: the transfer of the integral-idempotent lifting clause from `A` to `B`.
-/

-- Proof sketch: extract the integral-idempotent lifting clause from Lemma `15.11.6` for `(A, I)`.
-- If `C` is integral over `B`, then it is integral over `A` by scalar-tower transitivity, so the
-- same clause applies to `I B`. Applying the reverse implication of the TFAE for `(B, I B)` gives
-- the desired henselian instance.
/-- Lemma 15.11.8: if `(A, I)` is a henselian pair and `A → B` is an integral ring map, then the
pair `(B, I B)` is henselian. -/
instance ideal_map_henselianRing_of_isIntegral :
    HenselianRing B (Ideal.map (algebraMap A B) I) := by
  sorry

end

/-! ### Lemma_15_11_9 (from Chap15) -/
universe u

section

variable {A : Type u} [CommRing A] (I J : Ideal A)

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra, compared along a subideal `I ≤ J` and the
  quotient pair on `A ⧸ I`;
- sampled owner declarations:
  `HenselianRing`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`,
  `Ideal.quotientMk_bijective_idempotentMap_of_henselianRing`,
  `ideal_map_henselianRing_of_isIntegral`;
- best owner abstraction: the public statement is source-facing, but its owner-level content is
  entirely expressed by the canonical predicate `HenselianRing`; the forward/reverse comparison with
  the quotient pair should therefore be stated directly in terms of `HenselianRing`, with the
  idempotent-lifting TFAE from Lemma `15.11.6` and the quotient transfer from Lemma `15.11.8`
  treated as derived bridge API rather than repackaged here;
- primitive data: the commutative ring `A`, ideals `I ≤ J`, and the canonical quotient ideal
  `J.map (Ideal.Quotient.mk I)` in `A ⧸ I`;
- derived API: henselianity of `(A, I)`, henselianity of the quotient pair
  `((A ⧸ I), J.map (Ideal.Quotient.mk I))`, and the integral-idempotent lifting criterion used in
  the proof strategy.

Source/core/bridge triage:
- `source-facing`: the equivalence decomposing henselianity of `(A, J)` into henselianity of
  `(A, I)` together with henselianity of the quotient pair;
- `core/canonical`: `HenselianRing`;
- `bridge/view`: Lemma `15.11.6` for idempotent lifting and Lemma `15.11.8` for passing henselian
  structures to quotient pairs.
-/

-- Proof sketch: for the forward implication, apply the idempotent-lifting characterization from
-- Lemma `15.11.6` to the composite maps `B → B / I B → B / J B` for integral `A`-algebras `B`,
-- using the two henselian hypotheses to get bijectivity on idempotents for the second arrow and
-- the composition. For the converse, first descend henselianity from `(A, J)` to the quotient pair
-- `(A ⧸ I, J / I)` by Lemma `15.11.8`, then use the same composite-idempotent argument to recover
-- henselianity of `(A, I)`.
/-- Lemma 15.11.9: for ideals `I ≤ J` in a commutative ring `A`, the pair `(A, J)` is henselian if
and only if both `(A, I)` and the quotient pair `(A ⧸ I, J / I)` are henselian, where `J / I` is
the image ideal `J.map (Ideal.Quotient.mk I)` in `A ⧸ I`. -/
theorem henselianRing_iff_henselianRing_and_quotient_henselianRing (hIJ : I ≤ J) :
    HenselianRing A J ↔
      HenselianRing A I ∧
        HenselianRing (A ⧸ I) (J.map (Ideal.Quotient.mk I)) := sorry

end

/-! ### Lemma_15_11_10 (from Chap15) -/
universe u

section

variable {A : Type u} [CommRing A] (I I' : Ideal A)
variable [HenselianRing A I] [HenselianRing A I']

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra, compared through the quotient pair
  criterion for a subideal `I ≤ J`;
- sampled owner declarations:
  `HenselianRing`,
  `ideal_map_henselianRing_of_isIntegral`,
  `henselianRing_iff_henselianRing_and_quotient_henselianRing`,
  `Ideal.map_sup`;
- best owner abstraction: the public conclusion is again the canonical owner
  `HenselianRing A (I + I')`; the quotient-pair comparison from Lemma `15.11.9` and the quotient
  transport from Lemma `15.11.8` are derived bridge API, not new local owners;
- primitive data: the ideals `I`, `I'`, the two henselian owner instances on `A`, and the
  canonical quotient map `Ideal.Quotient.mk I : A →+* A ⧸ I`;
- derived API: the quotient henselian structure on `A ⧸ I` coming from `I'`, and the ideal-map
  identity `map (Ideal.Quotient.mk I) (I + I') = map (Ideal.Quotient.mk I) I'`.

Source/core/bridge triage:
- `source-facing`: the henselianity of the sum pair `(A, I + I')`;
- `core/canonical`: `HenselianRing`;
- `bridge/view`: Lemma `15.11.9` for the quotient criterion and Lemma `15.11.8` for passing
  henselianity to quotient rings.
-/

-- Proof sketch: apply Lemma `15.11.9` with `I ≤ I + I'`. The quotient ideal
-- `(I + I') / I` is canonically `I' / I` because `I / I = 0`, and Lemma `15.11.8` supplies the
-- henselian structure on that quotient pair from `(A, I')`. The forward implication of
-- Lemma `15.11.9` then yields henselianity of `(A, I + I')`.
/-- Lemma 15.11.10: if `(A, I)` and `(A, I')` are henselian pairs, then the
pair `(A, I + I')` is henselian. -/
instance ideal_add_henselianRing : HenselianRing A (I + I') := by
  refine
    (henselianRing_iff_henselianRing_and_quotient_henselianRing I (I + I') le_sup_left).2 ?_
  refine ⟨inferInstance, ?_⟩
  simpa [Ideal.map_sup] using
    (show HenselianRing (A ⧸ I) (Ideal.map (algebraMap A (A ⧸ I)) I') from
      ideal_map_henselianRing_of_isIntegral I')

end

/-! ### Lemma_15_11_11 (from Chap15) -/
universe u v

section

variable {J : Type v} {A : J → Type u} [∀ j, CommRing (A j)]
variable (I : ∀ j, Ideal (A j))

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra and their behavior under finite products;
- sampled owner declarations:
  `HenselianRing`,
  `HenselianRing.jac`,
  `HenselianRing.is_henselian`,
  `inverseSystem_limit_henselianRing`;
- best owner abstraction: the canonical owner remains `HenselianRing`; this file should not
  introduce a product-specific wrapper for henselian pairs, only the product/component bridge for
  that owner;
- primitive data: the ideal family `I` and the owner instances `HenselianRing (A j) (I j)` or
  `HenselianRing ((j : J) → A j) (Ideal.pi I)`;
- derived API: the componentwise instance extracted from the product pair, the product instance
  assembled from the component pairs, and the source-facing textbook `iff`.

Source/core/bridge triage:
- `source-facing`: the textbook equivalence `henselianRing_pi_iff`;
- `core/canonical`: the owner `HenselianRing`;
- `bridge/view`: the two instance declarations transporting `HenselianRing` between the product
  pair and its components.
-/

/-- If the product pair is henselian, then each component pair is henselian. -/
instance henselianRing_of_pi_henselianRing (j : J)
    [HenselianRing (∀ j, A j) (Ideal.pi I)] : HenselianRing (A j) (I j) := sorry

/-- If each component pair is henselian, then the product pair is henselian. -/
instance pi_henselianRing [∀ j, HenselianRing (A j) (I j)] :
    HenselianRing (∀ j, A j) (Ideal.pi I) := sorry

-- Proof sketch: for the forward implication, apply henselianity along each projection
-- `Π j, A j → A i`, which sends `Ideal.pi I` to `I i`. For the reverse implication, use that the
-- Jacobson-radical condition and the Hensel lifting property are both checked componentwise in a
-- product ring.
/-- Lemma 15.11.11: the product pair `((j : J) → A j, Ideal.pi I)` is henselian if and only if
each component pair `(A j, I j)` is henselian. -/
theorem henselianRing_pi_iff :
    HenselianRing (∀ j, A j) (Ideal.pi I) ↔ ∀ j, HenselianRing (A j) (I j) := by
  constructor
  · intro h j
    let _ : HenselianRing (∀ j, A j) (Ideal.pi I) := h
    infer_instance
  · intro h
    let _ : ∀ j, HenselianRing (A j) (I j) := h
    infer_instance

end

/-! ### Lemma_15_11_12 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CommRingCat

universe u v

section

variable {J : Type v} [Preorder J]
variable (F : Jᵒᵖ ⥤ CommRingCat.{u})
variable (I : ∀ j : Jᵒᵖ, Ideal (F.obj j))
variable [UnivLE.{v, u}]

/- Domain-style sampling:
- primary domain: inverse limits of henselian pairs in commutative algebra;
- sampled same-domain owner declarations:
  `HenselianRing`,
  `HenselianRing.is_henselian`,
  `henselianRing_pi_iff`,
  `directedSystem_directLimit_henselianRing`;
- best owner abstraction: the public conclusion should stay the canonical owner
  `HenselianRing ((limit F : CommRingCat.{u}) : Type u)
    (⨅ j, Ideal.comap ((limit.π F j).hom) (I j))`; there is no separate inverse-system wrapper
  notion to introduce here;
- primitive data: the inverse system `F`, the ideal family `I`, and the compatibility maps `hI`;
- derived API: the limit object is supplied canonically by the owner instance
  `CommRingCat.hasLimitsOfSize`, activated here by `[UnivLE.{v, u}]`, and the conclusion is the
  induced henselian-pair instance on that limit ring with the canonical inverse-limit ideal.

Source/core/bridge triage:
- `source-facing`: closure of compatible inverse systems of henselian pairs under inverse limits;
- `core/canonical`: the owner class `HenselianRing`;
- `bridge/view`: the inverse-limit ring `limit F` and the limit ideal
  `⨅ j, Ideal.comap ((limit.π F j).hom) (I j)`.
-/

-- Proof sketch: by Categories, Lemma `4.14.11`, it is enough to treat products and equalizers.
-- The product case is Lemma `15.11.11`. For equalizers, use Gabber's criterion from
-- Lemma `15.11.6`: units in `1 + I` are detected after mapping to the ambient henselian pair, so
-- `I` lies in the Jacobson radical by Lemma `10.19.1`; then a Gabber polynomial has a unique root
-- in each ambient henselian pair, and uniqueness forces the lifted roots to agree in the
-- equalizer, producing the desired root in the limit pair.
/-- Lemma 15.11.12: if `F : Jᵒᵖ ⥤ CommRingCat` is an inverse system of commutative rings over a
preordered set and `I j` is a compatible inverse system of henselian ideals on the stages, then
the inverse-limit ring `limit F`, equipped with the limit ideal
`⨅ j, Ideal.comap ((limit.π F j).hom) (I j)`, is a henselian pair. -/
instance inverseSystem_limit_henselianRing
    (hI : ∀ ⦃j k : Jᵒᵖ⦄ (f : j ⟶ k), Ideal.map (F.map f).hom (I j) ≤ I k)
    [∀ j, HenselianRing (F.obj j) (I j)] :
    HenselianRing ((limit F : CommRingCat.{u}) : Type u)
      (⨅ j, Ideal.comap ((limit.π F j).hom) (I j)) := sorry

end

/-! ### Lemma_15_11_13 (from Chap15) -/
universe u v

section

open Ring.DirectLimit

variable {J : Type v} [Preorder J] [Nonempty J] [IsDirectedOrder J]
variable (A : J → Type u) [∀ j, CommRing (A j)]
variable (I : ∀ j, Ideal (A j))
variable (f : ∀ j k, j ≤ k → A j →+* A k)

variable [DirectedSystem A (f · · ·)]

/- Domain-style sampling for filtered colimits of henselian pairs:
- primary domain: commutative algebra of henselian pairs under filtered colimits
- inspected same-domain owners/constructions:
  `Ring.DirectLimit`, `Ring.DirectLimit.of`, `HenselianRing`,
  `Ideal.le_ring_jacobson_of_henselianRing`
- best owner abstraction: the ambient colimit pair is expressed directly by the canonical owner
  `HenselianRing (Ring.DirectLimit A (f · · ·)) (⨆ j, Ideal.map (of A (f · · ·) j) (I j))`;
  there is no separate source-facing wrapper here

Source/core/bridge triage:
- `source-facing`: closure of henselian pairs under filtered colimits
- `core/canonical`: the owner class `HenselianRing`
- `bridge/view`: the direct-limit ring together with the supremum ideal coming from the compatible
  stage ideals

Primitive data is the directed system of rings and ideals together with the compatibility maps
`hI`. Since that compatibility is not inferable from the colimit ring and ideal, it belongs as an
explicit input of the public instance header. The henselian structure on the colimit pair is then
derived from that data, so the file should expose the canonical owner instance directly rather than
introducing any presentation wrapper.
-/

local notation "A∞" => Ring.DirectLimit A (f · · ·)
local notation "I∞" => ⨆ j, Ideal.map (of A (f · · ·) j) (I j)

-- Proof sketch: first show that every element of `1 + I∞` comes from some stage and is therefore
-- a unit by the Jacobson-radical condition there, giving the chapter-level containment
-- `I∞ ≤ Ring.jacobson A∞`. Then descend a monic polynomial over `A∞` and a coprime factorization
-- of its reduction modulo `I∞` to a common stage, apply the henselian lifting property in that
-- stage, and map the lifted factorization to the direct limit.
/-- Lemma 15.11.13: filtered colimits of henselian pairs are henselian. More precisely, if the
stage ideals form a directed system of henselian pairs over a directed set, then the supremum of
their images in the ring direct limit is a henselian ideal of the direct limit ring. -/
instance directedSystem_directLimit_henselianRing
    (hI : ∀ ⦃j k⦄ (h : j ≤ k), Ideal.map (f j k h) (I j) ≤ I k)
    [∀ j, HenselianRing (A j) (I j)] :
    HenselianRing A∞ I∞ :=
  sorry

end

/-! ### Example_15_11_14_Moret_Bailly (from Chap15) -/
open scoped TensorProduct
open Algebra.TensorProduct
open IsLocalRing

noncomputable section

section

variable (p : ℕ) [Fact p.Prime]

/-
Domain-style sampling:
- primary domain: henselian pairs and local/non-local behavior of the tensor square of the
  `p`-adic integers;
- sampled owner declarations of the same kind:
  `HenselianRing`,
  `Ideal.le_ring_jacobson_of_henselianRing`,
  `isLocalHom_of_le_jacobson_bot`,
  `RingHom.domain_isLocalRing`,
  `PadicInt.residueField`,
  `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`;
- best owner abstraction: the source-facing statement is genuinely about the pair
  `(ℤ_[p] ⊗[ℤ] ℤ_[p], (p))`, so the main theorem should stay at the pair owner
  `HenselianRing Aₚ pAₚ`; the quotient-to-residue-field comparison and the non-locality
  contradiction are derived API, while the Moret-Bailly idempotent formula is a source-facing
  companion witness;
- primitive data: the prime `p`, the tensor square `Aₚ`, and the canonical extended maximal ideal
  `pAₚ = Ideal.map (algebraMap ℤ_[p] Aₚ) (maximalIdeal ℤ_[p])`, which is canonically the source
  ideal `(p)`;
- derived API: if `HenselianRing Aₚ pAₚ` held, then
  the owner field `HenselianRing.jac` and `isLocalHom_of_le_jacobson_bot` would make the quotient
  map `Aₚ → Aₚ ⧸ pAₚ` local, and
  `RingHom.domain_isLocalRing` would force `Aₚ` to be local because `Aₚ ⧸ pAₚ` is identified by
  `Algebra.TensorProduct.quotIdealMapEquivQuotTensor` and `PadicInt.residueField` with the residue
  field `𝔽_p`; the odd-prime nontrivial idempotent is a companion witness rather than part of the
  main source-facing theorem.

Source/core/bridge triage:
- `source-facing`: `padicInteger_tensor_self_not_henselianRing`;
- `core/canonical`: `HenselianRing`, `IsLocalHom`, `IsLocalRing`,
  `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`, and `PadicInt.residueField`;
- `bridge/view`: the induced comparison `Aₚ ⧸ pAₚ ≃ κ(ℤ_[p])` and the explicit Moret-Bailly
  idempotent built from a square root of `1 + p`.
-/
local notation "Aₚ" => ℤ_[p] ⊗[ℤ] ℤ_[p]
local notation "mₚ" => maximalIdeal ℤ_[p]
local notation "κₚ" => ResidueField ℤ_[p]
local notation "pAₚ" => Ideal.map (algebraMap ℤ_[p] Aₚ) mₚ

-- Proof sketch: `Algebra.TensorProduct.quotIdealMapEquivQuotTensor Aₚ mₚ` identifies
-- `Aₚ ⧸ pAₚ` with `κₚ ⊗[ℤ_[p]] Aₚ`. Reassociating this tensor product and canceling the base
-- change along `ℤ_[p] → κₚ`, then applying `PadicInt.residueField`, identifies it with `κₚ`, so
-- it is local. If `(Aₚ, pAₚ)` were henselian, then the owner field `HenselianRing.jac` together
-- with `isLocalHom_of_le_jacobson_bot` would show that the quotient map `Aₚ → Aₚ ⧸ pAₚ` is a
-- local homomorphism. Since the target is local,
-- `RingHom.domain_isLocalRing` would force `Aₚ` to be local. Moret-Bailly shows that `Spec Aₚ` is
-- disconnected; for odd primes `p`, the companion idempotent theorem below gives an explicit
-- nontrivial idempotent witness.
private theorem padicInteger_tensor_self_quotient_isLocalRing :
    IsLocalRing (Aₚ ⧸ pAₚ) := by
  let _ : IsLocalRing κₚ := inferInstance
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor Aₚ mₚ
  -- The canonical quotient/tensor owner above is the correct bridge. The remaining identification
  -- with `κₚ` uses tensor reassociation, base-change cancellation, and `PadicInt.residueField`.
  sorry

private theorem padicInt_two_isUnit_of_two_lt (hp_odd : 2 < p) : IsUnit (2 : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  exact (PadicInt.norm_natCast_eq_one_iff).2 <|
    Nat.coprime_of_lt_prime (by decide) hp_odd Fact.out

private theorem exists_padicInt_unit_sq_eq_one_add_p_of_two_lt (hp_odd : 2 < p) :
    ∃ u : ℤ_[p]ˣ, (u : ℤ_[p]) ^ 2 = 1 + p := by
  sorry

/-- The canonical tensor-square ideal in Example 15.11.14 is the source ideal `(p)`. -/
theorem padicInteger_tensor_self_pIdeal_eq_span :
    pAₚ = Ideal.span ({algebraMap ℤ_[p] Aₚ p} : Set Aₚ) := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton]

-- Moret-Bailly's explicit tensor-square idempotent attached to a square root of `1 + p`.
def padicInteger_tensor_self_moretBaillyIdempotent [Invertible (2 : ℤ_[p])]
    (u : ℤ_[p]ˣ) : Aₚ :=
  ((⅟(2 : ℤ_[p])) ⊗ₜ[ℤ] (1 : ℤ_[p])) *
    (1 - ((↑u⁻¹ : ℤ_[p]) ⊗ₜ[ℤ] (↑u : ℤ_[p])))

-- If `u² = 1 + p`, Moret-Bailly's explicit tensor-square element is idempotent.
theorem padicInteger_tensor_self_moretBaillyIdempotent_isIdempotent
    [Invertible (2 : ℤ_[p])]
    (u : ℤ_[p]ˣ) (hu : (u : ℤ_[p]) ^ 2 = 1 + p) :
    IsIdempotentElem (padicInteger_tensor_self_moretBaillyIdempotent p u) := by
  sorry

-- If `u² = 1 + p`, Moret-Bailly's explicit tensor-square idempotent is nonzero.
theorem padicInteger_tensor_self_moretBaillyIdempotent_ne_zero
    [Invertible (2 : ℤ_[p])]
    (u : ℤ_[p]ˣ) (hu : (u : ℤ_[p]) ^ 2 = 1 + p) :
    padicInteger_tensor_self_moretBaillyIdempotent p u ≠ 0 := by
  sorry

-- If `u² = 1 + p`, Moret-Bailly's explicit tensor-square idempotent is not `1`.
theorem padicInteger_tensor_self_moretBaillyIdempotent_ne_one
    [Invertible (2 : ℤ_[p])]
    (u : ℤ_[p]ˣ) (hu : (u : ℤ_[p]) ^ 2 = 1 + p) :
    padicInteger_tensor_self_moretBaillyIdempotent p u ≠ 1 := by
  sorry

/-- For odd primes `p`, Moret-Bailly exhibits a nontrivial idempotent in
`ℤ_[p] ⊗[ℤ] ℤ_[p]`. -/
theorem padicInteger_tensor_self_exists_nontrivial_idempotent_of_two_lt (hp_odd : 2 < p) :
    ∃ e : Aₚ, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  let h2 : IsUnit (2 : ℤ_[p]) := padicInt_two_isUnit_of_two_lt p hp_odd
  letI := h2.invertible
  obtain ⟨u, hu⟩ := exists_padicInt_unit_sq_eq_one_add_p_of_two_lt p hp_odd
  refine ⟨padicInteger_tensor_self_moretBaillyIdempotent p u, ?_⟩
  exact ⟨
    padicInteger_tensor_self_moretBaillyIdempotent_isIdempotent p u hu,
    padicInteger_tensor_self_moretBaillyIdempotent_ne_zero p u hu,
    padicInteger_tensor_self_moretBaillyIdempotent_ne_one p u hu⟩

/-- Moret-Bailly's tensor square `ℤ_[p] ⊗[ℤ] ℤ_[p]` is not local. -/
theorem padicInteger_tensor_self_not_isLocalRing :
    ¬ IsLocalRing Aₚ := by
  -- `Spec (ℤ_[p] ⊗[ℤ] ℤ_[p])` is disconnected; for odd primes the companion theorem above gives
  -- an explicit nontrivial idempotent witnessing this.
  sorry

/-- Example 15.11.14 (Moret-Bailly): the coproduct of the henselian pairs `(ℤ_[p], (p))` and
`(ℤ_[p], (p))`, namely the pair `(ℤ_[p] ⊗[ℤ] ℤ_[p], (p))`, is not henselian. -/
theorem padicInteger_tensor_self_not_henselianRing :
    ¬ HenselianRing Aₚ (Ideal.span ({algebraMap ℤ_[p] Aₚ p} : Set Aₚ)) := by
  rw [← padicInteger_tensor_self_pIdeal_eq_span p]
  intro hH
  haveI : HenselianRing Aₚ pAₚ := hH
  haveI : IsLocalHom (Ideal.Quotient.mk pAₚ) :=
    isLocalHom_of_le_jacobson_bot pAₚ <| by
      simpa [Ideal.jacobson_bot] using Ideal.le_ring_jacobson_of_henselianRing pAₚ
  haveI : IsLocalRing (Aₚ ⧸ pAₚ) := padicInteger_tensor_self_quotient_isLocalRing p
  have hlocal : IsLocalRing Aₚ := RingHom.domain_isLocalRing (Ideal.Quotient.mk pAₚ)
  exact padicInteger_tensor_self_not_isLocalRing p hlocal

end

/-! ### Lemma_15_11_15 (from Chap15) -/
universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: closure of henselian ideals in the complete lattice `Ideal A`;
- sampled same-domain owner declarations:
  `HenselianRing`,
  `ideal_add_henselianRing`,
  `directedSystem_directLimit_henselianRing`,
  `Ideal.sSup_eq_iSup`;
- best owner abstraction: the public core object is the canonical supremum ideal
  `sSup {I : Ideal A | HenselianRing A I}`; henselianity and maximality are derived theorems about
  that ideal, not primitive data of a wrapper package.

Source/core/bridge triage:
- `source-facing`: the existence of a largest henselian ideal of `A`;
- `core/canonical`: the owner predicate `HenselianRing A I` on the complete lattice `Ideal A`;
- `bridge/view`: the supremum ideal of all henselian ideals together with its universal upper-bound
  property.

Primitive data is only the ambient ring `A` and the set of ideals carrying the owner predicate
`HenselianRing A`. The largest henselian ideal is therefore a canonical lattice construction, so
the file should expose that ideal directly and keep the existential statement only as a thin
source-facing consequence.
-/

/-- The supremum of all henselian ideals of `A`. -/
def largestHenselianIdeal : Ideal A :=
  sSup {I : Ideal A | HenselianRing A I}

-- Proof sketch: henselian ideals are closed under finite sums by Lemma `15.11.10`, so the set of
-- henselian ideals is directed under inclusion after replacing any pair by their sum. Apply Lemma
-- `15.11.13` to the constant directed system indexed by henselian ideals with identity transition
-- maps. The resulting direct-limit ideal is exactly the supremum of all henselian ideals.
/-- The supremum of all henselian ideals of `A` is henselian. -/
instance largestHenselianIdeal_henselianRing :
    HenselianRing A largestHenselianIdeal := by
  sorry

/-- Every henselian ideal of `A` is contained in the largest henselian ideal. -/
theorem le_largestHenselianIdeal (I : Ideal A) [HenselianRing A I] :
    I ≤ largestHenselianIdeal := by
  exact le_sSup (show HenselianRing A I from inferInstance)

/-- The largest henselian ideal is the greatest henselian ideal of `A`. -/
theorem isGreatest_largestHenselianIdeal :
    IsGreatest {I : Ideal A | HenselianRing A I} largestHenselianIdeal := by
  refine ⟨show HenselianRing A largestHenselianIdeal from inferInstance, ?_⟩
  intro I hI
  let _ : HenselianRing A I := hI
  exact le_largestHenselianIdeal I

/-- Lemma 15.11.15: in a commutative ring `A`, there exists a henselian ideal containing every
henselian ideal of `A`; equivalently, there is a largest ideal `I` such that `(A, I)` is a
henselian pair. -/
theorem exists_largest_henselianIdeal :
    ∃ I : Ideal A, HenselianRing A I ∧ ∀ J : Ideal A, HenselianRing A J → J ≤ I := by
  refine ⟨largestHenselianIdeal, inferInstance, ?_⟩
  intro J hJ
  let _ : HenselianRing A J := hJ
  exact le_largestHenselianIdeal J

end

/-! ### Lemma_15_11_16 (from Chap15) -/
universe u

section

open PrimeSpectrum
open scoped PrimeSpectrum

variable {A : Type u} [CommRing A]
variable (I : Ideal A) [HenselianRing A I] (p : PrimeSpectrum A)

/- Domain-style sampling:
- primary domain: commutative algebra of henselian pairs, quotient spectra, and connectedness of
  closed subsets of `Spec(A)`;
- sampled owner declarations:
  `HenselianRing`,
  `ideal_map_henselianRing_of_isIntegral`,
  `Ideal.primeSpectrum_quotient_homeomorph_zeroLocus`,
  `primeSpectrum_connectedSpace_iff_idempotents_trivial`;
- best owner abstraction: the source-facing theorem remains the connectedness statement for the
  closed subset `V(p + I)`, but its canonical proof/data flow is owned by the quotient-spectrum
  homeomorphism onto a zero locus, the third-isomorphism equivalence
  `DoubleQuot.quotQuotEquivQuotSup`, and the Chapter 10 connectedness criterion for spectra;
- primitive data: the prime `p`, the ideal `I`, the quotient ring `A ⧸ p.asIdeal`, and the mapped
  ideal `Ideal.map (Ideal.Quotient.mk p.asIdeal) I`;
- derived API: henselianity of the mapped pair, the double-quotient identification with
  `A ⧸ (p.asIdeal ⊔ I)`, and the idempotent-triviality criterion for connected prime spectra.

Source/core/bridge triage:
- `source-facing`: connectedness of the closed subset `V(p + I)` in `Spec(A)`;
- `core/canonical`: `HenselianRing`, `DoubleQuot.quotQuotEquivQuotSup`,
  `Ideal.primeSpectrum_quotient_homeomorph_zeroLocus`, and
  `primeSpectrum_connectedSpace_iff_idempotents_trivial`;
- `bridge/view`: passing from `V(p + I)` to the spectrum of the quotient
  `(A ⧸ p.asIdeal) ⧸ Ideal.map (Ideal.Quotient.mk p.asIdeal) I`.
-/

-- Proof sketch: by Lemma `15.11.8`, the quotient pair
-- `(A ⧸ p.asIdeal, Ideal.map (Ideal.Quotient.mk p.asIdeal) I)` is henselian. Thus it is enough to
-- prove connectedness of `Spec ((A ⧸ p.asIdeal) ⧸ Ideal.map (Ideal.Quotient.mk p.asIdeal) I)`.
-- Since `A ⧸ p.asIdeal` is a domain, any disconnection would give a nontrivial idempotent in this
-- quotient by Lemma `10.21.4`; Lemma `15.11.6` then lifts that idempotent to a nontrivial
-- idempotent of the domain `A ⧸ p.asIdeal`, a contradiction.
/-- Lemma 15.11.16: for a henselian pair `(A, I)` and a prime ideal `p` of `A`, the closed subset
`V(p + I)` of `Spec(A)` is connected. -/
theorem connectedSpace_zeroLocus_prime_add_of_henselianRing :
    ConnectedSpace (V(((p.asIdeal + I : Ideal A) : Set A))) := by
  sorry

end
