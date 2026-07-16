import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.ZariskisMainTheorem
import StacksProject_2024.stacks_project.Chap10.Lemma_10_17_7

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

/-- Helper for Lemma 15.11.5: the quotient map from the reduction of the integral closure to
`B ⧸ I B` induced by the inclusion `B' → B`. -/
private abbrev quotientComparison (J : Ideal A) :
    integralClosure A B ⧸ Ideal.map (algebraMap A (integralClosure A B)) J →ₐ[A ⧸ J]
      B ⧸ Ideal.map (algebraMap A B) J :=
  AlgHom.extendScalarsOfSurjective (Ideal.Quotient.mkₐ_surjective A J) <|
    Ideal.quotientMapₐ (Ideal.map (algebraMap A B) J) (integralClosure A B).val
      (integralClosure_ideal_map_le_comap J)

local instance quotientComparisonAlgebra (J : Ideal A) :
    Algebra (integralClosure A B ⧸ Ideal.map (algebraMap A (integralClosure A B)) J)
      (B ⧸ Ideal.map (algebraMap A B) J) :=
  (quotientComparison (A := A) (B := B) J).toRingHom.toAlgebra

/-- Helper for Lemma 15.11.5: the first projection of the given product decomposition, pulled back
along the quotient comparison map from the integral closure quotient. -/
private abbrev firstProjectionComparison
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    Q →ₐ[Abar] C₁ :=
  ((AlgHom.fst Abar C₁ C₂).comp hprod.toAlgHom).comp (quotientComparison I)

/-- Helper for Lemma 15.11.5: the canonical away map from the integral closure to `B`. -/
private noncomputable abbrev awayComparison (g : B') :=
  Localization.awayMapₐ (integralClosure A B).val g

/-- Helper for Lemma 15.11.5: the quotient cutting out the first component selected by the
idempotent `e`. -/
private abbrev idempotentFactor (e : Q) :=
  Q ⧸ Ideal.span ({e} : Set Q)

/-- Helper for Lemma 15.11.5: the canonical quotient map to the factor cut out by `e`. -/
private abbrev idempotentFactorMk (e : Q) :=
  Ideal.Quotient.mk (Ideal.span ({e} : Set Q))

/-- Helper for Lemma 15.11.5: the canonical quotient map to the complementary factor cut out by
`1 - e`. -/
private abbrev complementaryFactorMk (e : Q) :=
  Ideal.Quotient.mk (Ideal.span ({1 - e} : Set Q))

/-- Helper for Lemma 15.11.5: `quotientComparison` sends the class of an integral-closure element
to its class in `B ⧸ I B`. -/
private theorem quotientComparison_mk (x : B') :
    quotientComparison (A := A) (B := B) I (Ideal.Quotient.mk IB' x) =
      Ideal.Quotient.mk IB ((integralClosure A B).val x) := by
  -- The quotient comparison is defined by extending the canonical quotient map, so on quotient
  -- classes represented by elements of `B'` it is definitionally the expected class in `B ⧸ I B`.
  rfl

/-- Helper for Lemma 15.11.5: the pulled-back first projection evaluates on a quotient class as
the first coordinate of the given decomposition of `B ⧸ I B`. -/
private theorem firstProjectionComparison_mk
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) (x : B') :
    firstProjectionComparison (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod
        (Ideal.Quotient.mk IB' x) =
      (hprod (Ideal.Quotient.mk IB ((integralClosure A B).val x))).1 := by
  -- Expand the pulled-back first projection. The previous lemma identifies the quotient
  -- comparison on classes coming from `B'`.
  rfl

/-- Helper for Lemma 15.11.5: the pulled-back first projection restricts to the canonical
`A / I`-algebra map on base elements. -/
private theorem firstProjectionComparison_algebraMap
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) (x : Abar) :
    firstProjectionComparison (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod
        (algebraMap Abar Q x) =
      algebraMap Abar C₁ x := by
  -- Both comparison maps are `A / I`-algebra morphisms, so the pulled-back first projection is a
  -- retraction of the base algebra structure.
  calc
    firstProjectionComparison (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod
        (algebraMap Abar Q x) =
      (AlgHom.fst Abar C₁ C₂)
        (hprod (quotientComparison (A := A) (B := B) I (algebraMap Abar Q x))) := by
          rfl
    _ =
      (AlgHom.fst Abar C₁ C₂) (hprod (algebraMap Abar (B ⧸ IB) x)) := by
        rw [show quotientComparison (A := A) (B := B) I (algebraMap Abar Q x) =
            algebraMap Abar (B ⧸ IB) x by
              exact (quotientComparison (A := A) (B := B) I).commutes x]
    _ = (AlgHom.fst Abar C₁ C₂) (algebraMap Abar (C₁ × C₂) x) := by
      rw [show hprod (algebraMap Abar (B ⧸ IB) x) = algebraMap Abar (C₁ × C₂) x by
            exact hprod.commutes x]
    _ = algebraMap Abar C₁ x := by
      rfl

/-- Helper for Lemma 15.11.5: the pulled-back first projection `Q → C₁` is an integral ring
map because `C₁` is finite over the base `A / I`. -/
private theorem firstProjectionComparison_isIntegral
    [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    RingHom.IsIntegral
      (firstProjectionComparison (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod).toRingHom := by
  intro c
  let φ :=
    firstProjectionComparison (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod
  letI : Algebra Q C₁ := φ.toRingHom.toAlgebra
  letI : IsScalarTower Abar Q C₁ :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- The comparison morphism is the identity on the base `A / I`.
      change algebraMap Abar C₁ x = φ (algebraMap Abar Q x)
      symm
      exact
        firstProjectionComparison_algebraMap
          (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod x
  have hc : IsIntegral Abar c := IsIntegral.of_finite Abar c
  -- Integrality ascends from `A / I` to `Q` along the scalar tower.
  simpa [φ, IsIntegral] using (hc.tower_top : IsIntegral Q c)

/-- Helper for Lemma 15.11.5: the image of `Spec(C₁) → Spec(Q)` under the pulled-back first
projection is closed. This is the closed half of the later clopen-image argument. -/
private theorem firstProjectionComparison_range_isClosed
    [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    IsClosed
      (Set.range
        (PrimeSpectrum.comap
          (firstProjectionComparison (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod).toRingHom)) := by
  let φ :=
    (firstProjectionComparison (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod).toRingHom
  have hIntegral : RingHom.IsIntegral φ :=
    firstProjectionComparison_isIntegral
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod
  -- Integral morphisms induce closed maps on prime spectra, so the image of all of `Spec(C₁)` is
  -- closed in `Spec(Q)`.
  have hClosedImage :
      IsClosed ((PrimeSpectrum.comap φ) '' (Set.univ : Set (PrimeSpectrum C₁))) :=
    (PrimeSpectrum.isClosedMap_comap_of_isIntegral φ hIntegral) Set.univ isClosed_univ
  convert hClosedImage using 1
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, Set.mem_univ x, rfl⟩
  · rintro ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩

/-- Helper for Lemma 15.11.5: a future characteristic localization witness maps to `1` in the
first factor of the prescribed decomposition. -/
private theorem characteristic_witness_first_component
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) (g : B')
    (hg :
      hprod (quotientComparison (A := A) (B := B) I (Ideal.Quotient.mk IB' g)) = (1, 0)) :
    firstProjectionComparison (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod
        (Ideal.Quotient.mk IB' g) = 1 := by
  -- Taking first coordinates of the characteristic equality gives the first-factor normalization.
  simpa [firstProjectionComparison] using congrArg Prod.fst hg

/-- Helper for Lemma 15.11.5: the same characteristic localization witness maps to `0` in the
second factor of the prescribed decomposition of `B ⧸ I B`. -/
private theorem characteristic_witness_second_component
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) (g : B')
    (hg :
      hprod (quotientComparison (A := A) (B := B) I (Ideal.Quotient.mk IB' g)) = (1, 0)) :
    (hprod (quotientComparison (A := A) (B := B) I (Ideal.Quotient.mk IB' g))).2 = 0 := by
  -- Taking second coordinates records that the witness is supported on the first component.
  simpa using congrArg Prod.snd hg

/-- Helper for Lemma 15.11.5: the governing source object `hprod.symm (1, 0)` cutting out the
first component is idempotent in `B ⧸ I B`. -/
private theorem first_component_controller_isIdempotent
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    IsIdempotentElem (hprod.symm ((1 : C₁), (0 : C₂))) := by
  -- Transport the evident idempotence of `(1, 0)` back along the given product decomposition.
  apply hprod.injective
  simp

/-- Helper for Lemma 15.11.5: localizing the product `C₁ × C₂` away from `(1, 0)` identifies it
with the first factor `C₁`. -/
private theorem prod_fst_isLocalization_away_one_zero :
    letI : Algebra (C₁ × C₂) C₁ := (AlgHom.fst Abar C₁ C₂).toRingHom.toAlgebra
    IsLocalization.Away (((1 : C₁), (0 : C₂)) : C₁ × C₂) C₁ := by
  letI : Algebra (C₁ × C₂) C₁ := (AlgHom.fst Abar C₁ C₂).toRingHom.toAlgebra
  have hker :
      RingHom.ker (algebraMap (C₁ × C₂) C₁) =
        Ideal.span ({((0 : C₁), (1 : C₂))} : Set (C₁ × C₂)) := by
    -- The first projection kills exactly the complementary idempotent `(0, 1)`.
    ext x
    rw [Ideal.mem_span_singleton, RingHom.mem_ker]
    constructor
    · intro hx
      change x.1 = 0 at hx
      exact ⟨(0, x.2), by
        ext
        · simp [hx]
        · simp⟩
    · rintro ⟨y, rfl⟩
      change (((0 : C₁), (1 : C₂)) * y).1 = 0
      simp
  have hcomplement :
      ((0 : C₁), (1 : C₂)) = 1 - (((1 : C₁), (0 : C₂)) : C₁ × C₂) := by
    -- Rewriting the kernel generator into the complementary-idempotent form matches the away API.
    ext
    · simp
    · simp
  -- The product away-localization theorem now turns the first projection into the required owner
  -- localization map.
  refine IsLocalization.away_of_isIdempotentElem ?_ ?_ ?_
  · simp [IsIdempotentElem]
  · simpa [hcomplement] using hker
  · simpa using (Prod.fst_surjective : Function.Surjective (algebraMap (C₁ × C₂) C₁))

/-- Helper for Lemma 15.11.5: localizing `B / I B` away from the first-component controller is
canonically the same as the first factor `C₁`. -/
private noncomputable abbrev first_component_away_equiv
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    Localization.Away (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂)) ≃ₐ[Abar] C₁ := by
  let c := hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂)
  letI : Algebra (C₁ × C₂) C₁ := (AlgHom.fst Abar C₁ C₂).toRingHom.toAlgebra
  letI : IsLocalization.Away (((1 : C₁), (0 : C₂)) : C₁ × C₂) C₁ :=
    prod_fst_isLocalization_away_one_zero (A := A) (I := I)
  have hpow :
      Submonoid.map hprod.toMonoidHom (Submonoid.powers c) =
        Submonoid.powers (((1 : C₁), (0 : C₂)) : C₁ × C₂) := by
    -- The product equivalence sends the chosen controller exactly to `(1, 0)`, hence also sends
    -- its powers to the powers of `(1, 0)`.
    ext x
    constructor
    · rintro ⟨y, ⟨n, rfl⟩, rfl⟩
      refine ⟨n, ?_⟩
      simp [c]
    · rintro ⟨n, rfl⟩
      refine ⟨c ^ n, ⟨n, rfl⟩, ?_⟩
      simp [c]
  -- Transport the model away-localization of the product across the given algebra equivalence.
  exact IsLocalization.algEquivOfAlgEquiv
    (Localization.Away c) C₁ hprod hpow

/-- Helper for Lemma 15.11.5: the away localization cutting out the first component is a
quasi-finite `A / I`-algebra because it is equivalent to the finite algebra `C₁`. -/
private theorem first_component_away_quasiFinite
    [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    Algebra.QuasiFinite Abar
      (Localization.Away (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂))) := by
  -- Replace the away localization by the explicit finite first factor.
  exact
    (Algebra.QuasiFinite.iff_of_algEquiv
      (first_component_away_equiv
        (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod)).mpr inferInstance

/-- Helper for Lemma 15.11.5: after contracting a prime of the first-component away localization
back to `B / I B`, the iterated localization `(B / I B)_q` is canonically the same local ring as
the localization of the away ring at that prime. -/
private noncomputable abbrev first_component_away_atPrime_algEquiv
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂))
    (qAway :
      PrimeSpectrum
        (Localization.Away (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂)))) :
    Localization.AtPrime
        (PrimeSpectrum.comap
          (algebraMap (B ⧸ IB)
            (Localization.Away (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂)))) qAway).asIdeal ≃ₐ[B ⧸ IB]
      Localization.AtPrime qAway.asIdeal :=
  -- The canonical iterated-localization equivalence is naturally `B / I B`-linear.
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂))) qAway.asIdeal

/-- Helper for Lemma 15.11.5: every prime of the first-component basic open in `Spec(B / I B)` is
already quasi-finite over `A / I`. -/
private theorem first_component_quasiFiniteAt_of_basicOpen
    [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂))
    (q : PrimeSpectrum (B ⧸ IB))
    (hq : q ∈ PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂))) :
    Algebra.QuasiFiniteAt Abar q.asIdeal := by
  let c := hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂)
  -- Move the chosen prime into the away localization so the source-faithful controller ring is
  -- the only quasi-finite owner we need to transport.
  change q ∈ (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum (B ⧸ IB))) at hq
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away c) c] at hq
  rcases hq with ⟨qAway, rfl⟩
  change
    Algebra.QuasiFinite Abar
      (Localization.AtPrime
        (PrimeSpectrum.comap (algebraMap (B ⧸ IB) (Localization.Away c)) qAway).asIdeal)
  letI :
      Algebra.QuasiFinite Abar (Localization.Away c) :=
    first_component_away_quasiFinite
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod
  letI :
      IsScalarTower Abar (B ⧸ IB)
        (Localization.AtPrime
          (PrimeSpectrum.comap (algebraMap (B ⧸ IB) (Localization.Away c)) qAway).asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI :
      IsScalarTower Abar (B ⧸ IB) (Localization.AtPrime qAway.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- Route correction: first use the away-level quasi-finiteness, then transport once across the
  -- canonical iterated-localization equivalence to the actual local ring at `q`.
  exact
    (Algebra.QuasiFinite.iff_of_algEquiv
      (AlgEquiv.restrictScalars Abar <|
        first_component_away_atPrime_algEquiv
          (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod qAway)).2 inferInstance

/-- Helper for Lemma 15.11.5: a prime of `S` lying over `p` corresponds to a canonical prime of
the fiber ring `p.Fiber S`. -/
private noncomputable abbrev fiberPrimeOver
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    PrimeSpectrum (p.asIdeal.Fiber S) :=
  PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩

/-- Helper for Lemma 15.11.5: the fiber prime attached to `q` contracts back to the original
prime ideal of `S`. -/
private theorem fiberPrimeOver_asIdeal_comap
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    Ideal.comap Algebra.TensorProduct.includeRight.toRingHom
        (fiberPrimeOver p q hq).asIdeal = q.asIdeal := by
  -- The preimage/fiber equivalence is defined so that forgetting back to `Spec(S)` recovers `q`.
  change
    ((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeOver p q hq)).1.asIdeal =
      q.asIdeal
  exact congrArg
    (fun x : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} ↦ x.1.asIdeal)
    ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, hq⟩)

/-- Helper for Lemma 15.11.5: quasi-finiteness at a prime of a finite type algebra is equivalent
to quasi-finiteness at the corresponding fiber prime over its contraction. -/
private theorem quasiFiniteAt_iff_quasiFiniteAt_fiberPrime
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    Algebra.QuasiFiniteAt R q.asIdeal ↔
      Algebra.QuasiFiniteAt p.asIdeal.ResidueField (fiberPrimeOver p q hq).asIdeal := by
  constructor
  · intro h
    letI : Algebra.QuasiFiniteAt R q.asIdeal := h
    have hfiber :
        Ideal.comap Algebra.TensorProduct.includeRight.toRingHom
            (fiberPrimeOver p q hq).asIdeal = q.asIdeal :=
      fiberPrimeOver_asIdeal_comap p q hq
    -- Proof comment: the base-change theorem transports quasi-finiteness from the ambient prime
    -- to the corresponding point of the closed fiber.
    exact
      Algebra.QuasiFiniteAt.baseChange q.asIdeal (fiberPrimeOver p q hq).asIdeal <|
        by simpa using hfiber.symm
  · intro h
    letI : q.asIdeal.LiesOver p.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hq).symm⟩
    letI : Algebra.QuasiFiniteAt p.asIdeal.ResidueField (fiberPrimeOver p q hq).asIdeal := h
    have hfiber :
        Ideal.comap Algebra.TensorProduct.includeRight.toRingHom
            (fiberPrimeOver p q hq).asIdeal = q.asIdeal :=
      fiberPrimeOver_asIdeal_comap p q hq
    -- Proof comment: the residue-field criterion then upgrades the fiber-prime witness back to
    -- quasi-finiteness at the original prime.
    exact
      Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField
        p.asIdeal q.asIdeal (fiberPrimeOver p q hq).asIdeal <|
          by simpa using hfiber

/-- Helper for Lemma 15.11.5: the quotient-homeomorphism image of a point of `Spec(B / I B)` is
the corresponding upstairs prime of `B` lying over `I B`. -/
private noncomputable abbrev first_component_upstairs_prime
    (q : PrimeSpectrum (B ⧸ IB)) :
    PrimeSpectrum B :=
  (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus IB q).1

/-- Helper for Lemma 15.11.5: the upstairs prime extracted from the quotient homeomorphism has the
expected underlying ideal `Ideal.comap (Ideal.Quotient.mk IB) q.asIdeal`. -/
private theorem first_component_upstairs_prime_asIdeal
    (q : PrimeSpectrum (B ⧸ IB)) :
    (first_component_upstairs_prime (A := A) (B := B) I q).asIdeal =
      Ideal.comap (Ideal.Quotient.mk IB) q.asIdeal := by
  -- The quotient-homeomorphism was defined using the spectrum comap of the quotient map.
  simpa [first_component_upstairs_prime, Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply]

/-- Helper for Lemma 15.11.5: contracting the quotient-side base prime along `A → A / I`
recovers the base prime under the corresponding upstairs point of `Spec(B)`. -/
private theorem first_component_base_prime_comap
    (q : PrimeSpectrum (B ⧸ IB)) :
    Ideal.comap (Ideal.Quotient.mk I)
        (PrimeSpectrum.comap (algebraMap Abar (B ⧸ IB)) q).asIdeal =
      (first_component_upstairs_prime (A := A) (B := B) I q).asIdeal.under A := by
  -- Both contractions are computed by following `A → B → B / I B`, so the two ideals agree
  -- elementwise after rewriting the upstairs prime by the quotient-homeomorphism formula.
  rw [first_component_upstairs_prime_asIdeal (A := A) (B := B) I q]
  ext a
  change algebraMap Abar (B ⧸ IB) (Ideal.Quotient.mk I a) ∈ q.asIdeal ↔
    Ideal.Quotient.mk IB (algebraMap A B a) ∈ q.asIdeal
  rfl

/-- Helper for Lemma 15.11.5: the quotient map `A → A / I` induces a bijection on the residue
fields of the matched base primes attached to a first-component point `q`. -/
private theorem first_component_quotient_residueField_bijective
    (q : PrimeSpectrum (B ⧸ IB)) :
    let p : PrimeSpectrum B := first_component_upstairs_prime (A := A) (B := B) I q
    let rbar : PrimeSpectrum Abar := PrimeSpectrum.comap (algebraMap Abar (B ⧸ IB)) q
    Function.Bijective
      (Ideal.ResidueField.mapₐ (p.asIdeal.under A) rbar.asIdeal
        (Algebra.ofId A Abar) (by
          simpa using
            (first_component_base_prime_comap (A := A) (B := B) I q).symm)) := by
  let p : PrimeSpectrum B := first_component_upstairs_prime (A := A) (B := B) I q
  let rbar : PrimeSpectrum Abar := PrimeSpectrum.comap (algebraMap Abar (B ⧸ IB)) q
  -- The quotient map is surjective, so it is surjective on stalks and hence bijective on the
  -- two residue fields attached to matching quotient primes.
  exact
    (RingHom.surjectiveOnStalks_of_surjective
      (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).residueFieldMap_bijective
        (p.asIdeal.under A) rbar.asIdeal
        (by
          simpa using
            (first_component_base_prime_comap (A := A) (B := B) I q).symm)

/-- Helper for Lemma 15.11.5: the quotient map `A → A / I` identifies the residue field of the
base prime under the upstairs point of `Spec(B)` with the residue field of the matched quotient
prime in `Spec(A / I)`. -/
private noncomputable abbrev first_component_quotient_residueField_algEquiv
    (q : PrimeSpectrum (B ⧸ IB)) :
    let p : PrimeSpectrum B := first_component_upstairs_prime (A := A) (B := B) I q
    let rbar : PrimeSpectrum Abar := PrimeSpectrum.comap (algebraMap Abar (B ⧸ IB)) q
    (p.asIdeal.under A).ResidueField ≃ₐ[A] rbar.asIdeal.ResidueField :=
  let p : PrimeSpectrum B := first_component_upstairs_prime (A := A) (B := B) I q
  let rbar : PrimeSpectrum Abar := PrimeSpectrum.comap (algebraMap Abar (B ⧸ IB)) q
  -- Package the already proved bijectivity on residue fields as an explicit algebra equivalence;
  -- this isolates the remaining blocker in the upstairs quasi-finite bridge to the tensor/fiber
  -- comparison alone.
  AlgEquiv.ofBijective
    (Ideal.ResidueField.mapₐ (p.asIdeal.under A) rbar.asIdeal
      (Algebra.ofId A Abar) (by
        simpa using
          (first_component_base_prime_comap (A := A) (B := B) I q).symm))
    (first_component_quotient_residueField_bijective (A := A) (B := B) I q)

/-- Helper for Lemma 15.11.5: the quotient-side closed fiber is canonically the residue-field
base change of `B` over `A`. -/
private noncomputable abbrev first_component_quotient_fiber_normalization
    (q : PrimeSpectrum (B ⧸ IB)) :
    (PrimeSpectrum.comap (algebraMap Abar (B ⧸ IB)) q).asIdeal.Fiber (B ⧸ IB) ≃ₐ[
      (PrimeSpectrum.comap (algebraMap Abar (B ⧸ IB)) q).asIdeal.ResidueField]
      TensorProduct A
        ((PrimeSpectrum.comap (algebraMap Abar (B ⧸ IB)) q).asIdeal.ResidueField) B := by
  let rbar : PrimeSpectrum Abar := PrimeSpectrum.comap (algebraMap Abar (B ⧸ IB)) q
  letI : IsScalarTower A Abar rbar.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ rfl
  -- Proof comment: first rewrite `B / I B` as the quotient base change `(A / I) ⊗[A] B`, then
  -- cancel the redundant middle base change from `A` to `A / I`.
  exact
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl :
        rbar.asIdeal.ResidueField ≃ₐ[rbar.asIdeal.ResidueField] rbar.asIdeal.ResidueField)
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I)).trans <|
      Algebra.TensorProduct.cancelBaseChange A Abar rbar.asIdeal.ResidueField
        rbar.asIdeal.ResidueField B

/-- Helper for Lemma 15.11.5: the first-component point `q` already determines a quasi-finite
prime of the closed fiber of `A / I → B / I B`. -/
private theorem first_component_closedFiber_quasiFiniteAt_of_basicOpen
    [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂))
    (q : PrimeSpectrum (B ⧸ IB))
    (hq : q ∈ PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂))) :
    let rbar : PrimeSpectrum Abar := PrimeSpectrum.comap (algebraMap Abar (B ⧸ IB)) q
    let Qbar : PrimeSpectrum (rbar.asIdeal.Fiber (B ⧸ IB)) := fiberPrimeOver rbar q rfl
    Algebra.QuasiFiniteAt rbar.asIdeal.ResidueField Qbar.asIdeal := by
  let rbar : PrimeSpectrum Abar := PrimeSpectrum.comap (algebraMap Abar (B ⧸ IB)) q
  let Qbar : PrimeSpectrum (rbar.asIdeal.Fiber (B ⧸ IB)) := fiberPrimeOver rbar q rfl
  have hqfinite : Algebra.QuasiFiniteAt Abar q.asIdeal :=
    first_component_quasiFiniteAt_of_basicOpen
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod q hq
  letI : Algebra.QuasiFiniteAt Abar q.asIdeal := hqfinite
  have hQbar :
      Ideal.comap Algebra.TensorProduct.includeRight.toRingHom Qbar.asIdeal = q.asIdeal :=
    fiberPrimeOver_asIdeal_comap rbar q rfl
  -- Route correction: first move from quasi-finiteness at `q` to quasi-finiteness at the
  -- corresponding closed-fiber prime `Qbar`; only afterwards compare that closed fiber with the
  -- matching closed fiber of `A → B`.
  exact
    Algebra.QuasiFiniteAt.baseChange q.asIdeal Qbar.asIdeal <|
      by simpa [Qbar] using hQbar.symm

/-- Helper for Lemma 15.11.5: on the first-component basic open, the local owner hypothesis for
Zariski's Main Theorem is already available. This isolates the source-faithful step where the
proof passes from quasi-finiteness at `q` to the owner `ZariskisMainProperty`. -/
private theorem first_component_zariskiMainProperty_of_basicOpen
    [Algebra.FiniteType A B] [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂))
    (q : PrimeSpectrum (B ⧸ IB))
    (hq : q ∈ PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂))) :
    Algebra.ZariskisMainProperty Abar q.asIdeal := by
  letI : Algebra.FiniteType A (B ⧸ IB) := by
    rw [← RingHom.finiteType_algebraMap, ← (Ideal.Quotient.mkₐ A IB).comp_algebraMap]
    exact RingHom.FiniteType.comp
      (AlgHom.FiniteType.of_surjective (Ideal.Quotient.mkₐ A IB) Ideal.Quotient.mk_surjective)
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Algebra.FiniteType Abar (B ⧸ IB) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A Abar (B ⧸ IB)
  letI : Algebra.QuasiFiniteAt Abar q.asIdeal :=
    first_component_quasiFiniteAt_of_basicOpen
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod q hq
  -- Route correction: record the owner theorem application once, so the remaining blocker in the
  -- shrink lemma is only the transport/descent from the owner witness back to `Q`.
  exact Algebra.ZariskisMainProperty.of_finiteType q.asIdeal

/-- Helper for Lemma 15.11.5: the residue-field equivalence attached to a first-component point
respects the base map from `A`. This packages the scalar-tower comparison needed when transporting
closed-fiber data from `A / I → B / I B` back to `A → B`. -/
private theorem first_component_quotient_residueField_algEquiv_commutes
    (q : PrimeSpectrum (B ⧸ IB)) (a : A) :
    let p : PrimeSpectrum B := first_component_upstairs_prime (A := A) (B := B) I q
    let rbar : PrimeSpectrum Abar := PrimeSpectrum.comap (algebraMap Abar (B ⧸ IB)) q
    first_component_quotient_residueField_algEquiv (A := A) (B := B) I q
      (algebraMap A (p.asIdeal.under A).ResidueField a) =
      algebraMap A rbar.asIdeal.ResidueField a := by
  intro p rbar
  -- Proof comment: this is exactly the `A`-algebra compatibility built into the residue-field
  -- equivalence.
  exact (first_component_quotient_residueField_algEquiv (A := A) (B := B) I q).commutes a

/-- Helper for Lemma 15.11.5: the prime of `B` lying over a first-component point of
`Spec(B / I B)` should be quasi-finite over `A`. This is the source-faithful bridge from the
quotient-side point back to the actual prime of `B` used in the textbook proof. -/
private theorem first_component_quasiFiniteAt_upstairs_of_basicOpen
    [Algebra.FiniteType A B] [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂))
    (q : PrimeSpectrum (B ⧸ IB))
    (hq : q ∈ PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂))) :
    Algebra.QuasiFiniteAt A (Ideal.comap (Ideal.Quotient.mk IB) q.asIdeal) := by
  -- Route correction: the next pass should keep the residue-field scalar tower explicit via
  -- `first_component_quotient_residueField_algEquiv_commutes`, then transport the closed-fiber
  -- prime across the normalized fiber comparison using a small `includeRight` compatibility lemma
  -- before applying `Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField`.
  let _ :=
    first_component_quotient_fiber_normalization
      (A := A) (B := B) I q
  let _ :=
    first_component_quotient_residueField_algEquiv_commutes
      (A := A) (B := B) I q
  -- TODO: build the theorem-local normalized-fiber comparison over the upstairs residue field,
  -- prove that it carries the quotient-side `includeRight` precomposed with `Ideal.Quotient.mk IB`
  -- to the genuine upstairs `includeRight`, and then transport the quasi-finite closed-fiber
  -- witness to the upstairs fiber prime.
  sorry

/-- Helper for Lemma 15.11.5: every point of the first-component basic open of `Spec(B / I B)`
has a direct Zariski-main witness `g ∈ B'` whose away map `B'_g → B_g` is bijective. -/
private theorem exists_local_iso_witness_on_first_component
    [Algebra.FiniteType A B] [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂))
    (q : PrimeSpectrum (B ⧸ IB))
    (hq : q ∈ PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂))) :
    ∃ g : B',
      PrimeSpectrum.comap (quotientComparison (A := A) (B := B) I).toRingHom q ∈
        PrimeSpectrum.basicOpen (Ideal.Quotient.mk IB' g) ∧
      Function.Bijective (awayComparison (A := A) (B := B) g) := by
  let p : Ideal B := Ideal.comap (Ideal.Quotient.mk IB) q.asIdeal
  letI : p.IsPrime := Ideal.comap_isPrime (Ideal.Quotient.mk IB) q.asIdeal
  have hpfinite : Algebra.QuasiFiniteAt A p :=
    first_component_quasiFiniteAt_upstairs_of_basicOpen
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod q hq
  letI : Algebra.QuasiFiniteAt A p := hpfinite
  have hZMT : Algebra.ZariskisMainProperty A p :=
    Algebra.ZariskisMainProperty.of_finiteType (R := A) p
  rcases hZMT with ⟨g, hgq, hbij⟩
  refine ⟨g, ?_, hbij⟩
  -- Rewriting through `quotientComparison_mk` identifies basic-open membership with `g ∉ p`.
  change quotientComparison (A := A) (B := B) I (Ideal.Quotient.mk IB' g) ∉ q.asIdeal
  simpa [p, quotientComparison_mk] using hgq

/-- Helper for Lemma 15.11.5: for `c : C₁`, the pair `(c, 0)` is integral over `A / I`. -/
private theorem first_component_pair_isIntegral
    [Module.Finite Abar C₁] (c : C₁) :
    IsIntegral Abar (((c, (0 : C₂)) : C₁ × C₂)) := by
  -- Choose a monic polynomial for `c`, then multiply by `X` so the same polynomial also kills
  -- the second coordinate `0`.
  rcases IsIntegral.of_finite Abar c with ⟨p, hpmonic, hp⟩
  refine ⟨p * Polynomial.X, hpmonic.mul Polynomial.monic_X, ?_⟩
  calc
    Polynomial.aeval (((c, (0 : C₂)) : C₁ × C₂)) (p * Polynomial.X) =
        Polynomial.aeval (((c, (0 : C₂)) : C₁ × C₂)) p * (((c, (0 : C₂)) : C₁ × C₂)) := by
          simp
    _ = 0 := by
      have hfst :
          (Polynomial.aeval (((c, (0 : C₂)) : C₁ × C₂)) p).1 = Polynomial.aeval c p := by
        simpa [Polynomial.aeval_def] using
          Polynomial.hom_eval₂ p (algebraMap Abar (C₁ × C₂)) (RingHom.fst C₁ C₂)
            (((c, (0 : C₂)) : C₁ × C₂))
      ext
      · calc
          ((Polynomial.aeval (((c, (0 : C₂)) : C₁ × C₂)) p) *
              (((c, (0 : C₂)) : C₁ × C₂))).1 =
              (Polynomial.aeval (((c, (0 : C₂)) : C₁ × C₂)) p).1 * c := by
                rfl
          _ = Polynomial.aeval c p * c := by rw [hfst]
          _ = 0 := by
            simpa [Polynomial.aeval_def, mul_comm] using congrArg (fun x : C₁ => c * x) hp
      · simp

/-- Helper for Lemma 15.11.5: the entire first-component controller `hprod.symm (c, 0)` is
integral over `A / I`. -/
private theorem first_component_controller_isIntegral
    [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) (c : C₁) :
    IsIntegral Abar (hprod.symm (((c, (0 : C₂)) : C₁ × C₂))) := by
  -- Transport the integral pair `(c, 0)` back along the given product decomposition.
  exact IsIntegral.map hprod.symm.toAlgHom <|
    first_component_pair_isIntegral (A := A) (C₁ := C₁) (C₂ := C₂) (I := I) c

/-- Helper for Lemma 15.11.5: once every integral element of `B / I B` lifts through
`quotientComparison`, the pulled-back first projection onto `C₁` is surjective. -/
private theorem firstProjectionComparison_surjective_of_integral_lift
    [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂))
    (hlift :
      ∀ z : B ⧸ IB, IsIntegral Abar z →
        ∃ q : Q, quotientComparison (A := A) (B := B) I q = z) :
    Function.Surjective
      (firstProjectionComparison (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod) := by
  intro c
  have hz :
      IsIntegral Abar (hprod.symm (((c, (0 : C₂)) : C₁ × C₂))) :=
    first_component_controller_isIntegral
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod c
  rcases hlift (hprod.symm (((c, (0 : C₂)) : C₁ × C₂))) hz with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  -- After rewriting the lifted element back to `hprod.symm (c, 0)`, the first projection is
  -- exactly `c`.
  simpa [firstProjectionComparison, hq]

/-- Helper for Lemma 15.11.5: an injective integral-lift description packages
`quotientComparison` as the integral closure of `A / I` inside `B / I B`. -/
private theorem quotientComparison_isIntegralClosure_of_exists_preimage
    (hinj : Function.Injective (quotientComparison (A := A) (B := B) I))
    (hlift :
      ∀ z : B ⧸ IB, IsIntegral Abar z →
        ∃ q : Q, quotientComparison (A := A) (B := B) I q = z) :
    IsIntegralClosure Q Abar (B ⧸ IB) := by
  refine IsIntegralClosure.mk hinj ?_
  intro z
  constructor
  · exact hlift z
  · rintro ⟨q, rfl⟩
    -- Elements coming from `Q` are integral over `A / I`, and integrality is preserved by the
    -- comparison map to `B ⧸ I B`.
    have hqA : IsIntegral A q := Algebra.IsIntegral.isIntegral (R := A) q
    exact IsIntegral.map (quotientComparison (A := A) (B := B) I) <|
      IsIntegral.tower_top hqA

/-- Helper for Lemma 15.11.5: once `Q` is known to be the integral closure of `A / I` in
`B / I B`, the source quotient identifies with the canonical owner ring `integralClosure (A / I)
(B / I B)`. -/
private noncomputable abbrev quotientComparison_owner_equiv
    [IsIntegralClosure Q Abar (B ⧸ IB)] :
    Q ≃ₐ[Abar] integralClosure Abar (B ⧸ IB) :=
  IsIntegralClosure.equiv Abar Q (B ⧸ IB) (integralClosure Abar (B ⧸ IB))

/-- Helper for Lemma 15.11.5: after transporting `Q` to the canonical owner integral closure, the
owner inclusion into `B / I B` is still the original quotient comparison map. -/
private theorem quotientComparison_owner_equiv_comp
    [IsIntegralClosure Q Abar (B ⧸ IB)] :
    (integralClosure Abar (B ⧸ IB)).val.comp
        (quotientComparison_owner_equiv (A := A) (B := B) I).toAlgHom =
      quotientComparison (A := A) (B := B) I := by
  letI : Algebra.IsIntegral Abar Q := by
    exact ⟨fun q ↦ IsIntegralClosure.isIntegral Abar (B ⧸ IB) q⟩
  ext q
  -- Both routes are the canonical `A / I`-algebra map from `Q` into `B / I B`; `simp` reduces
  -- the owner-equivalence side to the explicit `IsIntegralClosure.lift`, whose image in the
  -- ambient ring is given by `IsIntegralClosure.algebraMap_mk'`.
  change
    (((quotientComparison_owner_equiv (A := A) (B := B) I q :
        integralClosure Abar (B ⧸ IB)) : B ⧸ IB)) =
      quotientComparison (A := A) (B := B) I q
  dsimp [quotientComparison_owner_equiv, IsIntegralClosure.equiv, IsIntegralClosure.lift]
  change
    algebraMap (integralClosure Abar (B ⧸ IB)) (B ⧸ IB)
        (IsIntegralClosure.mk' (integralClosure Abar (B ⧸ IB))
          (quotientComparison (A := A) (B := B) I q)
          (IsIntegral.map (quotientComparison (A := A) (B := B) I) <|
            Algebra.IsIntegral.isIntegral (R := Abar) (A := Q) q)) =
      quotientComparison (A := A) (B := B) I q
  exact
    IsIntegralClosure.algebraMap_mk' (integralClosure Abar (B ⧸ IB))
      (quotientComparison (A := A) (B := B) I q)
      (IsIntegral.map (quotientComparison (A := A) (B := B) I) <|
        Algebra.IsIntegral.isIntegral (R := Abar) (A := Q) q)

/-- Helper for Lemma 15.11.5: the underlying ring-hom version of
`quotientComparison_owner_equiv_comp`. This isolates the exact transport equality needed when
comparing away maps. -/
private theorem quotientComparison_owner_equiv_comp_toRingHom
    [IsIntegralClosure Q Abar (B ⧸ IB)] :
    (((integralClosure Abar (B ⧸ IB)).val.comp
        (quotientComparison_owner_equiv (A := A) (B := B) I).toAlgHom).toRingHom) =
      (quotientComparison (A := A) (B := B) I).toRingHom := by
  -- Forgetting the algebra structure does not change the comparison identity.
  ext q
  exact AlgHom.congr_fun (quotientComparison_owner_equiv_comp (A := A) (B := B) I) q

/-- Helper for Lemma 15.11.5: localizing a ring equivalence away from a chosen element is again
bijective. -/
private theorem awayMap_bijective_of_ringEquiv
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (r : R) :
    Function.Bijective (Localization.awayMap e.toRingHom r) := by
  have hpow :
      Submonoid.map e.toMonoidHom (Submonoid.powers r) =
        Submonoid.powers (e r) := by
    -- The ring equivalence sends powers of `r` exactly to powers of `e r`.
    ext x
    constructor
    · rintro ⟨y, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, by simp⟩
    · rintro ⟨n, rfl⟩
      exact ⟨r ^ n, ⟨n, rfl⟩, by simp⟩
  let ψ : Localization.Away r ≃+* Localization.Away (e r) :=
    IsLocalization.ringEquivOfRingEquiv
      (Localization.Away r) (Localization.Away (e r)) e hpow
  have hψ : ψ.toRingHom = Localization.awayMap e.toRingHom r := by
    -- Both maps are the canonical localization map induced by `e`, so uniqueness identifies them.
    apply (IsLocalization.ringHom_ext (M := Submonoid.powers r) (S := Localization.Away r))
    rfl
  simpa [hψ] using ψ.bijective

/-- Helper for Lemma 15.11.5: once `quotientComparison` is recognized as the integral closure,
surjectivity of the first projection is immediate from the canonical lifting property. -/
private theorem firstProjectionComparison_surjective_of_isIntegralClosure
    [Module.Finite Abar C₁]
    [IsIntegralClosure Q Abar (B ⧸ IB)]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    Function.Surjective
      (firstProjectionComparison (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod) := by
  refine
    firstProjectionComparison_surjective_of_integral_lift
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod ?_
  intro z hz
  rcases IsIntegralClosure.isIntegral_iff (A := Q) (R := Abar) (B := B ⧸ IB) (x := z) |>.mp hz with
    ⟨q, hq⟩
  -- Under the algebra structure induced by `quotientComparison`, the canonical lift is exactly
  -- the element supplied by `IsIntegralClosure.isIntegral_iff`.
  refine ⟨q, ?_⟩
  simpa [RingHom.algebraMap_toAlgebra] using hq

/-- Helper for Lemma 15.11.5: inside `Spec(B / I B)`, the `C₁`-factor of the given product
decomposition is exactly the basic open cut out by the controller `hprod.symm (1, 0)`. -/
private theorem first_component_range_eq_basicOpen
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    Set.range
        (PrimeSpectrum.comap
          (((AlgHom.fst Abar C₁ C₂).comp hprod.toAlgHom).toRingHom)) =
      PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂)) := by
  have hfstRange :
      Set.range (PrimeSpectrum.comap ((AlgHom.fst Abar C₁ C₂).toRingHom)) =
        PrimeSpectrum.basicOpen (((1 : C₁), (0 : C₂)) : C₁ × C₂) := by
    -- Reuse the explicit away-localization model of the product first projection.
    letI : Algebra (C₁ × C₂) C₁ := (AlgHom.fst Abar C₁ C₂).toRingHom.toAlgebra
    letI : IsLocalization.Away (((1 : C₁), (0 : C₂)) : C₁ × C₂) C₁ :=
      prod_fst_isLocalization_away_one_zero (A := A) (I := I)
    simpa using
      (PrimeSpectrum.localization_away_comap_range C₁
        (((1 : C₁), (0 : C₂)) : C₁ × C₂))
  -- Transport the product-side basic-open description back across the equivalence `hprod`.
  rw [show PrimeSpectrum.comap
      (((AlgHom.fst Abar C₁ C₂).comp hprod.toAlgHom).toRingHom) =
        PrimeSpectrum.comap hprod.toRingHom ∘
          PrimeSpectrum.comap ((AlgHom.fst Abar C₁ C₂).toRingHom) by
        ext x
        rfl,
    Set.range_comp, hfstRange]
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- Membership in the transported image is exactly nonvanishing of the pulled-back controller.
    simpa [PrimeSpectrum.mem_basicOpen] using hx
  · intro hp
    -- Apply the inverse product equivalence to move the prime back to the pure product setting.
    refine ⟨PrimeSpectrum.comap hprod.symm.toRingHom p, ?_, ?_⟩
    · change ((1 : C₁), (0 : C₂)) ∉ Ideal.comap hprod.symm.toRingHom p.asIdeal
      change hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂) ∉ p.asIdeal
      simpa [PrimeSpectrum.mem_basicOpen] using hp
    · -- The forward and inverse spectrum maps of an algebra equivalence cancel on the nose.
      apply PrimeSpectrum.ext
      ext r
      change hprod.symm (hprod r) ∈ p.asIdeal ↔ r ∈ p.asIdeal
      simp

/-- Helper for Lemma 15.11.5: the image of `Spec(C₁)` inside `Spec(Q)` is the image of the basic
open first-component locus in `Spec(B / I B)` under the quotient-comparison map. -/
private theorem firstProjectionComparison_range_eq_image_first_component_basicOpen
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    Set.range
        (PrimeSpectrum.comap
          (firstProjectionComparison (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod).toRingHom) =
      PrimeSpectrum.comap (quotientComparison (A := A) (B := B) I).toRingHom ''
        PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂)) := by
  -- Unfold the composite spectrum map and replace the `C₁`-range by the explicit first-component
  -- basic open computed above.
  rw [show PrimeSpectrum.comap
      (firstProjectionComparison (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod).toRingHom =
        PrimeSpectrum.comap (quotientComparison (A := A) (B := B) I).toRingHom ∘
          PrimeSpectrum.comap
            (((AlgHom.fst Abar C₁ C₂).comp hprod.toAlgHom).toRingHom) by
        ext x
        rfl,
    Set.range_comp,
    first_component_range_eq_basicOpen
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod]

/-- Helper for Lemma 15.11.5: once the image of `Spec(C₁)` in `Spec(Q)` is open, the already
proved closed-image statement upgrades it to a clopen basic open cut out by a complementary
idempotent. -/
private theorem exists_complementary_idempotent_of_firstProjectionComparison_range_isOpen
    [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂))
    (hRangeOpen :
      IsOpen
        (Set.range
          (PrimeSpectrum.comap
            (firstProjectionComparison
              (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod).toRingHom))) :
    ∃ (e : Q), IsIdempotentElem e ∧
      Set.range
          (PrimeSpectrum.comap
            (firstProjectionComparison
              (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod).toRingHom) =
        PrimeSpectrum.basicOpen (1 - e) := by
  let imageSet :
      Set (PrimeSpectrum Q) :=
    Set.range
      (PrimeSpectrum.comap
        (firstProjectionComparison
          (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod).toRingHom)
  have hRangeClosed : IsClosed imageSet :=
    firstProjectionComparison_range_isClosed
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod
  have hClopen : IsClopen imageSet := ⟨hRangeClosed, hRangeOpen⟩
  -- Classify the clopen image by the unique idempotent whose basic open equals it.
  obtain ⟨u, hu, huImage⟩ :=
    (PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen hClopen).exists
  refine ⟨1 - u, hu.one_sub, ?_⟩
  -- Re-orient the idempotent so the first component is recorded as `D(1 - e)`.
  simpa [imageSet, sub_sub_cancel] using huImage

/-- Helper for Lemma 15.11.5: the idempotents `e` and `1 - e` sum to `1`. -/
private theorem idempotent_add_one_sub_eq_one (e : Q) :
    e + (1 - e) = 1 := by
  -- This is the normalization of the two complementary idempotents.
  simpa using add_sub_cancel_left e (1 : Q)

/-- Helper for Lemma 15.11.5: the idempotents `e` and `1 - e` multiply to zero. -/
private theorem idempotent_mul_one_sub_eq_zero {e : Q} (he : IsIdempotentElem e) :
    e * (1 - e) = 0 := by
  -- Expanding the product and using `e^2 = e` gives the orthogonality relation.
  simpa [mul_sub, he.eq] using sub_eq_zero.mpr he.eq

/-- Helper for Lemma 15.11.5: once the `C₁`-component is identified with the quotient by `e`, the
canonical idempotent splitting produces the required product decomposition of `Q`. -/
private noncomputable abbrev product_decomposition_of_first_component_idempotent
    {e : Q} (he : IsIdempotentElem e)
    (firstFactor : idempotentFactor (A := A) (B := B) I e ≃ₐ[Abar] C₁) :
    Q ≃ₐ[Abar] (C₁ × (Q ⧸ Ideal.span ({1 - e} : Set Q))) :=
  (AlgEquiv.prodQuotientOfIsIdempotentElem Abar (S := Q) he he.one_sub
      (idempotent_add_one_sub_eq_one (A := A) (B := B) I e)
      (idempotent_mul_one_sub_eq_zero (A := A) (B := B) I he)).trans
    (AlgEquiv.prodCongr firstFactor
      (AlgEquiv.refl :
        (Q ⧸ Ideal.span ({1 - e} : Set Q)) ≃ₐ[Abar]
          (Q ⧸ Ideal.span ({1 - e} : Set Q))))

/-- Helper for Lemma 15.11.5: under the canonical idempotent split, a lift whose quotient classes
are `1` in the first factor and `0` in the complementary factor maps to `(1, 0)`. -/
private theorem product_decomposition_of_first_component_idempotent_mk
    {e : Q} (he : IsIdempotentElem e)
    (firstFactor : idempotentFactor (A := A) (B := B) I e ≃ₐ[Abar] C₁)
    (g : B')
    (hgfirst :
      firstFactor
          (idempotentFactorMk (A := A) (B := B) I e (Ideal.Quotient.mk IB' g)) = 1)
    (hgsecond :
      complementaryFactorMk (A := A) (B := B) I e (Ideal.Quotient.mk IB' g) = 0) :
    product_decomposition_of_first_component_idempotent
        (A := A) (B := B) (C₁ := C₁) I he firstFactor
        (Ideal.Quotient.mk IB' g) = (1, 0) := by
  -- The canonical split records exactly the two quotient classes of the witness.
  ext
  · change firstFactor
        (idempotentFactorMk (A := A) (B := B) I e (Ideal.Quotient.mk IB' g)) = 1
    exact hgfirst
  · change complementaryFactorMk
        (A := A) (B := B) I e (Ideal.Quotient.mk IB' g) = 0
    exact hgsecond

/-- Helper for Lemma 15.11.5: the kernel of the first projection `R × S → R` is generated by the
distinguished idempotent `(0, 1)`. -/
private theorem prod_fst_ker_eq_span_zero_one
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    RingHom.ker (AlgHom.fst R R S).toRingHom = Ideal.span ({(0, (1 : S))} : Set (R × S)) := by
  -- Check membership directly: pairs with zero first coordinate are exactly multiples of
  -- `(0, 1)`.
  apply le_antisymm
  · intro x hx
    rcases x with ⟨r, s⟩
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_span_singleton]
    refine ⟨(1, s), ?_⟩
    ext
    · simpa using hx
    · simp
  · intro x hx
    rw [RingHom.mem_ker]
    rcases Ideal.mem_span_singleton.mp hx with ⟨y, rfl⟩
    simp

/-- Helper for Lemma 15.11.5: under an algebra equivalence with a product, the induced first
projection has kernel generated by the preimage of `(0, 1)`. -/
private theorem ker_first_projection_eq_span_symm_zero_one
    {R : Type u} {S : Type v} {T : Type _}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (φ : S ≃ₐ[R] (R × T)) :
    RingHom.ker (((AlgHom.fst R R T).comp φ.toAlgHom).toRingHom) =
      Ideal.span ({φ.symm (0, (1 : T))} : Set S) := by
  -- Transport the explicit kernel generator of the product projection through `φ`.
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_span_singleton]
    refine ⟨φ.symm (1, (φ x).2), ?_⟩
    have hx0 : (φ x).1 = 0 := by
      simpa [AlgHom.comp_apply] using hx
    exact φ.injective <| by
      calc
        φ x = (0, (φ x).2) := by
          ext <;> simp [hx0]
        _ = (0, (1 : T)) * (1, (φ x).2) := by
          simp
        _ = φ (φ.symm (0, (1 : T)) * φ.symm (1, (φ x).2)) := by
          simp
  · intro x hx
    rw [RingHom.mem_ker]
    rcases Ideal.mem_span_singleton.mp hx with ⟨y, rfl⟩
    simp [AlgHom.comp_apply]

/-- Helper for Lemma 15.11.5: the first projection `R₁ × S → R₁` has kernel generated by the
distinguished complementary idempotent `(0, 1)` even when `R₁` is only an algebra over the base
ring `R`. -/
private theorem prod_general_fst_ker_eq_span_zero_one
    {R : Type u} {R₁ : Type v} {S : Type _}
    [CommRing R] [CommRing R₁] [CommRing S]
    [Algebra R R₁] [Algebra R S] :
    RingHom.ker (AlgHom.fst R R₁ S).toRingHom =
      Ideal.span ({(0, (1 : S))} : Set (R₁ × S)) := by
  -- Check membership directly: an element lies in the kernel exactly when its first coordinate is
  -- zero, which means it is a multiple of `(0, 1)`.
  apply le_antisymm
  · intro x hx
    rcases x with ⟨r, s⟩
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_span_singleton]
    refine ⟨(1, s), ?_⟩
    ext
    · simpa using hx
    · simp
  · intro x hx
    rw [RingHom.mem_ker]
    rcases Ideal.mem_span_singleton.mp hx with ⟨y, rfl⟩
    simp

/-- Helper for Lemma 15.11.5: after identifying `S` with a product `R₁ × T`, the pulled-back
first projection has kernel generated by the preimage of `(0, 1)`. -/
private theorem ker_general_first_projection_eq_span_symm_zero_one
    {R : Type u} {R₁ : Type v} {S : Type _} {T : Type _}
    [CommRing R] [CommRing R₁] [CommRing S] [CommRing T]
    [Algebra R R₁] [Algebra R S] [Algebra R T]
    (φ : S ≃ₐ[R] (R₁ × T)) :
    RingHom.ker (((AlgHom.fst R R₁ T).comp φ.toAlgHom).toRingHom) =
      Ideal.span ({φ.symm (0, (1 : T))} : Set S) := by
  -- Transport the explicit kernel computation for the model product along the algebra
  -- equivalence `φ`.
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_span_singleton]
    refine ⟨φ.symm (1, (φ x).2), ?_⟩
    have hx0 : (φ x).1 = 0 := by
      simpa [AlgHom.comp_apply] using hx
    exact φ.injective <| by
      calc
        φ x = (0, (φ x).2) := by
          ext <;> simp [hx0]
        _ = (0, (1 : T)) * (1, (φ x).2) := by
          simp
        _ = φ (φ.symm (0, (1 : T)) * φ.symm (1, (φ x).2)) := by
          simp
  · intro x hx
    rw [RingHom.mem_ker]
    rcases Ideal.mem_span_singleton.mp hx with ⟨y, rfl⟩
    simp [AlgHom.comp_apply]

/-- Helper for Lemma 15.11.5: any product decomposition of `Q` with first factor `C₁` identifies
the quotient by the kernel idempotent of the first projection with `C₁`. -/
private theorem exists_first_factor_of_product_decomposition
    {D : Type _} [CommRing D] [Algebra Abar D]
    (productDecomposition : Q ≃ₐ[Abar] (C₁ × D)) :
    ∃ (e : Q) (he : IsIdempotentElem e)
      (firstFactor : idempotentFactor (A := A) (B := B) I e ≃ₐ[Abar] C₁),
        ∀ x : Q,
          firstFactor (idempotentFactorMk (A := A) (B := B) I e x) =
            ((AlgHom.fst Abar C₁ D).comp productDecomposition.toAlgHom) x := by
  let τ : Q →ₐ[Abar] C₁ :=
    (AlgHom.fst Abar C₁ D).comp productDecomposition.toAlgHom
  have hsurj : Function.Surjective τ := by
    intro x
    refine ⟨productDecomposition.symm (x, 0), ?_⟩
    -- The inverse image of `(x, 0)` maps back to `x` under the first projection.
    simp [τ]
  let e : Q := productDecomposition.symm (0, (1 : D))
  have he : IsIdempotentElem e := by
    -- Pull back the evident idempotence of `(0, 1)` along the product decomposition.
    change e * e = e
    apply productDecomposition.injective
    simp [e]
  have hker : RingHom.ker τ.toRingHom = Ideal.span ({e} : Set Q) := by
    -- The kernel is exactly the pullback of the model kernel of the first projection.
    simpa [τ, e] using
      ker_general_first_projection_eq_span_symm_zero_one
        (R := Abar) (R₁ := C₁) (S := Q) (T := D) productDecomposition
  let firstFactor : idempotentFactor (A := A) (B := B) I e ≃ₐ[Abar] C₁ :=
    (Ideal.quotientEquivAlgOfEq Abar hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  refine ⟨e, he, firstFactor, ?_⟩
  intro x
  -- Evaluating the quotient-by-kernel equivalence on a class recovers the original first
  -- projection `τ`.
  change
    (Ideal.quotientKerAlgEquivOfSurjective hsurj)
        ((Ideal.quotientEquivAlgOfEq Abar hker.symm)
          (Ideal.Quotient.mk (Ideal.span ({e} : Set Q)) x)) =
      τ x
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk hsurj x

/-- Helper for Lemma 15.11.5: a compatible product decomposition of `Q` retracts the base algebra
on its first projection. -/
private theorem first_projection_retract_of_first_component_split
    {D : Type _} [CommRing D] [Algebra Abar D]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂))
    (productDecomposition : Q ≃ₐ[Abar] (C₁ × D))
    (toSecondFactor : D →ₐ[Abar] C₂)
    (hcompat :
      hprod.toAlgHom.comp (quotientComparison (A := A) (B := B) I) =
        (AlgHom.prodMap (AlgHom.id Abar C₁) toSecondFactor).comp
          productDecomposition.toAlgHom) :
    ∀ x : Abar,
      ((AlgHom.fst Abar C₁ D).comp productDecomposition.toAlgHom)
        (algebraMap Abar Q x) = algebraMap Abar C₁ x := by
  -- Compare first coordinates in the compatibility square and simplify the quotient comparison on
  -- base elements.
  intro x
  have hfirst :
      (hprod
          (quotientComparison (A := A) (B := B) I
            (algebraMap Abar Q x))).1 =
        (productDecomposition (algebraMap Abar Q x)).1 := by
    simpa [AlgHom.comp_apply] using
      congrArg Prod.fst (AlgHom.congr_fun hcompat (algebraMap Abar Q x))
  have hbase :
      (hprod
          (quotientComparison (A := A) (B := B) I
            (algebraMap Abar Q x))).1 = algebraMap Abar C₁ x := by
    -- On base elements, `quotientComparison` is the canonical `A / I`-algebra map to `B / I B`.
    rw [(quotientComparison (A := A) (B := B) I).commutes x]
    simpa using congrArg Prod.fst (hprod.commutes x)
  exact hfirst.symm.trans hbase

/-- Helper for Lemma 15.11.5: if every point of the first-component basic open in
`Spec(B / I B)` admits a basic-open neighborhood in `Spec(Q)` contained in the descended image,
then that descended image is open. -/
private theorem first_component_image_isOpen_of_pointwise_basicOpen_shrinks
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂))
    (hShrink :
      ∀ q : PrimeSpectrum (B ⧸ IB),
        q ∈ PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂)) →
          ∃ u : Q,
            PrimeSpectrum.comap (quotientComparison (A := A) (B := B) I).toRingHom q ∈
              PrimeSpectrum.basicOpen u ∧
            (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum Q)) ⊆
              PrimeSpectrum.comap (quotientComparison (A := A) (B := B) I).toRingHom ''
                PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂))) :
    IsOpen
      (Set.range
        (PrimeSpectrum.comap
          (firstProjectionComparison
            (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod).toRingHom)) := by
  rw [firstProjectionComparison_range_eq_image_first_component_basicOpen
    (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod]
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨q, hq, rfl⟩
  rcases hShrink q hq with ⟨u, huMem, huSubset⟩
  -- The local shrink gives a basic-open neighborhood of the chosen point already contained in the
  -- descended image.
  exact Filter.mem_of_superset
    (PrimeSpectrum.isOpen_basicOpen.mem_nhds huMem) huSubset

/-- Helper for Lemma 15.11.5: once the pointwise basic-open shrinks are available, the clopen
first-component image in `Spec(Q)` yields the complementary idempotent cutting out that image. -/
private theorem exists_first_component_complementary_idempotent_of_pointwise_basicOpen_shrinks
    [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂))
    (hShrink :
      ∀ q : PrimeSpectrum (B ⧸ IB),
        q ∈ PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂)) →
          ∃ u : Q,
            PrimeSpectrum.comap (quotientComparison (A := A) (B := B) I).toRingHom q ∈
              PrimeSpectrum.basicOpen u ∧
            (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum Q)) ⊆
              PrimeSpectrum.comap (quotientComparison (A := A) (B := B) I).toRingHom ''
                PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂))) :
    ∃ (e : Q), IsIdempotentElem e ∧
      Set.range
          (PrimeSpectrum.comap
            (firstProjectionComparison
              (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod).toRingHom) =
        PrimeSpectrum.basicOpen (1 - e) := by
  have hRangeOpen :
      IsOpen
        (Set.range
          (PrimeSpectrum.comap
            (firstProjectionComparison
              (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod).toRingHom)) :=
    first_component_image_isOpen_of_pointwise_basicOpen_shrinks
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod hShrink
  -- The already proved closed-image half now upgrades the image to the complementary idempotent
  -- basic open in `Spec(Q)`.
  exact
    exists_complementary_idempotent_of_firstProjectionComparison_range_isOpen
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod hRangeOpen

/-- Helper for Lemma 15.11.5: a unit cannot lie in a prime ideal. -/
private theorem isUnit_not_mem_prime {R : Type*} [CommRing R] {u : R}
    (hu : IsUnit u) (p : PrimeSpectrum R) :
    u ∉ p.asIdeal := by
  intro hup
  -- A prime ideal containing a unit would be the unit ideal, contradicting primality.
  have hTop : p.asIdeal = ⊤ :=
    Ideal.eq_top_of_isUnit_mem p.asIdeal hup hu
  exact p.isPrime.ne_top hTop

/-- Helper for Lemma 15.11.5: multiplying by a unit does not change a basic open. -/
private theorem basicOpen_mul_isUnit_right {R : Type*} [CommRing R] (x y : R)
    (hy : IsUnit y) :
    PrimeSpectrum.basicOpen (x * y) = PrimeSpectrum.basicOpen x := by
  rw [PrimeSpectrum.basicOpen_mul]
  have hyTop : PrimeSpectrum.basicOpen y = ⊤ := by
    ext p
    constructor
    · intro _
      simp
    · intro _
      -- Units stay out of every prime ideal, so their basic open is all of `Spec`.
      change y ∉ p.asIdeal
      exact isUnit_not_mem_prime hy p
  -- Intersecting with the full basic open leaves the original chart unchanged.
  simpa [hyTop]

/-- Helper for Lemma 15.11.5: a basic open in an away localization descends to a principal basic
open `D(u * g)` on the base ring. -/
private theorem image_basicOpen_of_away_localization_eq_basicOpen_mul
    {R : Type*} [CommRing R] (g : R) (z : Localization.Away g) :
    ∃ u : R,
      PrimeSpectrum.comap (algebraMap R (Localization.Away g)) '' PrimeSpectrum.basicOpen z =
        PrimeSpectrum.basicOpen (u * g) := by
  let a : R := (IsLocalization.sec (Submonoid.powers g) z).1
  let s : Submonoid.powers g := (IsLocalization.sec (Submonoid.powers g) z).2
  refine ⟨a, ?_⟩
  have hsUnit : IsUnit ((algebraMap R (Localization.Away g)) ↑s) :=
    IsLocalization.map_units (Localization.Away g) s
  have hz :
      PrimeSpectrum.basicOpen z =
        PrimeSpectrum.basicOpen (algebraMap R (Localization.Away g) a) := by
    -- Write `z` as a numerator times an invertible denominator and discard the unit factor.
    calc
      PrimeSpectrum.basicOpen z =
          PrimeSpectrum.basicOpen (z * (algebraMap R (Localization.Away g)) ↑s) := by
            symm
            exact basicOpen_mul_isUnit_right z ((algebraMap R (Localization.Away g)) ↑s) hsUnit
      _ = PrimeSpectrum.basicOpen (algebraMap R (Localization.Away g) a) := by
            rw [IsLocalization.sec_spec (Submonoid.powers g) z]
  -- Pull back the numerator basic open and intersect with the known image `D(g)` of the away
  -- localization map on spectra.
  calc
    PrimeSpectrum.comap (algebraMap R (Localization.Away g)) '' PrimeSpectrum.basicOpen z =
        PrimeSpectrum.comap (algebraMap R (Localization.Away g)) ''
          PrimeSpectrum.basicOpen (algebraMap R (Localization.Away g) a) := by
          rw [hz]
    _ = ((PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)) ∩
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away g)))) := by
          rw [← PrimeSpectrum.comap_basicOpen (algebraMap R (Localization.Away g)) a,
            TopologicalSpace.Opens.coe_comap, ContinuousMap.coe_mk,
            Set.image_preimage_eq_inter_range]
    _ = ((PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)) ∩
          PrimeSpectrum.basicOpen g) := by
          rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    _ = (PrimeSpectrum.basicOpen (a * g) : Set (PrimeSpectrum R)) := by
          simpa using congrArg
            (fun U : TopologicalSpace.Opens (PrimeSpectrum R) => (U : Set (PrimeSpectrum R)))
            (PrimeSpectrum.basicOpen_mul a g).symm

/-- Helper for Lemma 15.11.5: the unresolved source-faithful frontier can be packaged as one
Zariski-main comparison statement combining the local basic-open shrinks with the descended
idempotent split and its localization witness. -/
private theorem exists_basicOpen_shrink_in_first_component_image
    [Algebra.FiniteType A B] [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂))
    (q : PrimeSpectrum (B ⧸ IB))
    (hq : q ∈ PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂))) :
    ∃ u : Q,
      PrimeSpectrum.comap (quotientComparison (A := A) (B := B) I).toRingHom q ∈
        PrimeSpectrum.basicOpen u ∧
      (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum Q)) ⊆
        PrimeSpectrum.comap (quotientComparison (A := A) (B := B) I).toRingHom ''
          PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂)) := by
  -- Route correction: the source-faithful local witness in `B'` is now available. The remaining
  -- work here is only the denominator-clearing descent of a principal open from `B'_g` back to
  -- `Q = B' / I B'`.
  obtain ⟨g, hgMem, hgBij⟩ :=
    exists_local_iso_witness_on_first_component
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod q hq
  -- TODO: choose a principal basic open around the image of `q` in `Spec(B'_g)`, transport it
  -- across the bijection `B'_g ≃ B_g`, and descend it through
  -- `image_basicOpen_of_away_localization_eq_basicOpen_mul` to obtain the required `u : Q`.
  let _ := hgMem
  let _ := hgBij
  sorry

/-- Helper for Lemma 15.11.5: the unresolved source-faithful frontier can be packaged as one
Zariski-main comparison statement combining the local basic-open shrinks with the descended
idempotent split and its localization witness. -/
private theorem exists_first_component_zariski_main_package
    [Algebra.FiniteType A B] [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    (∀ q : PrimeSpectrum (B ⧸ IB),
        q ∈ PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂)) →
          ∃ u : Q,
            PrimeSpectrum.comap (quotientComparison (A := A) (B := B) I).toRingHom q ∈
              PrimeSpectrum.basicOpen u ∧
            (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum Q)) ⊆
              PrimeSpectrum.comap (quotientComparison (A := A) (B := B) I).toRingHom ''
                PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂))) ∧
    ∃ (e : Q) (he : IsIdempotentElem e)
      (firstFactor : idempotentFactor (A := A) (B := B) I e ≃ₐ[Abar] C₁)
      (toSecondFactor : (Q ⧸ Ideal.span ({1 - e} : Set Q)) →ₐ[Abar] C₂) (g : B'),
        let productDecomposition :=
          product_decomposition_of_first_component_idempotent
            (A := A) (B := B) (C₁ := C₁) I he firstFactor
        hprod.toAlgHom.comp (quotientComparison (A := A) (B := B) I) =
              (AlgHom.prodMap (AlgHom.id Abar C₁) toSecondFactor).comp
              productDecomposition.toAlgHom ∧
          firstFactor
              (idempotentFactorMk (A := A) (B := B) I e (Ideal.Quotient.mk IB' g)) = 1 ∧
          complementaryFactorMk (A := A) (B := B) I e (Ideal.Quotient.mk IB' g) = 0 ∧
          Function.Bijective (awayComparison (A := A) (B := B) g) := by
  -- Route correction: the global integral-closure detour is no longer the frontier. What remains
  -- is one geometric package: local Zariski-main on the first-component basic open, followed by
  -- the quotient-factor identification and the final globalized away-bijectivity step.
  have hShrink :
      ∀ q : PrimeSpectrum (B ⧸ IB),
        q ∈ PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂)) →
          ∃ u : Q,
            PrimeSpectrum.comap (quotientComparison (A := A) (B := B) I).toRingHom q ∈
              PrimeSpectrum.basicOpen u ∧
            (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum Q)) ⊆
              PrimeSpectrum.comap (quotientComparison (A := A) (B := B) I).toRingHom ''
                PrimeSpectrum.basicOpen (hprod.symm (((1 : C₁), (0 : C₂)) : C₁ × C₂)) := by
    intro q hq
    exact
      exists_basicOpen_shrink_in_first_component_image
        (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod q hq
  refine ⟨hShrink, ?_⟩
  have hIdempotent :
      ∃ (e : Q), IsIdempotentElem e ∧
        Set.range
            (PrimeSpectrum.comap
              (firstProjectionComparison
                (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod).toRingHom) =
          PrimeSpectrum.basicOpen (1 - e) :=
    exists_first_component_complementary_idempotent_of_pointwise_basicOpen_shrinks
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod hShrink
  -- TODO: from the clopen description of the first-component image, recover the quotient factor
  -- `Q / (e) ≃ C₁`, assemble the compatible second-factor map to `C₂`, choose a lift of `1 - e`,
  -- and globalize the away-bijective witness on `D(1 - e)`.
  let _ := hIdempotent
  sorry

/-- Helper for Lemma 15.11.5: the remaining geometric phase should produce the idempotent cutting
out the first component of `Spec(Q)`, together with the comparison map to `C₂` and a lift whose
away map is bijective. -/
private theorem exists_first_component_idempotent_witness
    [Algebra.FiniteType A B] [Module.Finite Abar C₁]
    (hprod : (B ⧸ IB) ≃ₐ[Abar] (C₁ × C₂)) :
    ∃ (e : Q) (he : IsIdempotentElem e)
      (firstFactor : idempotentFactor (A := A) (B := B) I e ≃ₐ[Abar] C₁)
      (toSecondFactor : (Q ⧸ Ideal.span ({1 - e} : Set Q)) →ₐ[Abar] C₂) (g : B'),
        let productDecomposition :=
          product_decomposition_of_first_component_idempotent
            (A := A) (B := B) (C₁ := C₁) I he firstFactor
        hprod.toAlgHom.comp (quotientComparison (A := A) (B := B) I) =
            (AlgHom.prodMap (AlgHom.id Abar C₁) toSecondFactor).comp
              productDecomposition.toAlgHom ∧
          firstFactor
              (idempotentFactorMk (A := A) (B := B) I e (Ideal.Quotient.mk IB' g)) = 1 ∧
          complementaryFactorMk (A := A) (B := B) I e (Ideal.Quotient.mk IB' g) = 0 ∧
          Function.Bijective (awayComparison (A := A) (B := B) g) := by
  -- Unpack the descended idempotent split and localization witness from the consolidated package.
  exact
    (exists_first_component_zariski_main_package
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod).2

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
  -- Route correction: the proof now isolates the genuinely geometric phase into a single helper.
  -- Once that helper supplies the idempotent witness, the remaining work is the canonical
  -- idempotent-product packaging handled below.
  obtain ⟨e, he, firstFactor, toSecondFactor, g, hdata⟩ :=
    exists_first_component_idempotent_witness
      (A := A) (B := B) (C₁ := C₁) (C₂ := C₂) I hprod
  let productDecomposition :=
    product_decomposition_of_first_component_idempotent
      (A := A) (B := B) (C₁ := C₁) I he firstFactor
  refine ⟨e, he, productDecomposition, toSecondFactor, g, ?_⟩
  -- Unpack the geometric witness data and finish with the canonical idempotent split.
  dsimp [productDecomposition] at hdata ⊢
  rcases hdata with ⟨hcompat, hgfirst, hgsecond, hAway⟩
  refine ⟨hcompat, ?_, hAway⟩
  exact
    product_decomposition_of_first_component_idempotent_mk
      (A := A) (B := B) (C₁ := C₁) I he firstFactor g hgfirst hgsecond

end
