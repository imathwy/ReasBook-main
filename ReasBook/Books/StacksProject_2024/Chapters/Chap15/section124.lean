import Mathlib
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.SetTheory.Cardinal.ENat

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_124_1 (from Chap15) -/
universe u v

open IsLocalRing Valuation

/- Domain-style sampling for Definition 15.124.1:
- primary domain: valuation rings, their fraction fields, and the induced morphisms on value
  groups;
- sampled owner declarations:
  `Valuation.HasExtension.ofComapInteger`,
  `ValuativeExtension.mapValueGroupWithZero`,
  `FractionRing.liftAlgebra`;
- best owner abstraction: the induced map on value groups should come from the canonical
  valuation-extension owner on fraction fields, with the underlying fraction-field algebra supplied
  canonically;
- primitive-vs-derived split: the extension data are the injective local algebra map `A → B` and
  its induced fraction-field algebra; the fraction-field valuation extension, weakly-unramified
  predicate, residue degree, and ramification index are derived from that owner abstraction.

Source/core/bridge triage:
- `source-facing`: `IsExtensionOfValuationRings` and `WeaklyUnramified`;
- `core/canonical`: the fraction-field algebra map, `Valuation.HasExtension`, and
  `ValuativeExtension.mapValueGroupWithZero`;
- `bridge/view`: the private proof that the target valuation integers pull back to the source
  valuation integers.
-/

/-- Definition 15.124.1 (1): an extension of valuation rings is an injective local algebra map
`A → B` between valuation rings. -/
class IsExtensionOfValuationRings (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [ValuationRing A] [IsDomain B] [ValuationRing B] : Prop
    extends IsLocalHom (algebraMap A B) where
  algebraMap_injective : Function.Injective (algebraMap A B)

section

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]

/-- The identity map of a valuation ring is an extension of valuation rings. -/
instance valuationRingSelfExtension : IsExtensionOfValuationRings A A where
  toIsLocalHom := by simpa using isLocalHom_id A
  algebraMap_injective := fun _ _ h ↦ h

end

namespace IsExtensionOfValuationRings

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A] [ValuationRing A] [IsDomain B] [ValuationRing B]
variable [h : IsExtensionOfValuationRings A B]

local notation "K" => FractionRing A
local notation "L" => FractionRing B
local notation "ΓL" => ValuativeRel.ValueGroupWithZero L
local notation "vA" => ValuationRing.valuation A K
local notation "vB" => ValuationRing.valuation B L

/-- The `A`-action on `B` is faithful because the structure map `A → B` is injective. -/
instance faithfulSMul : FaithfulSMul A B :=
  (faithfulSMul_iff_algebraMap_injective A B).mpr h.algebraMap_injective

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

private theorem fractionRing_integer_comap_eq :
    Subring.comap (algebraMap K L) (Valuation.integer vB) = Valuation.integer vA := by
  ext x
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact (ValuationRing.mem_integer_iff A K x).2 ⟨0, by simp [hx0]⟩
    · rw [Subring.mem_comap, ValuationRing.mem_integer_iff] at hx
      obtain ⟨b, hb⟩ := hx
      rcases (ValuationRing.iff_isInteger_or_isInteger A K).mp inferInstance x with
        hax | hxinv
      · exact (ValuationRing.mem_integer_iff A K x).2 hax
      · obtain ⟨a, ha⟩ := hxinv
        have ha' : algebraMap B L (algebraMap A B a) = (algebraMap K L x)⁻¹ := by
          calc
            algebraMap B L (algebraMap A B a) = algebraMap A L a := by
              simpa [RingHom.comp_apply] using
                (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B L) a).symm
            _ = algebraMap K L (algebraMap A K a) := by
              simpa [RingHom.comp_apply] using
                DFunLike.congr_fun (IsScalarTower.algebraMap_eq A K L) a
            _ = (algebraMap K L x)⁻¹ := by
              rw [ha]
              simp
        have hmul : b * algebraMap A B a = 1 := by
          apply IsFractionRing.injective B L
          calc
            algebraMap B L (b * algebraMap A B a)
                = algebraMap B L b * algebraMap B L (algebraMap A B a) := by simp
            _ = algebraMap K L x * (algebraMap K L x)⁻¹ := by rw [hb, ha']
            _ = algebraMap B L 1 := by simp [hx0]
        have hunitB : IsUnit (algebraMap A B a) := IsUnit.of_mul_eq_one_right b hmul
        have hunitA : IsUnit a := isUnit_of_map_unit (algebraMap A B) a hunitB
        refine (ValuationRing.mem_integer_iff A K x).2 ?_
        refine ⟨↑hunitA.unit⁻¹, ?_⟩
        simpa [hx0] using congrArg Inv.inv ha
  · intro hx
    rw [Subring.mem_comap, ValuationRing.mem_integer_iff]
    obtain ⟨a, ha⟩ := (ValuationRing.mem_integer_iff A K x).1 hx
    refine ⟨algebraMap A B a, ?_⟩
    rw [← ha]
    calc
      algebraMap B L (algebraMap A B a) = algebraMap A L a := by
        simpa [RingHom.comp_apply] using
          (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B L) a).symm
      _ = algebraMap K L (algebraMap A K a) := by
        simpa [RingHom.comp_apply] using
          DFunLike.congr_fun (IsScalarTower.algebraMap_eq A K L) a

private noncomputable instance fractionRingValuativeRel_source : ValuativeRel K :=
  ValuativeRel.ofValuation vA

private noncomputable instance fractionRingValuativeRel_target : ValuativeRel L :=
  ValuativeRel.ofValuation vB

private instance fractionRing_valuation_compatible_source : Valuation.Compatible vA :=
  Valuation.Compatible.ofValuation vA

private instance fractionRing_valuation_compatible_target : Valuation.Compatible vB :=
  Valuation.Compatible.ofValuation vB

private instance fractionRing_hasExtension : Valuation.HasExtension vA vB :=
  Valuation.HasExtension.ofComapInteger (fractionRing_integer_comap_eq A B)

private instance fractionRingValuativeExtension : ValuativeExtension K L where
  vle_iff_vle a b := by
    simpa [Valuation.vle_iff_le vA, Valuation.vle_iff_le vB]
      using Valuation.HasExtension.val_map_le_iff vA vB a b

/-- Definition 15.124.1 (2): an extension `A ⊆ B` of valuation rings is weakly unramified if the
induced map of value groups is bijective. -/
def WeaklyUnramified : Prop :=
  Function.Bijective (ValuativeExtension.mapValueGroupWithZero K L)

/-- Definition 15.124.1 (3): if the residue-field extension `κ_A ⊆ κ_B` is finite, its residue
degree is the vector-space dimension `[κ_B : κ_A]`. -/
noncomputable def residueDegree [FiniteDimensional (ResidueField A) (ResidueField B)] : ℕ :=
  Module.finrank (ResidueField A) (ResidueField B)

/-- The ramification index of an extension of valuation rings is the cardinality of the quotient
of the target value group by the image of the induced map on value groups. -/
noncomputable def ramificationIndex : ℕ∞ :=
  ENat.card
    (ΓLˣ ⧸ MonoidWithZeroHom.valueGroup (ValuativeExtension.mapValueGroupWithZero K L))

/-- The ramification index of an extension of valuation rings is positive. -/
theorem ramificationIndex_pos :
    0 < ramificationIndex A B := by
  simp [ramificationIndex]

end IsExtensionOfValuationRings

section IntegralClosure

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [ValuationRing A]
variable [Field L] [Algebra A L] [FaithfulSMul A L]

omit [IsDomain A] [ValuationRing A] in
private theorem integralClosure_algebraMap_injective :
    Function.Injective (algebraMap A (integralClosure A L)) := by
  refine Function.Injective.of_comp (f := algebraMap (integralClosure A L) L) ?_
  simpa [IsScalarTower.algebraMap_eq A (integralClosure A L) L] using
    (FaithfulSMul.algebraMap_injective A L : Function.Injective (algebraMap A L))

/-- The normalization map `A → integralClosure A L` is an extension of valuation rings as soon as
the normalization is itself a valuation ring and the original `A`-action on `L` is faithful. -/
instance [ValuationRing (integralClosure A L)] :
    IsExtensionOfValuationRings A (integralClosure A L) where
  toIsLocalHom :=
    (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom
      integralClosure_algebraMap_injective
  algebraMap_injective := integralClosure_algebraMap_injective

end IntegralClosure

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsDiscreteValuationRing B]
variable [h : IsExtensionOfDiscreteValuationRings A B]

/-- A discrete-valuation-ring extension is canonically an extension of valuation rings. -/
instance discreteValuationRingExtension_toIsExtensionOfValuationRings :
    IsExtensionOfValuationRings A B where
  toIsLocalHom := h.toIsLocalHom
  algebraMap_injective := h.algebraMap_injective

end

/-! ### Lemma_15_124_2 (from Chap15) -/
open IsLocalRing
open IsExtensionOfValuationRings

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [ValuationRing A]
variable [CommRing B] [IsDomain B] [ValuationRing B]
variable [Algebra A B] [h : IsExtensionOfValuationRings A B]

local notation "K[" A "]" => FractionRing A

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

-- Proof sketch: compare the induced map `A → B` on valuation rings with the reduction modulo their
-- maximal ideals. The usual linear-independence argument over the residue field shows that any
-- residue-field basis lifts to a `K`-linearly independent family in `L`, forcing finiteness.
/-- The residue field extension of a finite fraction-field extension of valuation rings is
finite-dimensional. -/
theorem finiteDimensional_residueField_of_finiteDimensional_fractionField_extension
    [FiniteDimensional K[A] K[B]] :
    FiniteDimensional (ResidueField A) (ResidueField B) := sorry

attribute [local instance]
  finiteDimensional_residueField_of_finiteDimensional_fractionField_extension

-- Proof sketch: pick units of `B` whose residue classes are linearly independent over
-- `ResidueField A` and pick nonzero elements whose values represent distinct cosets in the quotient
-- `Γ_B / Γ_A`. The textbook minimal-valuation argument shows that all products `bᵢ cⱼ` are
-- `K`-linearly independent in `L`, giving the stated inequality.
/-- Lemma 15.124.2: if `A ⊆ B` is an extension of valuation rings with fraction fields `K ⊆ L`
and `L / K` is finite, then the value-group index times the residue-field degree is bounded by the
fraction-field degree. -/
theorem ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension
    [FiniteDimensional K[A] K[B]] :
    ramificationIndex A B * residueDegree A B ≤
      Module.finrank K[A] K[B] := sorry

end

/-! ### Lemma_15_124_3 (from Chap15) -/
universe u v

section

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [IsPurelyInseparable (FractionRing A) L]

local notation "K" => FractionRing A
local notation "B" => integralClosure A L

/- Domain-style sampling for Lemma 15.124.3:
- primary domain: valuation rings, integral closures, and purely inseparable fraction-field
  extensions.
- inspected owner declarations:
  `IsExtensionOfValuationRings`,
  `integralClosure.isFractionRing_of_algebraic`,
  `Algebra.IsIntegral.isLocalHom`,
  `FaithfulSMul.of_field_isFractionRing`.
- best owner abstraction: `IsExtensionOfValuationRings` for clause `(3)`, with the fraction-field
  statement in clause `(2)` recalled directly from `integralClosure.isFractionRing_of_algebraic`.
- primitive-vs-derived split:
  primitive data: the valuation-ring structure on `B = integralClosure A L`.
  derived API: the fraction-field instance on `B` and the extension-of-valuation-rings bridge
  from `A` to `B`. -/

/- Source/core/bridge triage for Lemma 15.124.3:
- source-facing: clause `(1)`, asserting that the integral closure in a purely inseparable
  extension is again a valuation ring.
- core/canonical: `integralClosure.isFractionRing_of_algebraic` and
  `Algebra.IsIntegral.isLocalHom`, together with
  `FaithfulSMul.of_field_isFractionRing`.
- bridge/view: clause `(3)`, packaging the canonical injective local algebra map
  `A → integralClosure A L` as `IsExtensionOfValuationRings A B`.

Clause `(2)` adds no new owner-level mathematics beyond the existing integral-closure theorem, so
the refined surface should recall that theorem directly rather than keep a parallel local
instance. -/

private instance algebraic_of_purelyInseparable :
    Algebra.IsAlgebraic A L :=
  IsFractionRing.comap_isAlgebraic_iff.mpr <|
    IsPurelyInseparable.isAlgebraic K L

local instance faithfulSmul_targetField : FaithfulSMul A L :=
  FaithfulSMul.of_field_isFractionRing A L K L

/-- Lemma 15.124.3 (1): if `A` is a valuation ring and `L / FractionRing A` is purely
inseparable, then the integral closure `B = integralClosure A L` is a valuation ring. -/
instance integralClosure_valuationRing_of_purelyInseparable :
    ValuationRing B := sorry

/- Lemma 15.124.3 (2): for a purely inseparable extension `L / FractionRing A`, the integral
closure `B = integralClosure A L` has fraction field `L`. Canonically, this is the owner
`IsFractionRing B L`, obtained here from
`integralClosure.isFractionRing_of_algebraic` after specializing algebraicity and the injectivity
of `A → L` coming from the faithful `A`-action on the field `L`. -/
#check (integralClosure.isFractionRing_of_algebraic
  (fun x hx ↦ (FaithfulSMul.algebraMap_injective A L) <| by simpa using hx) : IsFractionRing B L)

/- Lemma 15.124.3 (3): for a purely inseparable extension `L / FractionRing A`, the inclusion
`A → integralClosure A L` is an extension of valuation rings. This is the canonical normalization
instance from `Definition_15_124_1`, using clause `(1)` and the canonical faithful `A`-action on
`L` coming from the fraction-field tower. -/

#synth IsExtensionOfValuationRings A B

end

/-! ### Lemma_15_124_4 (from Chap15) -/
open Ideal
open IsExtensionOfValuationRings

universe u v

section

variable {R : Type u}
variable [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsNormalRing R]

/- Domain-style sampling for Lemma 15.124.4:
- primary domain: height-one localizations of Noetherian normal domains and weakly unramified
  extensions of valuation rings;
- sampled owner declarations:
  `IsExtensionOfDiscreteValuationRings`,
  `IsExtensionOfValuationRings`,
  `IsExtensionOfValuationRings.WeaklyUnramified`,
  `Localization.AtPrime.algebraOfLiesOver`,
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`;
- best owner abstraction: the localized branch should use the discrete-valuation-ring owner
  `IsExtensionOfDiscreteValuationRings`, with the valuation-ring owner
  `IsExtensionOfValuationRings` and the weakly-unramified predicate derived from it; the localized
  algebra is already the canonical `Localization.AtPrime` owner instance from the lying-over
  hypothesis rather than local wrapper data;
- primitive-vs-derived split: the primitive source data are the height-one points
  `p : { p : PrimeSpectrum _ // p.asIdeal.height = 1 }` and
  `q : { q : PrimeSpectrum _ // q.asIdeal.height = 1 }` together with the lying-over condition
  `q.1.asIdeal.LiesOver p.1.asIdeal`; the localized algebra, valuation-ring structure,
  extension-of-discrete-valuation-rings instance, and weakly unramified predicate are derived
  API on that owner.

Source/core/bridge triage:
- `source-facing`: `IsWeaklyUnramifiedHeightOneBranch` and
  `HasWeaklyUnramifiedHeightOneBranches`;
- `core/canonical`: `IsExtensionOfDiscreteValuationRings`, `IsExtensionOfValuationRings`, and
  `IsExtensionOfValuationRings.WeaklyUnramified`;
- `bridge/view`: the canonical localized `Algebra` structure
  `Localization.AtPrime p → Localization.AtPrime q` induced by `q.LiesOver p`. -/

/-- A height-one localization of a Noetherian normal domain is a discrete valuation ring. -/
private instance localizationAtHeightOnePrime_isDiscreteValuationRing
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    IsDiscreteValuationRing (Localization.AtPrime p.1.asIdeal) := by
  sorry

end

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsDomain A] [IsDomain B]
variable [IsNormalRing A] [IsNormalRing B]
variable [Module.Flat A B]

/-- The canonical localized algebra for a height-one branch `q` lying over `p`. -/
private noncomputable instance localizationAtHeightOnePrime_algebra
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 }) [q.1.asIdeal.LiesOver p.1.asIdeal] :
    Algebra (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
  (Localization.localRingHom p.1.asIdeal q.1.asIdeal (algebraMap A B) Ideal.LiesOver.over).toAlgebra

/-- A height-one branch lying over another height-one branch induces an extension of discrete
valuation rings on localizations. -/
private instance localizationAtHeightOnePrime_isExtensionOfDiscreteValuationRings
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 }) [q.1.asIdeal.LiesOver p.1.asIdeal] :
    IsExtensionOfDiscreteValuationRings
      (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) := by
  sorry

variable (A) (B) in
/-- A height-one branch `q` over `p` is weakly unramified when the induced localization
`A_p → B_q` is weakly unramified. -/
def IsWeaklyUnramifiedHeightOneBranch
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 })
    (hq : q.1.asIdeal.LiesOver p.1.asIdeal) : Prop :=
  letI : q.1.asIdeal.LiesOver p.1.asIdeal := hq
  let _ : Algebra (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
    localizationAtHeightOnePrime_algebra p q
  let _ : IsExtensionOfDiscreteValuationRings
      (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
    localizationAtHeightOnePrime_isExtensionOfDiscreteValuationRings p q
  WeaklyUnramified (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal)

variable (A) (B) in
/-- Every height-one prime of `A` admits a height-one branch in `B` whose localized extension is
weakly unramified. -/
def HasWeaklyUnramifiedHeightOneBranches : Prop :=
  ∀ p : { p : PrimeSpectrum A // p.asIdeal.height = 1 },
    ∃ q : { q : PrimeSpectrum B // q.asIdeal.height = 1 },
      ∃ hq : q.1.asIdeal.LiesOver p.1.asIdeal,
        IsWeaklyUnramifiedHeightOneBranch A B p q hq

-- Proof sketch: for each height-one point `p` of `Spec A`, use normality and Noetherianness to
-- view `A_p` and the chosen `B_q` as discrete valuation rings. Weak unramifiedness forces the
-- valuation of `f` in `A_p` to be divisible by `n`. Intersect the corresponding symbolic powers
-- over all minimal height-one primes of `f`, tensor the resulting ideal with `B`, and use the
-- flat local hypothesis to descend that this ideal is free of rank one. A generator `g ∈ A` then
-- has local valuations equal to those of `h`, so `f` differs from `g ^ n` by a unit of `A`.
/-- Lemma 15.124.4: let `A → B` be a flat local homomorphism of Noetherian local normal domains.
If `f ∈ A` becomes a unit times an `n`-th power in `B`, and every height-one
prime of `A` has a height-one prime of `B` above it with weakly unramified localized extension,
then `f` is already a unit times an `n`-th power in `A`. -/
theorem exists_unit_mul_pow_in_source_of_exists_unit_mul_pow_in_target
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    {f : A} {h : B} {n : ℕ}
    (hbranch : HasWeaklyUnramifiedHeightOneBranches A B)
    (hpow : ∃ w : Bˣ, algebraMap A B f = (w : B) * h ^ n) :
    ∃ (g : A) (u : Aˣ), f = (u : A) * g ^ n := sorry

end

/-! ### Lemma_15_124_5 (from Chap15) -/
open IsLocalRing
open IsExtensionOfValuationRings

universe u v

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
variable {B : Type v} [CommRing B] [Algebra A B] [Algebra.Etale A B]
variable (m : Ideal B) [m.IsPrime] [m.LiesOver (maximalIdeal A)]

local notation "Bₘ" => Localization.AtPrime m

/- Domain-style sampling for Lemma 15.124.5:
- primary domain: étale localizations over valuation rings and the induced weakly unramified
  extension-of-valuation-rings owner;
- sampled owner declarations:
  `IsExtensionOfValuationRings`,
  `IsExtensionOfValuationRings.WeaklyUnramified`,
  `IsLocalization.AtPrime.isLocalRing`,
  `Localization.localRingHom`,
  `IsLocalHom.mk`,
  `map_eq_maximalIdeal_of_exists_etale_away`;
- best owner abstraction: the source-facing main theorem should conclude the canonical owner
  predicate `WeaklyUnramified A Bₘ`, while the localized domain,
  valuation-ring support, and extension-of-valuation-rings structure are supplied by canonical
  localization owners together with the one genuinely new local bridge instance;
- primitive-vs-derived split:
  primitive data: the prime `m` of `B` together with the lying-over condition over `maximalIdeal A`;
  derived API: the local branch fact that `Bₘ` is a domain, the local valuation-ring support on
  `Bₘ`, the local bridge instance `IsExtensionOfValuationRings A Bₘ`, and the
  weakly-unramified conclusion.

Source/core/bridge triage:
- `source-facing`: the weakly unramified branch over `maximalIdeal A`;
- `core/canonical`: `IsExtensionOfValuationRings`, `WeaklyUnramified`, and the canonical
  localization-at-prime algebra;
- `bridge/view`: the canonical instance layer realizing `Bₘ` as the
  canonical target valuation ring over `A`. -/

local instance : IsDomain Bₘ := by
  sorry

local instance : ValuationRing Bₘ := by
  sorry

/-- The canonical map from `A` to the localization at a prime over `maximalIdeal A` is an
extension of valuation rings. -/
instance localizationAtPrime_isExtensionOfValuationRings_of_etale :
    IsExtensionOfValuationRings A Bₘ := by
  sorry

-- Proof sketch: apply the valuation-ring analogue of the étale-local normal Noetherian argument
-- to the localization `B_m`. The prime above `maximalIdeal A` gives the canonical local
-- `A`-algebra structure on `Localization.AtPrime m`; one shows this localization is again a
-- valuation ring, that the induced local map is injective, and that the induced map on value
-- groups is bijective.
/-- Lemma 15.124.5: if `A` is a valuation ring, `A → B` is étale, and `m` is a prime of `B`
lying over the maximal ideal of `A`, then the canonical localized branch `Bₘ` is weakly
unramified over `A`. -/
theorem localizationAtPrime_isWeaklyUnramifiedExtensionOfValuationRings_of_etale :
    WeaklyUnramified A Bₘ := by
  sorry

end

/-! ### Lemma_15_124_6 (from Chap15) -/
universe u

open IsExtensionOfValuationRings

section

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {Ah : Type u} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/- Domain-style sampling for Lemma 15.124.6:
- primary domain: valuation rings and weakly unramified extensions along henselization towers;
- sampled owner declarations:
  `IsExtensionOfValuationRings`,
  `WeaklyUnramified`,
  `localizationAtPrime_isWeaklyUnramifiedExtensionOfValuationRings_of_etale`,
  `IsHenselizationOf` / `IsStrictHenselizationOf`;
- best owner abstraction: the primitive source data are the henselization and
  strict-henselization owners on the two structural maps, while the valuation-ring structures,
  extension-of-valuation-rings instances, and weakly-unramified predicates are derived API;
- primitive-vs-derived split:
  primitive data: the chosen henselization `A → Ah` and strict henselization `Ah → Ash`;
  derived API: `IsDomain`, `ValuationRing`, `IsExtensionOfValuationRings`, and the two
  `WeaklyUnramified` statements.

Source/core/bridge triage:
- `source-facing`: the tower statement that both comparison maps in the henselization tower are
  weakly unramified;
- `core/canonical`: `IsExtensionOfValuationRings` and `WeaklyUnramified`;
- `bridge/view`: the étale filtered-colimit presentations supplied by
  `IsHenselizationOf` and `IsStrictHenselizationOf`, together with Lemma `15.124.5` on each étale
  local stage.
-/

/-- A henselization of a valuation ring is again a domain. -/
instance : IsDomain Ah := sorry

/-- A henselization of a valuation ring is again a valuation ring. -/
instance : ValuationRing Ah := sorry

/-- The canonical map from a valuation ring to its henselization is an extension of valuation
rings. -/
instance : IsExtensionOfValuationRings A Ah := sorry

/-- A henselization of a valuation ring is weakly unramified over the base valuation ring. -/
theorem henselization_weaklyUnramified : WeaklyUnramified A Ah := sorry

section

variable {Ash : Type u} [CommRing Ash] [Algebra Ah Ash] [IsStrictHenselizationOf Ah Ash]

/-- A strict henselization over a henselization of a valuation ring is again a domain. -/
instance : IsDomain Ash := sorry

/-- A strict henselization over a henselization of a valuation ring is again a valuation ring. -/
instance : ValuationRing Ash := sorry

/-- The canonical map from a henselization of a valuation ring to a strict henselization over it
is an extension of valuation rings. -/
instance :
    IsExtensionOfValuationRings Ah Ash := sorry

/-- A strict henselization over a henselization of a valuation ring is weakly unramified. -/
theorem strictHenselizationOverHenselization_weaklyUnramified :
    WeaklyUnramified Ah Ash := sorry

end

variable {Ash : Type u} [CommRing Ash] [Algebra Ah Ash]

-- Proof sketch: combine the two canonical weakly unramified statements for the maps
-- `A → Ah` and `Ah → Ash`. The preceding instances record that both target rings remain valuation
-- rings and that both algebra maps are extensions of valuation rings.
/-- Lemma 15.124.6: if `A` is a valuation ring, `Ah` is a henselization of `A`, and `Ash` is a
strict henselization of `Ah`, then the inclusions `A ⊆ Ah` and `Ah ⊆ Ash` are extensions of
valuation rings and both are weakly unramified. -/
theorem henselization_tower_weaklyUnramified [IsStrictHenselizationOf Ah Ash] :
    WeaklyUnramified A Ah ∧ WeaklyUnramified Ah Ash := by
  exact ⟨henselization_weaklyUnramified, strictHenselizationOverHenselization_weaklyUnramified⟩

end
