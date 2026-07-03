import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import StacksProject_2024.Chap15.Definition_15_124_1

-- Declarations for this item will be appended below by the statement pipeline.

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
