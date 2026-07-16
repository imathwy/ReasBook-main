import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import StacksProject_2024.stacks_project.Chap15.Definition_15_124_1

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

section FaithfulTargetField

variable {A : Type u} [CommRing A]
variable {L : Type v} [Field L] [Algebra A L] [FaithfulSMul A L]

/-- Helper for Lemma 15.124.3: the faithful `A`-action on `L` makes `A → L` injective. -/
private theorem algebraMap_eq_zero_of_faithful_targetField {x : A} (hx : algebraMap A L x = 0) :
    x = 0 := by
  have hmap : algebraMap A L x = algebraMap A L 0 := by
    simpa using hx
  exact (FaithfulSMul.algebraMap_injective A L) hmap

end FaithfulTargetField

/-- Helper for Lemma 15.124.3: the integral closure of `A` in the algebraic extension `L` still
has fraction field `L`. -/
private theorem integralClosure_isFractionRing_of_purelyInseparable :
    IsFractionRing B L := by
  -- Clause `(2)` is exactly the standard fraction-field theorem for integral closures in
  -- algebraic extensions.
  exact integralClosure.isFractionRing_of_algebraic
    (fun x hx ↦ algebraMap_eq_zero_of_faithful_targetField (A := A) (L := L) hx)

section IntegralClosureInteger

variable {A : Type u} [CommRing A]
variable {L : Type v} [Field L] [Algebra A L]

/-- Helper for Lemma 15.124.3: an element of `L` integral over `A` is literally represented by an
element of the integral closure `integralClosure A L`. -/
private theorem isInteger_integralClosure_of_isIntegral {x : L} (hx : IsIntegral A x) :
    IsLocalization.IsInteger (integralClosure A L) x := by
  -- Package the integral element as a point of the subtype defining the integral closure.
  change x ∈ (algebraMap (integralClosure A L) L).rangeS
  exact ⟨⟨x, hx⟩, rfl⟩

end IntegralClosureInteger

/-- Helper for Lemma 15.124.3: in a purely inseparable extension of fraction fields, every
element of `L` or its inverse is integral over the valuation ring `A`. -/
private theorem integral_or_integral_inv_of_purelyInseparable (x : L) :
    IsIntegral A x ∨ IsIntegral A x⁻¹ := by
  let q := ringExpChar K
  letI : ExpChar K q := ringExpChar.of_eq (R := K) rfl
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem (F := K) (E := L) q x
  have hqpos : 0 < q ^ n := expChar_pow_pos K q n
  obtain hyA | hyA := ValuationRing.isInteger_or_isInteger A y
  · left
    -- If the purely inseparable power comes from `A`, that power of `x` is integral over `A`.
    have hyIntegral : IsIntegral A (algebraMap K L y) := by
      rcases hyA with ⟨a, ha⟩
      have hmap : algebraMap K L y = algebraMap A L a := by
        rw [← ha]
        simp [IsScalarTower.algebraMap_eq A K L]
      rw [hmap]
      exact isIntegral_algebraMap
    have hpowIntegral : IsIntegral A (x ^ q ^ n) := by
      simpa [hy] using hyIntegral
    exact IsIntegral.of_pow hqpos hpowIntegral
  · right
    -- If the inverse comes from `A`, the same argument applied to inverses gives integrality of
    -- `x⁻¹`.
    have hyIntegral : IsIntegral A (algebraMap K L y⁻¹) := by
      rcases hyA with ⟨a, ha⟩
      have hmap : algebraMap K L y⁻¹ = algebraMap A L a := by
        rw [← ha]
        simp [IsScalarTower.algebraMap_eq A K L]
      rw [hmap]
      exact isIntegral_algebraMap
    have hyInvIntegral : IsIntegral A ((algebraMap K L y)⁻¹) := by
      simpa [map_inv] using hyIntegral
    have hpowIntegral : IsIntegral A ((x⁻¹) ^ q ^ n) := by
      simpa [hy, inv_pow] using hyInvIntegral
    exact IsIntegral.of_pow hqpos hpowIntegral

/-- Lemma 15.124.3 (1): if `A` is a valuation ring and `L / FractionRing A` is purely
inseparable, then the integral closure `B = integralClosure A L` is a valuation ring. -/
instance integralClosure_valuationRing_of_purelyInseparable :
    ValuationRing B := by
  -- Work in the fraction field `L` of the integral closure so the valuation-ring criterion can
  -- be applied directly.
  letI : IsFractionRing B L := integralClosure_isFractionRing_of_purelyInseparable
  rw [ValuationRing.iff_isInteger_or_isInteger B L]
  intro x
  -- The purely inseparable power argument reduces the valuation-ring criterion for `B` to
  -- integrality over `A`.
  obtain hx | hx := integral_or_integral_inv_of_purelyInseparable (A := A) (L := L) x
  · left
    exact isInteger_integralClosure_of_isIntegral (A := A) (L := L) hx
  · right
    exact isInteger_integralClosure_of_isIntegral (A := A) (L := L) hx

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
