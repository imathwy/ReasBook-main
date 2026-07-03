import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.SetTheory.Cardinal.ENat
import StacksProject_2024.Chap15.Definition_15_112_1

-- Declarations for this item will be appended below by the statement pipeline.

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
