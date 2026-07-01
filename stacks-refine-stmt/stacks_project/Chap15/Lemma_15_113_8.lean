import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise
open IntermediateField
open Algebra

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [Algebra.IsAlgebraic K L]

local notation "G" => Gal(L / K)
local notation "B" => integralClosure A L
local notation "B[" H "]" => FixedPoints.subalgebra A B H
local notation "L[" H "]" => IntermediateField.fixedField H

/- Domain-style sampling for Lemma 15.113.8:
- primary domain: integral closures and fixed objects for subgroup actions of `Gal(L / K)` on the
  integral closure `B = integralClosure A L`;
- sampled owner declarations:
  `Ideal.inertia`,
  `FixedPoints.subalgebra`,
  `IntermediateField.fixedField`,
  `algebraMap_galRestrict_apply`;
- best owner abstraction: for a subgroup `H : Subgroup Gal(L / K)`, the fixed `A`-subalgebra
  `FixedPoints.subalgebra A B H` of the integral closure and the fixed field
  `IntermediateField.fixedField H`;
- primitive data: the canonical fixed-subalgebra owner `FixedPoints.subalgebra A B H`;
- derived API: the canonical map `B^H → L^H` and the source-facing inertia specialization obtained
  by setting `H = m.inertia G`.

Layer triage:
- `source-facing`: the inertia specialization saying `B^I` is the integral closure of `A` in
  `L^I`, together with the later local étale statement;
- `core/canonical`: the owner pair `FixedPoints.subalgebra A B H` /
  `IntermediateField.fixedField H`;
- `bridge/view`: the canonical map from the fixed subalgebra to the fixed field.

The bridge layer therefore belongs at the general subgroup level. Only the final étale statement
should remain in the local inertia/maximal-ideal section. -/

variable (H : Subgroup Gal(L/K))

-- Proof sketch: an element of the fixed subalgebra is fixed in `L` by every element of `H`, so
-- its image lies in the fixed field `L^H`.
private theorem fixedSubalgebra_mem_fixedField (x : B[H]) :
    algebraMap B L x ∈ L[H] :=
  sorry

private noncomputable abbrev fixedSubalgebraToFixedField : B[H] →ₐ[A] L[H] :=
  show B[H] →ₐ[A] L[H] from
    AlgHom.codRestrict
      ((IsScalarTower.toAlgHom A B L).comp (B[H]).val)
      (((L[H]).toSubalgebra : Subalgebra K L).restrictScalars A)
      (fixedSubalgebra_mem_fixedField H)

private noncomputable instance fixedSubalgebraToFixedFieldAlgebra :
    Algebra B[H] L[H] :=
  (fixedSubalgebraToFixedField H).toRingHom.toAlgebra

-- Proof sketch: an element of `L^H` integral over `A` already lies in the ambient integral
-- closure `B`, and the fixed-field condition forces it to land in the fixed subalgebra `B^H`.
/-- Companion bridge theorem: for any subgroup `H ≤ Gal(L / K)`, the fixed subalgebra `B^H` of
the integral closure `B` is the integral closure of `A` in the fixed field `L^H`. -/
theorem fixedSubalgebra_isIntegralClosure
    : IsIntegralClosure B[H] A L[H] := sorry

variable (m : Ideal (integralClosure A L))

local notation "I" => m.inertia Gal(L / K)

/-- Lemma 15.113.8 (1): the inertia fixed subalgebra `B^I` is the integral closure of `A` in the
inertia fixed field `L^I`. -/
theorem inertiaFixedSubalgebra_isIntegralClosure
    : IsIntegralClosure B[I] A L[I] :=
  fixedSubalgebra_isIntegralClosure I

end

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "G" => Gal(L / K)
local notation "B" => integralClosure A L
local notation "B[" H "]" => FixedPoints.subalgebra A B H

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

local notation "I" => m.inertia G

-- Proof sketch: let `m' = B^I ∩ m`. Show that the extension of discrete valuation rings
-- `A → (B^I)_{m'}` is weakly unramified and has separable residue-field extension, then apply the
-- étale criterion of Lemma `10.143.7`.
/-- Lemma 15.113.8 (2): if `m' = B^I ∩ m`, then `A → (B^I)_{m'}` is étale, expressed as the
statement that `A → B^I` is étale at the prime `m'`. -/
theorem inertiaFixedSubalgebra_isEtaleAt_under
    : IsEtaleAt A (m.under B[I]) := sorry

end
