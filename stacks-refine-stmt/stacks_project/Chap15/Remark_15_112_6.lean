import Mathlib
import stacks_project.Chap10.Lemma_10_120_18
import stacks_project.Chap15.Lemma_15_105_23

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Ideal IsLocalRing
open scoped BigOperators

/-
Domain-style sampling for Remark 15.112.6:
- primary domain: ramification and inertia for finite separable extensions of fraction fields of
  discrete valuation rings, together with the henselian local integral-closure specialization;
- sampled owner declarations:
  `integralClosure.isFractionRing_of_finite_extension`,
  `IsIntegralClosure.finite`,
  `integralClosure_isDedekindDomain_of_ringKrullDim_eq_one`,
  `Ideal.sum_ramification_inertia`,
  `integralClosure_henselianLocalRing`,
  `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`;
- best owner abstraction: the core owner is the integral closure `integralClosure A L`;
- primitive data: the owner ring `B = integralClosure A L`; the fraction-field extension
  `L / FractionRing A` together with its separability is only primitive for the ramification
  identity, while the henselian uniqueness statement needs only the integral-closure-in-a-field
  owner and the henselian local source ring;
- derived API: the fraction-field structure on `B`, finiteness over `A` from
  `IsIntegralClosure.finite`, the ramification/inertia identity, and the henselian-locality of `B`
  used to identify the unique prime above `maximalIdeal A`.

Source/core/bridge triage:
 - `core/canonical`: `integralClosure A L` together with the sampled mathlib/project owner
  theorems above;
 - `source-facing`: the specialized degree formula and the henselian uniqueness result;
 - `bridge/view`: the specialization from the general ramification theorem to the DVR setting, and
  the use of the canonical henselian-local owner instance on `integralClosure A L`.
-/

section Ramification

variable {A : Type u} {L : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]

local notation "K" => FractionRing A
local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A

private theorem not_isField : ¬ IsField A := by
  intro hA
  exact IsDiscreteValuationRing.not_a_field A
    ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hA)

local instance : Module.Finite A B :=
  IsIntegralClosure.finite A K L B

local instance : IsFractionRing B L :=
  integralClosure.isFractionRing_of_finite_extension K L

local instance : IsDedekindDomain B :=
  integralClosure_isDedekindDomain_of_ringKrullDim_eq_one
    (IsPrincipalIdealRing.ringKrullDim_eq_one A not_isField)

-- Proof sketch: apply the fundamental identity `Ideal.sum_ramification_inertia` to the maximal
-- ideal of `A` and the integral closure `B` in `L`; the separable finite extension hypothesis
-- yields the finite integral-closure owner by `IsIntegralClosure.finite`.
/-- Remark 15.112.6: if `A` is a discrete valuation ring with fraction field `FractionRing A`,
`L / FractionRing A` is a finite separable extension, then for the integral closure
`B = integralClosure A L` the degree `[L : FractionRing A]` is the sum over the primes of `B`
above the maximal ideal of `A` of the products of ramification indices and residue degrees. -/
theorem integralClosure_finrank_eq_sum_ramificationIdx_mul_inertiaDeg :
    Module.finrank K L =
      ∑ Q ∈ primesOverFinset p B,
        Ideal.ramificationIdx p Q * Ideal.inertiaDeg p Q := by
  simpa using
    (Ideal.sum_ramification_inertia B K L (IsDiscreteValuationRing.not_a_field A)).symm

end Ramification

section Henselian

variable {A : Type u} {L : Type v}
variable [CommRing A] [Field L] [Algebra A L] [HenselianLocalRing A]

local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A

local instance : Algebra.IsIntegral A B :=
  IsIntegralClosure.isIntegral_algebra A L

local instance : HenselianLocalRing B :=
  integralClosure_henselianLocalRing

private instance liesOver_maximalIdeal_of_isMaximal (P : Ideal B) [P.IsMaximal] :
    P.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)).symm⟩

-- Proof sketch: the canonical owner instance puts the integral closure `B` of a henselian local
-- ring in a field back in the henselian-local world. Any prime of `B` above `maximalIdeal A` is
-- maximal by integrality, hence equals the unique maximal ideal of the local ring `B`.
/-- If `A` is henselian local, then exactly one prime of the integral closure lies above the
maximal ideal of `A`. -/
theorem integralClosure_primesOver_maximalIdeal_eq_singleton_of_henselianLocalRing
    : primesOver p B = {maximalIdeal B} := by
  ext P
  constructor
  · intro hP
    let _ : P.IsPrime := hP.1
    let _ : P.LiesOver p := hP.2
    exact Set.mem_singleton_iff.mpr <| IsLocalRing.eq_maximalIdeal <|
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P <| by
        simpa [P.over_def p] using (maximalIdeal.isMaximal A : IsMaximal p)
  · rintro rfl
    exact ⟨inferInstance, inferInstance⟩

end Henselian
