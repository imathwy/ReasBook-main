import Mathlib
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Spectrum.Prime.Basic
import StacksProject_2024.Chap15.Definition_15_37_3
import StacksProject_2024.Chap15.Definition_15_112_1
import StacksProject_2024.Chap15.Lemma_15_105_23
import StacksProject_2024.Chap15.Lemma_15_124_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x y z

open Ideal IsLocalRing
open scoped TensorProduct

/-
Domain-style sampling for Remark 15.115.1:
- primary domain: reduced tensor-product base change for extensions of discrete valuation rings,
  together with the integral-closure owners on the generic and special fibers;
- sampled owner declarations:
  `IsIntegralClosure.finite`,
  `integralClosure.isDedekindDomain`,
  `IsExtensionOfDiscreteValuationRings`,
  `integralClosure_valuationRing_of_purelyInseparable`;
- owner abstraction: the source-facing objects are the canonical integral closures
  `A₁ = integralClosure A K₁` and `B₁ = integralClosure B ((L ⊗[K] K₁)_red)`, together with the
  canonical comparison map `reducedTensorBaseChangeIntegralClosureMap : A₁ →ₐ[A] B₁`;
- primitive data: the discrete valuation rings `A ⊂ B`, their fraction fields `K ⊂ L`, and the
  field extension `K₁ / K`, with the `A₁`-algebra structure on `B₁` derived from the comparison
  map;
- derived API: the canonical `Spec(B₁) → Spec(A₁)` map in general, then Dedekind/noetherian
  consequences for `B₁`, finiteness in the finite-separable case, and the
  extension-of-discrete-valuation-rings structure in the finite purely inseparable case.
-/

section

variable {A : Type u} {K : Type v} {K1 : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]

local notation "A1" => integralClosure A K1

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section BaseChange

variable {B : Type x} {L : Type y}
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]

local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

local instance l1CommRing : CommRing L1 :=
  Ideal.Quotient.commRing _

/-- The canonical `A`-algebra map `K₁ → L₁` induced by the right tensor-factor embedding
`K₁ → L ⊗[K] K₁` and passage to the reduced quotient. -/
private abbrev rightTensorFactorToReducedTensorBaseChange : K1 →ₐ[A] L1 :=
  (Ideal.Quotient.mkₐ A _).comp
    ((Algebra.TensorProduct.includeRight : K1 →ₐ[K] L ⊗[K] K1).restrictScalars A)

/-- The canonical map `A₁ → L₁` induced by the right tensor-factor embedding
`K₁ → L ⊗[K] K₁` and passage to the reduced quotient. -/
private abbrev integralClosureToReducedTensorBaseChange : A1 →ₐ[A] L1 :=
  (integralClosure A L1).val.comp
    rightTensorFactorToReducedTensorBaseChange.mapIntegralClosure

/-- Elements of `A₁` map into the integral closure `B₁` inside the reduced base change `L₁`. -/
private theorem integralClosureToReducedTensorBaseChange_mem_integralClosure (x : A1) :
    integralClosureToReducedTensorBaseChange x ∈ B1 := sorry

/-- The canonical map `A₁ → B₁` induced by reduced tensor-product base change. -/
def reducedTensorBaseChangeIntegralClosureMap : A1 →ₐ[A] B1 :=
  AlgHom.codRestrict
    integralClosureToReducedTensorBaseChange
    ((integralClosure B L1).restrictScalars A)
    integralClosureToReducedTensorBaseChange_mem_integralClosure

/-- The reduced tensor-product integral closure carries its canonical `A₁`-algebra structure
through `reducedTensorBaseChangeIntegralClosureMap`. -/
instance : Algebra A1 B1 :=
  reducedTensorBaseChangeIntegralClosureMap.toRingHom.toAlgebra

/-- The canonical map from the tensor base change `A₁ ⊗[A] B` to the reduced tensor-product
integral closure `B₁`. -/
noncomputable def tensorBaseChangeToReducedTensorBaseChangeIntegralClosure :
    A1 ⊗[A] B →ₐ[A1] B1 :=
  ((IsScalarTower.toAlgHom A B B1).liftEquiv A A1 B B1)

/-- If `A → B` is formally smooth for the `maximalIdeal B`-adic topology, then the reduced
tensor-product integral closure `B₁` is canonically identified with the tensor base change
`A₁ ⊗[A] B`, equivalently with `B ⊗[A] A₁` via `Algebra.TensorProduct.comm`. -/
theorem tensorBaseChangeToReducedTensorBaseChangeIntegralClosure_bijective_of_formallySmoothForAdic
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)) :
    Function.Bijective
      (((IsScalarTower.toAlgHom A B B1).liftEquiv A A1 B B1).toFun) := by
  sorry

/-- Under the same formal-smoothness hypothesis, the canonical reduced tensor-product integral
closure `B₁` is canonically identified with the tensor base change `A₁ ⊗[A] B`. -/
noncomputable def tensorBaseChangeIntegralClosureEquivOfFormallySmoothForAdic
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)) :
    A1 ⊗[A] B ≃ₐ[A1] B1 :=
  AlgEquiv.ofBijective
    ((IsScalarTower.toAlgHom A B B1).liftEquiv A A1 B B1)
    (tensorBaseChangeToReducedTensorBaseChangeIntegralClosure_bijective_of_formallySmoothForAdic
      hfs)

-- Proof sketch: the reduced tensor product `L₁` is a finite product of finite extensions of
-- `K₁`; the integral closure of the Dedekind domain `A₁` in each factor is again Dedekind.
-- Their product is exactly `B₁`, so `B₁` is a Dedekind ring.
/-- Remark 15.115.1: if `K₁ / K` is finite, then the integral closure `B₁` of `B` in
`L₁ = (L ⊗[K] K₁)_red` is a Dedekind ring. -/
instance reducedTensorBaseChangeIntegralClosure_isDedekindRing [FiniteDimensional K K1] :
    IsDedekindRing B1 := sorry

-- Proof sketch: factor `A₁ → B₁` as the faithfully flat tensor-base-change map
-- `A₁ → A₁ ⊗[A] B` followed by the integral map `A₁ ⊗[A] B → B₁`. Surjectivity on spectra for the
-- first map comes from faithful flatness, and the second map has lying over by integrality.
/-- Remark 15.115.1: the canonical map `Spec(B₁) → Spec(A₁)` is surjective. -/
theorem primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A1 B1)) := by
  sorry

variable [FiniteDimensional K K1]

/-- Remark 15.115.1: if `K₁ / K` is finite, then the integral closure `A₁` of `A` in `K₁` is a
Dedekind domain. -/
instance : IsDedekindDomain A1 :=
  by
    sorry

instance integralClosure_localizationAtMaximal_isDiscreteValuationRing
    (p : Ideal A1) [p.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  sorry

instance reducedTensorBaseChangeIntegralClosure_localizationAtMaximal_isDomain
    (q : Ideal B1) [q.IsMaximal] :
    IsDomain (Localization.AtPrime q) := by
  sorry

instance reducedTensorBaseChangeIntegralClosure_localizationAtMaximal_isDiscreteValuationRing
    (q : Ideal B1) [q.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  sorry

-- Proof sketch: `A₁` is a Dedekind domain by the preceding instance, `B₁` is a Dedekind ring by
-- the previous theorem, and localizing at maximal ideals picks out discrete valuation factors. The
-- branch map induced by `A₁ → B₁` is therefore an injective local map between discrete valuation
-- rings, so it is canonically an extension of discrete valuation rings.
/-- For maximal ideals `p ⊂ A₁` and `q ⊂ B₁` with `q` lying over `p`, the induced localized map
`(A₁)_p → (B₁)_q` is an extension of discrete valuation rings. -/
instance isExtensionOfDiscreteValuationRings_localizationBranch
    (p : Ideal A1) [p.IsMaximal] (q : Ideal B1) [q.IsMaximal]
    [q.LiesOver p] :
    IsExtensionOfDiscreteValuationRings (Localization.AtPrime p) (Localization.AtPrime q) := by
  sorry

-- Proof sketch: the spectrum-surjectivity theorem gives at least one prime of `B₁` above each
-- maximal ideal `p ⊂ A₁`, and integrality makes that prime maximal. If `B` is henselian, then the
-- source-facing branch statement of Remark `15.115.1` says that there is only one such maximal
-- ideal, i.e. `B₁` has exactly one branch above each maximal ideal of `A₁`.
/-- Remark 15.115.1: if `K₁ / K` is finite and `B` is henselian, then for every maximal ideal
`p ⊂ A₁` there is a unique maximal ideal `q ⊂ B₁` lying over `p`. -/
theorem existsUnique_maximalIdeal_liesOver_of_reducedTensorBaseChangeIntegralClosure_of_henselian
    [HenselianLocalRing B] (p : Ideal A1) [p.IsMaximal] :
    ∃! q : Ideal B1, q.IsMaximal ∧ q.LiesOver p := by
  sorry

/- Remark 15.115.1: if `K₁ / K` is finite separable, then the integral closure `A₁` of `A` in
`K₁` is finite over `A`. This is the canonical theorem `IsIntegralClosure.finite`. -/
#check IsIntegralClosure.finite

-- Proof sketch: when `K₁ / K` is finite separable, the reduced tensor product `L₁` is a finite
-- product of finite separable extensions of `L`. The integral closure of the discrete valuation
-- ring `B` in each factor is finite over `B` by `IsIntegralClosure.finite`, so their product,
-- namely `B₁`, is finite over `B`.
/-- Remark 15.115.1: if `K₁ / K` is finite separable, then the integral closure `B₁` of `B` in
`L₁ = (L ⊗[K] K₁)_red` is finite over `B`. -/
theorem reducedTensorBaseChangeIntegralClosure_moduleFinite_of_finite_separable
    [Algebra.IsSeparable K K1] :
    Module.Finite B B1 := by
  sorry

end BaseChange

-- Proof sketch: the public `A₁` Dedekind-domain instance above gives the one-dimensional normal
-- owner. Reuse the chapter owner instance `integralClosure_henselianLocalRing` to put the finite
-- integral closure back in the henselian-local world; then a local Dedekind domain is a discrete
-- valuation ring.
/-- Over a henselian discrete valuation ring, the integral closure in a finite field extension is
again a discrete valuation ring. -/
theorem integralClosure_isDiscreteValuationRing_of_henselian
    [FiniteDimensional K K1] [HenselianLocalRing A] :
    IsDiscreteValuationRing A1 := by
  sorry

-- Proof sketch: a finite purely inseparable extension gives a unique prime above the maximal ideal
-- of `A`, so the finite integral closure `A1` is local. Combine this with the Dedekind-domain
-- property to conclude that `A1` is a discrete valuation ring.
/-- For a finite purely inseparable extension `K1 / K`, the integral closure of a discrete
valuation ring `A` in `K1` is again a discrete valuation ring. -/
theorem integralClosure_isDiscreteValuationRing_of_finite_purelyInseparable
    [FiniteDimensional K K1] [IsPurelyInseparable K K1] :
    IsDiscreteValuationRing A1 := by
  sorry

section BaseChange

variable {B : Type x} {L : Type y}
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [FiniteDimensional K K1] [IsPurelyInseparable K K1]

local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

-- Proof sketch: `A₁` is a discrete valuation ring by the preceding purely inseparable integral-
-- closure instance. In the purely inseparable base-change case the reduced tensor product `L₁`
-- stays local on the generic fiber, so `B₁` is again a discrete valuation ring; the canonical map
-- `A₁ → B₁` is then the injective local algebra map from Remark 15.115.1.
/-- Remark 15.115.1: if `K₁ / K` is finite purely inseparable, then `B₁` is a domain. -/
theorem reducedTensorBaseChangeIntegralClosure_isDomain_of_finite_purelyInseparable :
    IsDomain B1 := by
  sorry

local instance :
    IsDomain B1 :=
  reducedTensorBaseChangeIntegralClosure_isDomain_of_finite_purelyInseparable

/-- Remark 15.115.1: if `K₁ / K` is finite purely inseparable, then `B₁` is a discrete valuation
ring. -/
instance reducedTensorBaseChangeIntegralClosure_isDiscreteValuationRing_of_finite_purelyInseparable :
    IsDiscreteValuationRing B1 := by
  sorry

end BaseChange

end
