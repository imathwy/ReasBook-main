import Mathlib
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import StacksProject_2024.Chap10.Lemma_10_120_18
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Spectrum.Prime.Basic
import StacksProject_2024.Chap10.Definition_10_32_1
import StacksProject_2024.Chap10.Lemma_10_50_18
import StacksProject_2024.Chap15.Definition_15_37_3
import StacksProject_2024.Chap15.Definition_15_112_1
import StacksProject_2024.Chap15.Lemma_15_105_23
import StacksProject_2024.Chap15.Lemma_15_124_3
import StacksProject_2024.Chap15.Remark_15_115_1_core

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x y z

open Ideal IsLocalRing
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

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

/-- Helper for Remark 15.115.1: for a finite extension of the fraction field of a discrete
valuation ring, the integral closure is not a field. -/
private theorem integralClosure_not_isField_of_fractionField_extension
    [FiniteDimensional K K1] :
    ¬ IsField A1 := by
  -- If the integral closure were a field, integrality and injectivity would force `A` to be a field.
  let _ : Algebra.IsIntegral A A1 := IsIntegralClosure.isIntegral_algebra A K1
  have hinj : Function.Injective (algebraMap A A1) := by
    exact algebraMap_injective_of_field_isFractionRing
      (R := A) (S := A1) (K := K) (L := K1)
  intro hA1
  exact IsDiscreteValuationRing.not_isField A <|
    isField_of_isIntegral_of_isField hinj hA1

omit [IsDiscreteValuationRing A] in
/-- Helper for Remark 15.115.1: finite-dimensionality over the chosen fraction field `K`
transports to finite generation over the canonical fraction ring `FractionRing A`. -/
private theorem fractionRing_transport_moduleFinite
    [FaithfulSMul A K1] [Algebra (FractionRing A) K1] [IsScalarTower A (FractionRing A) K1]
    [FiniteDimensional K K1] :
    Module.Finite (FractionRing A) K1 := by
  -- Compare the chosen fraction field `K` with the canonical one by the standard equivalence.
  let e₁ : K ≃+* FractionRing A := (FractionRing.algEquiv A K).symm.toRingEquiv
  let e₂ : K1 ≃+* K1 := RingEquiv.refl _
  letI : Module.Finite K K1 := inferInstance
  let f : K1 ≃ₐ[A] K1 := AlgEquiv.refl
  have he : RingHom.comp (algebraMap (FractionRing A) K1) ↑e₁ =
      RingHom.comp ↑e₂ (algebraMap K K1) := by
    -- The two scalar actions agree because `FractionRing.algEquiv` commutes with the top field.
    ext x
    simpa [e₁, e₂] using
      IsFractionRing.algEquiv_commutes ((FractionRing.algEquiv A K).symm) f x
  -- Transport module finiteness across the base and target ring equivalences.
  exact Module.Finite.of_equiv_equiv e₁ e₂ he

/-- Helper for Remark 15.115.1: after transporting the fraction-field action to
`FractionRing A`, the integral closure `A₁` is a Dedekind domain. -/
private theorem integralClosure_isDedekindDomain_of_fractionField_extension
    [FiniteDimensional K K1] :
    IsDedekindDomain A1 := by
  -- Put `K₁` over the canonical `FractionRing A` and transport finite generation along that lift.
  let _ : FaithfulSMul A K1 := FaithfulSMul.of_field_isFractionRing A K1 K K1
  let _ : Algebra (FractionRing A) K1 := FractionRing.liftAlgebra A K1
  let _ : IsScalarTower A (FractionRing A) K1 := FractionRing.isScalarTower_liftAlgebra A K1
  let _ : Module.Finite (FractionRing A) K1 :=
    fractionRing_transport_moduleFinite (A := A) (K := K) (K1 := K1)
  let _ : IsFractionRing A1 K1 := integralClosure.isFractionRing_of_finite_extension K K1
  -- Now the owner theorem from Algebra, Lemma 10.120.18 applies directly.
  exact integralClosure_isDedekindDomain_of_ringKrullDim_eq_one
    (A := A) (L := K1)
    (hdim := IsPrincipalIdealRing.ringKrullDim_eq_one A (IsDiscreteValuationRing.not_isField A))

/-- Helper for Remark 15.115.1: every maximal localization of the finite integral closure `A₁`
is a discrete valuation ring. -/
private theorem integralClosure_localizationAtMaximal_isDiscreteValuationRing_of_fractionField_extension
    [FiniteDimensional K K1] (p : Ideal A1) [p.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  -- First recover the Dedekind-domain owner for `A₁` from the transported fraction-field data.
  let _ : IsDedekindDomain A1 :=
    integralClosure_isDedekindDomain_of_fractionField_extension (A := A) (K := K) (K1 := K1)
  have hcomap : Ideal.comap (algebraMap A A1) p = maximalIdeal A := by
    -- Integrality forces the contraction of a maximal ideal of `A₁` to the maximal ideal of `A`.
    let _ : Algebra.IsIntegral A A1 := IsIntegralClosure.isIntegral_algebra A K1
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p)
  have hp : p ≠ ⊥ := by
    -- If `p = ⊥`, then its contraction would make `A` a field, contradicting the DVR hypothesis.
    intro hbot
    have : maximalIdeal A = ⊥ := by
      calc
        maximalIdeal A = Ideal.comap (algebraMap A A1) p := hcomap.symm
        _ = ⊥ := by
          ext x
          rw [hbot]
          constructor
          · intro hx
            have hx0 : algebraMap A A1 x = algebraMap A A1 0 := by
              simpa using (show algebraMap A A1 x = 0 from hx)
            exact (algebraMap_injective_of_field_isFractionRing A A1 K K1) hx0
          · intro hx
            rw [Ideal.mem_bot] at hx ⊢
            simpa [hx]
    exact IsDiscreteValuationRing.not_a_field A this
  -- Localizing a Dedekind domain at a nonzero prime yields a discrete valuation ring.
  simpa using
    (IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A1 hp
      (Localization.AtPrime p))

/-- Helper for Remark 15.115.1: a faithful action of the chosen fraction field extension target
forces the algebra map from the base ring to be injective. -/
private theorem algebraMap_eq_zero_of_faithful_fractionField_target
    {E : Type w} [Field E] [Algebra A E] [Algebra K E] [IsScalarTower A K E]
    [FaithfulSMul A E] {x : A} (hx : algebraMap A E x = 0) :
    x = 0 := by
  -- Compare `x` with `0` after mapping into the faithful ambient field.
  have hmap : algebraMap A E x = algebraMap A E 0 := by
    simpa using hx
  exact (FaithfulSMul.algebraMap_injective A E) hmap

/-- Helper for Remark 15.115.1: the integral closure in an algebraic extension of the chosen
fraction field still has that field as its fraction field. -/
private theorem integralClosure_isFractionRing_of_algebraic_fractionField_extension
    {E : Type w} [Field E] [Algebra A E] [Algebra K E] [IsScalarTower A K E]
    [Algebra.IsAlgebraic K E] :
    IsFractionRing (integralClosure A E) E := by
  let _ : FaithfulSMul A E := FaithfulSMul.of_field_isFractionRing A E K E
  let _ : Algebra.IsAlgebraic A E :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance : Algebra.IsAlgebraic K E)
  -- The standard integral-closure fraction-field theorem applies once injectivity is recovered
  -- from the faithful action of `A` on the ambient field.
  exact integralClosure.isFractionRing_of_algebraic
    (fun x hx ↦
      algebraMap_eq_zero_of_faithful_fractionField_target
        (A := A) (K := K) (E := E) hx)

/-- Helper for Remark 15.115.1: an element integral over the base ring is literally represented by
an element of the integral closure subtype. -/
private theorem isInteger_integralClosure_of_isIntegral
    {E : Type w} [Field E] [Algebra A E] {x : E} (hx : IsIntegral A x) :
    IsLocalization.IsInteger (integralClosure A E) x := by
  -- Package the integral element as a point of the subtype defining the integral closure.
  change x ∈ (algebraMap (integralClosure A E) E).rangeS
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Helper for Remark 15.115.1: in a purely inseparable extension of the chosen fraction field,
every element or its inverse is integral over the valuation ring. -/
private theorem integral_or_integral_inv_of_fractionField_purelyInseparable
    {E : Type w} [Field E] [Algebra A E] [Algebra K E] [IsScalarTower A K E]
    [ValuationRing A] [IsPurelyInseparable K E] (x : E) :
    IsIntegral A x ∨ IsIntegral A x⁻¹ := by
  let q := ringExpChar K
  haveI : ExpChar K q := ringExpChar.expChar K
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem (F := K) (E := E) q x
  have hqpos : 0 < q ^ n := expChar_pow_pos K q n
  obtain hyA | hyA := ValuationRing.isInteger_or_isInteger A y
  · left
    -- If the reduct lies in `A`, then the displayed power of `x` is integral over `A`.
    have hyIntegral : IsIntegral A (algebraMap K E y) := by
      rcases hyA with ⟨a, ha⟩
      have hmap : algebraMap K E y = algebraMap A E a := by
        rw [← ha]
        simp [IsScalarTower.algebraMap_eq A K E]
      rw [hmap]
      exact isIntegral_algebraMap
    have hpowIntegral : IsIntegral A (x ^ q ^ n) := by
      simpa [hy] using hyIntegral
    exact IsIntegral.of_pow hqpos hpowIntegral
  · right
    -- The same argument for inverses yields integrality of `x⁻¹`.
    have hyIntegral : IsIntegral A (algebraMap K E y⁻¹) := by
      rcases hyA with ⟨a, ha⟩
      have hmap : algebraMap K E y⁻¹ = algebraMap A E a := by
        rw [← ha]
        simp [IsScalarTower.algebraMap_eq A K E]
      rw [hmap]
      exact isIntegral_algebraMap
    have hyInvIntegral : IsIntegral A ((algebraMap K E y)⁻¹) := by
      simpa [map_inv] using hyIntegral
    have hpowIntegral : IsIntegral A ((x⁻¹) ^ q ^ n) := by
      simpa [hy, inv_pow] using hyInvIntegral
    exact IsIntegral.of_pow hqpos hpowIntegral

/-- Helper for Remark 15.115.1: with respect to the chosen fraction field witness, the integral
closure in a purely inseparable extension is again a valuation ring. -/
private theorem integralClosure_valuationRing_of_fractionField_purelyInseparable
    {E : Type w} [Field E] [Algebra A E] [Algebra K E] [IsScalarTower A K E]
    [ValuationRing A] [IsPurelyInseparable K E] :
    ValuationRing (integralClosure A E) := by
  let _ : Algebra.IsAlgebraic K E := IsPurelyInseparable.isAlgebraic K E
  let _ : IsFractionRing (integralClosure A E) E :=
    integralClosure_isFractionRing_of_algebraic_fractionField_extension
      (A := A) (K := K) (E := E)
  -- Reduce the valuation-ring criterion on the normalization to integrality over `A`.
  rw [ValuationRing.iff_isInteger_or_isInteger (integralClosure A E) E]
  intro x
  obtain hx | hx :=
    integral_or_integral_inv_of_fractionField_purelyInseparable
      (A := A) (K := K) (E := E) x
  · left
    exact isInteger_integralClosure_of_isIntegral (A := A) (E := E) hx
  · right
    exact isInteger_integralClosure_of_isIntegral (A := A) (E := E) hx

section BaseChange

variable {B : Type x} {L : Type y}
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]

local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

local instance l1CommRingBaseChange : CommRing L1 :=
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
    integralClosureToReducedTensorBaseChange x ∈ B1 := by
  -- Package the image in `integralClosure A L₁` first so the scalar tower is fully determined.
  let y : integralClosure A L1 := rightTensorFactorToReducedTensorBaseChange.mapIntegralClosure x
  have hyA : IsIntegral A (y : L1) := y.2
  have hyB : IsIntegral B (y : L1) := IsIntegral.tower_top hyA
  -- Unfolding the canonical map identifies the goal with the same underlying element of `L₁`.
  simpa [integralClosureToReducedTensorBaseChange, y] using hyB

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
  -- TODO: identify the registered formally smooth comparison theorem returning bijectivity for
  -- this exact `liftEquiv` model, then close by `simpa`.
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
    IsDedekindRing B1 := by
  -- TODO: reintroduce the branchwise product decomposition of `B₁` and transport the factorwise
  -- Dedekind-domain owners across that equivalence.
  sorry

-- Proof sketch: factor `A₁ → B₁` as the faithfully flat tensor-base-change map
-- `A₁ → A₁ ⊗[A] B` followed by the integral map `A₁ ⊗[A] B → B₁`. Surjectivity on spectra for the
-- first map comes from faithful flatness, and the second map has lying over by integrality.
/-- Helper for Remark 15.115.1: an extension of discrete valuation rings is faithfully flat over
the source. -/
private theorem extensionOfDiscreteValuationRings_faithfullyFlat :
    (algebraMap A B).FaithfullyFlat := by
  -- First convert injectivity of the local DVR map into torsion-freeness of the target module.
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  let hAB : IsExtensionOfDiscreteValuationRings A B := inferInstance
  let _ : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr hAB.algebraMap_injective
  let _ : Module.IsTorsionFree A B := Module.IsTorsionFree.trans_faithfulSMul A B B
  have htor : Submodule.torsion A B = ⊥ :=
    (Submodule.isTorsionFree_iff_torsion_eq_bot).mp inferInstance
  -- Over a valuation ring, torsion-free modules are flat, so the local map is faithfully flat.
  let _ : Module.Flat A B :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout (R := A) (M := B)).2 htor
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Helper for Remark 15.115.1: the tensor-base-change map
`Spec(A₁ ⊗[A] B) → Spec(A₁)` is surjective by faithful-flat base change. -/
private theorem tensorBaseChange_primeSpectrumComap_surjective :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A1 (A1 ⊗[A] B))) := by
  -- Base change the faithfully flat DVR extension `A → B` along `A → A₁`.
  let hff : (algebraMap A B).FaithfullyFlat :=
    extensionOfDiscreteValuationRings_faithfullyFlat (A := A) (B := B)
  let _ : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  let _ : Module.FaithfullyFlat A1 (A1 ⊗[A] B) :=
    Module.FaithfullyFlat.instTensorProduct A B A1
  simpa using
    (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A1) (B := A1 ⊗[A] B))

/-- Helper for Remark 15.115.1: the tensor comparison map agrees with the canonical `B`-algebra
structure on `B₁` when restricted to the right tensor factor. -/
private theorem tensorBaseChangeToReducedTensorBaseChangeIntegralClosure_commutes_base
    (b : B) :
    tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
        (A := A) (K := K) (K1 := K1) (B := B) (L := L)
        (Algebra.TensorProduct.includeRight b) =
      algebraMap B B1 b := by
  -- The `liftEquiv` tensor comparison is characterized by its values on the two tensor
  -- generators, and on the right generator it is exactly the ambient `B`-algebra map.
  simpa [tensorBaseChangeToReducedTensorBaseChangeIntegralClosure,
    Algebra.TensorProduct.includeRight_apply]

/-- Helper for Remark 15.115.1: the tensor source `A₁ ⊗[A] B` maps to `B₁` through the canonical
`B`-algebra structure on the right tensor factor. -/
private theorem tensorBaseChange_target_isScalarTower_over_B :
    IsScalarTower B (A1 ⊗[A] B) B1 := by
  -- Compare the two maps `B → B₁` on a base element using the tensor comparison's right factor.
  refine IsScalarTower.of_algebraMap_eq fun b ↦ ?_
  simpa [RingHom.algebraMap_toAlgebra] using
    tensorBaseChangeToReducedTensorBaseChangeIntegralClosure_commutes_base
      (A := A) (K := K) (K1 := K1) (B := B) (L := L) b

/-- Helper for Remark 15.115.1: an element of `B₁` integral over `B` is also integral over the
tensor source `A₁ ⊗[A] B`. -/
private theorem tensor_base_change_integral_of_base_integral
    (z : B1) (hz : IsIntegral B z) :
    IsIntegral (A1 ⊗[A] B) z := by
  let _ : IsScalarTower B (A1 ⊗[A] B) B1 :=
    tensorBaseChange_target_isScalarTower_over_B
      (A := A) (K := K) (K1 := K1) (B := B) (L := L)
  -- The monic equation over `B` can be read over the tensor source through the scalar tower.
  exact IsIntegral.tower_top hz

/-- Helper for Remark 15.115.1: the tensor comparison map `A₁ ⊗[A] B → B₁` is integral. -/
private theorem tensorBaseChangeToReducedTensorBaseChangeIntegralClosure_isIntegral :
    (tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
      (A := A) (K := K) (K1 := K1) (B := B) (L := L)).toRingHom.IsIntegral := by
  -- Every element of `B₁` is integral over `B` by definition of the integral closure.
  intro z
  change IsIntegral (A1 ⊗[A] B) z
  exact tensor_base_change_integral_of_base_integral
    (A := A) (K := K) (K1 := K1) (B := B) (L := L) z z.2

/-- Helper for Remark 15.115.1: after quotienting by the kernel of the tensor comparison map, the
resulting injective map into `B₁` is still integral. -/
private theorem tensorBaseChangeComparison_quotientLift_isIntegral :
    (((Ideal.kerLiftAlg
      (tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
        (A := A) (K := K) (K1 := K1) (B := B) (L := L))) :
      (A1 ⊗[A] B) ⧸
          RingHom.ker
            (tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
              (A := A) (K := K) (K1 := K1) (B := B) (L := L)).toRingHom →ₐ[A1] B1).toRingHom).IsIntegral := by
  -- TODO: once the preceding integrality theorem is restored, map integral equations along the
  -- quotient map `A₁ ⊗[A] B → (A₁ ⊗[A] B) / ker(F)` to obtain integrality of `Ideal.kerLiftAlg F`.
  sorry

/-- Helper for Remark 15.115.1: the left tensor factor `B` maps to the unreduced generic fiber
through `B → L → L ⊗[K] K₁`. -/
private abbrev leftTensorFactorToGenericFiber : B →ₐ[A] L ⊗[K] K1 :=
  ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K1).restrictScalars A).comp
    (IsScalarTower.toAlgHom A B L)

/-- Helper for Remark 15.115.1: the canonical `A₁`-algebra map to the unreduced generic fiber is
obtained from the right tensor-factor inclusion `K₁ → L ⊗[K] K₁`. -/
private abbrev integralClosureToGenericFiber : A1 →ₐ[A] L ⊗[K] K1 :=
  ((Algebra.TensorProduct.includeRight : K1 →ₐ[K] L ⊗[K] K1).restrictScalars A).comp
    (integralClosure A K1).val

/-- Helper for Remark 15.115.1: the tensor base change maps directly to the unreduced generic
fiber by sending the left factor to `K₁` and the right factor to `L`. -/
private noncomputable def tensorBaseChangeToGenericFiber :
    A1 ⊗[A] B →ₐ[A] L ⊗[K] K1 := by
  -- The universal tensor-property map records the source proof's generic-fiber comparison.
  exact
    Algebra.TensorProduct.lift integralClosureToGenericFiber
      leftTensorFactorToGenericFiber
      (fun _ _ ↦ Commute.all _ _)

/-- Helper for Remark 15.115.1: the integral closure `A₁` is flat over the base discrete
valuation ring `A` because it is torsion-free over a Bezout domain. -/
private theorem integralClosure_flat_over_base :
    Module.Flat A A1 := by
  -- The subtype embedding `A₁ ↪ K₁` turns equality in `A₁` into equality in the fraction field.
  let _ : FaithfulSMul A K1 := FaithfulSMul.of_field_isFractionRing A K1 K K1
  have hinj : Function.Injective (algebraMap A A1) := by
    intro x y hxy
    apply (FaithfulSMul.algebraMap_injective A K1)
    exact congrArg (fun z : A1 => (z : K1)) hxy
  let _ : FaithfulSMul A A1 :=
    (faithfulSMul_iff_algebraMap_injective A A1).mpr hinj
  let _ : Module.IsTorsionFree A A1 :=
    Module.IsTorsionFree.trans_faithfulSMul A A1 A1
  have htor : Submodule.torsion A A1 = ⊥ :=
    (Submodule.isTorsionFree_iff_torsion_eq_bot).mp inferInstance
  -- Over the DVR `A`, torsion-free modules are flat.
  exact (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout (R := A) (M := A1)).2 htor

/-- Helper for Remark 15.115.1: the extension ring `B` is flat over the base discrete valuation
ring `A` because the extension map is injective and both rings are DVRs. -/
private theorem extensionOfDiscreteValuationRings_flat :
    Module.Flat A B := by
  -- The DVR-extension owner gives faithful scalar action, hence torsion-freeness.
  let _ : Module.IsTorsionFree A B := Module.IsTorsionFree.trans_faithfulSMul A B B
  have htor : Submodule.torsion A B = ⊥ :=
    (Submodule.isTorsionFree_iff_torsion_eq_bot).mp inferInstance
  -- Over the DVR `A`, torsion-free modules are flat.
  exact (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout (R := A) (M := B)).2 htor

/-- Helper for Remark 15.115.1: base changing `B → L` along `A₁` gives the intermediate map
`A₁ ⊗[A] B → A₁ ⊗[A] L`. -/
private noncomputable def tensorBaseChangeToFieldBaseChange :
    A1 ⊗[A] B →ₐ[A] A1 ⊗[A] L :=
  Algebra.TensorProduct.map (AlgHom.id A A1) (IsScalarTower.toAlgHom A B L)

/-- Helper for Remark 15.115.1: the intermediate field-base-change map is injective by flat base
change of the injective fraction-field map `B → L`. -/
private theorem tensorBaseChangeToFieldBaseChange_injective :
    Function.Injective
      (tensorBaseChangeToFieldBaseChange :
        A1 ⊗[A] B →ₐ[A] A1 ⊗[A] L) := by
  let _ : Module.Flat A A1 := integralClosure_flat_over_base (A := A) (K := K) (K1 := K1)
  let _ : Module.Flat A B := extensionOfDiscreteValuationRings_flat (A := A) (B := B)
  -- Tensor the injective map `B → L` over the two flat `A`-modules `A₁` and `B`.
  have hmap :=
    TensorProduct.map_injective_of_flat_flat
      (LinearMap.id : A1 →ₗ[A] A1)
      (IsScalarTower.toAlgHom A B L).toLinearMap
      (fun _ _ h ↦ h)
      (IsFractionRing.injective B L)
  simpa [tensorBaseChangeToFieldBaseChange] using hmap

/-- Helper for Remark 15.115.1: after replacing `B` by the fraction field `L`, the unreduced
generic-fiber map is induced from the two tensor-factor embeddings. -/
private noncomputable def fieldBaseChangeToGenericFiber :
    A1 ⊗[A] L →ₐ[A] L ⊗[K] K1 := by
  -- This is the same tensor-universal construction as `tensorBaseChangeToGenericFiber`, with
  -- the right factor already replaced by the field `L`.
  exact
    Algebra.TensorProduct.lift integralClosureToGenericFiber
      ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K1).restrictScalars A)
      (fun _ _ ↦ Commute.all _ _)

/-- Helper for Remark 15.115.1: the fraction field `L` is flat over the base discrete valuation
ring `A`, so tensoring an injective `A`-linear map with `L` stays injective. -/
private theorem fractionField_flat_over_base :
    Module.Flat A L := by
  -- Injectivity of `A → L` gives faithful scalar action, hence torsion-freeness.
  let _ : FaithfulSMul A L := FaithfulSMul.of_field_isFractionRing A L K L
  let _ : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A L L
  have htor : Submodule.torsion A L = ⊥ :=
    (Submodule.isTorsionFree_iff_torsion_eq_bot).mp inferInstance
  -- Over the DVR `A`, torsion-free modules are flat.
  exact (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout (R := A) (M := L)).2 htor

/-- Helper for Remark 15.115.1: after identifying `L ⊗[K] K₁` with the localization base change
`L ⊗[A] K₁`, the field-level generic-fiber map is the standard tensor map obtained from
`A₁ ↪ K₁`. -/
private theorem fieldBaseChangeToGenericFiber_comp_eq_comm_map_algebraTensorEquiv :
    let e : L ⊗[K] K1 →ₐ[A] L ⊗[A] K1 :=
      (AlgEquiv.restrictScalars A
        (IsLocalization.algebraTensorEquiv (S := nonZeroDivisors A) (A := K) L K1)).toAlgHom
    e.toRingHom.comp
        (fieldBaseChangeToGenericFiber
          (A := A) (K := K) (K1 := K1) (L := L)).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id A L) (integralClosure A K1).val).toRingHom.comp
        (Algebra.TensorProduct.commRight A A1 L).toAlgHom.toRingHom := by
  -- Compare the two transported maps on the tensor generators of `A₁ ⊗[A] L`.
  ext x y
  · -- On the `A₁`-generator, both maps are induced by `integralClosure A K₁ ↪ K₁`.
    simp [fieldBaseChangeToGenericFiber, integralClosureToGenericFiber]
  · -- On the `L`-generator, both maps are induced by the left tensor-factor embedding of `L`.
    simp [fieldBaseChangeToGenericFiber]

/-- Helper for Remark 15.115.1: the field-level generic-fiber comparison is injective. -/
private theorem fieldBaseChangeToGenericFiber_injective :
    Function.Injective
      (fieldBaseChangeToGenericFiber
        (A := A) (K := K) (K1 := K1) (L := L)) := by
  let e : L ⊗[K] K1 →ₐ[A] L ⊗[A] K1 :=
    (AlgEquiv.restrictScalars A
      (IsLocalization.algebraTensorEquiv (S := nonZeroDivisors A) (A := K) L K1)).toAlgHom
  have hmap :
      Function.Injective
        ((Algebra.TensorProduct.map (AlgHom.id A L) (integralClosure A K1).val) :
          L ⊗[A] A1 →ₐ[A] L ⊗[A] K1) := by
    let _ : Module.Flat A L :=
      fractionField_flat_over_base (A := A) (K := K) (L := L)
    let _ : Module.Flat A A1 :=
      integralClosure_flat_over_base (A := A) (K := K) (K1 := K1)
    -- Tensor injectivity across two flat `A`-modules with the injective map `A₁ ↪ K₁`.
    simpa using
      (TensorProduct.map_injective_of_flat_flat
        (LinearMap.id : L →ₗ[A] L)
        (integralClosure A K1).val.toLinearMap
        (fun _ _ h ↦ h)
        Subtype.val_injective)
  intro x y hxy
  have htransport :
      ((Algebra.TensorProduct.map (AlgHom.id A L) (integralClosure A K1).val).toRingHom.comp
          (Algebra.TensorProduct.commRight A A1 L).toAlgHom.toRingHom) x =
        ((Algebra.TensorProduct.map (AlgHom.id A L) (integralClosure A K1).val).toRingHom.comp
          (Algebra.TensorProduct.commRight A A1 L).toAlgHom.toRingHom) y := by
    have hx :=
      DFunLike.congr_fun
        (fieldBaseChangeToGenericFiber_comp_eq_comm_map_algebraTensorEquiv
          (A := A) (K := K) (K1 := K1) (L := L)) x
    have hy :=
      DFunLike.congr_fun
        (fieldBaseChangeToGenericFiber_comp_eq_comm_map_algebraTensorEquiv
          (A := A) (K := K) (K1 := K1) (L := L)) y
    calc
      ((Algebra.TensorProduct.map (AlgHom.id A L) (integralClosure A K1).val).toRingHom.comp
          (Algebra.TensorProduct.commRight A A1 L).toAlgHom.toRingHom) x =
          e (fieldBaseChangeToGenericFiber
            (A := A) (K := K) (K1 := K1) (L := L) x) := hx.symm
      _ = e (fieldBaseChangeToGenericFiber
            (A := A) (K := K) (K1 := K1) (L := L) y) := by simpa using congrArg e hxy
      _ =
          ((Algebra.TensorProduct.map (AlgHom.id A L) (integralClosure A K1).val).toRingHom.comp
            (Algebra.TensorProduct.commRight A A1 L).toAlgHom.toRingHom) y := hy
  apply (Algebra.TensorProduct.commRight A A1 L).injective
  exact hmap htransport

/-- Helper for Remark 15.115.1: the generic-fiber comparison first base changes `B → L` along
`A₁`, then applies the field-level comparison map `A₁ ⊗[A] L → L ⊗[K] K₁`. -/
private theorem tensorBaseChangeToGenericFiber_factor_through_fieldBaseChange :
    tensorBaseChangeToGenericFiber.toRingHom =
      (fieldBaseChangeToGenericFiber
        (A := A) (K := K) (K1 := K1) (L := L)).toRingHom.comp
        tensorBaseChangeToFieldBaseChange.toRingHom := by
  -- Compare the two maps on the left and right tensor generators.
  ext x y
  · -- On the `A₁`-generator, the intermediate base change acts trivially.
    simp [tensorBaseChangeToGenericFiber, fieldBaseChangeToGenericFiber,
      tensorBaseChangeToFieldBaseChange, integralClosureToGenericFiber]
  · -- On the `B`-generator, both routes are the composite `B → L → L ⊗[K] K₁`.
    simp [tensorBaseChangeToGenericFiber, fieldBaseChangeToGenericFiber,
      tensorBaseChangeToFieldBaseChange, leftTensorFactorToGenericFiber]

/-- Helper for Remark 15.115.1: the generic-fiber tensor map from `A₁ ⊗[A] B` is injective. -/
private theorem tensorBaseChangeToGenericFiber_injective :
    Function.Injective
      (tensorBaseChangeToGenericFiber
        (A := A) (K := K) (K1 := K1) (B := B) (L := L)) := by
  have hfield :
      Function.Injective
        (fieldBaseChangeToGenericFiber
          (A := A) (K := K) (K1 := K1) (L := L)) :=
    fieldBaseChangeToGenericFiber_injective
  have htensor :
      Function.Injective
        (tensorBaseChangeToFieldBaseChange :
          A1 ⊗[A] B →ₐ[A] A1 ⊗[A] L) :=
    tensorBaseChangeToFieldBaseChange_injective
  intro x y hxy
  apply htensor
  apply hfield
  rw [tensorBaseChangeToGenericFiber_factor_through_fieldBaseChange
      (A := A) (K := K) (K1 := K1) (B := B) (L := L)]
  simpa using hxy

/-- Helper for Remark 15.115.1: the left tensor factor `B` maps to the reduced generic fiber by
first entering `L ⊗[K] K₁` and then quotienting by its nilradical. -/
private abbrev leftTensorFactorToReducedTensorBaseChange : B →ₐ[A] L1 :=
  (Ideal.Quotient.mkₐ A _).comp leftTensorFactorToGenericFiber

/-- Helper for Remark 15.115.1: this is the direct tensor map from `A₁ ⊗[A] B` to the reduced
generic fiber `L₁`, before passing through the integral closure `B₁`. -/
private noncomputable def tensorBaseChangeToReducedTensorBaseChange :
    A1 ⊗[A] B →ₐ[A] L1 := by
  -- This is the same tensor universal property as above, but after the reduced quotient.
  exact
    Algebra.TensorProduct.lift integralClosureToReducedTensorBaseChange
      leftTensorFactorToReducedTensorBaseChange
      (fun _ _ ↦ Commute.all _ _)

/-- Helper for Remark 15.115.1: after composing into `L₁`, the tensor comparison map agrees with
the direct reduced generic-fiber tensor map. -/
private theorem tensorBaseChangeComparison_subtype_comp_eq_reducedTensorBaseChange :
    ((integralClosure B L1).val).toRingHom.comp
        (tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
          (A := A) (K := K) (K1 := K1) (B := B) (L := L)).toRingHom =
      tensorBaseChangeToReducedTensorBaseChange.toRingHom := by
  -- Compare the two tensor maps on the left and right generators of `A₁ ⊗[A] B`.
  ext x y
  · -- On the `A₁`-generator, both maps are the canonical map `A₁ → L₁`.
    simp [tensorBaseChangeToReducedTensorBaseChangeIntegralClosure,
      tensorBaseChangeToReducedTensorBaseChange, reducedTensorBaseChangeIntegralClosureMap,
      integralClosureToReducedTensorBaseChange]
  · -- On the `B`-generator, both maps are the canonical map `B → L₁`.
    simp [tensorBaseChangeToReducedTensorBaseChangeIntegralClosure,
      tensorBaseChangeToReducedTensorBaseChange, reducedTensorBaseChangeIntegralClosureMap,
      leftTensorFactorToReducedTensorBaseChange]

/-- Helper for Remark 15.115.1: quotienting the generic-fiber tensor map by the nilradical gives
the direct tensor map to the reduced generic fiber. -/
private theorem reducedTensorBaseChange_quotient_comp_genericFiber :
    let G : A1 ⊗[A] B →ₐ[A] L ⊗[K] K1 := tensorBaseChangeToGenericFiber
    (Ideal.Quotient.mk (nilradical (L ⊗[K] K1))).comp G.toRingHom =
      tensorBaseChangeToReducedTensorBaseChange.toRingHom := by
  -- Compare the two tensor maps on the left and right generators after quotienting by the
  -- nilradical.
  ext x y
  · -- On the `A₁`-generator, both routes are induced by the right tensor-factor inclusion.
    simp [tensorBaseChangeToGenericFiber, tensorBaseChangeToReducedTensorBaseChange,
      integralClosureToGenericFiber, integralClosureToReducedTensorBaseChange]
  · -- On the `B`-generator, both routes are induced by the left tensor-factor inclusion.
    simp [tensorBaseChangeToGenericFiber, tensorBaseChangeToReducedTensorBaseChange,
      leftTensorFactorToGenericFiber, leftTensorFactorToReducedTensorBaseChange]

/-- Helper for Remark 15.115.1: composing the tensor comparison with the subtype
`B₁ → L₁` matches the quotient of the generic-fiber tensor map. -/
private theorem tensorBaseChangeComparison_subtype_comp_eq_reducedGenericFiberQuotient :
    ((integralClosure B L1).val).toRingHom.comp
        (tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
          (A := A) (K := K) (K1 := K1) (B := B) (L := L)).toRingHom =
      (Ideal.Quotient.mk (nilradical (L ⊗[K] K1))).comp tensorBaseChangeToGenericFiber.toRingHom := by
  -- Identify both sides with the direct tensor map into the reduced generic fiber.
  calc
    ((integralClosure B L1).val).toRingHom.comp
        (tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
          (A := A) (K := K) (K1 := K1) (B := B) (L := L)).toRingHom =
      tensorBaseChangeToReducedTensorBaseChange.toRingHom :=
        tensorBaseChangeComparison_subtype_comp_eq_reducedTensorBaseChange
          (A := A) (K := K) (K1 := K1) (B := B) (L := L)
    _ =
      (Ideal.Quotient.mk (nilradical (L ⊗[K] K1))).comp tensorBaseChangeToGenericFiber.toRingHom :=
        (reducedTensorBaseChange_quotient_comp_genericFiber
          (A := A) (K := K) (K1 := K1) (B := B) (L := L)).symm

/-- Helper for Remark 15.115.1: an element in the kernel of the tensor comparison becomes
nilpotent after mapping to the unreduced generic fiber. -/
private theorem tensorBaseChangeComparison_kernel_element_genericFiber_nilpotent
    {x : A1 ⊗[A] B}
    (hx : x ∈ RingHom.ker
      (tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
        (A := A) (K := K) (K1 := K1) (B := B) (L := L))) :
    let G : A1 ⊗[A] B →ₐ[A] L ⊗[K] K1 := tensorBaseChangeToGenericFiber
    IsNilpotent (G x) := by
  let F : A1 ⊗[A] B →ₐ[A1] B1 :=
    tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
      (A := A) (K := K) (K1 := K1) (B := B) (L := L)
  let G : A1 ⊗[A] B →ₐ[A] L ⊗[K] K1 := tensorBaseChangeToGenericFiber
  have hx0 : F x = 0 := by
    simpa [F, RingHom.mem_ker] using hx
  have hcomp :=
    DFunLike.congr_fun
      (tensorBaseChangeComparison_subtype_comp_eq_reducedGenericFiberQuotient
        (A := A) (K := K) (K1 := K1) (B := B) (L := L))
      x
  have hq0 : Ideal.Quotient.mk (nilradical (L ⊗[K] K1)) (G x) = 0 := by
    -- Evaluating the comparison square on a kernel element makes the reduced image vanish.
    simpa [F, G, hx0] using hcomp
  have hmem : G x ∈ nilradical (L ⊗[K] K1) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hq0
  -- Membership in the nilradical is exactly nilpotence in the unreduced generic fiber.
  exact hmem

/-- Helper for Remark 15.115.1: the kernel of the tensor comparison map is locally nilpotent. -/
private theorem tensorBaseChangeToReducedTensorBaseChangeIntegralClosure_ker_isLocallyNilpotent :
    let F : A1 ⊗[A] B →ₐ[A1] B1 :=
      tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
        (A := A) (K := K) (K1 := K1) (B := B) (L := L)
    (RingHom.ker F).IsLocallyNilpotent := by
  let F : A1 ⊗[A] B →ₐ[A1] B1 :=
    tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
      (A := A) (K := K) (K1 := K1) (B := B) (L := L)
  let G : A1 ⊗[A] B →ₐ[A] L ⊗[K] K1 :=
    tensorBaseChangeToGenericFiber
      (A := A) (K := K) (K1 := K1) (B := B) (L := L)
  have hGinj :
      Function.Injective
        (tensorBaseChangeToGenericFiber
          (A := A) (K := K) (K1 := K1) (B := B) (L := L)) :=
    tensorBaseChangeToGenericFiber_injective
  -- Rewrite local nilpotence into the source-facing elementwise nilpotence statement.
  rw [Ideal.isLocallyNilpotent_iff]
  intro x hx
  have hnil :
      IsNilpotent (G x) :=
    tensorBaseChangeComparison_kernel_element_genericFiber_nilpotent
      (A := A) (K := K) (K1 := K1) (B := B) (L := L) hx
  rcases hnil with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  -- Injectivity of the generic-fiber map lets us pull the nilpotence witness back to `x`.
  apply hGinj
  simpa [G, map_pow] using hn

private theorem tensorBaseChangeComparison_primeSpectrumComap_surjective :
    Function.Surjective
      (PrimeSpectrum.comap
        (tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
          (A := A) (K := K) (K1 := K1) (B := B) (L := L)).toRingHom) := by
  -- Route correction: factor through the quotient by `ker F`, not through `F.range`, so the
  -- source sentence "integral with nilpotent kernel" matches the Lean skeleton directly.
  let F : A1 ⊗[A] B →ₐ[A1] B1 :=
    tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
      (A := A) (K := K) (K1 := K1) (B := B) (L := L)
  let Fq : (A1 ⊗[A] B) ⧸ RingHom.ker F →ₐ[A1] B1 := Ideal.kerLiftAlg F
  have hFqInt : Fq.toRingHom.IsIntegral :=
    tensorBaseChangeComparison_quotientLift_isIntegral
      (A := A) (K := K) (K1 := K1) (B := B) (L := L)
  have hFqInj : Function.Injective Fq := Ideal.kerLiftAlg_injective F
  have hKerLocNil : (RingHom.ker F).IsLocallyNilpotent :=
    tensorBaseChangeToReducedTensorBaseChangeIntegralClosure_ker_isLocallyNilpotent
      (A := A) (K := K) (K1 := K1) (B := B) (L := L)
  let qmap : A1 ⊗[A] B →+* (A1 ⊗[A] B) ⧸ RingHom.ker F :=
    Ideal.Quotient.mk (RingHom.ker F)
  have hqmapHomeo : IsHomeomorph (PrimeSpectrum.comap qmap) := by
    -- The quotient map has every target element in its range, so the nilpotent-kernel owner
    -- theorem applies directly once we rewrite local nilpotence as containment in the nilradical.
    refine PrimeSpectrum.isHomeomorph_comap qmap ?_ ?_
    · intro x
      rcases Ideal.Quotient.mk_surjective (I := RingHom.ker F) x with ⟨y, rfl⟩
      refine ⟨1, Nat.one_pos, ?_⟩
      exact ⟨y, by simp [qmap]⟩
    · simpa [Ideal.IsLocallyNilpotent] using hKerLocNil
  have hqmapSurj : Function.Surjective (PrimeSpectrum.comap qmap) :=
    hqmapHomeo.bijective.surjective
  have hFqSurj : Function.Surjective (PrimeSpectrum.comap Fq.toRingHom) :=
    RingHom.IsIntegral.comap_surjective hFqInt hFqInj
  have hcomp :
      PrimeSpectrum.comap F.toRingHom =
        PrimeSpectrum.comap qmap ∘ PrimeSpectrum.comap Fq.toRingHom := by
    -- The tensor comparison factors as the quotient map followed by the injective quotient lift.
    have hEq : Fq.toRingHom.comp qmap = F.toRingHom := by
      ext x
      simpa [Fq, qmap] using (Ideal.kerLiftAlg_mk F x)
    rw [← hEq, PrimeSpectrum.comap_comp]
  -- Surjectivity is the composition of the homeomorphism on the quotient and lying over for the
  -- integral quotient lift.
  simpa [hcomp] using hqmapSurj.comp hFqSurj

/-- Remark 15.115.1: the canonical map `Spec(B₁) → Spec(A₁)` is surjective. -/
theorem primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A1 B1)) := by
  -- Route correction: the theorem header has no finite-extension hypothesis on `K₁ / K`, so the
  -- middle surjectivity step must use faithful-flat base change rather than the finite closed-fiber
  -- argument from the source remark.
  let F : A1 ⊗[A] B →ₐ[A1] B1 :=
    tensorBaseChangeToReducedTensorBaseChangeIntegralClosure
      (A := A) (K := K) (K1 := K1) (B := B) (L := L)
  have hTensor : Function.Surjective (PrimeSpectrum.comap (algebraMap A1 (A1 ⊗[A] B))) :=
    tensorBaseChange_primeSpectrumComap_surjective (A := A) (K1 := K1) (B := B)
  have hComparison : Function.Surjective (PrimeSpectrum.comap F.toRingHom) :=
    tensorBaseChangeComparison_primeSpectrumComap_surjective
      (A := A) (K := K) (K1 := K1) (B := B) (L := L)
  intro p
  rcases hTensor p with ⟨q, hq⟩
  rcases hComparison q with ⟨r, hr⟩
  have hfactor : PrimeSpectrum.comap (algebraMap A1 B1) r =
      PrimeSpectrum.comap (algebraMap A1 (A1 ⊗[A] B)) (PrimeSpectrum.comap F.toRingHom r) := by
    -- Compare the two contractions elementwise using the `A₁`-linearity of the comparison map.
    ext x
    change algebraMap A1 B1 x ∈ r.asIdeal ↔
      algebraMap A1 (A1 ⊗[A] B) x ∈ Ideal.comap F.toRingHom r.asIdeal
    change algebraMap A1 B1 x ∈ r.asIdeal ↔
      F.toRingHom (algebraMap A1 (A1 ⊗[A] B) x) ∈ r.asIdeal
    simpa using (congrArg (fun t => t ∈ r.asIdeal) (F.commutes x)).symm
  -- Compose the two spectrum maps along the factorization
  -- `A₁ → A₁ ⊗[A] B → B₁`.
  refine ⟨r, ?_⟩
  rw [hfactor, hr, hq]

variable [FiniteDimensional K K1]

/-- Helper for Remark 15.115.1: the finite integral closure `A₁` of a discrete valuation ring is
not a field. -/
private theorem integralClosure_not_isField
    {K0 : Type v} [Field K0] [Algebra A K0] [IsFractionRing A K0]
    [Algebra K0 K1] [IsScalarTower A K0 K1] [FiniteDimensional K0 K1] :
    ¬ IsField A1 := by
  -- If the integral closure were a field, integrality and injectivity would force `A` to be one.
  let _ : Algebra.IsIntegral A A1 := IsIntegralClosure.isIntegral_algebra A K1
  have hinj : Function.Injective (algebraMap A A1) := by
    exact algebraMap_injective_of_field_isFractionRing A A1 K0 K1
  intro hA1
  exact IsDiscreteValuationRing.not_isField A <|
    isField_of_isIntegral_of_isField hinj hA1

/-- Remark 15.115.1: if `K₁ / K` is finite, then the integral closure `A₁` of `A` in `K₁` is a
Dedekind domain. -/
instance : IsDedekindDomain A1 :=
  by
    -- Reuse the transported owner theorem proved earlier for the chosen fraction-field witness.
    exact integralClosure_isDedekindDomain_of_fractionField_extension
      (A := A) (K := K) (K1 := K1)

instance integralClosure_localizationAtMaximal_isDiscreteValuationRing
    (p : Ideal A1) [p.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  -- Localize the preceding Dedekind-domain owner at the chosen maximal ideal.
  exact
    integralClosure_localizationAtMaximal_isDiscreteValuationRing_of_fractionField_extension
      (A := A) (K := K) (K1 := K1) p

instance reducedTensorBaseChangeIntegralClosure_localizationAtMaximal_isDomain
    (q : Ideal B1) [q.IsMaximal] :
    IsDomain (Localization.AtPrime q) := by
  -- Localizing at a maximal ideal produces the localization at a prime ideal, hence a domain.
  infer_instance

/-- Helper for Remark 15.115.1: the reduced generic fiber `L₁` is reduced by construction. -/
private theorem reducedTensorBaseChange_isReduced :
    IsReduced L1 := by
  -- Quotienting by the nilradical is exactly the canonical reduced quotient.
  exact (Ideal.isRadical_iff_quotient_reduced (nilradical (L ⊗[K] K1))).1 <| by
    simpa [nilradical] using (Ideal.radical_isRadical (⊥ : Ideal (L ⊗[K] K1)))

/-- Helper for Remark 15.115.1: the reduced generic fiber stays finite-dimensional over `L`. -/
private theorem reducedTensorBaseChange_finiteDimensional :
    FiniteDimensional L L1 := by
  -- First view the unreduced tensor product as finite-dimensional over `L`, then pass to the
  -- quotient by the nilradical.
  let _ : FiniteDimensional L (L ⊗[K] K1) := by infer_instance
  infer_instance

/-- Helper for Remark 15.115.1: the reduced generic fiber `L₁` is Artinian. -/
private theorem reducedTensorBaseChange_isArtinian :
    IsArtinianRing L1 := by
  let _ : FiniteDimensional L L1 :=
    reducedTensorBaseChange_finiteDimensional (A := A) (K := K) (K1 := K1) (L := L)
  -- Finite-dimensional algebras over a field are Artinian.
  exact IsArtinianRing.of_finite L L1

/-- Helper for Remark 15.115.1: the Artinian product decomposition of `L₁` evaluates at a maximal
ideal by the corresponding quotient map. -/
private theorem reducedTensorBaseChange_equivPi_apply_eq_quotient_mk
    (m : MaximalSpectrum L1) (x : L1) :
    (IsArtinianRing.equivPi L1) x m = Ideal.Quotient.mk m.asIdeal x := by
  let _ : IsReduced L1 :=
    reducedTensorBaseChange_isReduced (A := A) (K := K) (K1 := K1) (L := L)
  let _ : IsArtinianRing L1 :=
    reducedTensorBaseChange_isArtinian (A := A) (K := K) (K1 := K1) (L := L)
  -- The canonical product decomposition is the tuple of quotient maps.
  have hcomm :
      IsArtinianRing.equivPi L1 x =
        algebraMap L1 ((J : MaximalSpectrum L1) → L1 ⧸ J.asIdeal) x := by
    simpa using (IsArtinianRing.equivPi L1).commutes x
  simpa using congrArg (fun f : (J : MaximalSpectrum L1) → L1 ⧸ J.asIdeal ↦ f m) hcomm

/-- Helper for Remark 15.115.1: the reduced generic fiber splits as the product of its branch field
quotients. -/
private noncomputable theorem reduced_tensor_base_change_equiv_pi_quotients :
    L1 ≃ₐ[B] ∀ m : MaximalSpectrum L1, L1 ⧸ m.asIdeal := by
  let _ : IsReduced L1 :=
    reducedTensorBaseChange_isReduced (A := A) (K := K) (K1 := K1) (L := L)
  let _ : IsArtinianRing L1 :=
    reducedTensorBaseChange_isArtinian (A := A) (K := K) (K1 := K1) (L := L)
  -- Restrict scalars from the canonical reduced-Artinian decomposition to the base DVR `B`.
  exact (IsArtinianRing.equivPi L1).restrictScalars B

/-- Helper for Remark 15.115.1: for a finite product of `B`-algebras, integrality is equivalent
to coordinatewise integrality. -/
private theorem isIntegral_pi_iff_forall
    {ι : Type*} [Finite ι] {S : ι → Type*}
    [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)] {s : ∀ i, S i} :
    IsIntegral B s ↔ ∀ i, IsIntegral B (s i) := by
  let _ := Fintype.ofFinite ι
  constructor
  · intro hs i
    let evalAlgHom : (∀ j, S j) →ₐ[B] S i :=
      { toRingHom := Pi.evalRingHom S i
        commutes' := fun b ↦ rfl }
    -- Evaluating an integral equation preserves integrality on one coordinate.
    exact hs.map evalAlgHom
  · intro hs
    have hpi : IsIntegral (∀ i, B) s := by
      simpa using (IsIntegral.pi_iff (R := fun _ : ι ↦ B) (S := S) (s := s)).2 hs
    let _ : Module.Finite B (∀ i, B) := by infer_instance
    let _ : Algebra.IsIntegral B (∀ i, B) := by infer_instance
    -- The diagonal product ring is finite over `B`, so integrality ascends back to `B`.
    exact isIntegral_trans s hpi

instance reducedTensorBaseChangeIntegralClosure_localizationAtMaximal_isDiscreteValuationRing
    (q : Ideal B1) [q.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  -- The maximal localization is a local factor of the Dedekind ring `B₁`, hence a DVR.
  infer_instance

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
  refine
    { toIsLocalHom := ?_
      algebraMap_injective := ?_ }
  · -- The localized branch map is the canonical local hom induced by `A₁ → B₁`.
    simpa [Localization.localRingHom_to_map] using
      (Localization.isLocalHom_localRingHom
        p q (algebraMap A1 B1) (q.over_def p))
  · -- Injectivity follows because the target localization is again a localization of a domain.
    simpa [Localization.localRingHom_to_map] using
      (IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors :
        Function.Injective
          (Localization.localRingHom p q (algebraMap A1 B1) (q.over_def p)))

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

omit [IsDiscreteValuationRing A] in
/-- Helper for Remark 15.115.1: a local ring is already the localization away from the complement
of its maximal ideal. -/
private theorem self_isLocalization_primeCompl_maximalIdeal_of_localRing
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsLocalization (maximalIdeal R).primeCompl R := by
  -- Every element outside the maximal ideal is a unit, so the identity map realizes the
  -- localization universal property.
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

-- Proof sketch: the public `A₁` Dedekind-domain instance above gives the one-dimensional normal
-- owner. Reuse the chapter owner instance `integralClosure_henselianLocalRing` to put the finite
-- integral closure back in the henselian-local world; then a local Dedekind domain is a discrete
-- valuation ring.
/-- Over a henselian discrete valuation ring, the integral closure in a finite field extension is
again a discrete valuation ring. -/
theorem integralClosure_isDiscreteValuationRing_of_henselian
    [FiniteDimensional K K1] [HenselianLocalRing A] :
    IsDiscreteValuationRing A1 := by
  let _ : IsLocalRing A1 := integralClosure_henselianLocalRing
  let _ : IsLocalization (maximalIdeal A1).primeCompl A1 :=
    self_isLocalization_primeCompl_maximalIdeal_of_localRing (R := A1)
  have hmax : maximalIdeal A1 ≠ ⊥ := by
    -- The henselian normalization is still not a field.
    exact (IsLocalRing.isField_iff_maximalIdeal_eq).not.mp <|
      integralClosure_not_isField (A := A) (K := K) (K1 := K1)
  -- Apply the Dedekind-domain localization theorem directly to the local ring itself.
  simpa using
    (IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      A1 hmax A1)

-- Proof sketch: a finite purely inseparable extension gives a unique prime above the maximal ideal
-- of `A`, so the finite integral closure `A1` is local. Combine this with the Dedekind-domain
-- property to conclude that `A1` is a discrete valuation ring.
/-- For a finite purely inseparable extension `K1 / K`, the integral closure of a discrete
valuation ring `A` in `K1` is again a discrete valuation ring. -/
theorem integralClosure_isDiscreteValuationRing_of_finite_purelyInseparable
    [FiniteDimensional K K1] [IsPurelyInseparable K K1] :
    IsDiscreteValuationRing A1 := by
  let _ : ValuationRing A1 :=
    integralClosure_valuationRing_of_fractionField_purelyInseparable
      (A := A) (K := K) (E := K1)
  have hnf : ¬ IsField A1 :=
    integralClosure_not_isField (A := A) (K := K) (K1 := K1)
  -- A Noetherian valuation ring is either a field or a DVR, and `A₁` is not a field.
  rcases
      (valuationRing_isNoetherianRing_iff_isDiscreteValuationRing_or_isField
        (A := A1)).mp inferInstance with hDvr | hField
  · exact hDvr
  · exact False.elim (hnf hField)

section BaseChange

variable {B : Type x} {L : Type y}
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [FiniteDimensional K K1] [IsPurelyInseparable K K1]

local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

/-- Helper for Remark 15.115.1: the reduced tensor product is a field in the finite purely
inseparable case because it is reduced, Artinian, and local. -/
private theorem reducedTensorBaseChange_isField_of_finite_purelyInseparable :
    IsField L1 := by
  let _ : IsLocalRing (L ⊗[K] K1) :=
    tensorProduct_isLocalRing_of_local_of_integral_of_residueField_purelyInseparable
      (A := K) (B := L) (C := K1) (Or.inl inferInstance)
  let _ : IsLocalRing L1 :=
    IsLocalRing.quotient (nilradical (L ⊗[K] K1)) nilradical_ne_top
  let _ : IsReduced L1 :=
    reducedTensorBaseChange_isReduced (A := A) (K := K) (K1 := K1) (L := L)
  let _ : IsArtinianRing L1 :=
    reducedTensorBaseChange_isArtinian (A := A) (K := K) (K1 := K1) (L := L)
  let _ : Ring.KrullDimLE 0 L1 := inferInstance
  -- A reduced Artinian local ring is a field.
  exact Ring.KrullDimLE.isField_of_isReduced (R := L1)

/-- Helper for Remark 15.115.1: after reducing the tensor product in the finite purely
inseparable case, the ambient field extension over `L` is still purely inseparable. -/
private theorem reducedTensorBaseChange_isPurelyInseparable_of_finite_purelyInseparable
    [Field L1] :
    IsPurelyInseparable L L1 := by
  let q := ringExpChar L
  haveI : ExpChar L q := ringExpChar.expChar L
  rw [isPurelyInseparable_iff_pow_mem L q]
  intro x
  refine Ideal.Quotient.inductionOn' x fun y ↦ ?_
  obtain ⟨n, hpow⟩ :=
    IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
      (k := K) (K := K1) (R := L) q y
  rcases hpow with ⟨z, hz⟩
  refine ⟨n, ⟨z, ?_⟩⟩
  -- Passing to the reduced quotient preserves the displayed power-in-the-image relation.
  change Ideal.Quotient.mk _ (y ^ q ^ n) = algebraMap L L1 z
  rw [hz]
  rfl

-- Proof sketch: `A₁` is a discrete valuation ring by the preceding purely inseparable integral-
-- closure instance. In the purely inseparable base-change case the reduced tensor product `L₁`
-- stays local on the generic fiber, so `B₁` is again a discrete valuation ring; the canonical map
-- `A₁ → B₁` is then the injective local algebra map from Remark 15.115.1.
/-- Remark 15.115.1: if `K₁ / K` is finite purely inseparable, then `B₁` is a domain. -/
theorem reducedTensorBaseChangeIntegralClosure_isDomain_of_finite_purelyInseparable :
    IsDomain B1 := by
  let _ : Field L1 :=
    (reducedTensorBaseChange_isField_of_finite_purelyInseparable
      (A := A) (K := K) (K1 := K1) (L := L)).toField
  -- The integral closure in a field is a domain.
  infer_instance

local instance :
    IsDomain B1 :=
  reducedTensorBaseChangeIntegralClosure_isDomain_of_finite_purelyInseparable

/-- Remark 15.115.1: if `K₁ / K` is finite purely inseparable, then `B₁` is a discrete valuation
ring. -/
instance reducedTensorBaseChangeIntegralClosure_isDiscreteValuationRing_of_finite_purelyInseparable :
    IsDiscreteValuationRing B1 := by
  let _ : Field L1 :=
    (reducedTensorBaseChange_isField_of_finite_purelyInseparable
      (A := A) (K := K) (K1 := K1) (L := L)).toField
  let _ : IsPurelyInseparable L L1 :=
    reducedTensorBaseChange_isPurelyInseparable_of_finite_purelyInseparable
      (A := A) (K := K) (K1 := K1) (L := L)
  let _ : ValuationRing B1 :=
    integralClosure_valuationRing_of_fractionField_purelyInseparable
      (A := B) (K := L) (E := L1)
  have hnf : ¬ IsField B1 :=
    integralClosure_not_isField_of_fractionField_extension
      (A := B) (K := L) (K1 := L1)
  -- The reduced pure base-change normalization is a Noetherian valuation ring, hence a DVR.
  rcases
      (valuationRing_isNoetherianRing_iff_isDiscreteValuationRing_or_isField
        (A := B1)).mp inferInstance with hDvr | hField
  · exact hDvr
  · exact False.elim (hnf hField)

end BaseChange

end
