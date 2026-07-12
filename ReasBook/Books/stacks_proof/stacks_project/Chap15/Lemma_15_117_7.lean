import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_36_10
import StacksProject_2024.Chap10.Lemma_10_37_15
import StacksProject_2024.Chap10.Lemma_10_112_4
import StacksProject_2024.Chap10.Lemma_10_119_10
import StacksProject_2024.Chap10.Lemma_10_119_12_Krull_Akizuki
import StacksProject_2024.Chap15.Definition_15_112_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open PrimeSpectrum Ideal IsLocalRing

universe u v w x y

noncomputable section

/-
Domain-style sampling for Lemma 15.117.7:
- primary domain: reduced tensor-product base change for extensions of discrete valuation rings,
  together with the canonical comparison map from the base-changed integral closure `A'` to `B'`;
- sampled owner declarations:
  `reducedTensorBaseChangeIntegralClosureMap`,
  `reducedTensorBaseChangeIntegralClosure_isDedekindRing`,
  `primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure`,
  `Algebra.finite_of_essFiniteType_of_isAlgebraic`;
- best owner abstraction: the `core/canonical` owner is the comparison map
  `reducedTensorBaseChangeIntegralClosureMap` from Remark `15.115.1`; the three numbered clauses
  here are `source-facing` consequences of that owner;
- primitive data: the DVR extension `A ⊆ B`, the fraction fields `K ⊆ L`, the algebraic base
  change field `K' / K`, and the source hypothesis that the integral closure `A'` is Noetherian;
- derived API: Noetherian consequences for `B'`, the induced surjection on spectra, and the
  residue-field finite-type statement via the canonical residue-field algebra.

Source/core/bridge triage:
- `source-facing`: the Noetherian conclusion in clause `(1)` and the residue-field finiteness
  statement in clause `(3)`, both under the ambient source hypothesis `[IsNoetherianRing A']`;
- `core/canonical`: the map `reducedTensorBaseChangeIntegralClosureMap`, the owner theorem
  `reducedTensorBaseChangeIntegralClosure_isDedekindRing`, and its spectrum-surjectivity companion
  `primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure`;
- `bridge/view`: clause `(2)` is exact-interface reuse of that upstream spectrum-surjectivity
  theorem, reused inside the source-faithful Noetherian context rather than through a duplicate
  local shell; clause `(3)` should be derived from the canonical residue-field finiteness owner,
  with the induced
  `κ(comap q)`-algebra structure on `κ(q)` kept as proof-local scaffolding rather than as the main
  public datum.
-/

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K' : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B] [Algebra.EssFiniteType A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra B L] [Algebra A L] [Algebra K L]
variable [IsFractionRing B L] [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K'] [Algebra A K'] [Algebra K K'] [IsScalarTower A K K']
variable [Algebra.IsAlgebraic K K']

local notation "A'" => integralClosure A K'
local notation "L'" => (L ⊗[K] K') ⧸ nilradical (L ⊗[K] K')
local notation "B'" => integralClosure B L'

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

local instance l'CommRing : CommRing L' :=
  Ideal.Quotient.commRing _

/-- Helper for Lemma 15.117.7: the canonical `A`-algebra map `K' → L'` induced by the right
tensor-factor embedding and passage to the reduced quotient. -/
private abbrev rightTensorFactorToReducedTensorBaseChange : K' →ₐ[A] L' :=
  (Ideal.Quotient.mkₐ A _).comp
    ((Algebra.TensorProduct.includeRight : K' →ₐ[K] L ⊗[K] K').restrictScalars A)

/-- Helper for Lemma 15.117.7: the canonical map `A' → L'` obtained by first mapping into the
integral closure of `A` in `L'` and then forgetting to `L'`. -/
private abbrev integralClosureToReducedTensorBaseChange : A' →ₐ[A] L' :=
  (integralClosure A L').val.comp
    rightTensorFactorToReducedTensorBaseChange.mapIntegralClosure

/-- Helper for Lemma 15.117.7: elements of `A'` map into the integral closure `B'` inside the
reduced tensor base change `L'`. -/
private theorem integralClosureToReducedTensorBaseChange_mem_integralClosure (x : A') :
    integralClosureToReducedTensorBaseChange x ∈ B' := by
  -- Package the image in `integralClosure A L'` first so the scalar tower is fully determined.
  let y : integralClosure A L' :=
    rightTensorFactorToReducedTensorBaseChange.mapIntegralClosure x
  have hyA : IsIntegral A (y : L') := y.2
  have hyB : IsIntegral B (y : L') := IsIntegral.tower_top hyA
  -- Unfolding the canonical map identifies the goal with the same underlying element of `L'`.
  simpa [integralClosureToReducedTensorBaseChange, y] using hyB

/-- Helper for Lemma 15.117.7: the canonical `A`-algebra map `K' → L'` induced by the right
tensor-factor embedding and passage to the reduced quotient. -/
private def reducedTensorBaseChangeIntegralClosureMap : A' →ₐ[A] B' :=
  AlgHom.codRestrict
    integralClosureToReducedTensorBaseChange
    ((integralClosure B L').restrictScalars A)
    integralClosureToReducedTensorBaseChange_mem_integralClosure

/-- Helper for Lemma 15.117.7: the reduced tensor-product integral closure carries its canonical
`A'`-algebra structure through the comparison map. -/
private instance : Algebra A' B' :=
  reducedTensorBaseChangeIntegralClosureMap.toRingHom.toAlgebra

/-- Helper for Lemma 15.117.7: the canonical map from the tensor base change `A' ⊗[A] B` to the
reduced tensor-product integral closure `B'`. -/
private noncomputable def tensorBaseChangeToReducedTensorBaseChangeIntegralClosure :
    A' ⊗[A] B →ₐ[A'] B' :=
  ((IsScalarTower.toAlgHom A B B').liftEquiv A A' B B')

/-- Helper for Lemma 15.117.7: the maximal-ideal residue field of a local ring agrees with its
ambient residue field. -/
private noncomputable abbrev maximalIdeal_residueField_equiv
    (R : Type*) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Lemma 15.117.7: for a prime localization, the maximal-ideal residue field is the
same as the residue field of the original prime. -/
private noncomputable abbrev prime_localization_maximalResidueField_equiv
    {R : Type*} [CommRing R] (I : Ideal R) [I.IsPrime] :
    (maximalIdeal (Localization.AtPrime I)).ResidueField ≃+* I.ResidueField := by
  -- Reinterpret the prime residue field as the ambient residue field of the local ring `R_I`.
  change (maximalIdeal (Localization.AtPrime I)).ResidueField ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime I)
  exact maximalIdeal_residueField_equiv (Localization.AtPrime I)

/-- Helper for Lemma 15.117.7: localizing at a prime does not change its residue field. -/
private noncomputable abbrev prime_localization_residueField_equiv
    {R : Type*} [CommRing R] (I : Ideal R) [I.IsPrime] :
    ResidueField (Localization.AtPrime I) ≃+* I.ResidueField :=
  (maximalIdeal_residueField_equiv (Localization.AtPrime I)).symm.trans
    (prime_localization_maximalResidueField_equiv I)

/-- Helper for Lemma 15.117.7: the maximal-ideal residue-field identification sends residue
classes of elements to the canonical local residue classes. -/
private theorem maximalIdeal_residueField_equiv_apply_algebraMap
    (R : Type*) [CommRing R] [IsLocalRing R] (a : R) :
    maximalIdeal_residueField_equiv R (algebraMap R (maximalIdeal R).ResidueField a) =
      IsLocalRing.residue R a := by
  -- Compare both sides through the inverse equivalence coming from the quotient/residue-field map.
  rw [show algebraMap R (maximalIdeal R).ResidueField a =
      algebraMap (ResidueField R) (maximalIdeal R).ResidueField (IsLocalRing.residue R a) by rfl]
  change
    maximalIdeal_residueField_equiv R
        ((maximalIdeal_residueField_equiv R).symm (IsLocalRing.residue R a)) =
      IsLocalRing.residue R a
  exact (maximalIdeal_residueField_equiv R).apply_symm_apply (IsLocalRing.residue R a)

/-- Helper for Lemma 15.117.7: after identifying ideal residue fields with local residue fields,
the ideal-level residue-field map becomes the canonical local residue-field map. -/
private theorem maximalIdeal_residueField_equiv_comp_residueFieldMap
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] :
    (maximalIdeal_residueField_equiv S).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (ResidueField.map f).comp (maximalIdeal_residueField_equiv R).toRingHom := by
  -- It suffices to check the comparison on residue classes of elements of `R`.
  apply Ideal.ResidueField.ringHom_ext
  ext a
  change
    maximalIdeal_residueField_equiv S
        (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) f
          (IsLocalRing.maximalIdeal_comap f).symm
          (algebraMap R (maximalIdeal R).ResidueField a)) =
      ResidueField.map f
        (maximalIdeal_residueField_equiv R (algebraMap R (maximalIdeal R).ResidueField a))
  rw [Ideal.ResidueField.map_algebraMap, maximalIdeal_residueField_equiv_apply_algebraMap,
    maximalIdeal_residueField_equiv_apply_algebraMap, IsLocalRing.ResidueField.map_residue]

/-- Helper for Lemma 15.117.7: the residue field at the zero prime of a domain is its fraction
field. -/
private noncomputable def zeroPrimeResidueField_algEquiv_fractionRing
    (R : Type*) [CommRing R] [IsDomain R] :
    FractionRing R ≃ₐ[R] ((⊥ : Ideal R).ResidueField) := by
  let e : R ≃ₐ[R] R ⧸ (⊥ : Ideal R) := (AlgEquiv.quotientBot R R).symm
  letI : IsFractionRing R ((⊥ : Ideal R).ResidueField) := by
    refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
    intro x
    change algebraMap R ((⊥ : Ideal R).ResidueField) x =
      algebraMap (R ⧸ (⊥ : Ideal R)) ((⊥ : Ideal R).ResidueField) (Ideal.Quotient.mk _ x)
    symm
    exact show
        algebraMap (R ⧸ (⊥ : Ideal R)) ((⊥ : Ideal R).ResidueField)
            (Ideal.Quotient.mk (⊥ : Ideal R) x) =
          algebraMap R ((⊥ : Ideal R).ResidueField) x by
      rfl
  -- `((⊥ : Ideal R).ResidueField)` is a fraction ring of `R`, so the standard owner equivalence
  -- identifies it with `FractionRing R`.
  exact FractionRing.algEquiv R ((⊥ : Ideal R).ResidueField)

/-- Helper for Lemma 15.117.7: residue fields of a prime of an essentially finite type map stay
essentially of finite type over the contracted residue field. -/
private theorem residueField_essFiniteType_of_prime_of_essFiniteType
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (q : PrimeSpectrum S) :
    Algebra.EssFiniteType (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField := by
  -- First view `κ(q)` as essentially finite type over the ambient target ring `S`.
  let _ : Algebra.EssFiniteType S q.asIdeal.ResidueField := inferInstance
  -- Then compose `R → S → κ(q)` and descend along the contracted residue-field map.
  let _ : Algebra.EssFiniteType R q.asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp R S q.asIdeal.ResidueField
  exact
    Algebra.EssFiniteType.of_comp R (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField

/-- Helper for Lemma 15.117.7: once the residue-field map over a prime of an essentially finite
type morphism is algebraic, it is automatically finite type. -/
private theorem residueField_finiteType_of_prime_of_essFiniteType_of_isAlgebraic
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (q : PrimeSpectrum S)
    [Algebra.IsAlgebraic (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField] :
    Algebra.FiniteType (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField := by
  -- The previous helper packages the geometric input as residue-field `EssFiniteType`.
  let _ :
      Algebra.EssFiniteType (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField :=
    residueField_essFiniteType_of_prime_of_essFiniteType q
  -- Over fields, `EssFiniteType + IsAlgebraic` upgrades to a finite extension, hence finite type.
  let _ : Module.Finite (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  infer_instance

/-- Helper for Lemma 15.117.7: the residue field of an integral target is integral over the base
ring. -/
private theorem residueField_isIntegral_over_base_of_integral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] [Algebra.IsIntegral R S] :
    Algebra.IsIntegral R (ResidueField S) := by
  -- The canonical quotient-to-residue-field map makes `κ(S)` integral over `S`.
  let _ : Algebra.IsIntegral S (ResidueField S) := inferInstance
  -- Then integrality descends along the tower `R → S → κ(S)`.
  exact Algebra.IsIntegral.trans S

/-- Helper for Lemma 15.117.7: an integral local homomorphism induces an integral residue-field
extension. -/
private theorem residueField_isIntegral_over_baseResidueField_of_localHom_of_integral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Algebra.IsIntegral R S] :
    Algebra.IsIntegral (ResidueField R) (ResidueField S) := by
  let ρ : ResidueField R →+* ResidueField S :=
    IsLocalRing.ResidueField.map (algebraMap R S)
  -- The composite `R → κ(R) → κ(S)` is the usual map `R → κ(S)`, so residue-field integrality
  -- follows by descending the already known integrality of `R → κ(S)`.
  have hcomp : (ρ.comp (IsLocalRing.residue R)).IsIntegral := by
    have hbase : (algebraMap R (ResidueField S)).IsIntegral := by
      exact
        algebraMap_isIntegral_iff.mpr
          (residueField_isIntegral_over_base_of_integral (R := R) (S := S))
    simpa [ρ, RingHom.comp_assoc, IsLocalRing.ResidueField.map_residue] using hbase
  have hρ : ρ.IsIntegral :=
    RingHom.IsIntegral.tower_top (IsLocalRing.residue R) ρ hcomp
  exact algebraMap_isIntegral_iff.mp (by simpa [ρ] using hρ)

/-- Helper for Lemma 15.117.7: an integral local homomorphism induces an algebraic extension on
residue fields. -/
private theorem residueField_isAlgebraic_of_localHom_of_integral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Algebra.IsIntegral R S] :
    Algebra.IsAlgebraic (ResidueField R) (ResidueField S) := by
  -- First prove the induced residue-field map is integral; over fields this is equivalent to
  -- algebraicity.
  rw [Algebra.isAlgebraic_iff_isIntegral]
  exact
    residueField_isIntegral_over_baseResidueField_of_localHom_of_integral (R := R) (S := S)

/-- Helper for Lemma 15.117.7: once the localized map at a prime is integral, the induced
prime-residue-field extension is algebraic. -/
private theorem residueField_isAlgebraic_of_prime_of_localized_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S)
    [Algebra.IsIntegral (Localization.AtPrime (q.asIdeal.under R))
      (Localization.AtPrime q.asIdeal)] :
    Algebra.IsAlgebraic (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField := by
  -- Reinterpret the prime residue fields as the local residue fields of the corresponding prime
  -- localizations, where the integral local-map theorem applies directly.
  change
    Algebra.IsAlgebraic
      (ResidueField (Localization.AtPrime (q.asIdeal.under R)))
      (ResidueField (Localization.AtPrime q.asIdeal))
  -- The localized map is integral, so the induced residue-field extension is algebraic.
  exact
    residueField_isAlgebraic_of_localHom_of_integral
      (R := Localization.AtPrime (q.asIdeal.under R))
      (S := Localization.AtPrime q.asIdeal)

/-- Helper for Lemma 15.117.7: if the induced fraction-field extension of domains is algebraic,
then the whole ring map is algebraic. -/
private theorem isAlgebraic_of_fractionRing_isAlgebraic
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]
    [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)]
    [Algebra.IsAlgebraic (FractionRing R) (FractionRing S)] :
    Algebra.IsAlgebraic R S := by
  let _ : Algebra.IsAlgebraic R (FractionRing S) :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance : Algebra.IsAlgebraic (FractionRing R) (FractionRing S))
  exact
    Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom R S (FractionRing S))
      (IsFractionRing.injective S (FractionRing S))

/-- Helper for Lemma 15.117.7: the source DVR `A` has Krull dimension `1`. -/
private theorem ringKrullDim_eq_one_of_baseDvr :
    ringKrullDim A = 1 := by
  -- A discrete valuation ring is a nonfield principal ideal ring, hence one-dimensional.
  exact IsPrincipalIdealRing.ringKrullDim_eq_one A (IsDiscreteValuationRing.not_isField A)

include K

/-- Helper for Lemma 15.117.7: the algebraic normalization `A'` still has fraction field `K'`. -/
private theorem aPrime_isFractionRing_of_algebraic :
    IsFractionRing A' K' := by
  let _ : Algebra.IsAlgebraic A K' :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance : Algebra.IsAlgebraic K K')
  let _ : FaithfulSMul A K' :=
    (faithfulSMul_iff_algebraMap_injective A K').mpr
      (algebraMap_injective_of_field_isFractionRing
        (R := A) (S := K') (K := K) (L := K'))
  -- Reuse the standard fraction-field owner for integral closures in algebraic extensions.
  exact integralClosure.isFractionRing_of_algebraic
    (fun x hx ↦ (FaithfulSMul.algebraMap_injective A K') <| by simpa using hx)

/-- Helper for Lemma 15.117.7: the normalization map `A → A'` is injective. -/
private theorem aPrime_algebraMap_injective :
    Function.Injective (algebraMap A A') := by
  let _ : IsFractionRing A' K' :=
    aPrime_isFractionRing_of_algebraic (A := A) (K := K) (K' := K')
  -- Compare both rings inside their common fraction field `K'`.
  exact algebraMap_injective_of_field_isFractionRing
    (R := A) (S := A') (K := K) (L := K')

/-- Helper for Lemma 15.117.7: the algebraic normalization `A'` of a DVR is not a field. -/
private theorem aPrime_not_isField :
    ¬ IsField A' := by
  let _ : Algebra.IsIntegral A A' := IsIntegralClosure.isIntegral_algebra A K'
  have hinj : Function.Injective (algebraMap A A') :=
    aPrime_algebraMap_injective (A := A) (K := K) (K' := K')
  -- If the normalization were a field, integrality and injectivity would force the DVR `A`
  -- itself to be a field.
  intro hA'
  exact IsDiscreteValuationRing.not_isField A <|
    isField_of_isIntegral_of_isField hinj hA'

/-- Helper for Lemma 15.117.7: the integral closure `A'` stays one-dimensional over the source
DVR `A`. -/
private theorem aPrime_ringKrullDim_eq_one :
    ringKrullDim A' = 1 := by
  let _ : Algebra.IsIntegral A A' := IsIntegralClosure.isIntegral_algebra A K'
  have hdim :
      ringKrullDim A = ringKrullDim A' :=
    ringKrullDim_eq_of_injective_algebraMap_of_isIntegral
      (aPrime_algebraMap_injective (A := A) (K := K) (K' := K'))
  -- Transfer the source DVR dimension across the integral injective normalization map.
  simpa [ringKrullDim_eq_one_of_baseDvr] using hdim.symm

/-- Helper for Lemma 15.117.7: the one-dimensional normalization `A'` satisfies the canonical
dimension-at-most-one owner used by later localizations. -/
private theorem aPrime_ringKrullDimLE_one :
    Ring.KrullDimLE 1 A' := by
  -- Repackage the already proved equality `ringKrullDim A' = 1` into the `KrullDimLE` API.
  have hdim : ringKrullDim A' ≤ 1 := by
    rw [aPrime_ringKrullDim_eq_one (A := A) (K := K) (K' := K')]
  exact Ring.krullDimLE_iff.mpr hdim

/-- Helper for Lemma 15.117.7: an essentially finite type extension of discrete valuation rings
has finite fraction-field degree. -/
private theorem fractionField_finiteDimensional_of_essFiniteType_dvr_extension :
    FiniteDimensional K L := by
  -- TODO: recover the standard generic-fiber finite-dimensionality bridge for essentially finite
  -- type extensions of discrete valuation rings.
  sorry

/-- Helper for Lemma 15.117.7: an extension of discrete valuation rings is faithfully flat over
the source. -/
private theorem extensionOfDiscreteValuationRings_faithfullyFlat :
    (algebraMap A B).FaithfullyFlat := by
  -- First convert injectivity of the DVR map into torsion-freeness of the target module.
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

/-- Helper for Lemma 15.117.7: the tensor-base-change map
`Spec(A' ⊗[A] B) → Spec(A')` is surjective by faithful-flat base change. -/
private theorem tensorBaseChange_primeSpectrumComap_surjective :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A' (A' ⊗[A] B))) := by
  -- Base change the faithfully flat DVR extension `A → B` along `A → A'`.
  let hff : (algebraMap A B).FaithfullyFlat :=
    extensionOfDiscreteValuationRings_faithfullyFlat (A := A) (B := B) (K := K)
  let _ : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  let _ : Module.FaithfullyFlat A' (A' ⊗[A] B) :=
    Module.FaithfullyFlat.instTensorProduct A B A'
  simpa using
    (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A') (B := A' ⊗[A] B))

section BaseChange

section

-- Proof sketch: the remaining work in this item now starts exactly at the tensor-comparison /
-- branch-decomposition frontier. The stable prefix above isolates the base-change algebra setup,
-- residue-field transport lemmas, and the one-dimensional normalization owners needed by the
-- source argument.

/-- Lemma 15.117.7 (1): if `A → B` is an essentially finite type extension of discrete valuation
rings, `K'/K` is algebraic, and the integral closure `A'` of `A` in `K'` is Noetherian, then the
integral closure `B'` of `B` in `L' = (L ⊗[K] K')_red` is Noetherian. -/
@[stacks 09IH]
theorem isNoetherianRing_integralClosure_of_reducedTensorProduct_baseChange
    (hA' : IsNoetherianRing (integralClosure A K'))
    : IsNoetherianRing B' := by
  -- TODO: complete the branchwise Krull-Akizuki argument and transport it back from the reduced
  -- generic-fiber product decomposition.
  let _ : IsNoetherianRing A' := hA'
  sorry

-- Proof sketch: clause `(2)` factors `A' → B'` through the faithfully flat tensor base change
-- `A' → A' ⊗[A] B` and the comparison map `A' ⊗[A] B → B'`. The first step is already closed by
-- `tensorBaseChange_primeSpectrumComap_surjective`; what remains is the source-faithful
-- quotient-by-kernel owner for the comparison map.
/- Lemma 15.117.7 (2): under the same Noetherian hypothesis on `A'`, the induced map
`Spec(B') → Spec(A')` is surjective. -/
theorem primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A' B')) := by
  -- TODO: prove surjectivity of the comparison map `Spec(B') → Spec(A' ⊗[A] B)` by factoring
  -- through the quotient by its nilpotent kernel, then compose with the faithful-flat tensor step.
  sorry

/- Proof sketch: after reducing a prime of `B'` to its unique supporting branch in the Artinian
product decomposition of the reduced generic fiber, the zero-contraction case should be handled by
fraction-field algebraicity and the nonzero-contraction case by localizing at the contracted prime
and applying Lemma `10.119.10 (3)`. -/
/-- Lemma 15.117.7 (3): under the same hypotheses, including that `A'` is Noetherian, for every
prime `q` of `B'`, the corresponding residue field extension `κ(q) / κ(q ∩ A')` is finitely
generated. -/
@[stacks 09IH]
theorem residueField_finiteType_of_reducedTensorProduct_baseChange
    (hA' : IsNoetherianRing (integralClosure A K'))
    (q : PrimeSpectrum B') :
    Algebra.FiniteType (q.asIdeal.under A').ResidueField q.asIdeal.ResidueField := by
  -- TODO: reduce `q` to its supporting branch in the reduced generic-fiber product decomposition,
  -- then split on whether the contracted prime of that branch is zero or nonzero.
  let _ : IsNoetherianRing A' := hA'
  let _ := q
  sorry

end

end BaseChange

end
