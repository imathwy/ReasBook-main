import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import StacksProject_2024.stacks_project.Chap10.Lemma_10_17_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_17_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_90_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_96_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_2
import StacksProject_2024.stacks_project.Chap10.Proposition_10_90_6
import StacksProject_2024.stacks_project.Chap15.PrincipalIdeal
import StacksProject_2024.stacks_project.Chap15.Theorem_15_90_18

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open TensorProduct

noncomputable section

universe u

namespace FGModuleCat

section CommRing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ≃ₗ[S] S :=
  { __ := AddEquiv.refl S
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower R S ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

private noncomputable def extendScalarsTensorEquiv (M : FGModuleCat R) :
    ↑((ModuleCat.extendScalars (algebraMap R S)).obj M.obj) ≃ₗ[S] TensorProduct R S M.obj :=
  TensorProduct.AlgebraTensorModule.congr
    (restrictScalarsSelfEquiv R S)
    (LinearEquiv.refl R M.obj)

variable {R S}

/-- Extension of scalars on finitely generated modules, obtained by restricting
`ModuleCat.extendScalars` to the canonical owner `FGModuleCat`. -/
noncomputable abbrev extendScalars (f : R →+* S) : FGModuleCat R ⥤ FGModuleCat S :=
  let _ : Algebra R S := f.toAlgebra
  (ModuleCat.isFG S).lift
    ((ModuleCat.isFG R).ι ⋙ ModuleCat.extendScalars f)
    (fun M ↦
      (inferInstance : Module.Finite S (TensorProduct R S M.obj)).equiv
        (by
          simpa using (extendScalarsTensorEquiv R S M)))

omit [Algebra R S] in
@[simp] lemma extendScalars_obj_obj (f : R →+* S) (M : FGModuleCat R) :
    ((extendScalars f).obj M).obj = ((ModuleCat.extendScalars f).obj M.obj) :=
  rfl

omit [Algebra R S] in
@[simp] lemma extendScalars_map_hom (f : R →+* S) {M N : FGModuleCat R} (g : M ⟶ N) :
    ((extendScalars f).map g).hom = (ModuleCat.extendScalars f).map g.hom :=
  rfl

end CommRing

end FGModuleCat

section ModuleCatTensorBridge

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Helper for Proposition 15.90.19: identify the restricted-scalars copy of `S` inside
`ModuleCat.extendScalars` with the ring `S` itself. -/
private noncomputable def moduleCatRestrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ≃ₗ[S] S :=
  { __ := AddEquiv.refl S
    map_smul' := fun _ _ ↦ rfl }

private instance moduleCatRestrictScalarsSelfIsScalarTower :
    IsScalarTower R S ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

/-- Helper for Proposition 15.90.19: extension of scalars in `ModuleCat` is canonically the usual
tensor product `S ⊗[R] M`. -/
private noncomputable def moduleCatExtendScalarsTensorEquiv (M : ModuleCat R) :
    ↑((ModuleCat.extendScalars (algebraMap R S)).obj M) ≃ₗ[S] TensorProduct R S M :=
  TensorProduct.AlgebraTensorModule.congr
    (moduleCatRestrictScalarsSelfEquiv R S)
    (LinearEquiv.refl R M)

end ModuleCatTensorBridge

section

variable {R : Type u} [CommRing R] (f : R)

open PrimeSpectrum
open scoped PrimeSpectrum

local notation "RHat" => principalAdicCompletion f
local notation "RHatf" => Localization.Away (algebraMap R RHat f)
local notation "Rf" => Localization.Away f
local notation "completionFG" => FGModuleCat.extendScalars (algebraMap R RHat)
local notation "completionOverlapFG" => FGModuleCat.extendScalars (algebraMap RHat RHatf)
local notation "localizationFG" => FGModuleCat.extendScalars (algebraMap R Rf)
local notation "localizationOverlapFG" =>
  FGModuleCat.extendScalars (Localization.awayMap (algebraMap R RHat) f)
local notation "FGGlueCat" =>
  CategoricalPullback
    completionOverlapFG
    localizationOverlapFG

/- Domain-style sampling for 15.90.19:
- primary domain: single-element formal glueing for finitely generated module categories over
  `R`, `R^∧`, `(R^∧)_f`, and `R_f`;
- sampled owner declarations:
  `FGModuleCat`,
  `FGModuleCat.extendScalars`,
  `formalGlueingSingleFunctor`,
  `CategoricalPullback`;
- best owner abstraction:
  the pullback of the finitely generated change-of-rings functors
  `completionOverlapFG` and `localizationOverlapFG`, with
  `formalGlueingSingleFunctor RHat f` used only as the ambient comparison model;
- primitive data:
  the completion ring `RHat`, the localization square
  `R → RHat`, `R → Rf`, `RHat → RHatf`, `Rf → RHatf`, and the canonical owner
  `FGModuleCat.extendScalars` on each edge;
- derived API:
  the formal glueing functor `FGModuleCat R ⥤ FGGlueCat` and the equivalence statement below.

Source/core/bridge triage:
- `source-facing`: `principalAdicFormalGlueingFGFunctor` and
  `principalAdicFormalGlueingFGFunctor_isEquivalence`;
- `core/canonical`: `FGModuleCat`, `FGModuleCat.extendScalars`, and
  `formalGlueingSingleFunctor RHat f`;
- `bridge/view`: the ambient `ModuleCat` formal glueing object used to furnish the comparison
  isomorphism and finiteness witnesses for the pullback object below.
-/

-- Proof sketch: for `M : FGModuleCat R`, the first component of
-- `formalGlueingSingleFunctor RHat f` is extension of scalars
-- `M ⊗[R] R^∧`, and the second component is `M ⊗[R] R_f`. Finite generation is preserved
-- by scalar extension along both `R → R^∧` and `R → R_f`.
/-- The completion component of the single-element formal glueing datum attached to a finitely
generated `R`-module is finitely generated over `R^∧`. -/
theorem principalAdicFormalGlueingSingleFunctor_fst_finite
    (M : FGModuleCat R) :
    Module.Finite RHat (((formalGlueingSingleFunctor RHat f).obj M.obj).fst) := by
  -- Proof comment: the first component is the completion-side scalar extension of `M`, and the
  -- earlier tensor-model equivalence turns finite generation into the standard base-change fact.
  let _ : Module.Finite RHat (TensorProduct R RHat M.obj) :=
    Module.Finite.base_change (R := R) (A := RHat) (M := M.obj)
  simpa using Module.Finite.equiv (FGModuleCat.extendScalarsTensorEquiv R RHat M).symm

/-- The localization component of the single-element formal glueing datum attached to a finitely
generated `R`-module is finitely generated over `R_f`. -/
theorem principalAdicFormalGlueingSingleFunctor_snd_finite
    (M : FGModuleCat R) :
    Module.Finite Rf (((formalGlueingSingleFunctor RHat f).obj M.obj).snd) := by
  -- Proof comment: the second component is the localization-side scalar extension of `M`, and the
  -- same tensor-model comparison reduces finite generation to base change along `R → R_f`.
  let _ : Module.Finite Rf (TensorProduct R Rf M.obj) :=
    Module.Finite.base_change (R := R) (A := Rf) (M := M.obj)
  simpa using Module.Finite.equiv (FGModuleCat.extendScalarsTensorEquiv R Rf M).symm

/-- Helper for Proposition 15.90.19: the first principal power ideal is the principal ideal
itself. -/
private theorem principalPowerIdeal_one_eq_principalIdeal :
    principalPowerIdeal f 1 = principalIdeal f := by
  -- Normalize exponent `1` once so all later quotient transports stay on the canonical
  -- source-facing owner `(f)`.
  simp [principalPowerIdeal]

/-- Helper for Proposition 15.90.19: the completion comparison on the powered quotient at
exponent `1` is exactly the principal-power quotient map. -/
private theorem principalAdicCompletion_powerOneQuotientMap_bijective :
    Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R RHat) f 1) := by
  let I : Ideal R := principalIdeal f
  let σ : R →+* RHat := algebraMap R RHat
  let e :
      (RHat ⧸ Ideal.map σ (I ^ 1)) ≃ₐ[R] (R ⧸ I ^ 1) :=
    (Ideal.quotientEquivAlgOfEq R
      (completionIdeal_pow_eq_ker_evalₐ (I := I) (principalIdeal_fg f) 1)).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (f := AdicCompletion.evalₐ I 1)
        (AdicCompletion.surjective_evalₐ I 1))
  have hmap :
      Ideal.map σ (I ^ 1) = principalPowerIdeal (σ f) 1 := by
    simp [I, σ, principalPowerIdeal, principalIdeal, Ideal.map_pow, Ideal.map_span,
      Set.image_singleton]
  have hq :
      Ideal.quotientMap (Ideal.map σ (I ^ 1)) σ Ideal.le_comap_map = e.symm.toRingHom := by
    -- Identify the quotient map on generators with the inverse completion quotient equivalence.
    apply Ideal.Quotient.ringHom_ext
    ext r
    dsimp [e, σ]
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ 1))
          (AdicCompletion.of I R r) =
        (Ideal.quotientEquivAlgOfEq R
          (completionIdeal_pow_eq_ker_evalₐ (I := I) (principalIdeal_fg f) 1).symm)
          ((Ideal.quotientKerAlgEquivOfSurjective
              (f := AdicCompletion.evalₐ I 1)
              (AdicCompletion.surjective_evalₐ I 1)).symm
            ((Ideal.Quotient.mk (I ^ 1)) r))
    rw [← AdicCompletion.evalₐ_of (I := I) 1 r]
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply
      (hf := AdicCompletion.surjective_evalₐ I 1)
      (a := AdicCompletion.of I R r)]
    rfl
  have htransport :
      principalPowerIdealImageQuotientMap σ f 1 =
        (Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
          (Ideal.quotientMap (Ideal.map σ (I ^ 1)) σ Ideal.le_comap_map) := by
    -- Rewrite the principal-power quotient owner into the generic quotient-map owner.
    apply Ideal.Quotient.ringHom_ext
    ext r
    dsimp [principalPowerIdealImageQuotientMap, principalPowerIdealQuotientMap]
    simpa [I, principalPowerIdeal, Ideal.quotientMap_mk] using
      (Ideal.quotientEquivAlgOfEq_mk (R₁ := R) (h := hmap) (x := σ r))
  rw [htransport, hq]
  simpa [RingHom.comp_apply] using
    (Ideal.quotientEquivAlgOfEq R hmap).bijective.comp e.symm.bijective

/-- Helper for Proposition 15.90.19: quotienting modulo `(x)` is the conjugate of quotienting
modulo `(x)^1` by the canonical quotient equivalences. -/
private theorem principalIdealQuotientMap_eq_conj_principalPowerIdealImageQuotientMap_one
    {S : Type u} [CommRing S] (σ : R →+* S) (x : R) :
    principalIdealQuotientMap σ x rfl =
      ((Ideal.quotEquivOfEq
          (principalPowerIdeal_one_eq_principalIdeal (R := S) (f := σ x))).toRingHom).comp
        ((principalPowerIdealImageQuotientMap σ x 1).comp
          ((Ideal.quotEquivOfEq
            (principalPowerIdeal_one_eq_principalIdeal (R := R) (f := x)).symm).toRingHom)) := by
  -- Compare both quotient maps after precomposing with the source quotient generator.
  apply Ideal.Quotient.ringHom_ext
  ext r
  simp [principalIdealQuotientMap, principalPowerIdealImageQuotientMap,
    principalPowerIdealQuotientMap, RingHom.comp_apply]

/-- Helper for Proposition 15.90.19: the completion map induces a bijection
`R / (f) ≃ R^∧ / (f)R^∧`. -/
theorem completion_principalIdealQuotientMap_bijective :
    Function.Bijective
      (principalIdealQuotientMap (algebraMap R RHat) f rfl) := by
  -- Route correction: work through the exponent-`1` powered quotient comparison and transport
  -- across the canonical quotient equivalences on source and target.
  have hpow :
      Function.Bijective
        (principalPowerIdealImageQuotientMap (algebraMap R RHat) f 1) :=
    principalAdicCompletion_powerOneQuotientMap_bijective (R := R) f
  rw [principalIdealQuotientMap_eq_conj_principalPowerIdealImageQuotientMap_one
    (R := R) (S := RHat) (σ := algebraMap R RHat) (x := f)]
  simpa [RingHom.comp_apply] using
    ((Ideal.quotEquivOfEq
      (principalPowerIdeal_one_eq_principalIdeal (R := RHat) (f := algebraMap R RHat f))).bijective.comp
        (hpow.comp
          (Ideal.quotEquivOfEq
            (principalPowerIdeal_one_eq_principalIdeal (R := R) (f := f)).symm).bijective))

/-- Helper for Proposition 15.90.19: the quotient-bijectivity hypothesis lifts every prime in
`V(f)` to the completion spectrum. -/
private theorem exists_prime_over_zeroLocus_of_principalIdealQuotientMap_bijective
    {p : PrimeSpectrum R}
    (hp : p ∈ PrimeSpectrum.zeroLocus (principalIdeal f : Set R)) :
    ∃ q : PrimeSpectrum RHat, PrimeSpectrum.comap (algebraMap R RHat) q = p := by
  let qmap := principalIdealQuotientMap (algebraMap R RHat) f rfl
  let x : PrimeSpectrum (R ⧸ principalIdeal f) :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus (principalIdeal f)).symm ⟨p, hp⟩
  have hsurj : Function.Surjective (PrimeSpectrum.comap qmap) :=
    (PrimeSpectrum.isHomeomorph_comap_of_bijective
      (completion_principalIdealQuotientMap_bijective (R := R) f)).bijective.surjective
  obtain ⟨x', hx'⟩ := hsurj x
  let q : PrimeSpectrum RHat :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus
      (principalIdeal (algebraMap R RHat f)) x').1
  have hq :
      PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdeal (algebraMap R RHat f))) x' = q := by
    simpa [q] using
      (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply
        (principalIdeal (algebraMap R RHat f)) x').symm
  have hp' :
      PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdeal f)) x = p := by
    have hx :
        (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus (principalIdeal f) x).1 = p := by
      simpa [x] using congrArg Subtype.val
        ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus
          (principalIdeal f)).apply_symm_apply ⟨p, hp⟩)
    rwa [Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply] at hx
  have hcomp :
      (Ideal.Quotient.mk (principalIdeal (algebraMap R RHat f))).comp (algebraMap R RHat) =
        qmap.comp (Ideal.Quotient.mk (principalIdeal f)) := by
    ext r
    simp [qmap, principalIdealQuotientMap]
  refine ⟨q, ?_⟩
  -- Functoriality of `Spec` reduces the claim to the lifted quotient prime `x'`.
  calc
    PrimeSpectrum.comap (algebraMap R RHat) q
        = PrimeSpectrum.comap (algebraMap R RHat)
            (PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdeal (algebraMap R RHat f))) x') := by
            rw [hq]
    _ = PrimeSpectrum.comap
          ((Ideal.Quotient.mk (principalIdeal (algebraMap R RHat f))).comp (algebraMap R RHat)) x' := by
          rw [← PrimeSpectrum.comap_comp_apply]
    _ = PrimeSpectrum.comap (qmap.comp (Ideal.Quotient.mk (principalIdeal f))) x' := by
          rw [hcomp]
    _ = PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdeal f))
          (PrimeSpectrum.comap qmap x') := by
          rw [PrimeSpectrum.comap_comp_apply]
    _ = PrimeSpectrum.comap (Ideal.Quotient.mk (principalIdeal f)) x := by
          rw [hx']
    _ = p := hp'

/-- Helper for Proposition 15.90.19: the completion and localization away from `f` cover
`Spec(R)`. -/
private theorem primeSpectrum_completion_sum_surjective :
    Function.Surjective
      (Sum.elim
        (PrimeSpectrum.comap (algebraMap R RHat))
        (PrimeSpectrum.comap (algebraMap R Rf))) := by
  intro p
  by_cases hf : f ∈ p.asIdeal
  · -- On the closed part `V(f)`, lift through the quotient comparison with the completion.
    have hp_zero : p ∈ PrimeSpectrum.zeroLocus (principalIdeal f : Set R) := by
      exact (PrimeSpectrum.mem_zeroLocus p (principalIdeal f : Set R)).2 <| by
        simpa [principalIdeal] using (Ideal.span_singleton_le_iff_mem p.asIdeal).2 hf
    obtain ⟨q, hq⟩ :=
      exists_prime_over_zeroLocus_of_principalIdealQuotientMap_bijective
        (R := R) f hp_zero
    exact ⟨Sum.inl q, hq⟩
  · -- On the open part `D(f)`, use the localization-away homeomorphism.
    let p' : PrimeSpectrum Rf :=
      (primeSpectrum_localizationAway_homeomorph_D f).symm
        ⟨p, (PrimeSpectrum.mem_basicOpen f p).2 hf⟩
    refine ⟨Sum.inr p', ?_⟩
    have hp' :
        (primeSpectrum_localizationAway_homeomorph_D f p').1 = p := by
      simpa [p'] using congrArg Subtype.val
        ((primeSpectrum_localizationAway_homeomorph_D f).apply_symm_apply
          ⟨p, (PrimeSpectrum.mem_basicOpen f p).2 hf⟩)
    simpa [primeSpectrum_localizationAway_homeomorph_D_apply] using hp'

/-- Helper for Proposition 15.90.19: a prime ideal on the second factor gives a prime ideal of a
product ring. -/
private theorem ideal_isPrime_ideal_top_prod
    {A B : Type*} [CommRing A] [CommRing B] {J : Ideal B} [hJ : J.IsPrime] :
    ((⊤ : Ideal A).prod J).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    have hmem : ((1 : A), (1 : B)) ∈ ((⊤ : Ideal A).prod J : Ideal (A × B)) := by
      simpa [htop]
    have hone : (1 : B) ∈ J := (Ideal.mem_prod _ _).1 hmem |>.2
    exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem J hone isUnit_one)
  · intro x y hxy
    have hxy' : x.2 * y.2 ∈ J := (Ideal.mem_prod _ _).1 hxy |>.2
    rcases hJ.mem_or_mem hxy' with hx | hy
    · exact Or.inl <| by simpa [Ideal.mem_prod, hx]
    · exact Or.inr <| by simpa [Ideal.mem_prod, hy]

/-- Helper for Proposition 15.90.19: the product map `R → R^∧ × R_f` is faithfully flat. -/
theorem principalAdicCompletion_localization_product_faithfullyFlat [IsNoetherianRing R] :
    RingHom.FaithfullyFlat (algebraMap R (RHat × Rf)) := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  constructor
  · -- Flatness is inherited from the completion and localization factors.
    let _ : IsCoherentRing R := noetherianRing_isCoherentRing (R := R)
    let M : Fin 2 → Type u
      | 0 => RHat
      | 1 => Rf
    letI : ∀ i : Fin 2, AddCommGroup (M i)
      | ⟨0, _⟩ => inferInstance
      | ⟨1, _⟩ => inferInstance
    letI : ∀ i : Fin 2, Module R (M i)
      | ⟨0, _⟩ => inferInstance
      | ⟨1, _⟩ => inferInstance
    have hflatFactors : ∀ i : Fin 2, Module.Flat R (M i)
      | ⟨0, _⟩ =>
          (RingHom.flat_algebraMap_iff :
            (algebraMap R RHat).Flat ↔ Module.Flat R RHat).mp
            (adicCompletion_algebraMap_flat (R := R) (I := principalIdeal f))
      | ⟨1, _⟩ => inferInstance
    have hProductsFlat :=
      ((coherent_tfae_flat_products (R := R)).out 0 1).mp
        (show IsCoherentRing R from inferInstance)
    have hflatPi :
        Module.Flat R ((i : Fin 2) → M i) :=
      hProductsFlat (Fin 2) M hflatFactors
    let _ : Module.Flat R ((i : Fin 2) → M i) := hflatPi
    exact RingHom.flat_algebraMap_iff.mpr <|
      Module.Flat.of_linearEquiv (LinearEquiv.piFinTwo R M).symm
  · intro p
    obtain ⟨q, hq⟩ := primeSpectrum_completion_sum_surjective (R := R) f p
    cases q with
    | inl qhat =>
        let qprod : PrimeSpectrum (RHat × Rf) :=
          ⟨qhat.asIdeal.prod (⊤ : Ideal Rf), Ideal.isPrime_ideal_prod_top⟩
        refine ⟨qprod, ?_⟩
        have hqIdeal :
            Ideal.comap (algebraMap R RHat) qhat.asIdeal = p.asIdeal := by
          simpa using congrArg PrimeSpectrum.asIdeal hq
        ext r
        rw [← hqIdeal]
        simp [qprod, Ideal.mem_prod, Ideal.mem_comap]
    | inr qf =>
        let qprod : PrimeSpectrum (RHat × Rf) :=
          ⟨(⊤ : Ideal RHat).prod qf.asIdeal, ideal_isPrime_ideal_top_prod⟩
        refine ⟨qprod, ?_⟩
        have hqIdeal :
            Ideal.comap (algebraMap R Rf) qf.asIdeal = p.asIdeal := by
          simpa using congrArg PrimeSpectrum.asIdeal hq
        ext r
        rw [← hqIdeal]
        simp [qprod, Ideal.mem_prod, Ideal.mem_comap]

/-- Helper for Proposition 15.90.19: the completion factor of `R^∧ × R_f` acts through the first
projection on `R^∧`. -/
private instance completionFactor_productModule :
    Module (RHat × Rf) RHat :=
  Module.compHom RHat (RingHom.fst RHat Rf)

/-- Helper for Proposition 15.90.19: the localization factor of `R^∧ × R_f` acts through the
second projection on `R_f`. -/
private instance localizationFactor_productModule :
    Module (RHat × Rf) Rf :=
  Module.compHom Rf (RingHom.snd RHat Rf)

/-- Helper for Proposition 15.90.19: the completion factor action is compatible with the base
action of `R`. -/
private instance completionFactor_product_isScalarTower :
    IsScalarTower R (RHat × Rf) RHat :=
  IsScalarTower.of_compHom R (RHat × Rf) RHat

/-- Helper for Proposition 15.90.19: the localization factor action is compatible with the base
action of `R`. -/
private instance localizationFactor_product_isScalarTower :
    IsScalarTower R (RHat × Rf) Rf :=
  IsScalarTower.of_compHom R (RHat × Rf) Rf

/-- Helper for Proposition 15.90.19: rewrite base change along `R → R^∧ × R_f` as the product of
the completion and localization base changes. -/
private noncomputable def tensorProduct_completion_localization_product_equiv
    (M : Type u) [AddCommGroup M] [Module R M] :
    TensorProduct R (RHat × Rf) M ≃ₗ[RHat × Rf]
      (TensorProduct R RHat M × TensorProduct R Rf M) := by
  -- Route correction: the source proof runs over the faithfully flat cover ring `R^∧ × R_f`, so
  -- we make that linearity owner explicit before applying the product-tensor decomposition.
  simpa using (TensorProduct.prodLeft R (RHat × Rf) RHat Rf M)

/-- Helper for Proposition 15.90.19: the completion ring is flat over the Noetherian base ring. -/
private theorem principalAdicCompletion_flat [IsNoetherianRing R] :
    Module.Flat R RHat := by
  -- Proof comment: adic completion is flat over a coherent ring, and Noetherian rings are
  -- coherent, so the algebra-map flatness criterion applies directly to `R^∧`.
  let _ : IsCoherentRing R := noetherianRing_isCoherentRing (R := R)
  exact
    (RingHom.flat_algebraMap_iff :
      (algebraMap R RHat).Flat ↔ Module.Flat R RHat).mp
      (adicCompletion_algebraMap_flat (R := R) (I := principalIdeal f))

/-- Helper for Proposition 15.90.19: the completion quotient comparison already has exactly the
shape required by Theorem `15.90.18` once the principal ideal is normalized to `Ideal.span`. -/
private theorem completion_principalIdealQuotientMap_bijective_as_formalGlueing_hypothesis :
    Function.Bijective
      (Ideal.quotientMap
        (Ideal.map (algebraMap R RHat) (Ideal.span ({f} : Set R)))
        (algebraMap R RHat)
        Ideal.le_comap_map) := by
  have hmap :
      Ideal.map (algebraMap R RHat) (Ideal.span ({f} : Set R)) =
        principalIdeal (algebraMap R RHat f) := by
    -- Normalize the mapped singleton ideal once so the formal-glueing quotient owner matches the
    -- principal-ideal owner from the earlier quotient-bijectivity theorem.
    simp only [principalIdeal, Ideal.map_span, Set.image_singleton]
  have hquot :
      Ideal.quotientMap
          (Ideal.map (algebraMap R RHat) (Ideal.span ({f} : Set R)))
          (algebraMap R RHat)
          Ideal.le_comap_map =
        principalIdealQuotientMap (algebraMap R RHat) f rfl := by
    -- Proof comment: once the ideal owner is rewritten, both quotient maps are determined by their
    -- effect on quotient classes, so comparison on representatives closes the goal.
    apply Ideal.Quotient.ringHom_ext
    ext r
    rw [hmap]
    simp [principalIdealQuotientMap, Ideal.quotientMap_mk]
  rw [hquot]
  exact completion_principalIdealQuotientMap_bijective (R := R) f

/-- Helper for Proposition 15.90.19: the ambient completion formal-glueing functor is an
equivalence once the quotient-map owner is normalized. -/
private theorem principalAdicFormalGlueingAmbient_isEquivalence [IsNoetherianRing R] :
    Functor.IsEquivalence (formalGlueingSingleFunctor RHat f) := by
  let _ : Module.Flat R RHat := principalAdicCompletion_flat (R := R) f
  -- Proof comment: this is exactly Theorem `15.90.18` specialized to the completion map, using
  -- the owner-normalized quotient comparison proved just above.
  exact
    formalGlueingSingleFunctor_isEquivalence_of_flat_of_quotientMap_bijective
      (R := R) (S := RHat) f
      (completion_principalIdealQuotientMap_bijective_as_formalGlueing_hypothesis
        (R := R) f)

/-- The formal glueing functor on finitely generated `R`-modules obtained by restricting the
single-element formal glueing functor for the `f`-adic completion to the pullback
`Mod^{fg}_{R^∧} ×_{Mod^{fg}_{(R^∧)_f}} Mod^{fg}_{R_f}`. -/
noncomputable abbrev principalAdicFormalGlueingFGFunctor :
    FGModuleCat R ⥤ FGGlueCat where
  obj M :=
    let X := (formalGlueingSingleFunctor RHat f).obj M.obj
    CategoricalPullback.mk
      ⟨X.fst, principalAdicFormalGlueingSingleFunctor_fst_finite f M⟩
      ⟨X.snd, principalAdicFormalGlueingSingleFunctor_snd_finite f M⟩
      ((ModuleCat.isFG RHatf).isoMk X.iso)
  map g :=
    let φ := (formalGlueingSingleFunctor RHat f).map g.hom
    CategoricalPullback.Hom.mk
      ((ModuleCat.isFG RHat).homMk φ.fst)
      ((ModuleCat.isFG Rf).homMk φ.snd)
      (by
        apply ObjectProperty.hom_ext
        exact φ.w)
  map_id M := by
    ext <;> simp
  map_comp g h := by
    ext <;> simp

/-- Helper for Proposition 15.90.19: finite generation over the completion and the localization
combines to finite generation after tensoring with the product ring `R^∧ × R_f`. -/
private theorem tensorProduct_completion_localization_product_finite
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite RHat (TensorProduct R RHat M)]
    [Module.Finite Rf (TensorProduct R Rf M)] :
    Module.Finite (RHat × Rf) (TensorProduct R (RHat × Rf) M) := by
  let _ :
      Module.Finite (RHat × Rf)
        (TensorProduct R RHat M × TensorProduct R Rf M) := by
    infer_instance
  -- Proof comment: the product target is finitely generated by instance search, and the
  -- product-tensor equivalence transports that finite generation back to the cover tensor product.
  simpa using
    Module.Finite.equiv
      (tensorProduct_completion_localization_product_equiv (R := R) (f := f) M).symm

/-- Helper for Proposition 15.90.19: if the completion-side and localization-side components of
the ambient formal-glueing datum are finitely generated, then the original `R`-module is finitely
generated. -/
private theorem finite_of_formalGlueingSingleFunctor_components [IsNoetherianRing R]
    (M : ModuleCat R)
    [Module.Finite RHat (((formalGlueingSingleFunctor RHat f).obj M).fst)]
    [Module.Finite Rf (((formalGlueingSingleFunctor RHat f).obj M).snd)] :
    Module.Finite R M := by
  let _ :
      Module.Finite RHat ↑((ModuleCat.extendScalars (algebraMap R RHat)).obj M) := by
    simpa [formalGlueingSingleFunctor]
      using (inferInstance :
        Module.Finite RHat (((formalGlueingSingleFunctor RHat f).obj M).fst))
  let _ :
      Module.Finite Rf ↑((ModuleCat.extendScalars (algebraMap R Rf)).obj M) := by
    simpa [formalGlueingSingleFunctor]
      using (inferInstance :
        Module.Finite Rf (((formalGlueingSingleFunctor RHat f).obj M).snd))
  have hcompletion :
      Module.Finite RHat (TensorProduct R RHat M) := by
    -- Proof comment: rewrite the completion component of the ambient glueing datum to the usual
    -- tensor base-change model over `R^∧`.
    simpa using
      Module.Finite.equiv
        (moduleCatExtendScalarsTensorEquiv R RHat M)
  have hlocalization :
      Module.Finite Rf (TensorProduct R Rf M) := by
    -- Proof comment: the localization component has the same tensor-model description over `R_f`.
    simpa using
      Module.Finite.equiv
        (moduleCatExtendScalarsTensorEquiv R Rf M)
  let _ : Module.Finite RHat (TensorProduct R RHat M) := hcompletion
  let _ : Module.Finite Rf (TensorProduct R Rf M) := hlocalization
  let _ : Module.Finite (RHat × Rf) (TensorProduct R (RHat × Rf) ↑M) :=
    tensorProduct_completion_localization_product_finite (R := R) (f := f) ↑M
  let _ : Module.FaithfullyFlat R (RHat × Rf) :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      (principalAdicCompletion_localization_product_faithfullyFlat (R := R) f)
  -- Proof comment: faithfully flat descent along `R → R^∧ × R_f` reflects finite generation from
  -- the tensor base change back to the original module.
  simpa using
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat
      (RHat × Rf) (R := R) (M := M)

/-- Helper for Proposition 15.90.19: the restricted formal-glueing functor is full because the
ambient formal-glueing functor is full and the lift preserves finite generation on source and
target. -/
private theorem principalAdicFormalGlueingFGFunctor_full [IsNoetherianRing R] :
    (principalAdicFormalGlueingFGFunctor f).Full where
  map_surjective := by
    intro M N g
    let _ : Functor.IsEquivalence (formalGlueingSingleFunctor RHat f) :=
      principalAdicFormalGlueingAmbient_isEquivalence (R := R) f
    let φ :
        ((formalGlueingSingleFunctor RHat f).obj M.obj) ⟶
          ((formalGlueingSingleFunctor RHat f).obj N.obj) :=
      CategoricalPullback.Hom.mk g.fst.hom g.snd.hom <| by
        -- Proof comment: forget the finite-generation wrappers on the compatibility square before
        -- applying ambient fullness.
        simpa using congrArg (fun k => k.hom) g.w
    obtain ⟨h, hh⟩ :=
      (inferInstance : (formalGlueingSingleFunctor RHat f).Full).map_surjective φ
    refine ⟨(ModuleCat.isFG R).homMk h, ?_⟩
    -- Proof comment: after replacing the ambient image by the prescribed pullback morphism, both
    -- restricted morphisms are literally the same structured pullback morphism.
    cases g
    cases hh
    rfl

/-- Helper for Proposition 15.90.19: the restricted formal-glueing functor is faithful because
the ambient formal-glueing functor is faithful and equality in `FGModuleCat` is equality of the
underlying linear maps. -/
private theorem principalAdicFormalGlueingFGFunctor_faithful [IsNoetherianRing R] :
    (principalAdicFormalGlueingFGFunctor f).Faithful where
  map_injective := by
    intro M N g h hgh
    let _ : Functor.IsEquivalence (formalGlueingSingleFunctor RHat f) :=
      principalAdicFormalGlueingAmbient_isEquivalence (R := R) f
    have hambient :
        (formalGlueingSingleFunctor RHat f).map g.hom =
          (formalGlueingSingleFunctor RHat f).map h.hom := by
      -- Proof comment: forgetting finite generation turns the restricted equality into the ambient
      -- pullback equality verbatim.
      cases hgh
      rfl
    have hhom :
        g.hom = h.hom :=
      (inferInstance : (formalGlueingSingleFunctor RHat f).Faithful).map_injective hambient
    exact ObjectProperty.hom_ext (ModuleCat.isFG R) hhom

/-- Helper for Proposition 15.90.19: the restricted formal-glueing functor is essentially
surjective by taking the ambient preimage and then descending finite generation via
faithfully-flat descent. -/
private theorem principalAdicFormalGlueingFGFunctor_essSurj [IsNoetherianRing R] :
    (principalAdicFormalGlueingFGFunctor f).EssSurj := by
  let _ : Functor.IsEquivalence (formalGlueingSingleFunctor RHat f) :=
    principalAdicFormalGlueingAmbient_isEquivalence (R := R) f
  refine Functor.EssSurj.mk ?_
  intro X
  let XAmbient :
      CategoricalPullback
        (ModuleCat.extendScalars (algebraMap RHat RHatf))
        (ModuleCat.extendScalars (Localization.awayMap (algebraMap R RHat) f)) :=
    CategoricalPullback.mk X.fst.obj X.snd.obj
      { hom := X.iso.hom.hom
        inv := X.iso.inv.hom
        hom_inv_id := by
          exact congrArg (fun k => k.hom) X.iso.hom_inv_id
        inv_hom_id := by
          exact congrArg (fun k => k.hom) X.iso.inv_hom_id }
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := formalGlueingSingleFunctor RHat f) XAmbient
  have hcompletion :
      Module.Finite RHat (((formalGlueingSingleFunctor RHat f).obj M).fst) := by
    let _ : Module.Finite RHat X.fst.obj := inferInstance
    -- Proof comment: transport completion-side finite generation backward across the ambient
    -- comparison isomorphism.
    simpa [XAmbient] using Module.Finite.equiv (R := RHat) ((asIso e.hom.fst).toLinearEquiv.symm)
  have hlocalization :
      Module.Finite Rf (((formalGlueingSingleFunctor RHat f).obj M).snd) := by
    let _ : Module.Finite Rf X.snd.obj := inferInstance
    -- Proof comment: the localization-side finite witness transports back in the same way.
    simpa [XAmbient] using Module.Finite.equiv (R := Rf) ((asIso e.hom.snd).toLinearEquiv.symm)
  let _ : Module.Finite RHat (((formalGlueingSingleFunctor RHat f).obj M).fst) := hcompletion
  let _ : Module.Finite Rf (((formalGlueingSingleFunctor RHat f).obj M).snd) := hlocalization
  have hM : Module.Finite R M :=
    finite_of_formalGlueingSingleFunctor_components (R := R) (f := f) M
  let Mfg : FGModuleCat R := ⟨M, hM⟩
  let e₁ :
      ((principalAdicFormalGlueingFGFunctor f).obj Mfg).fst ≅ X.fst :=
    (ModuleCat.isFG RHat).isoMk (asIso e.hom.fst)
  let e₂ :
      ((principalAdicFormalGlueingFGFunctor f).obj Mfg).snd ≅ X.snd :=
    (ModuleCat.isFG Rf).isoMk (asIso e.hom.snd)
  refine ⟨Mfg, ⟨CategoricalPullback.mkIso e₁ e₂ ?_⟩⟩
  -- Proof comment: after repackaging the two ambient component isomorphisms inside the finitely
  -- generated full subcategories, the original ambient pullback compatibility is unchanged.
  apply ObjectProperty.hom_ext
  simpa [Mfg, XAmbient, e₁, e₂] using e.hom.w

-- Proof sketch: the completion map `R → R^∧` is flat for Noetherian `R` by
-- Lemma `10.97.2`, and the quotient map `R / fR → R^∧ / f R^∧` is bijective.
-- Theorem `15.90.18` therefore gives an equivalence for the ambient module categories. The source
-- and target finite-generation conditions are preserved and reflected by the completion and
-- localization functors, so the equivalence restricts to the pullback of the finitely generated
-- module categories.
-- Proof comment: the ambient equivalence from Theorem `15.90.18` and the faithfully flat descent
-- along `R → R^∧ × R_f` give the restriction to finitely generated modules. The remaining Lean
-- gap is to transfer essential surjectivity from the ambient pullback to the `FGModuleCat`
-- pullback using `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`.
/-- Proposition 15.90.19: if `R` is Noetherian and `R^∧` is the `f`-adic completion of `R`, then
the functor sending a finitely generated `R`-module `M` to its completion-localization glueing
datum `(M^∧, M_f, can)` defines an equivalence from `Mod^{fg}_R` to the fiber product of the
finitely generated module categories over `R^∧`, `(R^∧)_f`, and `R_f`. -/
theorem principalAdicFormalGlueingFGFunctor_isEquivalence [IsNoetherianRing R] :
    Functor.IsEquivalence (principalAdicFormalGlueingFGFunctor f) := by
  let _ : (principalAdicFormalGlueingFGFunctor f).Faithful :=
    principalAdicFormalGlueingFGFunctor_faithful (R := R) f
  let _ : (principalAdicFormalGlueingFGFunctor f).Full :=
    principalAdicFormalGlueingFGFunctor_full (R := R) f
  let _ : (principalAdicFormalGlueingFGFunctor f).EssSurj :=
    principalAdicFormalGlueingFGFunctor_essSurj (R := R) f
  -- Proof comment: the restricted functor is faithful, full, and essentially surjective, so the
  -- standard equivalence packaging applies.
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

end
