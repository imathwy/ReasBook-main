import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace Algebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']
variable [FinitePresentation R S] [Module.Flat R R']

/- 
The proof is organized pointwise.  The remaining mathematical bridges are exactly the localized
base-change comparisons for cotangent homology and Kähler differentials; once those are available,
the smooth-locus equality is a direct rewrite through `smoothLocus_eq_compl_support_inter`.
-/

/-- Helper for Chap10 Lemma 10 137 17: a flat map of rings induces a faithfully flat map on
local rings at any lying-over pair of prime ideals. -/
private lemma faithfullyFlatAtPrime_of_flat_liesOver
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime P) := by
  -- The localization map is local, so flatness upgrades to faithful flatness over local rings.
  have hLocal :
      IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime P)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom p P (algebraMap A B) Ideal.LiesOver.over
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Helper for Chap10 Lemma 10 137 17: localization of a tensor base change is subsingleton
exactly when the localized original module is subsingleton, provided the local base change is
faithfully flat. -/
private lemma localizedTensorBaseChange_subsingleton_iff
    {A : Type u} {B : Type v} {M : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]
    (q' : PrimeSpectrum B)
    [Module.FaithfullyFlat
      (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q').asIdeal)
      (Localization.AtPrime q'.asIdeal)] :
    Subsingleton (LocalizedModule.AtPrime q'.asIdeal (B ⊗[A] M)) ↔
      Subsingleton
        (LocalizedModule.AtPrime (PrimeSpectrum.comap (algebraMap A B) q').asIdeal M) := by
  -- Route correction: factor the repeated localization transport through the canonical
  -- `rankAtStalk_baseChange` tensor normal form, then use faithful-flat reflection there.
  let q : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q'
  let e :
      LocalizedModule.AtPrime q'.asIdeal (B ⊗[A] M) ≃ₗ[Localization.AtPrime q'.asIdeal]
        Localization.AtPrime q'.asIdeal ⊗[Localization.AtPrime q.asIdeal]
          LocalizedModule.AtPrime q.asIdeal M :=
    LocalizedModule.equivTensorProduct q'.asIdeal.primeCompl (B ⊗[A] M) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B
        (Localization.AtPrime q'.asIdeal) (Localization.AtPrime q'.asIdeal) M) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q'.asIdeal) (Localization.AtPrime q'.asIdeal) M).symm ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (Localization.AtPrime q'.asIdeal)
          (Localization.AtPrime q'.asIdeal))
        (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl M).symm)
  -- The equivalence turns the upstairs localization into tensoring the downstairs localization
  -- by the faithfully flat local ring map.
  rw [e.toEquiv.subsingleton_congr]
  exact Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right
    (Localization.AtPrime q.asIdeal) (Localization.AtPrime q'.asIdeal)

/-- Helper for Chap10 Lemma 10 137 17: for a finite localized module over a local ring, freeness
descends and ascends along the faithfully flat localized tensor base change. -/
private lemma localizedTensorBaseChange_free_iff_of_finite
    {A : Type u} {B : Type v} {M : Type w}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]
    (q' : PrimeSpectrum B)
    [Module.FaithfullyFlat
      (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q').asIdeal)
      (Localization.AtPrime q'.asIdeal)]
    [Module.Finite
      (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q').asIdeal)
      (LocalizedModule.AtPrime (PrimeSpectrum.comap (algebraMap A B) q').asIdeal M)] :
    Module.Free (Localization.AtPrime q'.asIdeal)
        (LocalizedModule.AtPrime q'.asIdeal (B ⊗[A] M)) ↔
      Module.Free
        (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q').asIdeal)
        (LocalizedModule.AtPrime (PrimeSpectrum.comap (algebraMap A B) q').asIdeal M) := by
  -- Use the same tensor normal form as above; the reverse direction is base-change of a free
  -- module, and the forward direction descends flatness then uses finite flat over local is free.
  let q : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q'
  let e :
      LocalizedModule.AtPrime q'.asIdeal (B ⊗[A] M) ≃ₗ[Localization.AtPrime q'.asIdeal]
        Localization.AtPrime q'.asIdeal ⊗[Localization.AtPrime q.asIdeal]
          LocalizedModule.AtPrime q.asIdeal M :=
    LocalizedModule.equivTensorProduct q'.asIdeal.primeCompl (B ⊗[A] M) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B
        (Localization.AtPrime q'.asIdeal) (Localization.AtPrime q'.asIdeal) M) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q'.asIdeal) (Localization.AtPrime q'.asIdeal) M).symm ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (Localization.AtPrime q'.asIdeal)
          (Localization.AtPrime q'.asIdeal))
        (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl M).symm)
  constructor
  · intro h
    haveI : Module.Free (Localization.AtPrime q'.asIdeal)
        (Localization.AtPrime q'.asIdeal ⊗[Localization.AtPrime q.asIdeal]
          LocalizedModule.AtPrime q.asIdeal M) :=
      Module.Free.of_equiv e
    haveI : Module.Flat (Localization.AtPrime q'.asIdeal)
        (Localization.AtPrime q'.asIdeal ⊗[Localization.AtPrime q.asIdeal]
          LocalizedModule.AtPrime q.asIdeal M) :=
      Module.Flat.of_free
    haveI : Module.Flat (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal M) :=
      Module.Flat.of_flat_tensorProduct (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal M) (Localization.AtPrime q'.asIdeal)
    exact Module.free_of_flat_of_isLocalRing
  · intro h
    haveI : Module.Free (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal M) := h
    haveI : Module.Free (Localization.AtPrime q'.asIdeal)
        (Localization.AtPrime q'.asIdeal ⊗[Localization.AtPrime q.asIdeal]
          LocalizedModule.AtPrime q.asIdeal M) :=
      inferInstance
    exact Module.Free.of_equiv e.symm

omit [FinitePresentation R S] in
/-- Helper for Chap10 Lemma 10 137 17: the lifted base-change map on first cotangent homology
over `R' ⊗[R] S` is bijective before localization. -/
private lemma h1CotangentTensorBaseChangeMap_bijective :
    Function.Bijective
      ((LinearMap.liftBaseChange (R' ⊗[R] S)
        (H1Cotangent.map R R' S (R' ⊗[R] S))) :
          (R' ⊗[R] S) ⊗[S] H1Cotangent R S →ₗ[R' ⊗[R] S]
            H1Cotangent R' (R' ⊗[R] S)) := by
  -- Route correction: compare the `R' ⊗[R] S`-linear lifted map before localization with
  -- mathlib's flat `R'`-linear H1 base-change equivalence through the pushout tensor normal form.
  let e : (R' ⊗[R] S) ⊗[S] H1Cotangent R S ≃ₗ[R']
      R' ⊗[R] H1Cotangent R S :=
    Algebra.IsPushout.cancelBaseChange R R' S (R' ⊗[R] S) (H1Cotangent R S)
  let fB : (R' ⊗[R] S) ⊗[S] H1Cotangent R S →ₗ[R' ⊗[R] S]
      H1Cotangent R' (R' ⊗[R] S) :=
    LinearMap.liftBaseChange (R' ⊗[R] S) (H1Cotangent.map R R' S (R' ⊗[R] S))
  let f : (R' ⊗[R] S) ⊗[S] H1Cotangent R S →ₗ[R']
      H1Cotangent R' (R' ⊗[R] S) :=
    fB.restrictScalars R'
  -- The comparison is checked on pure tensors; the only scalar bridge is the tower action
  -- from `R'` through the tensor-product algebra.
  have hcomp :
      f.comp e.symm.toLinearMap = (Algebra.tensorH1CotangentOfFlat R S R').toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, f,
      LinearMap.coe_restrictScalars, fB, e, Algebra.IsPushout.cancelBaseChange_symm_tmul,
      LinearMap.liftBaseChange_tmul, Algebra.tensorH1CotangentOfFlat_tmul]
    exact IsScalarTower.algebraMap_smul (R' ⊗[R] S) r
      ((H1Cotangent.map R R' S (R' ⊗[R] S)) x)
  -- Bijectivity follows because both the pushout tensor normal form and flat H1 base change are
  -- linear equivalences.
  have hcompBij : Function.Bijective (f.comp e.symm.toLinearMap) := by
    simpa [hcomp] using (Algebra.tensorH1CotangentOfFlat R S R').bijective
  exact (Function.Bijective.of_comp_iff (f : _ → _) e.symm.bijective).mp hcompBij

omit [FinitePresentation R S] in
/-- Helper for Chap10 Lemma 10 137 17: localized first cotangent homology is zero after the
flat base change exactly when it is zero before base change at the contracted prime. -/
private lemma localizedH1Cotangent_subsingleton_baseChange_iff
    (q' : PrimeSpectrum (R' ⊗[R] S)) :
    Subsingleton (LocalizedModule.AtPrime q'.asIdeal (H1Cotangent R' (R' ⊗[R] S))) ↔
      Subsingleton (LocalizedModule.AtPrime
        (PrimeSpectrum.comap includeRight.toRingHom q').asIdeal (H1Cotangent R S)) := by
  -- First make the local map `S_q → (R' ⊗[R] S)_{q'}` faithfully flat at the lying-over pair.
  haveI : Module.Flat S (S ⊗[R] R') := Module.Flat.baseChange R S R'
  haveI : Module.Flat S (R' ⊗[R] S) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.commRight R S R').symm.toLinearEquiv
  let q : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S (R' ⊗[R] S)) q'
  haveI : q'.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  haveI : Module.FaithfullyFlat (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q'.asIdeal) :=
    faithfullyFlatAtPrime_of_flat_liesOver (p := q.asIdeal) (P := q'.asIdeal)
  -- Localize the bijective lifted H1 map, giving an equivalence between the upstairs H1 module
  -- and the localized tensor base-change module.
  let fB : (R' ⊗[R] S) ⊗[S] H1Cotangent R S →ₗ[R' ⊗[R] S]
      H1Cotangent R' (R' ⊗[R] S) :=
    LinearMap.liftBaseChange (R' ⊗[R] S) (H1Cotangent.map R R' S (R' ⊗[R] S))
  let eLoc :
      LocalizedModule.AtPrime q'.asIdeal ((R' ⊗[R] S) ⊗[S] H1Cotangent R S) ≃ₗ[
        Localization.AtPrime q'.asIdeal]
        LocalizedModule.AtPrime q'.asIdeal (H1Cotangent R' (R' ⊗[R] S)) :=
    LinearEquiv.ofBijective (LocalizedModule.map q'.asIdeal.primeCompl fB)
      ⟨LocalizedModule.map_injective q'.asIdeal.primeCompl fB
          h1CotangentTensorBaseChangeMap_bijective.injective,
        LocalizedModule.map_surjective q'.asIdeal.primeCompl fB
          h1CotangentTensorBaseChangeMap_bijective.surjective⟩
  have hTransport :
      Subsingleton (LocalizedModule.AtPrime q'.asIdeal (H1Cotangent R' (R' ⊗[R] S))) ↔
        Subsingleton
          (LocalizedModule.AtPrime q'.asIdeal ((R' ⊗[R] S) ⊗[S] H1Cotangent R S)) := by
    rw [eLoc.toEquiv.subsingleton_congr]
  -- The remaining equivalence is exactly the generic faithfully-flat localized tensor descent.
  have hBase :=
    localizedTensorBaseChange_subsingleton_iff (A := S) (B := R' ⊗[R] S)
      (M := H1Cotangent R S) q'
  simpa [q, RingHom.algebraMap_toAlgebra] using hTransport.trans hBase

/-- Helper for Chap10 Lemma 10 137 17: localized Kähler differentials are free after the flat
base change exactly when they are free before base change at the contracted prime. -/
private lemma localizedKaehler_free_baseChange_iff
    (q' : PrimeSpectrum (R' ⊗[R] S)) :
    Module.Free (Localization.AtPrime q'.asIdeal)
        (LocalizedModule.AtPrime q'.asIdeal Ω[R' ⊗[R] S⁄R']) ↔
      Module.Free (Localization.AtPrime (PrimeSpectrum.comap includeRight.toRingHom q').asIdeal)
        (LocalizedModule.AtPrime
          (PrimeSpectrum.comap includeRight.toRingHom q').asIdeal Ω[S⁄R]) := by
  -- First install the `S`-algebra structure on the tensor product and the faithful-flat local
  -- map at the lying-over pair of primes.
  letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  letI : Module S (R' ⊗[R] S) := Algebra.toModule
  haveI : Module.Flat S (S ⊗[R] R') := Module.Flat.baseChange R S R'
  haveI : Module.Flat S (R' ⊗[R] S) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.commRight R S R').symm.toLinearEquiv
  let q : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S (R' ⊗[R] S)) q'
  haveI : q'.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  haveI : Module.FaithfullyFlat (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q'.asIdeal) :=
    faithfullyFlatAtPrime_of_flat_liesOver (p := q.asIdeal) (P := q'.asIdeal)
  haveI : Module.Finite (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal Ω[S⁄R]) :=
    inferInstance
  -- Localize the Kähler base-change equivalence and use it to replace the upstairs
  -- differentials by the generic tensor base-change module.
  let e : (R' ⊗[R] S) ⊗[S] Ω[S⁄R] ≃ₗ[R' ⊗[R] S] Ω[R' ⊗[R] S⁄R'] :=
    KaehlerDifferential.tensorKaehlerEquiv R R' S (R' ⊗[R] S)
  let eLoc :
      LocalizedModule.AtPrime q'.asIdeal ((R' ⊗[R] S) ⊗[S] Ω[S⁄R]) ≃ₗ[
        Localization.AtPrime q'.asIdeal]
        LocalizedModule.AtPrime q'.asIdeal Ω[R' ⊗[R] S⁄R'] :=
    LinearEquiv.ofBijective (LocalizedModule.map q'.asIdeal.primeCompl e.toLinearMap)
      ⟨LocalizedModule.map_injective q'.asIdeal.primeCompl e.toLinearMap e.injective,
        LocalizedModule.map_surjective q'.asIdeal.primeCompl e.toLinearMap e.surjective⟩
  have hTransport :
      Module.Free (Localization.AtPrime q'.asIdeal)
          (LocalizedModule.AtPrime q'.asIdeal Ω[R' ⊗[R] S⁄R']) ↔
        Module.Free (Localization.AtPrime q'.asIdeal)
          (LocalizedModule.AtPrime q'.asIdeal ((R' ⊗[R] S) ⊗[S] Ω[S⁄R])) := by
    constructor
    · intro h
      haveI : Module.Free (Localization.AtPrime q'.asIdeal)
          (LocalizedModule.AtPrime q'.asIdeal Ω[R' ⊗[R] S⁄R']) := h
      exact Module.Free.of_equiv eLoc.symm
    · intro h
      haveI : Module.Free (Localization.AtPrime q'.asIdeal)
          (LocalizedModule.AtPrime q'.asIdeal ((R' ⊗[R] S) ⊗[S] Ω[S⁄R])) := h
      exact Module.Free.of_equiv eLoc
  -- The remaining equivalence is the generic finite faithfully-flat tensor descent lemma.
  have hBase :=
    localizedTensorBaseChange_free_iff_of_finite (A := S) (B := R' ⊗[R] S)
      (M := Ω[S⁄R]) q'
  simpa [q, RingHom.algebraMap_toAlgebra] using hTransport.trans hBase

/-- Helper for Chap10 Lemma 10 137 17: membership in the downstairs smooth locus is equivalent
to membership in the upstairs smooth locus at a prime of the tensor product. -/
private lemma mem_smoothLocus_baseChange_iff
    (q' : PrimeSpectrum (R' ⊗[R] S)) :
    PrimeSpectrum.comap includeRight.toRingHom q' ∈ smoothLocus R S ↔
      q' ∈ smoothLocus R' (R' ⊗[R] S) := by
  -- First rewrite the downstairs smoothness condition into the localized `H¹` and `Ω` criterion.
  have hDown :
      PrimeSpectrum.comap includeRight.toRingHom q' ∈ smoothLocus R S ↔
        Subsingleton (LocalizedModule.AtPrime
          (PrimeSpectrum.comap includeRight.toRingHom q').asIdeal (H1Cotangent R S)) ∧
          Module.Free
            (Localization.AtPrime (PrimeSpectrum.comap includeRight.toRingHom q').asIdeal)
            (LocalizedModule.AtPrime
              (PrimeSpectrum.comap includeRight.toRingHom q').asIdeal Ω[S⁄R]) := by
    have hcriterion :
        PrimeSpectrum.comap includeRight.toRingHom q' ∈ smoothLocus R S ↔
          PrimeSpectrum.comap includeRight.toRingHom q' ∈
            (Module.support S (H1Cotangent R S))ᶜ ∩ Module.freeLocus S Ω[S⁄R] := by
      simpa using
        congrArg (fun U : Set (PrimeSpectrum S) =>
          PrimeSpectrum.comap includeRight.toRingHom q' ∈ U)
          (smoothLocus_eq_compl_support_inter (R := R) (A := S))
    simpa only [Set.mem_inter_iff, Set.mem_compl_iff, Module.notMem_support_iff,
      Module.mem_freeLocus] using hcriterion
  -- The same criterion upstairs leaves exactly the two base-change bridge lemmas to apply.
  have hUp :
      q' ∈ smoothLocus R' (R' ⊗[R] S) ↔
        Subsingleton (LocalizedModule.AtPrime q'.asIdeal (H1Cotangent R' (R' ⊗[R] S))) ∧
          Module.Free (Localization.AtPrime q'.asIdeal)
            (LocalizedModule.AtPrime q'.asIdeal Ω[R' ⊗[R] S⁄R']) := by
    have hcriterion :
        q' ∈ smoothLocus R' (R' ⊗[R] S) ↔
          q' ∈ (Module.support (R' ⊗[R] S) (H1Cotangent R' (R' ⊗[R] S)))ᶜ ∩
            Module.freeLocus (R' ⊗[R] S) Ω[R' ⊗[R] S⁄R'] := by
      simpa using
        congrArg (fun U : Set (PrimeSpectrum (R' ⊗[R] S)) => q' ∈ U)
          (smoothLocus_eq_compl_support_inter (R := R') (A := R' ⊗[R] S))
    simpa only [Set.mem_inter_iff, Set.mem_compl_iff, Module.notMem_support_iff,
      Module.mem_freeLocus] using hcriterion
  -- With both loci in the same normal form, the two bridge equivalences finish the pointwise iff.
  rw [hDown, hUp]
  exact and_congr
    (localizedH1Cotangent_subsingleton_baseChange_iff (R := R) (S := S) (R' := R') q').symm
    (localizedKaehler_free_baseChange_iff (R := R) (S := S) (R' := R') q').symm

/- 
Domain-style sampling:
- primary domain: base change on `PrimeSpectrum` for the canonical smooth locus of a finitely
  presented ring map;
- sampled owner declarations of the same kind:
  `Algebra.smoothLocus`,
  `Algebra.smoothLocus_eq_compl_support_inter`,
  `Algebra.smoothLocus_comap_of_isLocalization`,
  `relativeDimensionAt_le_preimage_eq_baseChange`,
  `cohenMacaulayFiberLocus_baseChange_preimage_eq`;
- best owner abstraction: the canonical owner is `smoothLocus R S`; this file should state the
  base-change result directly for that owner rather than through a parallel set-builder or local
  wrapper;
- primitive data: the finitely presented map `R → S`, the flat base change `R → R'`, and the
  induced map `Spec(R' ⊗[R] S) → Spec(S)`;
- derived API: the inverse-image equality for the smooth locus under `PrimeSpectrum.comap
  includeRight.toRingHom`.

Source/core/bridge triage:
* `source-facing`: the smooth locus of a ring map;
* `core/canonical`: `Algebra.smoothLocus` and its local description via `IsSmoothAt`;
* `bridge/view`: inverse image along `PrimeSpectrum.comap includeRight.toRingHom`.
-/

-- Proof sketch: identify `smoothLocus` with the locus where the localized cotangent homology
-- vanishes and the localized Kähler differentials are free. Flat base change gives the forward
-- implication by `Algebra.tensorH1CotangentOfFlat` and preservation of freeness/projectivity.
-- For the reverse implication, localize at a prime `q'` of `R' ⊗[R] S`; since `S_q → S'_{q'}`
-- is faithfully flat, vanishing of localized `H¹(L)` descends along faithful flatness, and
-- finite-projectivity of localized Kähler differentials descends by Lemma `10.78.6`. Then apply
-- the local smoothness criterion of Lemma `10.137.11`.
/-- Chap10 Lemma 10 137 17: for a finitely presented ring map `R → S` and a flat base change `R → R'`,
if `S' = R' ⊗[R] S`, then the smooth locus of `R' → S'` is the inverse image of the smooth locus
of `R → S` under the induced map `Spec(S') → Spec(S)`. -/
@[stacks 00TG]
theorem smoothLocus_baseChange_preimage_eq :
    PrimeSpectrum.comap includeRight.toRingHom ⁻¹'
        smoothLocus R S =
      smoothLocus R' (R' ⊗[R] S) := by
  -- Extensionality reduces the set equality to the pointwise smoothness comparison above.
  ext q'
  exact mem_smoothLocus_baseChange_iff (R := R) (S := S) (R' := R') q'

end Algebra
