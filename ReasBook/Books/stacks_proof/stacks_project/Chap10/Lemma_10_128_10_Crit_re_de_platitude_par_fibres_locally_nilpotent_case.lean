import stacks_proof.stacks_project.Chap10.Definition_10_32_1
import stacks_proof.stacks_project.Chap10.Definition_10_54_1
import stacks_proof.stacks_project.Chap10.Definition_10_112_5
import stacks_proof.stacks_project.Chap10.Lemma_10_40_6
import stacks_proof.stacks_project.Chap10.Lemma_10_39_18
import stacks_proof.stacks_project.Chap10.Lemma_10_128_9
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped TensorProduct

universe u v w x y

section

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable {I : Ideal R}
variable [AddCommGroup M] [Module S' M]
variable [Algebra.FiniteType R S] [Algebra.FinitePresentation R S'] [Module.FinitePresentation S' M]

local notation "IS" => Ideal.map (algebraMap R S) I
local notation "FiberRing" => S ⧸ IS
local notation "FiberModule" => FiberRing ⊗[S] RestrictScalars S S' M

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
localizing an `A`-module and tensoring over the base ring commute. -/
private noncomputable def localizedTensorRightEquiv
    {R : Type*} {A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (T : Submonoid A) {X : Type*} [AddCommMonoid X] [Module R X] [Module A X]
    [IsScalarTower R A X] (Q : Type*) [AddCommMonoid Q] [Module R Q] :
    LocalizedModule T X ⊗[R] Q ≃ₗ[A] LocalizedModule T (X ⊗[R] Q) :=
  IsLocalizedModule.linearEquiv T
    (TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
    (LocalizedModule.mkLinearMap T (X ⊗[R] Q))

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the localized tensor map is the tensor map on the localized module. -/
private lemma localizedLTensorMap_eq
    {R : Type*} {A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (T : Submonoid A) {X : Type*} [AddCommMonoid X] [Module R X] [Module A X]
    [IsScalarTower R A X] {Q Q' : Type*} [AddCommMonoid Q] [AddCommMonoid Q']
    [Module R Q] [Module R Q'] (f : Q →ₗ[R] Q') :
    IsLocalizedModule.map T
        (TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
        (TensorProduct.AlgebraTensorModule.rTensor R Q' (LocalizedModule.mkLinearMap T X))
        (TensorProduct.AlgebraTensorModule.lTensor A X f) =
      TensorProduct.AlgebraTensorModule.lTensor A (LocalizedModule T X) f := by
  -- Proof progression: specialize the owner theorem to the concrete localization model.
  simpa using
    (IsLocalizedModule.map_lTensor (S := T) (R := R) (A := A) (M := X)
      (M' := LocalizedModule T X) (N := Q) (P := Q')
      (f := f) (g := LocalizedModule.mkLinearMap T X))

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the tensor-localization comparison intertwines localized tensor maps with tensor maps on the
localized module. -/
private lemma localizedLTensorIntertwines
    {R : Type*} {A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (T : Submonoid A) {X : Type*} [AddCommMonoid X] [Module R X] [Module A X]
    [IsScalarTower R A X] {Q Q' : Type*} [AddCommMonoid Q] [AddCommMonoid Q']
    [Module R Q] [Module R Q'] (f : Q →ₗ[R] Q') :
    ((LocalizedModule.map T (TensorProduct.AlgebraTensorModule.lTensor A X f)).restrictScalars A).comp
        (localizedTensorRightEquiv (R := R) (A := A) T Q).toLinearMap =
      (localizedTensorRightEquiv (R := R) (A := A) T Q').toLinearMap.comp
        (TensorProduct.AlgebraTensorModule.lTensor A (LocalizedModule T X) f) := by
  let eQ := localizedTensorRightEquiv (R := R) (A := A) (X := X) T Q
  let eQ' := localizedTensorRightEquiv (R := R) (A := A) (X := X) T Q'
  have hlocalized :
      IsLocalizedModule.map T
          (TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
          (TensorProduct.AlgebraTensorModule.rTensor R Q' (LocalizedModule.mkLinearMap T X))
          (TensorProduct.AlgebraTensorModule.lTensor A X f) =
        TensorProduct.AlgebraTensorModule.lTensor A (LocalizedModule T X) f :=
    localizedLTensorMap_eq (R := R) (A := A) (T := T) (X := X) f
  have hmap :
      (LocalizedModule.map T (TensorProduct.AlgebraTensorModule.lTensor A X f)).restrictScalars A =
        (eQ'.toLinearMap.comp
          (TensorProduct.AlgebraTensorModule.lTensor A (LocalizedModule T X) f)).comp
          eQ.symm.toLinearMap := by
    -- Proof progression: rewrite the localized map through the canonical localized-module
    -- comparison, then replace the middle map by `localizedLTensorMap_eq`.
    rw [LocalizedModule.restrictScalars_map_eq (R := A) (S := T)
      (g₁ := TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
      (g₂ := TensorProduct.AlgebraTensorModule.rTensor R Q' (LocalizedModule.mkLinearMap T X))
      (l := TensorProduct.AlgebraTensorModule.lTensor A X f)]
    rw [hlocalized]
    simpa [eQ, eQ', localizedTensorRightEquiv, IsLocalizedModule.linearEquiv,
      IsLocalizedModule.iso_localizedModule_eq_refl, LinearMap.comp_assoc]
  -- Proof progression: postcompose by `eQ` so the inverse comparison cancels.
  calc
    ((LocalizedModule.map T (TensorProduct.AlgebraTensorModule.lTensor A X f)).restrictScalars A).comp
        eQ.toLinearMap =
        (((eQ'.toLinearMap.comp
            (TensorProduct.AlgebraTensorModule.lTensor A (LocalizedModule T X) f)).comp
              eQ.symm.toLinearMap).comp eQ.toLinearMap) := by
            rw [hmap]
    _ = eQ'.toLinearMap.comp
        (TensorProduct.AlgebraTensorModule.lTensor A (LocalizedModule T X) f) := by
      ext z
      simp [LinearMap.comp_assoc]

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
injectivity after localizing a tensor map is equivalent to injectivity after tensoring with the
localized module. -/
private lemma localizedLTensor_injective_iff
    {R : Type*} {A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (T : Submonoid A) {X : Type*} [AddCommMonoid X] [Module R X] [Module A X]
    [IsScalarTower R A X] {Q Q' : Type*} [AddCommMonoid Q] [AddCommMonoid Q']
    [Module R Q] [Module R Q'] (f : Q →ₗ[R] Q') :
    Function.Injective (LocalizedModule.map T (TensorProduct.AlgebraTensorModule.lTensor A X f)) ↔
      Function.Injective (TensorProduct.AlgebraTensorModule.lTensor A (LocalizedModule T X) f) := by
  have hiff :=
    (IsLocalizedModule.map_injective_iff_localizedModuleMap_injective
      (S := T)
      (g₁ := TensorProduct.AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
      (g₂ := TensorProduct.AlgebraTensorModule.rTensor R Q' (LocalizedModule.mkLinearMap T X))
      (l := TensorProduct.AlgebraTensorModule.lTensor A X f)).symm
  rw [localizedLTensorMap_eq (R := R) (A := A) (T := T) (X := X) (f := f)] at hiff
  exact hiff

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
localizing an `A`-module preserves flatness over the base ring `R`. -/
private lemma flat_localizedModule_of_flat_over_base
    {R : Type*} {A : Type*} {X : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommMonoid X] [Module R X] [Module A X] [IsScalarTower R A X]
    (T : Submonoid A) (hX : Module.Flat R X) :
    Module.Flat R (LocalizedModule T X) := by
  rw [Module.Flat.iff_lTensor_injectiveₛ] at hX ⊢
  intro Q _ _ N
  have hTensor : Function.Injective (N.subtype.lTensor X) := hX N
  have hTensorA : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor A X N.subtype) := by
    simpa [TensorProduct.AlgebraTensorModule.coe_lTensor] using hTensor
  have hLocalized :
      Function.Injective
        (LocalizedModule.map T (TensorProduct.AlgebraTensorModule.lTensor A X N.subtype)) :=
    LocalizedModule.map_injective T
      (TensorProduct.AlgebraTensorModule.lTensor A X N.subtype) hTensorA
  have hLocalizedTensor :=
    (localizedLTensor_injective_iff (R := R) (A := A) T (X := X) N.subtype).mp hLocalized
  -- Proof progression: the submodule tensor-injectivity criterion is preserved by the localized
  -- tensor comparison.
  simpa [TensorProduct.AlgebraTensorModule.coe_lTensor] using hLocalizedTensor

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
if a module is flat over `R`, then its localization at a prime of an `R`-algebra is flat over the
localized base ring at the contracted prime. -/
private lemma flat_localizedModuleAtPrime_over_under_of_flat
    {R : Type*} {A : Type*} {X : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommMonoid X] [Module R X] [Module A X] [IsScalarTower R A X]
    (hX : Module.Flat R X) (q : PrimeSpectrum A) :
    Module.Flat (Localization.AtPrime (q.asIdeal.under R))
      (LocalizedModule.AtPrime q.asIdeal X) := by
  letI : Module (Localization.AtPrime (q.asIdeal.under R)) (LocalizedModule.AtPrime q.asIdeal X) :=
    Module.compHom (LocalizedModule.AtPrime q.asIdeal X)
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl)
  letI :
      IsScalarTower R (Localization.AtPrime (q.asIdeal.under R))
        (LocalizedModule.AtPrime q.asIdeal X) :=
      inferInstance
  have hLocalizedR : Module.Flat R (LocalizedModule.AtPrime q.asIdeal X) :=
    flat_localizedModule_of_flat_over_base (R := R) (A := A) q.asIdeal.primeCompl hX
  -- Proof progression: convert `R`-flatness of the localized module to flatness over
  -- `R_(q ∩ R)`.
  exact
    (Module.flat_iff_of_isLocalization
      (Localization.AtPrime (q.asIdeal.under R)) (q.asIdeal.under R).primeCompl
      (M := LocalizedModule.AtPrime q.asIdeal X)).mpr hLocalizedR

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
flatness over `R` descends from maximal localizations over the contracted base primes. -/
private lemma flat_of_flat_localizedModuleAtMaximal_over_under
    {R : Type*} {A : Type*} {X : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommMonoid X] [Module R X] [Module A X] [IsScalarTower R A X]
    (h :
      ∀ m : MaximalSpectrum A,
        Module.Flat (Localization.AtPrime (m.asIdeal.under R))
          (LocalizedModule.AtPrime m.asIdeal X)) :
    Module.Flat R X := by
  apply Module.flat_of_isLocalized_maximal
    (R := R) (S := A) (M := X)
    (Mₚ := fun P _ ↦ LocalizedModule.AtPrime P X)
    (f := fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl X)
  intro P hP
  letI : Module (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime P X) :=
    Module.compHom (LocalizedModule.AtPrime P X)
      (Localization.localRingHom (P.under R) P (algebraMap R A) rfl)
  letI :
      IsScalarTower R (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime P X) :=
      inferInstance
  have hPflat :
      Module.Flat (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime P X) :=
    h ⟨P, hP⟩
  -- Proof progression: each maximal-local hypothesis is an `R`-flat localized module.
  exact
    (Module.flat_iff_of_isLocalization
      (Localization.AtPrime (P.under R)) (P.under R).primeCompl
      (M := LocalizedModule.AtPrime P X)).mp hPflat

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
essential finite presentation descends when the source ring is localized. -/
private lemma essFinitePresentation_of_sourceLocalization
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (N : Submonoid A) [IsLocalization N B]
    (hAC : Algebra.EssFinitePresentation A C) :
    Algebra.EssFinitePresentation B C := by
  have hlocC : IsLocalization (Algebra.algebraMapSubmonoid C N) C := by
    -- Proof progression: denominators inverted in the localized source map to units in `C`.
    refine IsLocalization.at_units (Algebra.algebraMapSubmonoid C N) ?_
    rintro x ⟨n, hn, rfl⟩
    simpa [IsScalarTower.algebraMap_apply A B C] using
      (IsLocalization.map_units B ⟨n, hn⟩).map (algebraMap B C)
  letI : IsLocalization (Algebra.algebraMapSubmonoid C N) C := hlocC
  letI : Algebra.IsPushout A C B C := Algebra.isPushout_of_isLocalization N B C C
  have hbaseChange : Algebra.EssFinitePresentation B (B ⊗[A] C) := by
    -- Proof progression: base-change the essentially finitely presented `A`-algebra to `B`.
    letI : Algebra.EssFinitePresentation A C := hAC
    infer_instance
  letI : Algebra.EssFinitePresentation B (B ⊗[A] C) := hbaseChange
  let eRing : (B ⊗[A] C) ≃+* C :=
    (Algebra.TensorProduct.commRight A B C).toRingEquiv.trans
      (Algebra.IsPushout.equiv A C B C).toRingEquiv
  have hcompat :
      ∀ b : B, eRing (algebraMap B (B ⊗[A] C) b) = algebraMap B C b := by
    -- Proof progression: the pushout equivalence computes as the original localized map on `B`.
    intro b
    dsimp [eRing]
    rw [Algebra.IsPushout.equiv_tmul]
    simp
  let eAlg : (B ⊗[A] C) ≃ₐ[B] C := AlgEquiv.ofRingEquiv (R := B) (f := eRing) hcompat
  -- Proof progression: transport the base-changed presentation across the pushout equivalence.
  exact Algebra.EssFinitePresentation.equiv (R := B) (S := B ⊗[A] C) (T := C) eAlg

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the localization of `S'` at a prime is essentially finitely presented over the corresponding
localization of `R`. -/
private lemma localizedTopEssFinitePresentationAtPrime
    (q' : PrimeSpectrum S') :
    Algebra.EssFinitePresentation (Localization.AtPrime (q'.asIdeal.under R))
      (Localization.AtPrime q'.asIdeal) := by
  let p : Ideal R := q'.asIdeal.under R
  let Rq := Localization.AtPrime p
  let Tq := Localization.AtPrime q'.asIdeal
  letI : q'.asIdeal.LiesOver p := by
    dsimp [p]
    infer_instance
  have hRTq : Algebra.EssFinitePresentation R Tq := by
    -- Proof progression: first localize the finitely presented `R`-algebra `S'` at `q'`.
    exact Algebra.EssFinitePresentation.of_isLocalization
      (R := R) (S := Tq) (P := S') q'.asIdeal.primeCompl
  -- Proof progression: then descend along the source localization `R → R_(q'∩R)`.
  exact essFinitePresentation_of_sourceLocalization
    (A := R) (B := Rq) (C := Tq) p.primeCompl hRTq

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
relative flatness over `R` can be checked after localizing at every prime of the `R`-algebra. -/
private theorem flat_iff_flat_localizedModuleAtPrime_over_under
    {R : Type*} {A : Type*} {X : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommMonoid X] [Module R X] [Module A X] [IsScalarTower R A X] :
    Module.Flat R X ↔
      ∀ q : PrimeSpectrum A,
        Module.Flat (Localization.AtPrime (q.asIdeal.under R))
          (LocalizedModule.AtPrime q.asIdeal X) := by
  constructor
  · intro hX q
    exact flat_localizedModuleAtPrime_over_under_of_flat (R := R) (A := A) hX q
  · intro hPrime
    exact flat_of_flat_localizedModuleAtMaximal_over_under (R := R) (A := A)
      (X := X) fun m ↦ by
        simpa using hPrime m.toPrimeSpectrum

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the localized fiber of a nontrivial residue-field fiber is nontrivial. -/
private theorem localizedModuleAtPrime_tensor_residueField_nontrivial
    {A : Type*} {X : Type*} [CommRing A]
    [AddCommGroup X] [Module A X]
    (q : PrimeSpectrum A)
    (hq : Nontrivial (X ⊗[A] q.asIdeal.ResidueField)) :
    Nontrivial
      (LocalizedModule.AtPrime q.asIdeal X ⊗[Localization.AtPrime q.asIdeal]
        q.asIdeal.ResidueField) := by
  let Aq := Localization.AtPrime q.asIdeal
  let Xq := LocalizedModule.AtPrime q.asIdeal X
  let K := q.asIdeal.ResidueField
  have hleft : Nontrivial (K ⊗[A] X) := by
    exact (TensorProduct.comm A K X).nontrivial_congr.mpr hq
  have hcancel : Nontrivial (K ⊗[Aq] (Aq ⊗[A] X)) := by
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange A Aq K K X).nontrivial_congr.mpr hleft
  have hcomm : Nontrivial ((Aq ⊗[A] X) ⊗[Aq] K) := by
    exact (TensorProduct.comm Aq (Aq ⊗[A] X) K).nontrivial_congr.mpr hcancel
  let eTensor :
      Xq ⊗[Aq] K ≃ₗ[Aq] (Aq ⊗[A] X) ⊗[Aq] K :=
    TensorProduct.congr
      (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl X)
      (LinearEquiv.refl Aq K)
  -- Proof progression: replace the localized module by its tensor-product model.
  exact eTensor.nontrivial_congr.mpr hcomm

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
over a local ring, tensoring with the residue field is equivalent to quotienting by the maximal
ideal action. -/
private theorem nontrivialTensorLocalResidueField_iff_nontrivialQuotSMul
    {A : Type*} [CommRing A] [IsLocalRing A]
    {N : Type*} [AddCommGroup N] [Module A N] :
    Nontrivial (N ⊗[A] IsLocalRing.ResidueField A) ↔
      Nontrivial (N ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N))) := by
  have hker :
      RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)) =
        IsLocalRing.maximalIdeal A := by
    -- Proof progression: identify the residue-field map kernel with the maximal ideal.
    simpa [IsLocalRing.ResidueField.algebraMap_eq A] using
      (IsLocalRing.ker_residue (R := A))
  let eQuotKer :
      (A ⧸ RingHom.ker (algebraMap A (IsLocalRing.ResidueField A))) ≃ₐ[A]
        IsLocalRing.ResidueField A :=
    Ideal.quotientKerAlgEquivOfSurjective
      (R₁ := A) (f := Algebra.ofId A (IsLocalRing.ResidueField A))
      IsLocalRing.residue_surjective
  let eQuot :
      (A ⧸ IsLocalRing.maximalIdeal A) ≃ₗ[A] IsLocalRing.ResidueField A :=
    ((Ideal.quotientEquivAlgOfEq A hker.symm).trans eQuotKer).toLinearEquiv
  let e :
      N ⊗[A] IsLocalRing.ResidueField A ≃ₗ[A]
        N ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N)) :=
    (TensorProduct.comm A N (IsLocalRing.ResidueField A)) ≪≫ₗ
      (TensorProduct.congr
        eQuot.symm
        (LinearEquiv.refl A N)) ≪≫ₗ
      TensorProduct.quotTensorEquivQuotSMul N (IsLocalRing.maximalIdeal A)
  -- Proof progression: transport nontriviality across the canonical quotient/tensor comparison.
  exact e.nontrivial_congr

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
a nontrivial fiber of a flat module gives faithful flatness after localizing at the prime. -/
private theorem faithfullyFlat_localizedModuleAtPrime_of_nontrivial_fiber
    {A : Type*} {X : Type*} [CommRing A]
    [AddCommGroup X] [Module A X]
    (q : PrimeSpectrum A) (hflat_A : Module.Flat A X)
    (hq : Nontrivial (X ⊗[A] q.asIdeal.ResidueField)) :
    Module.FaithfullyFlat (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal X) := by
  let Aq := Localization.AtPrime q.asIdeal
  let Xq := LocalizedModule.AtPrime q.asIdeal X
  have hflatAq : Module.Flat Aq Xq := by
    let _ : Module.Flat A X := hflat_A
    simpa [Aq, Xq, LocalizedModule.AtPrime] using
      (Module.Flat.localizedModule (M := X) q.asIdeal.primeCompl)
  have htensor :
      Nontrivial (Xq ⊗[Aq] q.asIdeal.ResidueField) :=
    localizedModuleAtPrime_tensor_residueField_nontrivial (X := X) q hq
  have hquot :
      Nontrivial (Xq ⧸ (IsLocalRing.maximalIdeal Aq • (⊤ : Submodule Aq Xq))) := by
    exact
      (nontrivialTensorLocalResidueField_iff_nontrivialQuotSMul
        (A := Aq) (N := Xq)).mp htensor
  have hmax_ne :
      IsLocalRing.maximalIdeal Aq • (⊤ : Submodule Aq Xq) ≠ ⊤ := by
    exact Submodule.Quotient.nontrivial_iff.mp hquot
  -- Proof progression: over a local ring, flat plus nonzero closed fiber is faithfully flat.
  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal Aq Xq).2 ⟨hflatAq, ?_⟩
  intro J hJ hJtop
  have hJmax : J ≤ IsLocalRing.maximalIdeal Aq := IsLocalRing.le_maximalIdeal hJ
  apply hmax_ne
  exact eq_top_iff.2 <| by
    calc
      ⊤ = J • (⊤ : Submodule Aq Xq) := hJtop.symm
      _ ≤ IsLocalRing.maximalIdeal Aq • (⊤ : Submodule Aq Xq) :=
        Submodule.smul_mono hJmax le_rfl

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
faithfully flat localized modules descend flatness of the local ring map. -/
private theorem algebraMapAtPrime_flat_of_faithfullyFlat_localizedModule
    {R : Type*} {A : Type*} {X : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup X] [Module A X] [Module R X] [IsScalarTower R A X]
    (q : PrimeSpectrum A) (hflat_R : Module.Flat R X)
    (hff :
      Module.FaithfullyFlat (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal X)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := by
  let Rq := Localization.AtPrime (q.asIdeal.under R)
  let Aq := Localization.AtPrime q.asIdeal
  let Xq := LocalizedModule.AtPrime q.asIdeal X
  let f : Rq →+* Aq :=
    Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl
  let _ : Algebra Rq Aq := f.toAlgebra
  have hflatRq : Module.Flat Rq Xq := by
    simpa [Rq, Xq] using
      flat_localizedModuleAtPrime_over_under_of_flat
        (R := R) (A := A) (X := X) hflat_R q
  let _ : Module.Flat Rq Xq := hflatRq
  have hflatRqRestrict : Module.Flat Rq (RestrictScalars Rq Aq Xq) := by
    change Module.Flat Rq Xq
    exact hflatRq
  let _ : Module.Flat Rq (RestrictScalars Rq Aq Xq) := hflatRqRestrict
  let _ : Module.FaithfullyFlat Aq Xq := hff
  have hlocal : f.Flat := by
    simpa [f, Rq, Aq] using
      (algebraMap_flat_of_flat_of_faithfullyFlat
        (R := Rq) (S := Aq) (M := Xq))
  have hbase : (algebraMap R Rq).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    simpa [Rq] using
      (IsLocalization.flat (S := Rq) (p := (q.asIdeal.under R).primeCompl))
  have hcomp : (f.comp (algebraMap R Rq)).Flat :=
    RingHom.Flat.comp hbase hlocal
  have hfg : f.comp (algebraMap R Rq) = algebraMap R Aq := by
    ext r
    exact Localization.localRingHom_to_map
      (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl r
  -- Proof progression: the composite local map is the canonical map to `A_q`.
  rw [hfg] at hcomp
  simpa [Aq] using hcomp

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
if a module is flat over both rings and has nontrivial fiber at `q`, then `R → A_q` is flat. -/
private theorem atPrime_flat_of_flat_module_and_nontrivial_fiber_local
    {R : Type*} {A : Type*} {X : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup X] [Module A X] [Module R X] [IsScalarTower R A X]
    (q : PrimeSpectrum A) (hflat_R : Module.Flat R X)
    (hflat_A : Module.Flat A X)
    (hq : Nontrivial (X ⊗[A] q.asIdeal.ResidueField)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := by
  have hff :
      Module.FaithfullyFlat (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal X) :=
    faithfullyFlat_localizedModuleAtPrime_of_nontrivial_fiber
      (X := X) q hflat_A hq
  exact algebraMapAtPrime_flat_of_faithfullyFlat_localizedModule
    (R := R) (A := A) (X := X) q hflat_R hff

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
a locally nilpotent ideal is contained in every prime ideal. -/
lemma isLocallyNilpotent_le_prime
    {A : Type*} [CommRing A] {J : Ideal A} (hJ : J.IsLocallyNilpotent)
    (p : PrimeSpectrum A) :
    J ≤ p.asIdeal := by
  -- The chapter definition is containment in the nilradical, and every prime contains it.
  exact hJ.trans (nilradical_le_prime p.asIdeal)

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
contracting a prime through the middle ring of an algebra tower gives the same base prime as
contracting directly. -/
private lemma comap_asIdeal_under_eq_under
    {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (q : PrimeSpectrum C) :
    (PrimeSpectrum.comap (algebraMap B C) q).asIdeal.under A = q.asIdeal.under A := by
  -- Proof progression: unfold both contractions and use the scalar-tower identity for the
  -- two maps from the base ring to the top ring.
  simpa [PrimeSpectrum.comap_asIdeal, Ideal.under, IsScalarTower.algebraMap_eq A B C] using rfl

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
elements of `pS` vanish in the fiber ring `κ(p) ⊗[R] S`. -/
private lemma algebraMap_fiber_eq_zero_of_mem_map_at_under
    (p : PrimeSpectrum R) {x : S}
    (hx : x ∈ Ideal.map (algebraMap R S) p.asIdeal) :
    algebraMap S (p.asIdeal.Fiber S) x = 0 := by
  let φ : (R ⧸ p.asIdeal) ⊗[R] S →+* p.asIdeal.Fiber S :=
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R (R ⧸ p.asIdeal) p.asIdeal.ResidueField)
      (AlgHom.id R S)).toRingHom
  have hquot :
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) x :
        S ⧸ Ideal.map (algebraMap R S) p.asIdeal) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have htmul : (1 : R ⧸ p.asIdeal) ⊗ₜ[R] x = 0 := by
    let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p.asIdeal
    have hx' :
        e (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) x) =
          (1 : R ⧸ p.asIdeal) ⊗ₜ[R] x := rfl
    rw [← hx', hquot]
    simp [e]
  have hφ : φ ((1 : R ⧸ p.asIdeal) ⊗ₜ[R] x) = 0 := by
    rw [htmul, map_zero]
  -- Push vanishing through the tensor presentation of the fiber ring.
  simpa [φ] using hφ

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
if `I ≤ p`, then elements of `IS` vanish in the fiber ring over `p`. -/
private lemma algebraMap_fiber_eq_zero_of_mem_map_le
    (p : PrimeSpectrum R) (hpI : I ≤ p.asIdeal) {x : S}
    (hx : x ∈ IS) :
    algebraMap S (p.asIdeal.Fiber S) x = 0 := by
  -- Enlarge the mapped ideal from `IS` to `pS`, then use the canonical fiber vanishing.
  exact algebraMap_fiber_eq_zero_of_mem_map_at_under (R := R) (S := S) p
    (Ideal.map_mono hpI hx)

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the quotient fiber ring `S / IS` acts on the global fiber over any prime containing `I`. -/
@[reducible]
private noncomputable def quotientFiberAlgebra_at_under
    (p : PrimeSpectrum R) (hpI : I ≤ p.asIdeal) :
    Algebra FiberRing (p.asIdeal.Fiber S) :=
  (Ideal.Quotient.liftₐ IS (Algebra.ofId S (p.asIdeal.Fiber S))
    (fun _ hx ↦ algebraMap_fiber_eq_zero_of_mem_map_le (R := R) (S := S) (I := I) p hpI hx)
      ).toRingHom.toAlgebra

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the quotient-to-prime-fiber algebra map is induced by the original map from `S`. -/
private lemma quotientFiberAlgebra_algebraMap_mk_at_under
    (p : PrimeSpectrum R) (hpI : I ≤ p.asIdeal) (s : S) :
    let _ : Algebra FiberRing (p.asIdeal.Fiber S) :=
      quotientFiberAlgebra_at_under (R := R) (S := S) (I := I) p hpI
    algebraMap FiberRing (p.asIdeal.Fiber S) (Ideal.Quotient.mk IS s) =
      algebraMap S (p.asIdeal.Fiber S) s := by
  -- Both sides are the defining value of the quotient lift on the class of `s`.
  rfl

omit [Algebra R S'] [IsScalarTower R S S'] [Algebra.FiniteType R S]
  [Algebra.FinitePresentation R S'] [Module.FinitePresentation S' M] in
/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
flatness of the quotient fiber module base-changes to every global prime fiber. -/
private lemma primeFiberFlat_of_quotientFiberFlat
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (p : PrimeSpectrum R) :
    Module.Flat (p.asIdeal.Fiber S)
      ((p.asIdeal.Fiber S) ⊗[S] RestrictScalars S S' M) := by
  letI : Algebra FiberRing (p.asIdeal.Fiber S) :=
    quotientFiberAlgebra_at_under (R := R) (S := S) (I := I) p
      (isLocallyNilpotent_le_prime hI p)
  letI : IsScalarTower S FiberRing (p.asIdeal.Fiber S) :=
    IsScalarTower.of_algebraMap_eq fun s ↦ by
      -- The quotient algebra was defined by lifting the original map from `S`.
      simpa using
        quotientFiberAlgebra_algebraMap_mk_at_under
          (R := R) (S := S) (I := I) p (isLocallyNilpotent_le_prime hI p) s
  have hbase :
      Module.Flat (p.asIdeal.Fiber S) ((p.asIdeal.Fiber S) ⊗[FiberRing] FiberModule) := by
    -- Base change carries flatness from the quotient fiber owner to the prime-fiber owner.
    letI : Module.Flat FiberRing FiberModule := hflat_fiber
    infer_instance
  let e :
      (p.asIdeal.Fiber S) ⊗[FiberRing] FiberModule ≃ₗ[p.asIdeal.Fiber S]
        (p.asIdeal.Fiber S) ⊗[S] RestrictScalars S S' M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S FiberRing (p.asIdeal.Fiber S)
      (p.asIdeal.Fiber S) (RestrictScalars S S' M)
  -- Transport the base-changed flat module across the standard tensor cancellation.
  letI : Module.Flat (p.asIdeal.Fiber S) ((p.asIdeal.Fiber S) ⊗[FiberRing] FiberModule) :=
    hbase
  exact Module.Flat.of_linearEquiv e.symm

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
flatness over the prime fiber stays flat after localizing at the corresponding point of the
fiber. -/
private lemma fiberLocalTensorFlat_of_primeFiberFlat
    (q : PrimeSpectrum S)
    (hflat : Module.Flat ((q.asIdeal.under R).Fiber S)
      (((q.asIdeal.under R).Fiber S) ⊗[S] RestrictScalars S S' M)) :
    Module.Flat (fiberLocalRingAt R S q)
      ((fiberLocalRingAt R S q) ⊗[S] RestrictScalars S S' M) := by
  letI : IsScalarTower S ((q.asIdeal.under R).Fiber S) (fiberLocalRingAt R S q) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hbase :
      Module.Flat (fiberLocalRingAt R S q)
        ((fiberLocalRingAt R S q) ⊗[((q.asIdeal.under R).Fiber S)]
          (((q.asIdeal.under R).Fiber S) ⊗[S] RestrictScalars S S' M)) := by
    -- Base change localizes the flat module from the prime fiber to the local fiber ring.
    letI : Module.Flat ((q.asIdeal.under R).Fiber S)
      (((q.asIdeal.under R).Fiber S) ⊗[S] RestrictScalars S S' M) := hflat
    infer_instance
  let e :
      (fiberLocalRingAt R S q) ⊗[((q.asIdeal.under R).Fiber S)]
          (((q.asIdeal.under R).Fiber S) ⊗[S] RestrictScalars S S' M) ≃ₗ[
            fiberLocalRingAt R S q]
        (fiberLocalRingAt R S q) ⊗[S] RestrictScalars S S' M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S ((q.asIdeal.under R).Fiber S)
      (fiberLocalRingAt R S q) (fiberLocalRingAt R S q) (RestrictScalars S S' M)
  -- The tensor-cancellation equivalence returns the localized module to the `S`-tensor shape.
  letI : Module.Flat (fiberLocalRingAt R S q)
      ((fiberLocalRingAt R S q) ⊗[((q.asIdeal.under R).Fiber S)]
          (((q.asIdeal.under R).Fiber S) ⊗[S] RestrictScalars S S' M)) := hbase
  exact Module.Flat.of_linearEquiv e.symm

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the literal closed fiber of the localized map `R_(q ∩ R) → S_q`. -/
private abbrev localClosedFiberAtUnder (q : PrimeSpectrum S) : Type _ :=
  (IsLocalRing.maximalIdeal (Localization.AtPrime (q.asIdeal.under R))).Fiber
    (Localization.AtPrime q.asIdeal)

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the literal localized closed fiber has its canonical commutative ring structure. -/
private noncomputable instance localClosedFiberAtUnderCommRing (q : PrimeSpectrum S) :
    CommRing (localClosedFiberAtUnder (R := R) (S := S) q) := by
  -- Proof progression: unfold the owner; `Ideal.Fiber` supplies the ring structure.
  dsimp [localClosedFiberAtUnder]
  infer_instance

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the literal localized closed fiber is canonically a module over itself. -/
private noncomputable instance localClosedFiberAtUnderModule (q : PrimeSpectrum S) :
    Module (localClosedFiberAtUnder (R := R) (S := S) q)
      (localClosedFiberAtUnder (R := R) (S := S) q) :=
  Semiring.toModule

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the literal localized closed fiber is flat over itself. -/
private lemma localClosedFiberAtUnder_selfFlat (q : PrimeSpectrum S) :
    Module.Flat (localClosedFiberAtUnder (R := R) (S := S) q)
      (localClosedFiberAtUnder (R := R) (S := S) q) := by
  -- Proof progression: the self-module over any commutative ring is free, hence flat.
  infer_instance

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
prime-fiber flatness gives the exact closed-fiber flatness input for Lemma 10.128.9 after
localizing the top module at a prime of `S'`. -/
private lemma localClosedFiberLocalizedModuleFlatAtPrime_of_primeFiberFlat
    (q' : PrimeSpectrum S') :
    let q : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S') q'
    Module.Flat ((q.asIdeal.under R).Fiber S)
      (((q.asIdeal.under R).Fiber S) ⊗[S] RestrictScalars S S' M) →
    Module.Flat
      (Ideal.Fiber
        (IsLocalRing.maximalIdeal (Localization.AtPrime (q'.asIdeal.under R)))
        (Localization.AtPrime q.asIdeal))
      ((Ideal.Fiber
        (IsLocalRing.maximalIdeal (Localization.AtPrime (q'.asIdeal.under R)))
        (Localization.AtPrime q.asIdeal)) ⊗[Localization.AtPrime q.asIdeal]
          RestrictScalars (Localization.AtPrime q.asIdeal) (Localization.AtPrime q'.asIdeal)
            (LocalizedModule.AtPrime q'.asIdeal M)) := by
  -- Proof progression: the remaining structural step is now isolated in the exact spelling
  -- consumed by Lemma 10.128.9.  It should be proved by identifying the displayed closed fiber
  -- as a localization of the global prime fiber and then localizing the tensor module.
  intro hflat
  -- TODO(replan): prove the closed-fiber localization bridge
  -- `((q.asIdeal.under R).Fiber S) → (maximalIdeal R_(q'∩R)).Fiber S_q` and the
  -- localized-module tensor adapter for `LocalizedModule.AtPrime q'.asIdeal M`.
  sorry

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the locally nilpotent quotient-fiber hypothesis supplies the exact closed-fiber flatness input
at a prime of `S'`. -/
private lemma localClosedFiberLocalizedModuleFlatAtPrime_of_quotientFiberFlat
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (q' : PrimeSpectrum S') :
    let q : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S') q'
    Module.Flat
      (Ideal.Fiber
        (IsLocalRing.maximalIdeal (Localization.AtPrime (q'.asIdeal.under R)))
        (Localization.AtPrime q.asIdeal))
      ((Ideal.Fiber
        (IsLocalRing.maximalIdeal (Localization.AtPrime (q'.asIdeal.under R)))
        (Localization.AtPrime q.asIdeal)) ⊗[Localization.AtPrime q.asIdeal]
          RestrictScalars (Localization.AtPrime q.asIdeal) (Localization.AtPrime q'.asIdeal)
            (LocalizedModule.AtPrime q'.asIdeal M)) := by
  let q : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S') q'
  have hprime :
      Module.Flat ((q.asIdeal.under R).Fiber S)
        (((q.asIdeal.under R).Fiber S) ⊗[S] RestrictScalars S S' M) := by
    -- Proof progression: locally nilpotent ideals are contained in the base prime, so the
    -- quotient-fiber flatness base-changes to the global prime fiber over `q ∩ R`.
    simpa [q] using
      primeFiberFlat_of_quotientFiberFlat
        (R := R) (S := S) (S' := S') (M := M) (I := I)
        hI hflat_fiber ⟨q.asIdeal.under R, inferInstance⟩
  -- Proof progression: the only remaining bridge is the exact local closed-fiber transport.
  simpa [q] using
    localClosedFiberLocalizedModuleFlatAtPrime_of_primeFiberFlat
      (R := R) (S := S) (S' := S') (M := M) q' hprime

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the canonical fiber module over a prime is the residue-field tensor of the module. -/
private noncomputable def fiberModuleLinearEquiv
    {A : Type*} {B : Type*} {N : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (p : PrimeSpectrum A) :
    (p.asIdeal.Fiber B) ⊗[B] N ≃ₗ[B] N ⊗[A] p.asIdeal.ResidueField :=
  TensorProduct.comm B (p.asIdeal.Fiber B) N ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B N)
      (Algebra.TensorProduct.commRight A B p.asIdeal.ResidueField).symm.toLinearEquiv
      ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B B N p.asIdeal.ResidueField

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
a support point of the fiber-ring module contracts to a support point of the original module. -/
private lemma supportPoint_contraction_of_fiberRingSupport
    {A : Type*} {B : Type*} {N : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.Finite B N]
    (p : PrimeSpectrum A) (r : PrimeSpectrum (p.asIdeal.Fiber B))
    (hr : r ∈ Module.support (p.asIdeal.Fiber B) ((p.asIdeal.Fiber B) ⊗[B] N)) :
    let Qover := (PrimeSpectrum.preimageEquivFiber A B p).symm r
    let Q : PrimeSpectrum B := Qover.1
    Q ∈ Module.support B N ∧ PrimeSpectrum.comap (algebraMap A B) Q = p := by
  let Qover := (PrimeSpectrum.preimageEquivFiber A B p).symm r
  let Q : PrimeSpectrum B := Qover.1
  constructor
  · -- Proof progression: rewrite support on the fiber ring as the inverse image of support on `B`.
    change PrimeSpectrum.comap (algebraMap B (p.asIdeal.Fiber B)) r ∈ Module.support B N
    simpa [Module.Lemma_10_40_6 (R := B) (R' := p.asIdeal.Fiber B) (M := N)] using hr
  · -- Proof progression: the fiber-spectrum equivalence remembers that the contracted prime lies
    -- over the original prime `p`.
    simpa [Q, Qover] using Qover.2

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the local tower at a prime of `S'` has the flatness conclusion needed by the prime-local
criterion. -/
private lemma localizedModuleFlatAtPrime_of_locallyNilpotent
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M))
    (q' : PrimeSpectrum S') :
    Module.Flat (Localization.AtPrime (q'.asIdeal.under S))
      (LocalizedModule.AtPrime q'.asIdeal M) := by
  let q : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S') q'
  let p : Ideal R := q'.asIdeal.under R
  let Rq := Localization.AtPrime p
  let Sq := Localization.AtPrime q.asIdeal
  let Tq := Localization.AtPrime q'.asIdeal
  letI : Module R M := Module.compHom M (algebraMap R S')
  letI : IsScalarTower R S' M := by
    exact IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hq_under : q.asIdeal.under R = p := by
    simpa [q, p] using
      comap_asIdeal_under_eq_under (A := R) (B := S) (C := S') q'
  letI : q.asIdeal.LiesOver p := by
    rw [← hq_under]
    exact Ideal.over_under q.asIdeal
  letI : q'.asIdeal.LiesOver q.asIdeal := by
    simpa [q, PrimeSpectrum.comap_asIdeal] using (Ideal.over_under q'.asIdeal)
  -- Proof progression: localize the finite-type middle algebra to the tower
  -- `R_(q'∩R) → S_(q'∩S)`.
  have hRS : Algebra.EssFiniteType Rq Sq := by
    have hR_Sq : Algebra.EssFiniteType R Sq := inferInstance
    exact Algebra.EssFiniteType.of_comp R Rq Sq
  have hRS' : Algebra.EssFinitePresentation Rq Tq := by
    -- Proof progression: the top localized algebra is finitely presented after localizing both
    -- the source and target at the contracted prime.
    simpa [Rq, Tq, p] using
      localizedTopEssFinitePresentationAtPrime (R := R) (S' := S') q'
  have hclosed :
      Module.Flat (Ideal.Fiber (IsLocalRing.maximalIdeal Rq) Sq)
        ((Ideal.Fiber (IsLocalRing.maximalIdeal Rq) Sq) ⊗[Sq]
          RestrictScalars Sq Tq (LocalizedModule.AtPrime q'.asIdeal M)) := by
    -- Proof progression: all repeated closed-fiber transport is delegated to the exact
    -- consumer-facing helper for this local tower.
    simpa [q, p, Rq, Sq, Tq] using
      localClosedFiberLocalizedModuleFlatAtPrime_of_quotientFiberFlat
        (R := R) (S := S) (S' := S') (M := M) (I := I) hI hflat_fiber q'
  have hflat_Rq :
      Module.Flat Rq (RestrictScalars Rq Tq (LocalizedModule.AtPrime q'.asIdeal M)) := by
    -- Proof progression: the base flatness hypothesis localizes at the prime `q'`.
    simpa [Rq, Tq, p] using
      flat_localizedModuleAtPrime_over_under_of_flat (R := R) (A := S') (X := M) hflat_R q'
  have hflatSq :
      Module.Flat Sq (RestrictScalars Sq Tq (LocalizedModule.AtPrime q'.asIdeal M)) :=
    flat_over_middleRing_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
      (R := Rq) (S := Sq) (S' := Tq) (M := LocalizedModule.AtPrime q'.asIdeal M)
      hRS hRS' hclosed hflat_Rq
  -- Proof progression: `q` is the contraction of `q'`, so this is exactly the requested
  -- localization over `S`.
  simpa [q, Sq, Tq, PrimeSpectrum.comap_asIdeal] using hflatSq

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
a nontrivial fiber over `q : Spec S` has a supporting prime of `S'` above `q`. -/
private lemma exists_supportingPrime_over_of_nontrivial_fiber
    (q : PrimeSpectrum S)
    (hq : Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField)) :
    ∃ q' : PrimeSpectrum S',
      q'.asIdeal.under S = q.asIdeal ∧
        Nontrivial (LocalizedModule.AtPrime q'.asIdeal M) := by
  letI : Module S M := Module.compHom M (algebraMap S S')
  letI : IsScalarTower S S' M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hfiber : Nontrivial ((q.asIdeal.Fiber S') ⊗[S'] M) := by
    -- Proof progression: rewrite the displayed `S`-fiber as the fiber-ring tensor over `S'`.
    exact (fiberModuleLinearEquiv (A := S) (B := S') (N := M) q).nontrivial_congr.mpr
      (by simpa using hq)
  obtain ⟨r, hr⟩ :
      (Module.support (q.asIdeal.Fiber S') ((q.asIdeal.Fiber S') ⊗[S'] M)).Nonempty :=
    Module.nonempty_support_iff.mpr hfiber
  let Qover := (PrimeSpectrum.preimageEquivFiber S S' q).symm r
  let Q : PrimeSpectrum S' := Qover.1
  have hQ :
      Q ∈ Module.support S' M ∧ PrimeSpectrum.comap (algebraMap S S') Q = q := by
    -- Proof progression: contract the support point of the fiber module back to a support point
    -- of `M` over `S'`, remembering that it lies over `q`.
    simpa [Q, Qover] using
      supportPoint_contraction_of_fiberRingSupport (A := S) (B := S') (N := M) q r hr
  refine ⟨Q, ?_, ?_⟩
  · simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hQ.2
  · exact Module.mem_support_iff.mp hQ.1

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the local middle ring at a supporting prime of `S'` is essentially finitely presented over `R`. -/
private lemma localizedEssFinitePresentationAtPrime_of_locallyNilpotent
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M))
    (q' : PrimeSpectrum S')
    (hM : Nontrivial (LocalizedModule.AtPrime q'.asIdeal M)) :
    RingHom.EssFinitePresentation (algebraMap R (Localization.AtPrime (q'.asIdeal.under S))) := by
  let q : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S') q'
  let p : Ideal R := q'.asIdeal.under R
  let Rq := Localization.AtPrime p
  let Sq := Localization.AtPrime q.asIdeal
  let Tq := Localization.AtPrime q'.asIdeal
  letI : Module R M := Module.compHom M (algebraMap R S')
  letI : IsScalarTower R S' M := by
    exact IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hq_under : q.asIdeal.under R = p := by
    simpa [q, p] using
      comap_asIdeal_under_eq_under (A := R) (B := S) (C := S') q'
  letI : q.asIdeal.LiesOver p := by
    rw [← hq_under]
    exact Ideal.over_under q.asIdeal
  letI : q'.asIdeal.LiesOver q.asIdeal := by
    simpa [q, PrimeSpectrum.comap_asIdeal] using (Ideal.over_under q'.asIdeal)
  -- Proof progression: prepare the same local tower as in the flatness helper.
  have hRS : Algebra.EssFiniteType Rq Sq := by
    have hR_Sq : Algebra.EssFiniteType R Sq := inferInstance
    exact Algebra.EssFiniteType.of_comp R Rq Sq
  have hRS' : Algebra.EssFinitePresentation Rq Tq := by
    -- Proof progression: reuse the same localized-top finite-presentation bridge as in the
    -- flatness helper.
    simpa [Rq, Tq, p] using
      localizedTopEssFinitePresentationAtPrime (R := R) (S' := S') q'
  have hclosed :
      Module.Flat (Ideal.Fiber (IsLocalRing.maximalIdeal Rq) Sq)
        ((Ideal.Fiber (IsLocalRing.maximalIdeal Rq) Sq) ⊗[Sq]
          RestrictScalars Sq Tq (LocalizedModule.AtPrime q'.asIdeal M)) := by
    -- Proof progression: reuse the same exact closed-fiber input as in the flatness helper.
    simpa [q, p, Rq, Sq, Tq] using
      localClosedFiberLocalizedModuleFlatAtPrime_of_quotientFiberFlat
        (R := R) (S := S) (S' := S') (M := M) (I := I) hI hflat_fiber q'
  have hflat_Rq :
      Module.Flat Rq (RestrictScalars Rq Tq (LocalizedModule.AtPrime q'.asIdeal M)) := by
    -- Proof progression: `hflat_R` localizes to the base of the local tower.
    simpa [Rq, Tq, p] using
      flat_localizedModuleAtPrime_over_under_of_flat (R := R) (A := S') (X := M) hflat_R q'
  have hmid : Algebra.EssFinitePresentation Rq Sq :=
    middleRing_essFinitePresentation_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
      (R := Rq) (S := Sq) (S' := Tq) (M := LocalizedModule.AtPrime q'.asIdeal M)
      hM hRS hRS' hclosed hflat_Rq
  have hbase : RingHom.EssFinitePresentation (algebraMap R Rq) := by
    -- Proof progression: the map `R → R_(q'∩R)` is itself an essential finite presentation.
    rw [RingHom.essFinitePresentation_algebraMap]
    exact Algebra.EssFinitePresentation.of_isLocalization
      (R := R) (S := Rq) (P := R) p.primeCompl
  have hmidRing : RingHom.EssFinitePresentation (algebraMap Rq Sq) := by
    rw [RingHom.essFinitePresentation_algebraMap]
    exact hmid
  have hcomp :
      RingHom.EssFinitePresentation ((algebraMap Rq Sq).comp (algebraMap R Rq)) :=
    RingHom.EssFinitePresentation.comp hbase hmidRing
  have hcomp' : RingHom.EssFinitePresentation (algebraMap R Sq) := by
    have hcomp_eq : (algebraMap Rq Sq).comp (algebraMap R Rq) = algebraMap R Sq := by
      exact (IsScalarTower.algebraMap_eq R Rq Sq).symm
    simpa [hcomp_eq] using hcomp
  -- Proof progression: replace `Sq` by the displayed localization at `q'.asIdeal.under S`.
  simpa [Sq, q, PrimeSpectrum.comap_asIdeal] using hcomp'

/-- Helper for Chap10 Lemma 10 128 10 Crit re de platitude par fibres locally nilpotent case:
the localized middle ring is essentially finitely presented over the base at a nontrivial fiber. -/
private lemma localizedEssFinitePresentation_of_nontrivialFiber
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M))
    (q : PrimeSpectrum S)
    (hq : Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField)) :
    RingHom.EssFinitePresentation (algebraMap R (Localization.AtPrime q.asIdeal)) := by
  obtain ⟨q', hq', hM⟩ :=
    exists_supportingPrime_over_of_nontrivial_fiber q hq
  have hlocal :
      RingHom.EssFinitePresentation
        (algebraMap R (Localization.AtPrime (q'.asIdeal.under S))) :=
    localizedEssFinitePresentationAtPrime_of_locallyNilpotent
      (R := R) (S := S) (S' := S') (M := M) (I := I)
      hI hflat_fiber hflat_R q' hM
  -- Proof progression: the supporting prime was chosen over `q`, so its contracted localization
  -- is exactly the requested localization at `q`.
  have hqSpec : PrimeSpectrum.comap (algebraMap S S') q' = q := by
    apply PrimeSpectrum.ext
    simpa [PrimeSpectrum.comap_asIdeal] using hq'
  subst q
  simpa [PrimeSpectrum.comap_asIdeal] using hlocal

/- Domain-style sampling for the locally nilpotent fiberwise flatness criterion:
* primary domain: fiberwise flatness for finitely presented modules over a locally nilpotent
  thickening, with fiber hypotheses carried by the canonical fiber module owner;
* sampled owner declarations of the same kind:
  `Ideal.qoutMapEquivTensorQout`,
  `Definition_10_65_2.mem_relativeAssassin_iff_fiber`,
  `flat_over_middleRing_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base`,
  `middleRing_essFinitePresentation_of_essFiniteType_of_flat_closedFiber_and_flat_over_base`;
* best owner abstraction: the primitive fiber hypothesis should live on
  `FiberModule = FiberRing ⊗[S] M`, where `FiberRing = S ⧸ Ideal.map (algebraMap R S) I` is the
  quotient presentation of the arbitrary-ideal fiber ring, equivalently
  `(R ⧸ I) ⊗[R] S` via `Ideal.qoutMapEquivTensorQout`; the quotient module
  `M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))` is only a bridge view.

Primitive data vs. derived API:
* primitive data: the locally nilpotent ideal `I`, the algebra tower `R → S → S'`, the finite-type
  and finite-presentation hypotheses, the finitely presented `S'`-module `M`, flatness of the
  canonical fiber module `FiberModule` over `FiberRing`, and flatness of the restricted
  `R`-module `RestrictScalars R S' M`;
* derived API: flatness of the restricted `S`-module `RestrictScalars S S' M`, then flatness and
  essential finite presentation of the localizations `S_q` over `R`.

Source/core/bridge triage:
* `source-facing`: the three theorems below, which are the locally nilpotent variant of the
  fiberwise flatness criterion;
* `core/canonical`: the fiber module owner `FiberModule`, `Module.Flat`, and
  `RingHom.EssFinitePresentation`;
* `bridge/view`: the quotient models of the fiber ring and fiber module modulo `IS`.
-/

-- Proof sketch: first pass from the locally nilpotent ideal `I` to the closed fibers over the
-- primes `p = q ∩ R`; since `I ⊆ p`, base change of the canonical fiber-flatness hypothesis on
-- `FiberModule` yields flatness of the closed fiber over `p`. Apply the local fiberwise flatness
-- criterion of Lemma `10.128.9` to `R_p → S_q → S'_{q'}` for primes `q'` of `S'` above `q`,
-- obtaining flatness of the localized module over `S_q`. Then use the prime-local criterion for
-- flatness to conclude `RestrictScalars S S' M` is flat over `S`.
/-- Lemma 10.128.10 (Critère de platitude par fibres: locally nilpotent case): if `I` is a locally
nilpotent ideal of `R`, `R → S` is of finite type, `R → S'` is of finite presentation, `M` is a
finitely presented `S'`-module, the canonical fiber module
`FiberModule = (S ⧸ Ideal.map (algebraMap R S) I) ⊗[S] M`,
equivalently `M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))`, is flat over the
canonical fiber ring `FiberRing = S ⧸ Ideal.map (algebraMap R S) I`, equivalently
`(R ⧸ I) ⊗[R] S`, and the restricted `R`-module `RestrictScalars R S' M` is flat over `R`, then
the restricted `S`-module `RestrictScalars S S' M` is flat over `S`. -/
@[stacks 0CEL]
theorem flat_over_middleRing_of_locallyNilpotent_of_flat_over_base_and_flat_mod_extended_ideal
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M)) :
    Module.Flat S (RestrictScalars S S' M) := by
  letI : Module S M := Module.compHom M (algebraMap S S')
  letI : IsScalarTower S S' M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ by
    rfl
  -- Proof progression: reduce global flatness over `S` to flatness at every prime of `S'`.
  have hlocal : Module.Flat S M := by
    rw [flat_iff_flat_localizedModuleAtPrime_over_under (R := S) (A := S') (X := M)]
    intro q'
    exact localizedModuleFlatAtPrime_of_locallyNilpotent
      (R := R) (S := S) (S' := S') (M := M) (I := I) hI hflat_fiber hflat_R q'
  simpa using hlocal

-- Proof sketch: choose a prime `q'` of `S'` above `q` using the nontrivial fiber hypothesis and
-- Lemma `10.18.6`. For `p = q ∩ R`, the locally nilpotent hypothesis gives `I ⊆ p`, so base
-- change of `hflat_fiber` gives flatness of the canonical fiber over `p`. Apply Lemma `10.128.9`
-- to the local diagram `R_p → S_q → S'_{q'}` and the localized module `M_{q'}`.
/-- If the residue-field fiber `(RestrictScalars S S' M) ⊗[S] κ(q)` is nontrivial, then the
localization `S_q` is flat over `R`. -/
theorem localized_flat_of_locallyNilpotent_of_nontrivial_fiber
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M))
    (q : PrimeSpectrum S)
    (hq : Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := by
  letI : Module S M := Module.compHom M (algebraMap S S')
  letI : Module R M := Module.compHom M (algebraMap R S')
  letI : IsScalarTower S S' M := IsScalarTower.of_algebraMap_smul fun s m ↦ by
    rfl
  letI : IsScalarTower R S' M := IsScalarTower.of_algebraMap_smul fun r m ↦ by
    rfl
  letI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun r m ↦ by
    simpa [Module.compHom, RingHom.comp_apply] using
      (congrArg (fun f : R →+* S' ↦ f r • m) (IsScalarTower.algebraMap_eq R S S')).symm
  have hflat_S : Module.Flat S (RestrictScalars S S' M) :=
    flat_over_middleRing_of_locallyNilpotent_of_flat_over_base_and_flat_mod_extended_ideal
      (R := R) (S := S) (S' := S') (M := M) (I := I) hI hflat_fiber hflat_R
  have hflat_S' : Module.Flat S M := by
    simpa using hflat_S
  have hflat_R' : Module.Flat R M := by
    -- The `R`-module structures obtained by restricting through `S` or directly through `S'`
    -- are definitionally the same along the given scalar tower.
    simpa using hflat_R
  -- With `M` already flat over both `R` and `S`, the earlier local support criterion gives
  -- flatness of the local ring map at `q`.
  exact atPrime_flat_of_flat_module_and_nontrivial_fiber_local
    (R := R) (A := S) (X := M) q hflat_R' hflat_S' (by simpa using hq)

-- Proof sketch: with the same localization setup as above, Lemma `10.128.9` shows that the local
-- ring map `R_p → S_q` is essentially of finite presentation. Interpreting this as a statement
-- about the localized `R`-algebra `S_q` gives the claimed essential finite presentation.
/-- If the residue-field fiber `(RestrictScalars S S' M) ⊗[S] κ(q)` is nontrivial, then the
localization `S_q` is essentially of finite presentation over `R`. -/
theorem localized_essFinitePresentation_of_locallyNilpotent_of_nontrivial_fiber
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M))
    (q : PrimeSpectrum S)
    (hq : Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField)) :
    RingHom.EssFinitePresentation (algebraMap R (Localization.AtPrime q.asIdeal)) := by
  -- Proof progression: this shares the supporting-prime and closed-fiber transport setup with
  -- the flatness statement, but consumes the essential-finite-presentation conclusion of
  -- Lemma 10.128.9 instead.
  exact localizedEssFinitePresentation_of_nontrivialFiber
    (R := R) (S := S) (S' := S') (M := M) (I := I) hI hflat_fiber hflat_R q hq

end
