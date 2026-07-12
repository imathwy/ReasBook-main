import StacksProject_2024.Chap10.Lemma_10_143_10
import StacksProject_2024.Chap10.Proposition_10_138_13
import StacksProject_2024.Chap10.Lemma_10_143_11.Index

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open Algebra.Extension

universe u v w x

namespace RingHom

section

variable {Aprime : Type u} {A : Type v} {Bprime : Type w} {B : Type x}
variable [CommRing Aprime] [CommRing A] [CommRing Bprime] [CommRing B]
variable (g : Aprime →+* Bprime) (qA : Aprime →+* A) (qB : Bprime →+* B) (f : A →+* B)

/-- Helper for Lemma 10.143.11: once the square-zero kernel comparison makes the textbook ideal
map `Ideal.map (algebraMap R C) I → Ideal.map (algebraMap R B₁) I` surjective, the whole
comparison map `φAlg.toRingHom : C →+* B₁` is surjective as well. -/
lemma comparisonSurjectiveOfSquareZeroLift
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hSurjC : Function.Surjective qC)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hSqI : I ^ 2 = ⊥) :
    Function.Surjective φAlg.toRingHom := by
  have hTgtSq : (RingHom.ker qB) ^ 2 = ⊥ := by
    -- Transport the square-zero relation from `I` to the target kernel.
    rw [hTgt]
    simpa [Ideal.map_pow] using congrArg (Ideal.map (algebraMap R B₁)) hSqI
  have hIdealSurj :
      Function.Surjective
        (ideal_map_restrict (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp) := by
    -- The target square-zero kernel lets the textbook ideal map hit every target generator.
    exact ideal_map_restrict_surjective_of_square_zero
      hSurjC hq hcomp hTgtSq hTgt
  -- Quotient surjectivity upgrades ideal-level surjectivity to surjectivity of the ring map.
  exact comparison_surjective_of_ideal_map_surjective
    hSurjC hq hcomp hTgt hIdealSurj

/-- Helper for Lemma 10.143.11: an `R`-algebra equivalence transports the cotangent space of an
ideal to the cotangent space of its image ideal. -/
noncomputable def cotangentEquivMapAlgEquiv
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (J : Ideal A) :
    J.Cotangent ≃ₗ[R] (J.map e.toRingHom).Cotangent := by
  let forward :
      J.Cotangent →ₗ[R] (J.map e.toRingHom).Cotangent :=
    Ideal.mapCotangent J (J.map e.toRingHom) e (by
      intro x hx
      exact Ideal.mem_map_of_mem e.toRingHom hx)
  let backward :
      (J.map e.toRingHom).Cotangent →ₗ[R] J.Cotangent :=
    Ideal.mapCotangent (J.map e.toRingHom) J e.symm (by
      intro y hy
      rcases (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hy with ⟨x, hx, rfl⟩
      simpa using hx)
  refine LinearEquiv.ofLinear forward backward ?_ ?_
  · -- The forward map followed by the backward map is the identity on cotangent generators.
    ext x
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (J.map e.toRingHom) x
    rw [LinearMap.comp_apply]
    unfold forward backward
    rw [Ideal.mapCotangent_toCotangent]
    rw [Ideal.mapCotangent_toCotangent]
    apply (J.map e.toRingHom).toCotangent_eq.mpr
    simp
  · -- The backward map followed by the forward map is the identity on the original generators.
    ext x
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective J x
    rw [LinearMap.comp_apply]
    unfold forward backward
    rw [Ideal.mapCotangent_toCotangent]
    rw [Ideal.mapCotangent_toCotangent]
    apply J.toCotangent_eq.mpr
    simp

/-- Helper for Chap10 Lemma 10 143 11: the cotangent equivalence induced by an algebra
equivalence sends a cotangent generator to the corresponding generator of the image ideal. -/
lemma cotangentEquivMapAlgEquiv_toCotangent
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (J : Ideal A) (x : J) :
    cotangentEquivMapAlgEquiv e J (Ideal.toCotangent J x) =
      Ideal.toCotangent (J.map e.toRingHom) ⟨e x, Ideal.mem_map_of_mem e.toRingHom x.2⟩ := by
  -- Proof comment: unfold the transported cotangent equivalence and use the generator formula for
  -- `Ideal.mapCotangent`; the inverse half of `LinearEquiv.ofLinear` is irrelevant on generators.
  rfl

/-- Helper for Chap10 Lemma 10 143 11: the source cotangent module
`(Ideal.map (algebraMap R C) I).Cotangent` identifies with the common tensor model
`C ⊗[R] I.Cotangent` via flat base change along the étale source map `algebraMap R C`. -/
noncomputable def sourceMappedIdealCotangentEquivOfEtale
    {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
    {I : Ideal R}
    (hcEtale : (algebraMap R C).Etale) :
    C ⊗[R] I.Cotangent ≃ₗ[R] (Ideal.map (algebraMap R C) I).Cotangent := by
  have hSmooth : (algebraMap R C).Smooth :=
    (RingHom.etale_iff_formallyUnramified_and_smooth (algebraMap R C)).mp hcEtale |>.2
  have hFlat : (algebraMap R C).Flat := hSmooth.flat
  letI : Module.Flat R C := (RingHom.flat_algebraMap_iff).mp hFlat
  let eTensor :
      C ⊗[R] I.Cotangent ≃ₗ[R]
        (Ideal.map
          (includeRight.toRingHom : R →+* C ⊗[R] R) I).Cotangent :=
    (source_tensor_cotangent_equiv_of_flat I).restrictScalars R
  let eRid :
      (Ideal.map
        (includeRight.toRingHom : R →+* C ⊗[R] R) I).Cotangent ≃ₗ[R]
        (Ideal.map (algebraMap R C) I).Cotangent :=
    let eRidAlg : C ⊗[R] R ≃ₐ[R] C := Algebra.TensorProduct.rid R R C
    let eRidMap :=
      cotangentEquivMapAlgEquiv
        eRidAlg
        (Ideal.map (includeRight.toRingHom : R →+* C ⊗[R] R) I)
    let hRidMap :
        Ideal.map
            eRidAlg.toRingHom
            (Ideal.map (includeRight.toRingHom : R →+* C ⊗[R] R) I) =
          Ideal.map (algebraMap R C) I := by
      -- The right-unit tensor equivalence sends the image of `I` in `C ⊗[R] R`
      -- exactly to the usual image of `I` in `C`.
      rw [Ideal.map_map]
      congr 1
      ext r
      simp [eRidAlg, Algebra.smul_def]
    eRidMap.trans <|
      (Ideal.Cotangent.equivOfEq
        _
        _
        hRidMap).restrictScalars R
  -- First identify the tensor-model cotangent with the mapped ideal in `C ⊗[R] R`,
  -- then collapse `C ⊗[R] R` back to `C` through `TensorProduct.rid`.
  simpa using eTensor.trans eRid

/-- Helper for Chap10 Lemma 10 143 11: the étale source cotangent common model sends the pure
tensor `c ⊗ Ideal.toCotangent I x` to the cotangent class of `c * algebraMap R C x`. -/
lemma sourceMappedIdealCotangentEquivOfEtale_apply_tmul
    {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
    {I : Ideal R}
    (hcEtale : (algebraMap R C).Etale) (c : C) (x : I) :
    sourceMappedIdealCotangentEquivOfEtale (R := R) (C := C) (I := I) hcEtale
        (c ⊗ₜ[R] Ideal.toCotangent I x) =
      Ideal.toCotangent (Ideal.map (algebraMap R C) I)
        ⟨c * algebraMap R C x,
          Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (algebraMap R C) x.2)⟩ := by
  let J : Ideal (C ⊗[R] R) :=
    Ideal.map (Algebra.TensorProduct.includeRight.toRingHom : R →+* C ⊗[R] R) I
  let eRidAlg : C ⊗[R] R ≃ₐ[R] C := Algebra.TensorProduct.rid R R C
  have hSmooth : (algebraMap R C).Smooth :=
    (RingHom.etale_iff_formallyUnramified_and_smooth (algebraMap R C)).mp hcEtale |>.2
  have hFlat : (algebraMap R C).Flat := hSmooth.flat
  letI : Module.Flat R C := (RingHom.flat_algebraMap_iff).mp hFlat
  have hRidMap :
      Ideal.map eRidAlg.toRingHom J = Ideal.map (algebraMap R C) I := by
    -- The tensor right-unit collapses the extended ideal back to the ordinary mapped ideal.
    rw [Ideal.map_map]
    congr 1
    ext r
    simp [eRidAlg, Algebra.smul_def]
  have hTensor :
      ((source_tensor_cotangent_equiv_of_flat (R := R) (C := C) I).restrictScalars R)
          (c ⊗ₜ[R] Ideal.toCotangent I x) =
        c • Ideal.toCotangent J ⟨1 ⊗ₜ[R] x, Ideal.mem_map_of_mem _ x.2⟩ := by
    simpa [J] using Ideal.tensorCotangentEquiv_tmul (R := R) (T := C) (I := I) c x
  let xGen : J := ⟨1 ⊗ₜ[R] (x : R), Ideal.mem_map_of_mem _ x.2⟩
  let xMul : J :=
    ⟨(c ⊗ₜ[R] (1 : R)) * (1 ⊗ₜ[R] (x : R)),
      Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ x.2)⟩
  have hxRid :
      (algebraMap R C x * c : C) ∈ Ideal.map eRidAlg.toRingHom J := by
    simpa [xMul, eRidAlg, TensorProduct.rid_tmul, Algebra.smul_def, mul_comm] using
      (Ideal.mem_map_of_mem eRidAlg.toRingHom
        xMul.2)
  have hSmulGen :
      c • Ideal.toCotangent J xGen = Ideal.toCotangent J xMul := by
    have hxSmul : c • xGen = xMul := by
      apply Subtype.ext
      simp [xGen, xMul, Algebra.smul_def]
    exact congrArg (Ideal.toCotangent J) hxSmul
  have hMap :
      (cotangentEquivMapAlgEquiv eRidAlg J)
          (c • Ideal.toCotangent J
            ⟨1 ⊗ₜ[R] x, Ideal.mem_map_of_mem _ x.2⟩) =
        Ideal.toCotangent (Ideal.map eRidAlg.toRingHom J)
          ⟨algebraMap R C x * c, hxRid⟩ := by
    rw [hSmulGen, cotangentEquivMapAlgEquiv_toCotangent]
    congr 1
    apply Subtype.ext
    simp [xMul, eRidAlg, Algebra.smul_def, mul_comm]
  have hEqToCot :
      ((Ideal.Cotangent.equivOfEq
          (Ideal.map eRidAlg.toRingHom J)
          (Ideal.map (algebraMap R C) I)
          hRidMap).restrictScalars R)
        (Ideal.toCotangent (Ideal.map eRidAlg.toRingHom J) ⟨algebraMap R C x * c, hxRid⟩) =
      Ideal.toCotangent (Ideal.map (algebraMap R C) I)
        ⟨algebraMap R C x * c,
          Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem (algebraMap R C) x.2)⟩ := by
    simpa [J, eRidAlg, Algebra.smul_def] using
      (Ideal.Cotangent.equivOfEq_toCotangent
        (I := Ideal.map eRidAlg.toRingHom J)
        (J := Ideal.map (algebraMap R C) I)
        (hIJ := hRidMap)
        (x := ⟨algebraMap R C x * c, hxRid⟩))
  change
      ((Ideal.Cotangent.equivOfEq
          (Ideal.map eRidAlg.toRingHom J)
          (Ideal.map (algebraMap R C) I)
          hRidMap).restrictScalars R)
        ((cotangentEquivMapAlgEquiv eRidAlg J)
          (((source_tensor_cotangent_equiv_of_flat (R := R) (C := C) I).restrictScalars R)
            (c ⊗ₜ[R] Ideal.toCotangent I x))) =
    Ideal.toCotangent (Ideal.map (algebraMap R C) I)
      ⟨c * algebraMap R C x,
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (algebraMap R C) x.2)⟩
  rw [hTensor]
  calc
    ((Ideal.Cotangent.equivOfEq
        (Ideal.map eRidAlg.toRingHom J)
        (Ideal.map (algebraMap R C) I)
        hRidMap).restrictScalars R)
      ((cotangentEquivMapAlgEquiv eRidAlg J)
        (c • Ideal.toCotangent J
          ⟨1 ⊗ₜ[R] x, Ideal.mem_map_of_mem _ x.2⟩)) =
      ((Ideal.Cotangent.equivOfEq
          (Ideal.map eRidAlg.toRingHom J)
          (Ideal.map (algebraMap R C) I)
          hRidMap).restrictScalars R)
        (Ideal.toCotangent (Ideal.map eRidAlg.toRingHom J)
          ⟨algebraMap R C x * c, hxRid⟩) := by
            exact congrArg
              ((Ideal.Cotangent.equivOfEq
                (Ideal.map eRidAlg.toRingHom J)
                (Ideal.map (algebraMap R C) I)
                hRidMap).restrictScalars R)
              hMap
    _ =
      Ideal.toCotangent (Ideal.map (algebraMap R C) I)
        ⟨c * algebraMap R C x,
          Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (algebraMap R C) x.2)⟩ := by
          rw [hEqToCot]
          congr 1
          apply Subtype.ext
          simp [mul_comm]

/-- Helper for Chap10 Lemma 10 143 11: if `ker qB` is the mapped ideal `Ideal.map g I`, then the
source ideal `I` maps into the target kernel. -/
lemma sourceIdeal_le_comap_targetKernelOfKerEqMap
    {R : Type*} [CommRing R] {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {g : R →+* B₁} {qB : B₁ →+* B₀}
    (hTgt : RingHom.ker qB = Ideal.map g I) :
    I ≤ Ideal.comap g (RingHom.ker qB) := by
  intro x hx
  -- Rewrite the target kernel through the mapped ideal so the membership is immediate.
  rw [Ideal.mem_comap]
  simpa [hTgt] using (Ideal.mem_map_of_mem g hx : g x ∈ Ideal.map g I)

/-- Helper for Chap10 Lemma 10 143 11: the theorem-specific base-change hypothesis for the chosen
square-zero lift packages the target cotangent module as the quotient tensor model of `I`. -/
abbrev chosenLiftBaseChangeCotangentEquiv
    {R : Type*} [CommRing R] {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {g : R →+* B₁} {qB : B₁ →+* B₀}
    (hTgt : RingHom.ker qB = Ideal.map g I) : Prop :=
  letI : Algebra R B₁ := g.toAlgebra
  let hker : I ≤ Ideal.comap g (RingHom.ker qB) :=
    sourceIdeal_le_comap_targetKernelOfKerEqMap hTgt
  letI : Algebra (R ⧸ I) (B₁ ⧸ RingHom.ker qB) :=
    Ideal.Quotient.algebraQuotientOfLEComap hker
  ∃ e :
      ((B₁ ⧸ RingHom.ker qB) ⊗[R ⧸ I] I.Cotangent) ≃ₗ[B₁ ⧸ RingHom.ker qB]
        (RingHom.ker qB).Cotangent,
    ∀ x : I,
      e (1 ⊗ₜ[R ⧸ I] Ideal.toCotangent I x) =
        Ideal.toCotangent (RingHom.ker qB) ⟨g x, by
          have hxmap : g x ∈ Ideal.map g I := Ideal.mem_map_of_mem g x.2
          simpa [hTgt] using hxmap⟩

/-- Helper for Chap10 Lemma 10 143 11: replacing the quotient base `R ⧸ I` by `R` in the tensor
model of `I.Cotangent` is the standard `lidOfCompatibleSMul` followed by cancellation of the
redundant base change. -/
noncomputable def quotientBaseTensorCotangentEquiv
    {R : Type*} [CommRing R] {I : Ideal R} {T : Type*} [CommRing T]
    [Algebra R T] [Algebra (R ⧸ I) T] [IsScalarTower R (R ⧸ I) T] :
    (T ⊗[R ⧸ I] I.Cotangent) ≃ₗ[T] (T ⊗[R] I.Cotangent) := by
  letI : IsScalarTower R (R ⧸ I) I.Cotangent :=
    Module.IsTorsionBySet.isScalarTower (Ideal.isTorsionBySet_cotangent I)
  haveI : Algebra.IsEpi R (R ⧸ I) :=
    Algebra.isEpi_of_surjective_algebraMap R (R ⧸ I) Ideal.Quotient.mk_surjective
  let eLift :
      (T ⊗[R ⧸ I] I.Cotangent) ≃ₗ[T]
        (T ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] I.Cotangent)) :=
    TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl T _)
      (TensorProduct.lid' R (R ⧸ I) I.Cotangent).symm
  -- First insert the redundant `(R ⧸ I)`-factor, then cancel it on the acting ring.
  exact eLift.trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) T T I.Cotangent)

/-- Helper for Chap10 Lemma 10 143 11: the quotient-base normalization sends the distinguished
tensor generator `1 ⊗ₜ[R ⧸ I] Ideal.toCotangent I x` to the corresponding `R`-tensor generator. -/
lemma quotientBaseTensorCotangentEquiv_applyOneTmul
    {R : Type*} [CommRing R] {I : Ideal R} {T : Type*} [CommRing T]
    [Algebra R T] [Algebra (R ⧸ I) T] [IsScalarTower R (R ⧸ I) T]
    (x : I) :
    (quotientBaseTensorCotangentEquiv :
      (T ⊗[R ⧸ I] I.Cotangent) ≃ₗ[T] (T ⊗[R] I.Cotangent))
        (1 ⊗ₜ[R ⧸ I] Ideal.toCotangent I x) =
      (1 : T) ⊗ₜ[R] Ideal.toCotangent I x := by
  -- Unfold the normal-form equivalence once; both the inserted `lid'` and the base-change
  -- cancellation preserve the distinguished generator.
  simp [quotientBaseTensorCotangentEquiv]

/-- Helper for Chap10 Lemma 10 143 11: the quotient-base normalization fixes every pure tensor
whose cotangent factor is a distinguished generator. -/
lemma quotientBaseTensorCotangentEquiv_apply_tmul
    {R : Type*} [CommRing R] {I : Ideal R} {T : Type*} [CommRing T]
    [Algebra R T] [Algebra (R ⧸ I) T] [IsScalarTower R (R ⧸ I) T]
    (t : T) (x : I) :
    (quotientBaseTensorCotangentEquiv :
      (T ⊗[R ⧸ I] I.Cotangent) ≃ₗ[T] (T ⊗[R] I.Cotangent))
        (t ⊗ₜ[R ⧸ I] Ideal.toCotangent I x) =
      t ⊗ₜ[R] Ideal.toCotangent I x := by
  -- First rewrite the pure tensor as a scalar multiple of the distinguished generator `1 ⊗ x`.
  calc
    (quotientBaseTensorCotangentEquiv :
        (T ⊗[R ⧸ I] I.Cotangent) ≃ₗ[T] (T ⊗[R] I.Cotangent))
        (t ⊗ₜ[R ⧸ I] Ideal.toCotangent I x) =
      (quotientBaseTensorCotangentEquiv :
        (T ⊗[R ⧸ I] I.Cotangent) ≃ₗ[T] (T ⊗[R] I.Cotangent))
        (t • ((1 : T) ⊗ₜ[R ⧸ I] Ideal.toCotangent I x)) := by
          rw [TensorProduct.tmul_eq_smul_one_tmul]
    _ = t •
        ((quotientBaseTensorCotangentEquiv :
          (T ⊗[R ⧸ I] I.Cotangent) ≃ₗ[T] (T ⊗[R] I.Cotangent))
          (1 ⊗ₜ[R ⧸ I] Ideal.toCotangent I x)) := by
            rw [LinearEquiv.map_smul]
    _ = t • ((1 : T) ⊗ₜ[R] Ideal.toCotangent I x) := by
          rw [quotientBaseTensorCotangentEquiv_applyOneTmul]
    _ = t ⊗ₜ[R] Ideal.toCotangent I x := by
          rw [← TensorProduct.tmul_eq_smul_one_tmul]

/-- Helper for Chap10 Lemma 10 143 11: the inverse quotient-base normalization sends the pure
`R`-tensor `t ⊗ Ideal.toCotangent I x` back to the corresponding `R ⧸ I`-tensor. -/
lemma quotientBaseTensorCotangentEquiv_symm_apply_tmul
    {R : Type*} [CommRing R] {I : Ideal R} {T : Type*} [CommRing T]
    [Algebra R T] [Algebra (R ⧸ I) T] [IsScalarTower R (R ⧸ I) T]
    (t : T) (x : I) :
    ((quotientBaseTensorCotangentEquiv :
        (T ⊗[R ⧸ I] I.Cotangent) ≃ₗ[T] (T ⊗[R] I.Cotangent)).symm)
        (t ⊗ₜ[R] Ideal.toCotangent I x) =
      t ⊗ₜ[R ⧸ I] Ideal.toCotangent I x := by
  -- Proof comment: apply the forward normalization to both sides and reuse the direct formula on
  -- pure tensors.
  apply (quotientBaseTensorCotangentEquiv (R := R) (I := I) (T := T)).injective
  simpa using
    (quotientBaseTensorCotangentEquiv_apply_tmul (R := R) (I := I) (T := T) t x).symm

/-- Helper for Chap10 Lemma 10 143 11: `TensorProduct.congr` evaluates on a pure tensor by
transporting each factor separately. -/
theorem tensorProductCongr_apply_tmul
    {R : Type*} [CommSemiring R]
    {A : Type*} {B : Type*} {A' : Type*} {B' : Type*}
    [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [AddCommMonoid A'] [Module R A'] [AddCommMonoid B'] [Module R B']
    (e₁ : A ≃ₗ[R] A') (e₂ : B ≃ₗ[R] B') (a : A) (b : B) :
    TensorProduct.congr e₁ e₂ (a ⊗ₜ[R] b) = e₁ a ⊗ₜ[R] e₂ b := by
  -- Proof comment: `TensorProduct.congr` is defined on pure tensors by acting factorwise.
  rfl

/-- Helper for Chap10 Lemma 10 143 11: after rewriting the source quotient
`C ⧸ Ideal.map (algebraMap R C) I` to the literal quotient by `ker q`, the canonical quotient
equivalence still evaluates on `mk c` as `q c`. -/
lemma quotientEquivAlgOfEq_trans_quotientKerAlgEquivOfSurjective_mk
    {R : Type*} [CommRing R] {C : Type*} [CommRing C] {B₀ : Type*} [CommRing B₀]
    [Algebra R C] [Algebra R B₀]
    {I : Ideal R} {qAlg : C →ₐ[R] B₀}
    (hSurj : Function.Surjective qAlg)
    (hKer : RingHom.ker qAlg.toRingHom = Ideal.map (algebraMap R C) I)
    (c : C) :
    ((Ideal.quotientEquivAlgOfEq R hKer.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := qAlg) hSurj))
        (Ideal.Quotient.mk _ c) = qAlg c := by
  -- The first quotient equivalence only rewrites the ideal spelling, and the second is the usual
  -- quotient-by-kernel equivalence attached to the surjective map `qAlg`.
  change
    Ideal.quotientKerAlgEquivOfSurjective hSurj
        ((Ideal.quotientEquivAlgOfEq R hKer.symm) (Ideal.Quotient.mk _ c)) =
      qAlg c
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (f := qAlg) hSurj c

/-- Helper for Lemma 10.143.11: once a lift `B₁ → C` of the quotient map `qB : B₁ → B₀` exists,
formal unramifiedness of the source map `R → C` forces the comparison map `φ : C → B₁` to be
injective. -/
lemma comparison_injective_of_lift_back_of_formallyUnramified
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hqφ : qB.comp φ = qC)
    (hφ : φ.comp (algebraMap R C) = algebraMap R B₁)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥)
    (hUnram : (algebraMap R C).FormallyUnramified)
    (ψAlg : B₁ →ₐ[R] C)
    (hψ : qC.comp ψAlg.toRingHom = qB) :
    Function.Injective φ := by
  let φAlg : C →ₐ[R] B₁ :=
    { toRingHom := φ
      commutes' := fun r ↦ by
        -- Read `φ` as the `R`-algebra map determined by the commuting square.
        exact congrArg (fun h : R →+* B₁ ↦ h r) hφ }
  have hnil : IsNilpotent (RingHom.ker qC) := by
    -- The source kernel is the mapped square-zero ideal, hence nilpotent.
    rw [hSrc]
    exact isNilpotent_of_square_zero (Ideal.map (algebraMap R C) I) hSrcSq
  letI : Algebra.FormallyUnramified R C :=
    RingHom.formallyUnramified_algebraMap.mp hUnram
  have hleft : ψAlg.comp φAlg = AlgHom.id R C := by
    -- Both composites `ψ ∘ φ` and `id_C` reduce to the same quotient map `qC`.
    apply Algebra.FormallyUnramified.lift_unique_of_ringHom qC hnil
    ext x
    have hψx := congrArg (fun h : B₁ →+* B₀ ↦ h (φ x)) hψ
    have hqφx := congrArg (fun h : C →+* B₀ ↦ h x) hqφ
    simpa [AlgHom.comp_apply, RingHom.comp_apply, φAlg] using hψx.trans hqφx
  intro x y hxy
  -- Evaluate the left inverse on `φ x = φ y`.
  have hx : ψAlg (φ x) = x := by
    simpa [φAlg] using congrArg (fun h : C →ₐ[R] C ↦ h x) hleft
  have hy : ψAlg (φ y) = y := by
    simpa [φAlg] using congrArg (fun h : C →ₐ[R] C ↦ h y) hleft
  calc
    x = ψAlg (φ x) := hx.symm
    _ = ψAlg (φ y) := by rw [hxy]
    _ = y := hy

/-- Helper for Chap10 Lemma 10 143 11: if the residual kernel
`RingHom.ker φAlg.toRingHom ⊓ Ideal.map (algebraMap R C) I` vanishes, then the induced cotangent
comparison between the mapped square-zero ideals is bijective. -/
lemma mapCotangentBijectiveOfResidualKernelBot
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hSurj : Function.Surjective φAlg.toRingHom)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hResidual :
      RingHom.ker φAlg.toRingHom ⊓ Ideal.map (algebraMap R C) I = ⊥) :
    Function.Bijective
      (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
        φAlg
        (RingHom.ideal_map_le_comap_of_comp_eq (algebraMap R C) (algebraMap R B₁)
          φAlg.toRingHom I hcomp)) := by
  -- First use the packaged cotangent comparison theorem to get surjectivity and the exact kernel.
  rcases mapCotangent_surjective_and_ker_eq_residual_of_comp_eq_of_ker_eq
      hSurj hq hcomp hSrc hTgt with ⟨hCotSurj, hCotKer⟩
  have hResidualCot :
      ((Submodule.comap (Ideal.map (algebraMap R C) I).subtype (RingHom.ker φAlg.toRingHom)).map
        (Ideal.toCotangent (Ideal.map (algebraMap R C) I))).restrictScalars R = ⊥ := by
    -- The residual cotangent kernel disappears as soon as the residual ideal itself is zero.
    simpa using congrArg (fun K ↦ K.restrictScalars R)
      (residual_cotangent_kernel_eq_bot_of_inf_eq_bot
        (Ideal.map (algebraMap R C) I) (RingHom.ker φAlg.toRingHom) hResidual)
  have hCotInj :
      Function.Injective
        (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
          φAlg
          (RingHom.ideal_map_le_comap_of_comp_eq (algebraMap R C) (algebraMap R B₁)
            φAlg.toRingHom I hcomp)) := by
    -- Zero kernel upgrades the cotangent comparison to an injective linear map.
    apply LinearMap.ker_eq_bot.mp
    rw [hCotKer, hResidualCot]
  exact ⟨hCotInj, hCotSurj⟩

/-- Helper for Chap10 Lemma 10 143 11: in a commuting square `qB.comp φ = qC`, surjectivity of
the source quotient map `qC` and of the comparison map `φ` forces surjectivity of `qB`. -/
lemma surjective_of_surjective_comp_eq
    {A : Type*} [CommRing A] {B : Type*} [CommRing B] {C : Type*} [CommRing C]
    {φ : A →+* B} {qA : A →+* C} {qB : B →+* C}
    (hSurjA : Function.Surjective qA)
    (hcomp : qB.comp φ = qA) :
    Function.Surjective qB := by
  intro c
  -- First lift `c` through `qA`, then apply `φ` to that source point.
  obtain ⟨a, ha⟩ := hSurjA c
  refine ⟨φ a, ?_⟩
  calc
    qB (φ a) = qA a := by
      simpa [RingHom.comp_apply] using congrArg (fun h : A →+* C ↦ h a) hcomp
    _ = c := ha

/-- Helper for Chap10 Lemma 10 143 11: after identifying the source and target quotient kernels
with the textbook ideals, surjectivity of the explicit ideal comparison transports to surjectivity
of the owner kernel restriction map. -/
lemma kernel_restrict_surjective_of_ideal_map_surjective
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φ : C →+* B₁}
    (hq : qB.comp φ = qC) (hcomp : φ.comp c = g)
    (hSrc : RingHom.ker qC = Ideal.map c I)
    (hTgt : RingHom.ker qB = Ideal.map g I)
    (hIdealSurj : Function.Surjective (ideal_map_restrict c g φ I hcomp)) :
    Function.Surjective (kernel_restrict hq) := by
  intro y
  let yIdeal : Ideal.map g I := (ideal_equiv_ker qB (Ideal.map g I) hTgt).symm y
  obtain ⟨x, hx⟩ := hIdealSurj yIdeal
  refine ⟨(ideal_equiv_ker qC (Ideal.map c I) hSrc) x, ?_⟩
  -- Compare the kernel restriction with the explicit ideal map in the ideal coordinates.
  apply (ideal_equiv_ker qB (Ideal.map g I) hTgt).symm.injective
  calc
    (ideal_equiv_ker qB (Ideal.map g I) hTgt).symm
        (kernel_restrict hq
          ((ideal_equiv_ker qC (Ideal.map c I) hSrc) x)) =
      ideal_map_restrict c g φ I hcomp x := by
        simpa using
          kernel_restrict_eq_ideal_map_restrict hq hcomp hSrc hTgt x
    _ = yIdeal := hx
    _ = (ideal_equiv_ker qB (Ideal.map g I) hTgt).symm y := rfl

/-- Helper for Chap10 Lemma 10 143 11: injectivity of the ambient comparison ring map already
makes the explicit textbook ideal comparison injective. -/
lemma ideal_map_restrict_injective_of_ringHom_injective
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {φ : C →+* B₁}
    (hcomp : φ.comp (algebraMap R C) = algebraMap R B₁)
    (hφInj : Function.Injective φ) :
    Function.Injective
      (ideal_map_restrict (algebraMap R C) (algebraMap R B₁) φ I hcomp) := by
  intro x y hxy
  -- Compare the underlying ring elements and then use injectivity of `φ`.
  apply Subtype.ext
  exact hφInj (congrArg Subtype.val hxy)

/-- Helper for Chap10 Lemma 10 143 11: once the comparison ring map is injective, the residual
kernel inside the source textbook ideal is already zero. -/
lemma comparisonResidualKernelBotOfInjectiveComparison
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {φ : C →+* B₁}
    (hcomp : φ.comp (algebraMap R C) = algebraMap R B₁)
    (hφInj : Function.Injective φ) :
    RingHom.ker φ ⊓ Ideal.map (algebraMap R C) I = ⊥ := by
  -- Reduce the residual-kernel statement to injectivity of the textbook ideal comparison.
  exact RingHom.inf_eq_bot_of_ideal_map_restrict_injective hcomp
    (ideal_map_restrict_injective_of_ringHom_injective hcomp hφInj)

/-- Helper for Chap10 Lemma 10 143 11: the kernel of the comparison map `φAlg : C →ₐ[R] B₁`
already lies in the normalized source ideal because every element killed by `φAlg` is also killed
by the quotient map `qC`. -/
lemma comparisonKernel_le_sourceIdeal
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hq : qB.comp φAlg.toRingHom = qC)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I) :
    RingHom.ker φAlg.toRingHom ≤ Ideal.map (algebraMap R C) I := by
  -- Compare `qB ∘ φAlg` with `qC`, then use the source-kernel normalization.
  exact ker_le_ideal_map_of_comp_eq_of_ker_eq hq hSrc

/-- Helper for Chap10 Lemma 10 143 11: the comparison kernel is square-zero because it sits
inside the square-zero source ideal `Ideal.map (algebraMap R C) I`. -/
lemma comparisonKernel_squareZero
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hq : qB.comp φAlg.toRingHom = qC)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥) :
    (RingHom.ker φAlg.toRingHom) ^ 2 = ⊥ := by
  -- First place the comparison kernel in the source ideal, then inherit square-zero.
  exact square_zero_of_le_square_zero_ideal
    (comparisonKernel_le_sourceIdeal hq hSrc)
    hSrcSq

/-- Helper for Chap10 Lemma 10 143 11: the normalized target quotient kernel is nilpotent because
the mapped ideal `Ideal.map (algebraMap R B₁) I` is square-zero. -/
lemma targetKernelNilpotentOfMappedSquareZero
    {R : Type*} [CommRing R] {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R B₁]
    {I : Ideal R} {qB : B₁ →+* B₀}
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I) :
    IsNilpotent (RingHom.ker qB) := by
  have hTgtKerSq : (RingHom.ker qB) ^ 2 = ⊥ := by
    -- Rewrite the square-zero condition in the literal quotient-kernel spelling.
    simpa [hTgt] using hTgtSq
  -- Square-zero ideals are nilpotent of exponent at most `2`.
  exact isNilpotent_of_square_zero (RingHom.ker qB) hTgtKerSq

/-- Helper for Chap10 Lemma 10 143 11: a surjective formally étale comparison map with square-zero
kernel is already injective. -/
lemma comparisonInjectiveOfFormallyEtaleSurjective
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {φAlg : C →ₐ[R] B₁}
    (hSurj : Function.Surjective φAlg.toRingHom)
    (hForm : φAlg.toRingHom.FormallyEtale)
    (hKerSq : (RingHom.ker φAlg.toRingHom) ^ 2 = ⊥) :
    Function.Injective φAlg.toRingHom := by
  letI : Algebra C B₁ := φAlg.toRingHom.toAlgebra
  have hFormAlg : Algebra.FormallyEtale C B₁ := by
    -- Reinterpret the owner predicate on `φAlg.toRingHom` as the canonical algebra instance.
    simpa [RingHom.FormallyEtale, RingHom.algebraMap_toAlgebra] using hForm
  letI : Algebra.FormallyEtale C B₁ := hFormAlg
  have hkerIdem : IsIdempotentElem (RingHom.ker φAlg.toRingHom) := by
    -- Surjective formally étale algebra maps are exactly the ones with idempotent kernel.
    simpa [RingHom.algebraMap_toAlgebra] using
      (Algebra.FormallyEtale.iff_of_surjective hSurj).mp hFormAlg
  have hkerBot : RingHom.ker φAlg.toRingHom = ⊥ := by
    -- An idempotent square-zero ideal must vanish.
    exact eq_bot_of_isIdempotentElem_of_le_square_zero hkerIdem le_rfl hKerSq
  -- Kernel zero is the standard owner criterion for injectivity.
  exact (RingHom.injective_iff_ker_eq_bot φAlg.toRingHom).2 hkerBot

/-- Helper for Chap10 Lemma 10 143 11: the mapped source ideal
`Ideal.map (algebraMap R C) I` acts trivially on the tensor model `C ⊗[R] I.Cotangent`, so the
corresponding scalar multiple submodule is zero. -/
lemma mappedIdeal_smul_top_tensorCotangent_eq_bot
    {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
    {I : Ideal R} :
    (Ideal.map (algebraMap R C) I • (⊤ : Submodule C (C ⊗[R] I.Cotangent))) = ⊥ := by
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_bot]
    -- Every generator of the scalar multiple submodule already acts by zero on the tensor model.
    refine Submodule.smul_induction_on hz ?_ (fun _ _ hz₁ hz₂ ↦ by simp [hz₁, hz₂])
    intro x hx y hy
    simpa using
      mapped_ideal_smul_tensor_cotangent_eq_zero I ⟨x, hx⟩ y
  · exact bot_le

/-- Helper for Chap10 Lemma 10 143 11: quotienting the tensor model `C ⊗[R] I.Cotangent` by the
source mapped ideal does not change it, because that ideal acts trivially. -/
noncomputable def sourceTensorCotangentQuotientEquiv
    {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
    {I : Ideal R} :
    ((C ⧸ Ideal.map (algebraMap R C) I) ⊗[C] (C ⊗[R] I.Cotangent)) ≃ₗ[C]
      C ⊗[R] I.Cotangent := by
  let eQuot :=
    TensorProduct.quotTensorEquivQuotSMul
      (C ⊗[R] I.Cotangent)
      (Ideal.map (algebraMap R C) I)
  have hsmulBot :
      (Ideal.map (algebraMap R C) I • (⊤ : Submodule C (C ⊗[R] I.Cotangent))) = ⊥ := by
    -- The tensor model is already annihilated by the mapped source ideal.
    exact mappedIdeal_smul_top_tensorCotangent_eq_bot
  -- Replace the quotient by the zero submodule with the original tensor model.
  exact eQuot.trans <|
    Submodule.quotEquivOfEqBot _ hsmulBot

/-- Helper for Chap10 Lemma 10 143 11: after rewriting the source quotient as
`C ⧸ Ideal.map (algebraMap R C) I`, the quotient-tensor common model identifies with the original
tensor model `C ⊗[R] I.Cotangent`. -/
noncomputable def sourceMappedIdealQuotientTensorEquiv
    {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
    {I : Ideal R} :
    ((C ⧸ Ideal.map (algebraMap R C) I) ⊗[R] I.Cotangent) ≃ₗ[R] C ⊗[R] I.Cotangent := by
  let eCancel :
      ((C ⧸ Ideal.map (algebraMap R C) I) ⊗[R] I.Cotangent) ≃ₗ[R]
        ((C ⧸ Ideal.map (algebraMap R C) I) ⊗[C] (C ⊗[R] I.Cotangent)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      R C (C ⧸ Ideal.map (algebraMap R C) I)
      (C ⧸ Ideal.map (algebraMap R C) I) I.Cotangent).symm.restrictScalars R
  let eQuot :
      ((C ⧸ Ideal.map (algebraMap R C) I) ⊗[C] (C ⊗[R] I.Cotangent)) ≃ₗ[R]
        C ⊗[R] I.Cotangent :=
    (sourceTensorCotangentQuotientEquiv :
      ((C ⧸ Ideal.map (algebraMap R C) I) ⊗[C] (C ⊗[R] I.Cotangent)) ≃ₗ[C]
        C ⊗[R] I.Cotangent).restrictScalars R
  -- First insert the redundant base change over `C`, then remove the quotient by the annihilating
  -- mapped ideal.
  exact eCancel.trans eQuot

/-- Helper for Chap10 Lemma 10 143 11: the source cotangent module can be expressed from the
quotient-tensor model `((C ⧸ Ideal.map (algebraMap R C) I) ⊗[R] I.Cotangent)` without changing the
final cotangent target. -/
noncomputable def sourceMappedIdealCotangentCommonModel
    {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
    {I : Ideal R}
    (hcEtale : (algebraMap R C).Etale) :
    ((C ⧸ Ideal.map (algebraMap R C) I) ⊗[R] I.Cotangent) ≃ₗ[R]
      (Ideal.map (algebraMap R C) I).Cotangent := by
  -- Collapse the quotient-tensor model back to `C ⊗[R] I.Cotangent`, then apply the flat
  -- base-change description of the source cotangent module.
  exact
    sourceMappedIdealQuotientTensorEquiv.trans
      (sourceMappedIdealCotangentEquivOfEtale hcEtale)

/-- Helper for Chap10 Lemma 10 143 11: the quotient-tensor source common model sends the pure
tensor `mk c ⊗ Ideal.toCotangent I x` to the literal tensor `c ⊗ Ideal.toCotangent I x`. -/
lemma sourceMappedIdealQuotientTensorEquiv_apply_mk_tmul
    {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
    {I : Ideal R} (c : C) (x : I) :
    sourceMappedIdealQuotientTensorEquiv
        (R := R) (C := C) (I := I)
        (Ideal.Quotient.mk (Ideal.map (algebraMap R C) I) c ⊗ₜ[R] Ideal.toCotangent I x) =
      c ⊗ₜ[R] Ideal.toCotangent I x := by
  -- Proof comment: first insert the redundant base-change factor, then remove the quotient by the
  -- annihilating mapped ideal; the standard pure-tensor formulas compute the whole composite.
  calc
    sourceMappedIdealQuotientTensorEquiv
        (R := R) (C := C) (I := I)
        (Ideal.Quotient.mk (Ideal.map (algebraMap R C) I) c ⊗ₜ[R] Ideal.toCotangent I x) =
      c • ((1 : C) ⊗ₜ[R] Ideal.toCotangent I x) := by
        simp [sourceMappedIdealQuotientTensorEquiv, sourceTensorCotangentQuotientEquiv,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
    _ = c ⊗ₜ[R] Ideal.toCotangent I x := by
      rw [← TensorProduct.tmul_eq_smul_one_tmul]

/-- Helper for Chap10 Lemma 10 143 11: the inverse source quotient-tensor equivalence sends the
literal tensor `c ⊗ Ideal.toCotangent I x` back to the quotient tensor `mk c ⊗ Ideal.toCotangent
I x`. -/
lemma sourceMappedIdealQuotientTensorEquiv_symm_apply_tmul
    {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C]
    {I : Ideal R} (c : C) (x : I) :
    (sourceMappedIdealQuotientTensorEquiv
        (R := R) (C := C) (I := I)).symm (c ⊗ₜ[R] Ideal.toCotangent I x) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R C) I) c ⊗ₜ[R] Ideal.toCotangent I x := by
  -- Proof comment: apply the forward quotient-tensor equivalence to both sides and reuse the
  -- direct generator computation already proved above.
  apply (sourceMappedIdealQuotientTensorEquiv (R := R) (C := C) (I := I)).injective
  simpa using
    (sourceMappedIdealQuotientTensorEquiv_apply_mk_tmul (R := R) (C := C) (I := I) c x).symm

/-- Helper for Chap10 Lemma 10 143 11: the inverse source quotient equivalence sends the quotient
point `qC c` back to the literal source class `mk c`. -/
lemma sourceQuotientEquiv_symm_apply_qC
    {R : Type*} [CommRing R] {C : Type*} [CommRing C] {B₀ : Type*} [CommRing B₀]
    [Algebra R C] [Algebra R B₀]
    {I : Ideal R} {qCAlg : C →ₐ[R] B₀}
    (hSurjC : Function.Surjective qCAlg)
    (hSrc : RingHom.ker qCAlg.toRingHom = Ideal.map (algebraMap R C) I)
    (c : C) :
    let eSrcQuot : (C ⧸ Ideal.map (algebraMap R C) I) ≃ₐ[R] B₀ :=
      (Ideal.quotientEquivAlgOfEq R hSrc.symm).trans
        (Ideal.quotientKerAlgEquivOfSurjective (f := qCAlg) hSurjC)
    eSrcQuot.symm (qCAlg c) = Ideal.Quotient.mk _ c := by
  -- The source quotient is just the standard quotient-by-kernel model rewritten through `hSrc`.
  dsimp
  exact
    (((Ideal.quotientEquivAlgOfEq R hSrc.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := qCAlg) hSurjC)).symm_apply_eq).2
      (quotientEquivAlgOfEq_trans_quotientKerAlgEquivOfSurjective_mk
        (R := R) (qAlg := qCAlg) hSurjC hSrc c)

/-- Helper for Chap10 Lemma 10 143 11: the inverse target quotient equivalence sends the common
quotient point `qC c` back to the class of `φAlg c`. -/
lemma targetQuotientKerEquiv_symm_apply_qC
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁] [Algebra R B₀]
    {qCAlg : C →ₐ[R] B₀} {qBAlg : B₁ →ₐ[R] B₀} {φAlg : C →ₐ[R] B₁}
    (hSurjB : Function.Surjective qBAlg)
    (hq : qBAlg.comp φAlg = qCAlg)
    (c : C) :
    let eTgtQuot : (B₁ ⧸ RingHom.ker qBAlg.toRingHom) ≃ₐ[R] B₀ :=
      Ideal.quotientKerAlgEquivOfSurjective (f := qBAlg) hSurjB
    eTgtQuot.symm (qCAlg c) = Ideal.Quotient.mk _ (φAlg c) := by
  -- The target quotient inverse is normalized by the commuting square `qB ∘ φAlg = qC`.
  dsimp
  exact
    ((Ideal.quotientKerAlgEquivOfSurjective (f := qBAlg) hSurjB).symm_apply_eq).2 <|
      (congrArg (fun f : C →ₐ[R] B₀ ↦ f c) hq).symm.trans <|
        (Ideal.quotientKerAlgEquivOfSurjective_mk (f := qBAlg) hSurjB (φAlg c)).symm

/-- Helper for Chap10 Lemma 10 143 11: the target quotient equivalence sends the class of `φAlg c`
to the common quotient point `qC c`. -/
lemma targetQuotientKerEquiv_apply_mk
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁] [Algebra R B₀]
    {qCAlg : C →ₐ[R] B₀} {qBAlg : B₁ →ₐ[R] B₀} {φAlg : C →ₐ[R] B₁}
    (hSurjB : Function.Surjective qBAlg)
    (hq : qBAlg.comp φAlg = qCAlg)
    (c : C) :
    let eTgtQuot : (B₁ ⧸ RingHom.ker qBAlg.toRingHom) ≃ₐ[R] B₀ :=
      Ideal.quotientKerAlgEquivOfSurjective (f := qBAlg) hSurjB
    eTgtQuot (Ideal.Quotient.mk _ (φAlg c)) = qCAlg c := by
  -- Proof comment: after identifying the target quotient with `B₀`, the class of `φAlg c`
  -- evaluates by the defining formula of `quotientKerAlgEquivOfSurjective`.
  dsimp
  exact
    (Ideal.quotientKerAlgEquivOfSurjective_mk (f := qBAlg) hSurjB (φAlg c)).trans
      (congrArg (fun f : C →ₐ[R] B₀ ↦ f c) hq)

/-- Helper for Chap10 Lemma 10 143 11: transport the source cotangent module to the quotient
tensor common model `B₀ ⊗[R] I.Cotangent` by rewriting `B₀` as the quotient of `C`. -/
noncomputable def chosenLiftSourceCotangentEquiv
    {R : Type*} [CommRing R] {C : Type*} [CommRing C] {B₀ : Type*} [CommRing B₀]
    [Algebra R C] {I : Ideal R} {qC : C →+* B₀}
    (hcEtale : (algebraMap R C).Etale)
    (hSurjC : Function.Surjective qC)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I) :
    let _ : Algebra R B₀ := RingHom.toAlgebra (qC.comp (algebraMap R C))
    B₀ ⊗[R] I.Cotangent ≃ₗ[R] (Ideal.map (algebraMap R C) I).Cotangent := by
  letI : Algebra R B₀ := RingHom.toAlgebra (qC.comp (algebraMap R C))
  let qCAlg : C →ₐ[R] B₀ :=
    { toRingHom := qC
      commutes' := fun r ↦ rfl }
  let eSrcQuot : (C ⧸ Ideal.map (algebraMap R C) I) ≃ₐ[R] B₀ :=
    (Ideal.quotientEquivAlgOfEq R hSrc.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := qCAlg) hSurjC)
  -- First rewrite the common quotient `B₀` as the source quotient, then use the established
  -- source cotangent common model on that quotient tensor.
  exact
    (TensorProduct.congr eSrcQuot.symm.toLinearEquiv (LinearEquiv.refl R _)).trans
      (sourceMappedIdealCotangentCommonModel hcEtale)

/-- Helper for Chap10 Lemma 10 143 11: the quotient algebra induced by `hTgt` fits into the
scalar tower `R → R ⧸ I → B₁ ⧸ ker qB`, which is the compatibility needed by the quotient-base
tensor normalization. -/
lemma chosenLiftTargetQuotientTensorTower
    {R : Type*} [CommRing R] {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R B₁] {I : Ideal R} {qB : B₁ →+* B₀}
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I) :
    let hle : I ≤ Ideal.comap (algebraMap R B₁) (RingHom.ker qB) :=
      sourceIdeal_le_comap_targetKernelOfKerEqMap hTgt
    letI : Algebra (R ⧸ I) (B₁ ⧸ RingHom.ker qB) :=
      Ideal.Quotient.algebraQuotientOfLEComap hle
    IsScalarTower R (R ⧸ I) (B₁ ⧸ RingHom.ker qB) := by
  let hle : I ≤ Ideal.comap (algebraMap R B₁) (RingHom.ker qB) :=
    sourceIdeal_le_comap_targetKernelOfKerEqMap hTgt
  letI : Algebra (R ⧸ I) (B₁ ⧸ RingHom.ker qB) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (sourceIdeal_le_comap_targetKernelOfKerEqMap hTgt)
  -- The quotient algebra map is definitionally compatible with the ambient `R`-algebra map.
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- Helper for Chap10 Lemma 10 143 11: an `S`-linear equivalence can be viewed as `R`-linear
after restricting scalars along `R → S`, once the module structures are fixed. -/
noncomputable def linearEquivRestrictScalars
    {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    {M : Type*} [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower R S M]
    {N : Type*} [AddCommMonoid N] [Module S N] [Module R N] [IsScalarTower R S N]
    (e : M ≃ₗ[S] N) : M ≃ₗ[R] N :=
  e.restrictScalars R

/-- Helper for Chap10 Lemma 10 143 11: in the chosen-lift context, the theorem's quotient-level
base-change cotangent datum is exactly the extra input needed to recover injectivity of the
comparison map `φAlg : C →ₐ[R] B₁`. -/
lemma chosenLiftComparisonInjectiveOfBaseChange
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hcEtale : (algebraMap R C).Etale)
    (hSurjC : Function.Surjective qC)
    (hSurjB : Function.Surjective qB)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥)
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hBaseChange : chosenLiftBaseChangeCotangentEquiv hTgt) :
    Function.Injective φAlg.toRingHom := by
  letI : Algebra R B₀ := RingHom.toAlgebra (qC.comp (algebraMap R C))
  have hSurjφ : Function.Surjective φAlg.toRingHom := by
    have hIdealSurj :
        Function.Surjective
          (ideal_map_restrict (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp) := by
      -- The square-zero target kernel already makes the textbook ideal comparison surjective.
      exact ideal_map_restrict_surjective_of_square_zero hSurjC hq hcomp
        (by simpa [hTgt] using hTgtSq) hTgt
    -- Quotient surjectivity upgrades ideal-level surjectivity to surjectivity of `φAlg`.
    exact comparison_surjective_of_ideal_map_surjective hSurjC hq hcomp hTgt hIdealSurj
  let _ := hBaseChange
  let _ := hSurjφ
  let qCAlg : C →ₐ[R] B₀ :=
    { toRingHom := qC
      commutes' := fun r ↦ rfl }
  have hqBCommutes : ∀ r : R, qB (algebraMap R B₁ r) = algebraMap R B₀ r := by
    intro r
    -- Evaluate the commuting square on base elements so the target quotient inherits the expected
    -- `R`-algebra structure.
    change qB (algebraMap R B₁ r) = qC (algebraMap R C r)
    simpa [RingHom.comp_apply] using congrArg (fun f : C →+* B₀ ↦ f (algebraMap R C r)) hq
  let qBAlg : B₁ →ₐ[R] B₀ :=
    { toRingHom := qB
      commutes' := hqBCommutes }
  have hqAlg : qBAlg.comp φAlg = qCAlg := by
    -- The algebra-hom version of the commuting square is just the original ring-hom identity.
    ext c
    exact congrArg (fun f : C →+* B₀ ↦ f c) hq
  let eTgtQuot : (B₁ ⧸ RingHom.ker qB) ≃ₐ[R] B₀ :=
    Ideal.quotientKerAlgEquivOfSurjective (f := qBAlg) hSurjB
  let M := ((B₁ ⧸ RingHom.ker qB) ⊗[R] I.Cotangent)
  let eCotSrc : M ≃ₗ[R] (Ideal.map (algebraMap R C) I).Cotangent :=
    (TensorProduct.congr eTgtQuot.toLinearEquiv (LinearEquiv.refl R _)).trans
      (chosenLiftSourceCotangentEquiv hcEtale hSurjC hSrc)
  have hBaseChange' := hBaseChange
  dsimp [chosenLiftBaseChangeCotangentEquiv] at hBaseChange'
  rcases hBaseChange' with ⟨eBase, heBase⟩
  let hker : I ≤ Ideal.comap (algebraMap R B₁) (RingHom.ker qB) :=
    sourceIdeal_le_comap_targetKernelOfKerEqMap hTgt
  letI : Algebra (R ⧸ I) (B₁ ⧸ RingHom.ker qB) :=
    Ideal.Quotient.algebraQuotientOfLEComap hker
  letI : IsScalarTower R (R ⧸ I) (B₁ ⧸ RingHom.ker qB) :=
    chosenLiftTargetQuotientTensorTower hTgt
  letI : Module R ((B₁ ⧸ RingHom.ker qB) ⊗[R ⧸ I] I.Cotangent) :=
    Module.compHom _ (algebraMap R (B₁ ⧸ RingHom.ker qB))
  letI : Module R (RingHom.ker qB).Cotangent :=
    Module.compHom _ (algebraMap R (B₁ ⧸ RingHom.ker qB))
  letI : IsScalarTower R (B₁ ⧸ RingHom.ker qB) (RingHom.ker qB).Cotangent :=
    IsScalarTower.of_compHom R (B₁ ⧸ RingHom.ker qB) (RingHom.ker qB).Cotangent
  let eQuotBase :
      M ≃ₗ[R] ((B₁ ⧸ RingHom.ker qB) ⊗[R ⧸ I] I.Cotangent) :=
    linearEquivRestrictScalars
      ((quotientBaseTensorCotangentEquiv
        (R := R) (I := I) (T := B₁ ⧸ RingHom.ker qB)).symm)
  let eKerEq :
      (RingHom.ker qB).Cotangent ≃ₗ[R] (Ideal.map (algebraMap R B₁) I).Cotangent :=
    (Ideal.Cotangent.equivOfEq (RingHom.ker qB) (Ideal.map (algebraMap R B₁) I) hTgt)
      .restrictScalars R
  let eCotTgt : M ≃ₗ[R] (Ideal.map (algebraMap R B₁) I).Cotangent :=
    -- Proof comment: move from the `R`-tensor model to the quotient-base tensor, apply the
    -- base-change witness there, and then rewrite the target kernel along `hTgt`.
    eQuotBase.trans <| (eBase.restrictScalars R).trans eKerEq
  have hSrcGen :
      ∀ (c : C) (x : I),
        eCotSrc (Ideal.Quotient.mk _ (φAlg c) ⊗ₜ[R] Ideal.toCotangent I x) =
          Ideal.toCotangent (Ideal.map (algebraMap R C) I)
            ⟨c * algebraMap R C x,
              Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (algebraMap R C) x.2)⟩ := by
    intro c x
    -- Proof comment: rewrite the target quotient generator through the common quotient `B₀`, pull
    -- it back to the source quotient, and then evaluate the source cotangent common model.
    dsimp [eCotSrc]
    rw [tensorProductCongr_apply_tmul]
    have hqmk :
        eTgtQuot.toLinearEquiv (Ideal.Quotient.mk _ (φAlg c)) = qCAlg c := by
      simpa using
        targetQuotientKerEquiv_apply_mk
          (R := R) (C := C) (B₀ := B₀) (B₁ := B₁)
          (qCAlg := qCAlg) (qBAlg := qBAlg) (φAlg := φAlg) hSurjB hqAlg c
    rw [hqmk]
    have hqsrc :
        ((Ideal.quotientEquivAlgOfEq R hSrc.symm).trans
          (Ideal.quotientKerAlgEquivOfSurjective (f := qCAlg) hSurjC)).symm.toLinearEquiv
            (qCAlg c) =
          Ideal.Quotient.mk _ c := by
      simpa using
        sourceQuotientEquiv_symm_apply_qC
          (R := R) (C := C) (B₀ := B₀) (I := I) (qCAlg := qCAlg) hSurjC hSrc c
    rw [chosenLiftSourceCotangentEquiv, LinearEquiv.trans_apply, tensorProductCongr_apply_tmul, hqsrc]
    rw [sourceMappedIdealCotangentCommonModel, LinearEquiv.trans_apply,
      sourceMappedIdealQuotientTensorEquiv_apply_mk_tmul (R := R) (C := C) (I := I) c x]
    exact sourceMappedIdealCotangentEquivOfEtale_apply_tmul
      (R := R) (C := C) (I := I) hcEtale c x
  have hTgtGen :
      ∀ (c : C) (x : I),
        eCotTgt (Ideal.Quotient.mk _ (φAlg c) ⊗ₜ[R] Ideal.toCotangent I x) =
          Ideal.toCotangent (Ideal.map (algebraMap R B₁) I)
            ⟨φAlg c * algebraMap R B₁ x,
              Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (algebraMap R B₁) x.2)⟩ := by
    intro c x
    -- Proof comment: pass to the quotient-base tensor model, use the normalized base-change
    -- witness on the distinguished generator, and then rewrite the resulting scalar action as the
    -- target cotangent class of `φAlg c * algebraMap R B₁ x`.
    dsimp [eCotTgt]
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    rw [quotientBaseTensorCotangentEquiv_symm_apply_tmul]
    calc
      (eBase.restrictScalars R)
          (Ideal.Quotient.mk (RingHom.ker qB) (φAlg c) ⊗ₜ[R ⧸ I] Ideal.toCotangent I x) =
        Ideal.Quotient.mk (RingHom.ker qB) (φAlg c) •
          (eBase.restrictScalars R) (1 ⊗ₜ[R ⧸ I] Ideal.toCotangent I x) := by
            rw [TensorProduct.tmul_eq_smul_one_tmul, LinearEquiv.map_smul]
      _ = Ideal.Quotient.mk (RingHom.ker qB) (φAlg c) •
          Ideal.toCotangent (RingHom.ker qB)
            ⟨algebraMap R B₁ x, by
              have hxmap : algebraMap R B₁ x ∈ Ideal.map (algebraMap R B₁) I :=
                Ideal.mem_map_of_mem (algebraMap R B₁) x.2
              simpa [hTgt] using hxmap⟩ := by
            rw [heBase]
      _ =
        Ideal.toCotangent (RingHom.ker qB)
          ⟨φAlg c * algebraMap R B₁ x, by
            simpa [hTgt] using
              (Ideal.mul_mem_left
                (RingHom.ker qB) (φAlg c)
                (by
                  have hxmap : algebraMap R B₁ x ∈ Ideal.map (algebraMap R B₁) I :=
                    Ideal.mem_map_of_mem (algebraMap R B₁) x.2
                  simpa [hTgt] using hxmap))⟩ := by
            rw [← (Ideal.toCotangent (RingHom.ker qB)).map_smul]
            congr 1
            apply Subtype.ext
            simp [Algebra.smul_def]
      _ = Ideal.toCotangent (Ideal.map (algebraMap R B₁) I)
          ⟨φAlg c * algebraMap R B₁ x,
            Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (algebraMap R B₁) x.2)⟩ := by
            rw [Ideal.Cotangent.equivOfEq_toCotangent]
            congr 1
            apply Subtype.ext
            simp [hTgt]
  have hconj :
      LinearMap.comp
          (LinearMap.comp eCotTgt.symm.toLinearMap
            (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
              φAlg
              (ideal_map_le_comap_of_comp_eq
                (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)))
        eCotSrc.toLinearMap =
        (LinearMap.id : M →ₗ[R] M) := by
    -- Proof comment: both sides are linear, so it suffices to compare them on pure tensors; then
    -- surjectivity of `φAlg` and of `Ideal.toCotangent` reduces the claim to the two generator
    -- formulas already isolated above.
    apply TensorProduct.ext'
    intro b y
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective I y
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c, rfl⟩ := hSurjφ b'
    apply eCotTgt.injective
    -- After transporting across `eCotTgt`, both sides become the same target cotangent generator.
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_apply]
    calc
      eCotTgt
          (eCotTgt.symm
            ((Ideal.mapCotangent (Ideal.map (algebraMap R C) I)
                (Ideal.map (algebraMap R B₁) I) φAlg
                (ideal_map_le_comap_of_comp_eq
                  (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp))
              (eCotSrc (Ideal.Quotient.mk _ (φAlg c) ⊗ₜ[R] Ideal.toCotangent I x)))) =
        (Ideal.mapCotangent (Ideal.map (algebraMap R C) I)
            (Ideal.map (algebraMap R B₁) I) φAlg
            (ideal_map_le_comap_of_comp_eq
              (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp))
          (eCotSrc (Ideal.Quotient.mk _ (φAlg c) ⊗ₜ[R] Ideal.toCotangent I x)) := by
            exact
              LinearEquiv.apply_symm_apply eCotTgt
                ((Ideal.mapCotangent (Ideal.map (algebraMap R C) I)
                    (Ideal.map (algebraMap R B₁) I) φAlg
                    (ideal_map_le_comap_of_comp_eq
                      (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp))
                  (eCotSrc (Ideal.Quotient.mk _ (φAlg c) ⊗ₜ[R] Ideal.toCotangent I x)))
      _ = Ideal.toCotangent (Ideal.map (algebraMap R B₁) I)
            ⟨φAlg (c * algebraMap R C x),
              ideal_map_le_comap_of_comp_eq
                (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp
                  (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (algebraMap R C) x.2))⟩ := by
            rw [hSrcGen, Ideal.mapCotangent_toCotangent]
      _ = eCotTgt (Ideal.Quotient.mk _ (φAlg c) ⊗ₜ[R] Ideal.toCotangent I x) := by
            rw [hTgtGen]
            apply congrArg (Ideal.toCotangent (Ideal.map (algebraMap R B₁) I))
            apply Subtype.ext
            simp [map_mul]
  -- Route correction: once both cotangent sides are normalized on the target quotient tensor
  -- generators, the packaged common-model transport immediately gives injectivity.
  rcases common_model_ideal_transport_identity_of_cotangent_conjugation_eq_id
      hq hcomp hSrc hTgt hSrcSq hTgtSq eCotSrc eCotTgt hconj with
    ⟨eIdealSrc, eIdealTgt, htransport⟩
  exact comparison_injective_of_ideal_transport_identity
    hq hcomp hSrc eIdealSrc eIdealTgt htransport

/-- Helper for Chap10 Lemma 10 143 11: if the target quotient kernel is square-zero, then an
étale source `R → C` has at most one `R`-algebra lift of `qC : C → B₀` through
`qB : B₁ → B₀`. -/
lemma uniqueLiftOfEtaleSourceAlongSquareZeroTarget
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀}
    (hcEtale : (algebraMap R C).Etale)
    (hSurjB : Function.Surjective qB)
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I) :
    ∀ {ψ₁ ψ₂ : C →ₐ[R] B₁},
      qB.comp ψ₁.toRingHom = qC →
      qB.comp ψ₂.toRingHom = qC →
      ψ₁ = ψ₂ := by
  letI : Algebra R B₀ := RingHom.toAlgebra (qC.comp (algebraMap R C))
  letI : Algebra.Etale R C := by
    simpa [RingHom.etale_algebraMap] using hcEtale
  intro ψ₁ ψ₂ hq₁ hq₂
  have hqBCommutes : ∀ r : R, qB (algebraMap R B₁ r) = algebraMap R B₀ r := by
    intro r
    -- Evaluate the first lift on base elements to read `qB` as an `R`-algebra map.
    change qB (algebraMap R B₁ r) = qC (algebraMap R C r)
    calc
      qB (algebraMap R B₁ r) = qB (ψ₁ (algebraMap R C r)) := by
        simpa using congrArg qB (ψ₁.commutes' r).symm
      _ = qC (algebraMap R C r) := by
        exact congrArg (fun f : C →+* B₀ ↦ f (algebraMap R C r)) hq₁
  let qBAlg : B₁ →ₐ[R] B₀ :=
    { toRingHom := qB
      commutes' := hqBCommutes }
  have hKerSq : (RingHom.ker qB) ^ 2 = ⊥ := by
    -- Rewrite the square-zero hypothesis in the literal quotient-kernel spelling.
    simpa [hTgt] using hTgtSq
  have hQuotBij :
      Function.Bijective
        ((Ideal.Quotient.mkₐ R (RingHom.ker qB)).comp : (C →ₐ[R] B₁) → C →ₐ[R] B₁ ⧸ RingHom.ker qB) :=
    @Algebra.FormallyEtale.comp_bijective R C B₁ _ _ _ _ _ _
      (RingHom.ker qB) hKerSq
  have hQuotInj :
      Function.Injective
        ((Ideal.Quotient.mkₐ R (RingHom.ker qB)).comp : (C →ₐ[R] B₁) → C →ₐ[R] B₁ ⧸ RingHom.ker qB) :=
    hQuotBij.1
  let eQuot :=
    @Ideal.quotientKerAlgEquivOfSurjective R B₁ B₀ _ _ _ _ _ qBAlg hSurjB
  have hMkEq :
      ((Ideal.Quotient.mkₐ R (RingHom.ker qB)).comp ψ₁) =
        ((Ideal.Quotient.mkₐ R (RingHom.ker qB)).comp ψ₂) := by
    ext x
    apply eQuot.injective
    -- Both lifts become the same quotient map `qC` after identifying `B₁ ⧸ ker qB` with `B₀`.
    calc
      eQuot
          (((Ideal.Quotient.mkₐ R (RingHom.ker qB)).comp ψ₁) x) =
        qC x := by
          simpa [qBAlg, RingHom.comp_apply] using
            congrArg (fun f : C →+* B₀ ↦ f x) hq₁
      _ =
        eQuot
          (((Ideal.Quotient.mkₐ R (RingHom.ker qB)).comp ψ₂) x) := by
          simpa [qBAlg, RingHom.comp_apply] using
            (congrArg (fun f : C →+* B₀ ↦ f x) hq₂).symm
  -- Injectivity of the formally étale lifting map identifies the two algebra lifts.
  exact hQuotInj hMkEq

/-- Helper for Chap10 Lemma 10 143 11: the commuting square can be repackaged as a morphism of
`R`-extensions over the common quotient `B₀`, and the owner kernels agree with the textbook mapped
ideals on both sides. -/
lemma existsComparisonExtensionData
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hSurjC : Function.Surjective qC)
    (hSurjB : Function.Surjective qB)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I) :
    let _ : Algebra R B₀ := RingHom.toAlgebra (qC.comp (algebraMap R C))
    let qCAlg : C →ₐ[R] B₀ :=
      { toRingHom := qC
        commutes' := fun r ↦ rfl }
    let qBAlg : B₁ →ₐ[R] B₀ :=
      { toRingHom := qB
        commutes' := fun r ↦ by
          change qB (algebraMap R B₁ r) = qC (algebraMap R C r)
          have hbase := congrArg (fun f : C →+* B₀ ↦ f (algebraMap R C r)) hq
          simpa [RingHom.comp_apply, hcomp] using hbase }
    let Psrc : Algebra.Extension R B₀ := ofSurjective qCAlg hSurjC
    let Ptgt : Algebra.Extension R B₀ := ofSurjective qBAlg hSurjB
    ∃ _ : Psrc.Hom Ptgt,
      Psrc.ker = Ideal.map (algebraMap R C) I ∧
      Ptgt.ker = Ideal.map (algebraMap R B₁) I := by
  letI : Algebra R B₀ := RingHom.toAlgebra (qC.comp (algebraMap R C))
  let qCAlg : C →ₐ[R] B₀ :=
    { toRingHom := qC
      commutes' := fun r ↦ rfl }
  have hqBCommutes : ∀ r : R, qB (algebraMap R B₁ r) = algebraMap R B₀ r := by
    intro r
    -- Evaluate the quotient square on base elements so the target map becomes `R`-linear.
    change qB (algebraMap R B₁ r) = qC (algebraMap R C r)
    have hbase := congrArg (fun f : C →+* B₀ ↦ f (algebraMap R C r)) hq
    simpa [RingHom.comp_apply, hcomp] using hbase
  let qBAlg : B₁ →ₐ[R] B₀ :=
    { toRingHom := qB
      commutes' := hqBCommutes }
  let Psrc : Algebra.Extension R B₀ := ofSurjective qCAlg hSurjC
  let Ptgt : Algebra.Extension R B₀ := ofSurjective qBAlg hSurjB
  have hΦ :
      (IsScalarTower.toAlgHom R Ptgt.Ring B₀).comp φAlg =
        (IsScalarTower.toAlgHom R B₀ B₀).comp
          (IsScalarTower.toAlgHom R Psrc.Ring B₀) := by
    -- After packaging the square as extensions, the owner comparison map is still the original
    -- commuting square `qB ∘ φAlg = qC`.
    ext x
    exact congrArg (fun f : C →+* B₀ ↦ f x) hq
  let Φ : Psrc.Hom Ptgt := Hom.ofAlgHom φAlg hΦ
  refine ⟨Φ, ?_, ?_⟩
  · -- The source owner kernel is literally the kernel of `qC`.
    simpa [Psrc, qCAlg, RingHom.algebraMap_toAlgebra] using hSrc
  · -- The target owner kernel is literally the kernel of `qB`.
    simpa [Ptgt, qBAlg, RingHom.algebraMap_toAlgebra] using hTgt

/-- Helper for Chap10 Lemma 10 143 11: if the comparison map `φ : C → B₁` is flat, then the
square-zero quotient square `qB.comp φ = qC` already descends formal smoothness from the identity
map on the common quotient `B₀` back to `φ`. -/
lemma comparisonFormallySmoothOfFlatSquareZeroQuotient
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hφFlat : φAlg.toRingHom.Flat)
    (hSurjC : Function.Surjective qC)
    (hSurjB : Function.Surjective qB)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I) :
    φAlg.toRingHom.FormallySmooth := by
  let _ := hcomp
  have hSrcKerSq : (RingHom.ker qC) ^ 2 = ⊥ := by
    -- Rewrite the square-zero hypothesis in the literal source-kernel spelling.
    simpa [hSrc] using hSrcSq
  have hEqMap : RingHom.ker qB = Ideal.map φAlg.toRingHom (RingHom.ker qC) := by
    -- The target kernel is the image of the source kernel because both are the same mapped ideal.
    rw [hSrc, hTgt]
    simpa [Ideal.map_map, hcomp]
  have hIdSmooth : (RingHom.id B₀).FormallySmooth :=
    RingHom.FormallySmooth.of_bijective Function.bijective_id
  -- Descend formal smoothness from the identity on the quotient square.
  simpa using
    RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero
      φAlg.toRingHom hφFlat qC qB (RingHom.id B₀)
      hSurjC hSurjB
      (by simpa using hq)
      hSrcKerSq hEqMap hIdSmooth

/-- Helper for Chap10 Lemma 10 143 11: the injectivity step for an étale square-zero lift should
be proved by transporting the source and target cotangent spaces to one common model and checking
that the transported comparison map is the identity. -/
lemma comparisonInjectiveOfEtaleLift_ofCommonCotangentModel
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥)
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    {M : Type*} [AddCommGroup M] [Module R M]
    (eCotSrc : M ≃ₗ[R] (Ideal.map (algebraMap R C) I).Cotangent)
    (eCotTgt : M ≃ₗ[R] (Ideal.map (algebraMap R B₁) I).Cotangent)
    (hconj :
      LinearMap.comp
          (LinearMap.comp eCotTgt.symm.toLinearMap
            (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
              φAlg
              (ideal_map_le_comap_of_comp_eq
                (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)))
        eCotSrc.toLinearMap =
        (LinearMap.id : M →ₗ[R] M)) :
    Function.Injective φAlg.toRingHom := by
  rcases common_model_ideal_transport_identity_of_cotangent_conjugation_eq_id
      hq hcomp hSrc hTgt hSrcSq hTgtSq eCotSrc eCotTgt hconj with
    ⟨eIdealSrc, eIdealTgt, htransport⟩
  -- The common cotangent model immediately descends to the ideal model already used by the kernel API.
  exact comparison_injective_of_ideal_transport_identity hq hcomp hSrc eIdealSrc eIdealTgt
    htransport

/-- Helper for Chap10 Lemma 10 143 11: if a cotangent comparison becomes the identity after
transport to a common model, then the cotangent comparison itself is bijective. -/
lemma mapCotangentBijectiveOfConjugationEqId
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    [Algebra R S] [Algebra R T]
    {I₁ : Ideal S} {I₂ : Ideal T} {f : S →ₐ[R] T}
    (h : I₁ ≤ Ideal.comap f I₂)
    {M : Type*} [AddCommGroup M] [Module R M]
    (eSrc : I₁.Cotangent ≃ₗ[R] M)
    (eTgt : I₂.Cotangent ≃ₗ[R] M)
    (hconj :
      LinearMap.comp
          (LinearMap.comp eTgt.toLinearMap (Ideal.mapCotangent I₁ I₂ f h))
        eSrc.symm.toLinearMap =
        (LinearMap.id : M →ₗ[R] M)) :
    Function.Bijective (Ideal.mapCotangent I₁ I₂ f h) := by
  constructor
  · -- Injectivity is the existing common-model argument already packaged in the support file.
    exact mapCotangent_injective_of_conjugation_eq_id h eSrc eTgt hconj
  · intro y
    refine ⟨eSrc.symm (eTgt y), ?_⟩
    apply eTgt.injective
    -- Evaluate the conjugated identity on the chosen target coordinate.
    exact congrArg (fun l : M →ₗ[R] M ↦ l (eTgt y)) hconj

/-- Helper for Chap10 Lemma 10 143 11: once the ambient comparison map `φAlg : C →ₐ[R] B₁`
is injective, the literal textbook cotangent comparison is already bijective because its residual
kernel inside `Ideal.map (algebraMap R C) I` vanishes. -/
lemma mapCotangentBijectiveOfInjectiveComparison
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hSurjφ : Function.Surjective φAlg.toRingHom)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hφInj : Function.Injective φAlg.toRingHom) :
    Function.Bijective
      (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
        φAlg
        (ideal_map_le_comap_of_comp_eq
          (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)) := by
  have hResidual :
      RingHom.ker φAlg.toRingHom ⊓ Ideal.map (algebraMap R C) I = ⊥ := by
    -- Ambient injectivity collapses the residual comparison kernel inside the source ideal.
    exact comparisonResidualKernelBotOfInjectiveComparison hcomp hφInj
  -- The packaged cotangent-kernel theorem upgrades this vanishing kernel to bijectivity.
  exact mapCotangentBijectiveOfResidualKernelBot hSurjφ hq hcomp hSrc hTgt hResidual

/-- Helper for Chap10 Lemma 10 143 11: once the ambient comparison map is injective, the target
cotangent common model is the tautological inverse of the bijective textbook cotangent map. -/
lemma targetCotangentCommonModelOfInjectiveComparison
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hcEtale : (algebraMap R C).Etale)
    (hSurjC : Function.Surjective qC)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hφInj : Function.Injective φAlg.toRingHom) :
    ∃ eCotTgt : C ⊗[R] I.Cotangent ≃ₗ[R] (Ideal.map (algebraMap R B₁) I).Cotangent,
      LinearMap.comp
          (LinearMap.comp eCotTgt.symm.toLinearMap
            (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
              φAlg
              (ideal_map_le_comap_of_comp_eq
                (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)))
        ((sourceMappedIdealCotangentEquivOfEtale hcEtale :
            C ⊗[R] I.Cotangent ≃ₗ[R] (Ideal.map (algebraMap R C) I).Cotangent)).toLinearMap =
        (LinearMap.id : C ⊗[R] I.Cotangent →ₗ[R] C ⊗[R] I.Cotangent) := by
  have hTgtKerSq : (RingHom.ker qB) ^ 2 = ⊥ := by
    -- Rewrite the square-zero hypothesis in the literal target-kernel spelling.
    simpa [hTgt] using hTgtSq
  have hSurjφ : Function.Surjective φAlg.toRingHom := by
    have hIdealSurj :
        Function.Surjective
          (ideal_map_restrict (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp) := by
      -- Square-zero on the target kernel already gives surjectivity of the textbook ideal map.
      exact ideal_map_restrict_surjective_of_square_zero hSurjC hq hcomp hTgtKerSq hTgt
    -- Quotient surjectivity upgrades ideal-level surjectivity to surjectivity of `φAlg`.
    exact comparison_surjective_of_ideal_map_surjective hSurjC hq hcomp hTgt hIdealSurj
  have hCotBij :
      Function.Bijective
        (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
          φAlg
          (ideal_map_le_comap_of_comp_eq
            (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)) := by
    -- Once `φAlg` is injective, the residual cotangent kernel disappears automatically.
    exact mapCotangentBijectiveOfInjectiveComparison hSurjφ hq hcomp hSrc hTgt hφInj
  let eCotSrc :
      C ⊗[R] I.Cotangent ≃ₗ[R] (Ideal.map (algebraMap R C) I).Cotangent :=
    sourceMappedIdealCotangentEquivOfEtale hcEtale
  let eCotMap :
      (Ideal.map (algebraMap R C) I).Cotangent ≃ₗ[R]
        (Ideal.map (algebraMap R B₁) I).Cotangent :=
    LinearEquiv.ofBijective
      (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
        φAlg
        (ideal_map_le_comap_of_comp_eq
          (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp))
      hCotBij
  refine ⟨eCotSrc.trans eCotMap, ?_⟩
  -- With the target equivalence built from the inverse of a bijection, the conjugated map is
  -- definitionally the identity on the common model.
  ext x
  simp [eCotSrc, eCotMap, LinearMap.comp_apply]

/-- Helper for Chap10 Lemma 10 143 11: the remaining owner-level transport frontier is to build
the target cotangent common model directly from the packaged square-zero extension data, so that
the literal textbook cotangent comparison becomes the identity on `C ⊗[R] I.Cotangent`. -/
lemma targetCotangentCommonModelOfEtaleLiftDirect
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hcEtale : (algebraMap R C).Etale)
    (hSurjC : Function.Surjective qC)
    (hSurjB : Function.Surjective qB)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥)
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hBaseChange : chosenLiftBaseChangeCotangentEquiv hTgt) :
    ∃ eCotTgt : C ⊗[R] I.Cotangent ≃ₗ[R] (Ideal.map (algebraMap R B₁) I).Cotangent,
      LinearMap.comp
          (LinearMap.comp eCotTgt.symm.toLinearMap
            (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
              φAlg
              (ideal_map_le_comap_of_comp_eq
                (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)))
        ((sourceMappedIdealCotangentEquivOfEtale hcEtale :
            C ⊗[R] I.Cotangent ≃ₗ[R] (Ideal.map (algebraMap R C) I).Cotangent)).toLinearMap =
        (LinearMap.id : C ⊗[R] I.Cotangent →ₗ[R] C ⊗[R] I.Cotangent) := by
  have hφInj : Function.Injective φAlg.toRingHom := by
    -- Delegate the repaired injectivity step to the theorem-specific base-change helper.
    exact chosenLiftComparisonInjectiveOfBaseChange
      hcEtale hSurjC hSurjB hq hcomp hSrcSq hTgtSq hSrc hTgt hBaseChange
  exact targetCotangentCommonModelOfInjectiveComparison
    hcEtale hSurjC hq hcomp hTgtSq hSrc hTgt hφInj

/-- Helper for Chap10 Lemma 10 143 11: under the étale source and square-zero quotient
hypotheses, the literal textbook ideal comparison
`Ideal.map (algebraMap R C) I → Ideal.map (algebraMap R B₁) I` should be injective. -/
lemma idealMapRestrictInjectiveOfEtaleLift
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hcEtale : (algebraMap R C).Etale)
    (hSurjC : Function.Surjective qC)
    (hSurjB : Function.Surjective qB)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥)
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hBaseChange : chosenLiftBaseChangeCotangentEquiv hTgt) :
    Function.Injective
      (ideal_map_restrict (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp) := by
  rcases targetCotangentCommonModelOfEtaleLiftDirect
      hcEtale hSurjC hSurjB hq hcomp hSrcSq hTgtSq hSrc hTgt hBaseChange with
    ⟨eCotTgt, hconj⟩
  -- Route correction: use the direct cotangent/common-model identity instead of reopening the old
  -- elementwise lift-construction route inside the ideal comparison.
  exact ideal_map_restrict_injective_of_conjugation_eq_id
    hcomp hSrcSq
    (sourceMappedIdealCotangentEquivOfEtale hcEtale).symm
    eCotTgt.symm hconj

/-- Helper for Chap10 Lemma 10 143 11: once the literal ideal comparison is injective, the
residual comparison kernel inside the source mapped ideal vanishes immediately. -/
lemma comparisonResidualKernelBotOfEtaleLiftDirect
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hcEtale : (algebraMap R C).Etale)
    (hSurjC : Function.Surjective qC)
    (hSurjB : Function.Surjective qB)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥)
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hBaseChange : chosenLiftBaseChangeCotangentEquiv hTgt) :
    RingHom.ker φAlg.toRingHom ⊓ Ideal.map (algebraMap R C) I = ⊥ := by
  -- Reduce the residual-kernel statement to injectivity of the literal textbook ideal map.
  exact RingHom.inf_eq_bot_of_ideal_map_restrict_injective hcomp
    (idealMapRestrictInjectiveOfEtaleLift
      hcEtale hSurjC hSurjB hq hcomp hSrcSq hTgtSq hSrc hTgt hBaseChange)

/-- Helper for Chap10 Lemma 10 143 11: the remaining transport frontier is to show that the
literal cotangent comparison
`Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I) φAlg ...`
is bijective. Once that is known, the target common model is the corresponding linear equivalence
built from `LinearEquiv.ofBijective`. -/
lemma comparisonMapCotangentBijectiveOfEtaleLift
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hcEtale : (algebraMap R C).Etale)
    (hSurjC : Function.Surjective qC)
    (hSurjB : Function.Surjective qB)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥)
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hBaseChange : chosenLiftBaseChangeCotangentEquiv hTgt) :
    Function.Bijective
      (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
        φAlg
        (ideal_map_le_comap_of_comp_eq
          (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)) := by
  rcases targetCotangentCommonModelOfEtaleLiftDirect
      hcEtale hSurjC hSurjB hq hcomp hSrcSq hTgtSq hSrc hTgt hBaseChange with
    ⟨eCotTgt, hconj⟩
  -- Route correction: prove cotangent bijectivity directly from the common-model identity instead
  -- of routing it through the ideal injectivity theorem.
  exact mapCotangentBijectiveOfConjugationEqId
    (ideal_map_le_comap_of_comp_eq
      (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)
    (sourceMappedIdealCotangentEquivOfEtale hcEtale).symm
    eCotTgt.symm hconj

/-- Helper for Chap10 Lemma 10 143 11: once the textbook cotangent comparison is bijective, the
target cotangent module is the same common model as the source cotangent module. -/
lemma targetCotangentCommonModelOfBijectiveComparison
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {φAlg : C →ₐ[R] B₁}
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    {M : Type*} [AddCommGroup M] [Module R M]
    (eCotSrc : M ≃ₗ[R] (Ideal.map (algebraMap R C) I).Cotangent)
    (hCotBij :
      Function.Bijective
        (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
          φAlg
          (ideal_map_le_comap_of_comp_eq
            (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp))) :
    ∃ eCotTgt : M ≃ₗ[R] (Ideal.map (algebraMap R B₁) I).Cotangent,
      LinearMap.comp
          (LinearMap.comp eCotTgt.symm.toLinearMap
            (Ideal.mapCotangent
              (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I) φAlg
              (ideal_map_le_comap_of_comp_eq
                (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)))
        eCotSrc.toLinearMap =
        (LinearMap.id : M →ₗ[R] M) := by
  let eCotMap :
      (Ideal.map (algebraMap R C) I).Cotangent ≃ₗ[R]
        (Ideal.map (algebraMap R B₁) I).Cotangent :=
    LinearEquiv.ofBijective
      (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
        φAlg
        (ideal_map_le_comap_of_comp_eq
          (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp))
      hCotBij
  refine ⟨eCotSrc.trans eCotMap, ?_⟩
  -- The common-model identity is tautological once the target equivalence is `eCotSrc` followed
  -- by the inverse of the bijective cotangent comparison.
  ext x
  simp [eCotMap, LinearMap.comp_apply]

/-- Helper for Chap10 Lemma 10 143 11: under the étale source and surjective square-zero quotient
hypotheses, the target cotangent module identifies with the same tensor-model
`C ⊗[R] I.Cotangent` as the source, and the literal `Ideal.mapCotangent` comparison becomes the
identity after transporting both sides to that common model. -/
lemma targetCotangentCommonModelOfEtaleLift
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hcEtale : (algebraMap R C).Etale)
    (hSurjC : Function.Surjective qC)
    (hSurjB : Function.Surjective qB)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥)
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hBaseChange : chosenLiftBaseChangeCotangentEquiv hTgt) :
    ∃ eCotTgt : C ⊗[R] I.Cotangent ≃ₗ[R] (Ideal.map (algebraMap R B₁) I).Cotangent,
      LinearMap.comp
          (LinearMap.comp eCotTgt.symm.toLinearMap
            (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
              φAlg
              (ideal_map_le_comap_of_comp_eq
                (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)))
        ((sourceMappedIdealCotangentEquivOfEtale hcEtale :
            C ⊗[R] I.Cotangent ≃ₗ[R] (Ideal.map (algebraMap R C) I).Cotangent)).toLinearMap =
        (LinearMap.id : C ⊗[R] I.Cotangent →ₗ[R] C ⊗[R] I.Cotangent) := by
  -- Route correction: this common-model statement is now the primary transport lemma rather than
  -- a corollary of cotangent bijectivity.
  exact targetCotangentCommonModelOfEtaleLiftDirect
    hcEtale hSurjC hSurjB hq hcomp hSrcSq hTgtSq hSrc hTgt hBaseChange

/-- Helper for Chap10 Lemma 10 143 11: the injectivity step for an étale square-zero lift should
be proved by transporting the source and target cotangent spaces to one common model and checking
that the transported comparison map is the identity. -/
lemma comparisonInjectiveOfEtaleLiftViaTransport
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hcEtale : (algebraMap R C).Etale)
    (hSurjC : Function.Surjective qC)
    (hSurjB : Function.Surjective qB)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥)
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hBaseChange : chosenLiftBaseChangeCotangentEquiv hTgt) :
    Function.Injective φAlg.toRingHom := by
  let eCotSrc :
      C ⊗[R] I.Cotangent ≃ₗ[R] (Ideal.map (algebraMap R C) I).Cotangent :=
    sourceMappedIdealCotangentEquivOfEtale hcEtale
  have hCotBij :
      Function.Bijective
        (Ideal.mapCotangent (Ideal.map (algebraMap R C) I) (Ideal.map (algebraMap R B₁) I)
          φAlg
          (ideal_map_le_comap_of_comp_eq
            (algebraMap R C) (algebraMap R B₁) φAlg.toRingHom I hcomp)) :=
    comparisonMapCotangentBijectiveOfEtaleLift
      hcEtale hSurjC hSurjB hq hcomp hSrcSq hTgtSq hSrc hTgt hBaseChange
  rcases targetCotangentCommonModelOfBijectiveComparison
      hcomp eCotSrc hCotBij with
    ⟨eCotTgt, hconj⟩
  -- Route correction: once the literal `Ideal.mapCotangent` map is bijective, the target common
  -- model is `LinearEquiv.ofBijective` applied to that map, so the final conjugation identity is
  -- automatic.
  exact comparisonInjectiveOfEtaleLift_ofCommonCotangentModel
    hq hcomp hSrc hTgt hSrcSq hTgtSq eCotSrc eCotTgt hconj

/-- Helper for Chap10 Lemma 10 143 11: once the transport-based injectivity statement is in hand,
the residual comparison kernel inside `Ideal.map (algebraMap R C) I` vanishes immediately. -/
lemma comparisonResidualKernelBotOfEtaleLift
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hcEtale : (algebraMap R C).Etale)
    (hSurjC : Function.Surjective qC)
    (hSurjB : Function.Surjective qB)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp (algebraMap R C) = algebraMap R B₁)
    (hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥)
    (hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥)
    (hSrc : RingHom.ker qC = Ideal.map (algebraMap R C) I)
    (hTgt : RingHom.ker qB = Ideal.map (algebraMap R B₁) I)
    (hBaseChange : chosenLiftBaseChangeCotangentEquiv hTgt) :
    RingHom.ker φAlg.toRingHom ⊓ Ideal.map (algebraMap R C) I = ⊥ := by
  have hφInj : Function.Injective φAlg.toRingHom := by
    -- Delegate the hard step to the cotangent/common-model transport lemma.
    exact comparisonInjectiveOfEtaleLiftViaTransport
      hcEtale hSurjC hSurjB hq hcomp hSrcSq hTgtSq hSrc hTgt hBaseChange
  -- Once the ambient comparison map is injective, the residual comparison kernel vanishes.
  exact comparisonResidualKernelBotOfInjectiveComparison hcomp hφInj

/-- Helper for Chap10 Lemma 10 143 11: after choosing an étale lift `c : R → C` of the quotient
map `qC : C → B₀`, the remaining hard step is to prove that any square-zero lift
`φAlg : C →ₐ[R] B₁` of `qC` is injective once the source and target kernels are identified with the
same mapped ideal `I`. -/
lemma comparisonInjectiveOfEtaleLift
    {R : Type*} [CommRing R] {C : Type*} [CommRing C]
    {B₀ : Type*} [CommRing B₀] {B₁ : Type*} [CommRing B₁]
    [Algebra R C] [Algebra R B₁]
    {I : Ideal R} {c : R →+* C} {g : R →+* B₁}
    {qC : C →+* B₀} {qB : B₁ →+* B₀} {φAlg : C →ₐ[R] B₁}
    (hcEtale : c.Etale)
    (hSurjC : Function.Surjective qC)
    (hSurjB : Function.Surjective qB)
    (hq : qB.comp φAlg.toRingHom = qC)
    (hcomp : φAlg.toRingHom.comp c = g)
    (hSqI : I ^ 2 = ⊥)
    (hSrc : RingHom.ker qC = Ideal.map c I)
    (hTgt : RingHom.ker qB = Ideal.map g I)
    (hBaseChange : chosenLiftBaseChangeCotangentEquiv hTgt) :
    Function.Injective φAlg.toRingHom := by
  let φ : C →+* B₁ := φAlg.toRingHom
  letI : Algebra R C := c.toAlgebra
  letI : Algebra R B₁ := g.toAlgebra
  let φLift : C →ₐ[R] B₁ :=
    { toRingHom := φ
      commutes' := fun r ↦ by
        -- Reinterpret the given comparison ring map as an algebra map for the source-facing
        -- algebra structures induced by `c` and `g`.
        exact congrArg (fun h : R →+* B₁ ↦ h r) hcomp }
  have hqLift : qB.comp φLift.toRingHom = qC := by
    -- The quotient square is unchanged after repackaging `φ` with the `c`/`g` algebra structures.
    ext x
    exact congrArg (fun h : C →+* B₀ ↦ h x) hq
  have hcompLift : φLift.toRingHom.comp (algebraMap R C) = algebraMap R B₁ := by
    -- Under the source-facing algebra structures, `hcomp` is exactly the algebra-map commutation.
    ext r
    exact congrArg (fun h : R →+* B₁ ↦ h r) hcomp
  have hSrcSq : (Ideal.map (algebraMap R C) I) ^ 2 = ⊥ := by
    -- Transport the square-zero hypothesis from `I` to the source mapped ideal.
    simpa [RingHom.algebraMap_toAlgebra, Ideal.map_pow] using congrArg (Ideal.map c) hSqI
  have hTgtSq : (Ideal.map (algebraMap R B₁) I) ^ 2 = ⊥ := by
    -- Transport the same square-zero hypothesis to the target mapped ideal.
    simpa [RingHom.algebraMap_toAlgebra, Ideal.map_pow] using congrArg (Ideal.map g) hSqI
  have hSrcAlg : RingHom.ker qC = Ideal.map (algebraMap R C) I := by
    -- Keep the remaining comparison entirely in the `algebraMap` spelling expected by the
    -- cotangent and residual-kernel helpers.
    simpa [RingHom.algebraMap_toAlgebra] using hSrc
  have hTgtAlg : RingHom.ker qB = Ideal.map (algebraMap R B₁) I := by
    -- The target kernel normalization matches the same owner API boundary.
    simpa [RingHom.algebraMap_toAlgebra] using hTgt
  have hcEtaleAlg : (algebraMap R C).Etale := by
    -- Rewrite the chosen lift `c` to the ambient `algebraMap` spelling used by the helper API.
    simpa [RingHom.algebraMap_toAlgebra] using hcEtale
  have hBaseChangeAlg :
      chosenLiftBaseChangeCotangentEquiv hTgtAlg := by
    -- Repackage the theorem-specific cotangent datum in the `algebraMap` spelling used by the
    -- transport-based helper chain.
    simpa [chosenLiftBaseChangeCotangentEquiv, RingHom.algebraMap_toAlgebra] using hBaseChange
  -- Route correction: reuse the dedicated transport-based injectivity helper directly.
  have hφLiftInj : Function.Injective φLift.toRingHom :=
    comparisonInjectiveOfEtaleLiftViaTransport
      hcEtaleAlg hSurjC hSurjB hqLift hcompLift hSrcSq hTgtSq hSrcAlg hTgtAlg hBaseChangeAlg
  simpa [φLift] using hφLiftInj

/-
Domain-style sampling:
- primary domain: infinitesimal lifting of étale ring maps across square-zero extension squares;
- sampled owner API:
  `RingHom.Etale`,
  `RingHom.etale_iff_formallyUnramified_and_smooth`,
  `RingHom.FormallyUnramified.of_comp`,
  `RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero`;
- best owner abstraction: this is a source-facing lifting theorem, but its canonical owner
  predicate is `RingHom.Etale`;
- source-facing: the square-zero lifting criterion for étaleness in a commutative square of
  surjective ring maps;
- core/canonical: `RingHom.Etale`, together with its derived owner consequences
  `FormallyUnramified`, `Smooth`, `Flat`, and `FinitePresentation`;
- bridge/view: the commutative square `qB.comp g = f.comp qA` together with the base-change
  comparison identifying the target square-zero kernel with
  `B ⊗[Aprime] (ker qA).Cotangent`.

Primitive-vs-derived split:
- primitive data: the four ring maps, the commutative square, surjectivity, the square-zero
  hypotheses, and the base-change comparison for the square-zero kernels;
- derived API: the formal unramifiedness / smoothness / flatness consequences extracted from the
  owner predicate `Etale`.

This item adds genuine source-facing content, so the public theorem should stay a theorem about
`g.Etale`; the refinement is to keep the owner predicate explicit and avoid parallel local wrappers
around its derived formal properties.
-/

/-- Helper for Chap10 Lemma 10 143 11: after identifying the square-zero target cotangent with
`RingHom.ker qB`, every tensor in the quotient-level common model already lands in the mapped ideal
`Ideal.map g (RingHom.ker qA)`. -/
lemma targetKernel_mem_map_of_baseChangeCotangentEquiv_tmul
    [Algebra Aprime Bprime]
    [Algebra (Aprime ⧸ RingHom.ker qA) (Bprime ⧸ RingHom.ker qB)]
    (hcomm : qB.comp g = f.comp qA)
    (hSqB : (RingHom.ker qB) ^ 2 = ⊥)
    {e :
      ((Bprime ⧸ RingHom.ker qB) ⊗[Aprime ⧸ RingHom.ker qA] (RingHom.ker qA).Cotangent) ≃ₗ[Bprime ⧸
        RingHom.ker qB] (RingHom.ker qB).Cotangent}
    (he :
      ∀ x : RingHom.ker qA,
        e (1 ⊗ₜ[Aprime ⧸ RingHom.ker qA] Ideal.toCotangent (RingHom.ker qA) x) =
          Ideal.toCotangent (RingHom.ker qB) ⟨g x, by
            have hx : qA x = 0 := by
              exact x.2
            have hpoint := congrArg (fun h : Aprime →+* B ↦ h x) hcomm
            simpa [RingHom.comp_apply, hx] using hpoint⟩)
    (b' : Bprime) (x : RingHom.ker qA) :
    (((ideal_equiv_cotangent_of_square_zero (RingHom.ker qB) hSqB).symm
          (e ((Ideal.Quotient.mk (RingHom.ker qB) b') ⊗ₜ[Aprime ⧸ RingHom.ker qA]
            Ideal.toCotangent (RingHom.ker qA) x)) : RingHom.ker qB) : Bprime) ∈
      Ideal.map g (RingHom.ker qA) := by
  let eTgtSq := ideal_equiv_cotangent_of_square_zero (RingHom.ker qB) hSqB
  have hgx : g x ∈ RingHom.ker qB := by
    rw [RingHom.mem_ker]
    have hx0 : qA x = 0 := x.2
    have hpoint := congrArg (fun h : Aprime →+* B ↦ h x) hcomm
    simpa [RingHom.comp_apply, hx0] using hpoint
  have heval :
      e
          ((Ideal.Quotient.mk (RingHom.ker qB) b') ⊗ₜ[Aprime ⧸ RingHom.ker qA]
            Ideal.toCotangent (RingHom.ker qA) x) =
        (Ideal.Quotient.mk (RingHom.ker qB) b') •
          Ideal.toCotangent (RingHom.ker qB) ⟨g x, hgx⟩ := by
    have htmul :
        ((Ideal.Quotient.mk (RingHom.ker qB) b') ⊗ₜ[Aprime ⧸ RingHom.ker qA]
          Ideal.toCotangent (RingHom.ker qA) x) =
          (Ideal.Quotient.mk (RingHom.ker qB) b') •
            (1 ⊗ₜ[Aprime ⧸ RingHom.ker qA] Ideal.toCotangent (RingHom.ker qA) x) := by
      rw [TensorProduct.tmul_eq_smul_one_tmul]
    calc
      e
          ((Ideal.Quotient.mk (RingHom.ker qB) b') ⊗ₜ[Aprime ⧸ RingHom.ker qA]
            Ideal.toCotangent (RingHom.ker qA) x) =
        e
            ((Ideal.Quotient.mk (RingHom.ker qB) b') •
              (1 ⊗ₜ[Aprime ⧸ RingHom.ker qA] Ideal.toCotangent (RingHom.ker qA) x)) := by
                rw [htmul]
      _ =
        (Ideal.Quotient.mk (RingHom.ker qB) b') •
          e
            (1 ⊗ₜ[Aprime ⧸ RingHom.ker qA] Ideal.toCotangent (RingHom.ker qA) x) := by
              simpa using e.map_smul (Ideal.Quotient.mk (RingHom.ker qB) b')
                (1 ⊗ₜ[Aprime ⧸ RingHom.ker qA] Ideal.toCotangent (RingHom.ker qA) x)
      _ =
        (Ideal.Quotient.mk (RingHom.ker qB) b') •
          Ideal.toCotangent (RingHom.ker qB) ⟨g x, hgx⟩ := by
            rw [he]
  have hrepr :
      eTgtSq.symm
          (e
            ((Ideal.Quotient.mk (RingHom.ker qB) b') ⊗ₜ[Aprime ⧸ RingHom.ker qA]
              Ideal.toCotangent (RingHom.ker qA) x)) =
        b' • ⟨g x, hgx⟩ := by
    calc
      eTgtSq.symm
          (e
            ((Ideal.Quotient.mk (RingHom.ker qB) b') ⊗ₜ[Aprime ⧸ RingHom.ker qA]
              Ideal.toCotangent (RingHom.ker qA) x)) =
        eTgtSq.symm
          ((Ideal.Quotient.mk (RingHom.ker qB) b') •
            Ideal.toCotangent (RingHom.ker qB) ⟨g x, hgx⟩) := by
              rw [heval]
      _ =
        eTgtSq.symm
          (b' • Ideal.toCotangent (RingHom.ker qB) ⟨g x, hgx⟩) := by
              change
                eTgtSq.symm
                    ((algebraMap Bprime (Bprime ⧸ RingHom.ker qB) b') •
                      Ideal.toCotangent (RingHom.ker qB) ⟨g x, hgx⟩) =
                  _
              rfl
      _ = b' • eTgtSq.symm (Ideal.toCotangent (RingHom.ker qB) ⟨g x, hgx⟩) := by
              simpa using eTgtSq.symm.map_smul b' (Ideal.toCotangent (RingHom.ker qB) ⟨g x, hgx⟩)
      _ = b' • ⟨g x, hgx⟩ := by
              rw [show eTgtSq.symm (Ideal.toCotangent (RingHom.ker qB) ⟨g x, hgx⟩) =
                  ⟨g x, hgx⟩ by
                    simpa [eTgtSq] using
                      ideal_equiv_cotangent_of_square_zero_symm_toCotangent
                        (RingHom.ker qB) hSqB ⟨g x, hgx⟩]
  -- The distinguished tensor maps to a scalar multiple of `g x`, hence lies in the mapped ideal.
  rw [hrepr]
  simpa [smul_eq_mul] using
    (Ideal.mul_mem_left (Ideal.map g (RingHom.ker qA)) b' (Ideal.mem_map_of_mem g x.2))

/-- Helper for Chap10 Lemma 10 143 11: after identifying the square-zero target cotangent with
`RingHom.ker qB`, every tensor in the quotient-level common model already lands in the mapped ideal
`Ideal.map g (RingHom.ker qA)`. -/
lemma targetKernel_mem_map_of_baseChangeCotangentEquiv
    [Algebra Aprime Bprime]
    [Algebra (Aprime ⧸ RingHom.ker qA) (Bprime ⧸ RingHom.ker qB)]
    (hcomm : qB.comp g = f.comp qA)
    (hSqB : (RingHom.ker qB) ^ 2 = ⊥)
    {e :
      ((Bprime ⧸ RingHom.ker qB) ⊗[Aprime ⧸ RingHom.ker qA] (RingHom.ker qA).Cotangent) ≃ₗ[Bprime ⧸
        RingHom.ker qB] (RingHom.ker qB).Cotangent}
    (he :
      ∀ x : RingHom.ker qA,
        e (1 ⊗ₜ[Aprime ⧸ RingHom.ker qA] Ideal.toCotangent (RingHom.ker qA) x) =
          Ideal.toCotangent (RingHom.ker qB) ⟨g x, by
            have hx : qA x = 0 := by
              exact x.2
            have hpoint := congrArg (fun h : Aprime →+* B ↦ h x) hcomm
            simpa [RingHom.comp_apply, hx] using hpoint⟩)
    (z :
      (Bprime ⧸ RingHom.ker qB) ⊗[Aprime ⧸ RingHom.ker qA] (RingHom.ker qA).Cotangent) :
    (((ideal_equiv_cotangent_of_square_zero (RingHom.ker qB) hSqB).symm (e z) : RingHom.ker qB) :
        Bprime) ∈
      Ideal.map g (RingHom.ker qA) := by
  let eTgtSq := ideal_equiv_cotangent_of_square_zero (RingHom.ker qB) hSqB
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · -- The common-model origin maps to zero in the target ideal.
    simp
  · intro b m
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker qA) m
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    exact targetKernel_mem_map_of_baseChangeCotangentEquiv_tmul
      (g := g) (qA := qA) (qB := qB) (f := f) hcomm hSqB (e := e) he b' x
  · intro z₁ z₂ hz₁ hz₂
    -- The target mapped ideal is closed under addition.
    simpa [map_add] using (Ideal.add_mem (Ideal.map g (RingHom.ker qA)) hz₁ hz₂)

/-- Helper for Chap10 Lemma 10 143 11: the quotient-level base-change cotangent hypothesis forces
the target kernel to be exactly the image of `RingHom.ker qA` under `g`. -/
lemma targetKernel_eq_map_of_baseChangeCotangentEquiv
    (hcomm : qB.comp g = f.comp qA)
    (hSqB : (RingHom.ker qB) ^ 2 = ⊥)
    (hBaseChange :
      letI : Algebra Aprime Bprime := g.toAlgebra
      let hker : RingHom.ker qA ≤ Ideal.comap (algebraMap Aprime Bprime) (RingHom.ker qB) := by
        intro x hx
        rw [RingHom.mem_ker] at hx
        change qB ((algebraMap Aprime Bprime) x) = 0
        have hpoint := congrArg (fun h : Aprime →+* B ↦ h x) hcomm
        simpa [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, hx] using hpoint
      letI : Algebra (Aprime ⧸ RingHom.ker qA) (Bprime ⧸ RingHom.ker qB) :=
        Ideal.Quotient.algebraQuotientOfLEComap hker
      ∃ e :
        ((Bprime ⧸ RingHom.ker qB) ⊗[Aprime ⧸ RingHom.ker qA] (RingHom.ker qA).Cotangent) ≃ₗ[Bprime ⧸
          RingHom.ker qB] (RingHom.ker qB).Cotangent,
        ∀ x : RingHom.ker qA,
          e (1 ⊗ₜ[Aprime ⧸ RingHom.ker qA] Ideal.toCotangent (RingHom.ker qA) x) =
            Ideal.toCotangent (RingHom.ker qB) ⟨g x, by
              have hx : qA x = 0 := by
                exact x.2
              have hpoint := congrArg (fun h : Aprime →+* B ↦ h x) hcomm
              simpa [RingHom.comp_apply, hx] using hpoint⟩) :
    RingHom.ker qB = Ideal.map g (RingHom.ker qA) := by
  letI : Algebra Aprime Bprime := g.toAlgebra
  letI : Algebra (Aprime ⧸ RingHom.ker qA) (Bprime ⧸ RingHom.ker qB) :=
    Ideal.Quotient.algebraQuotientOfLEComap <| by
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker]
      have hx0 : qA x = 0 := hx
      have hpoint := congrArg (fun h : Aprime →+* B ↦ h x) hcomm
      simpa [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, hx0] using hpoint
  rcases hBaseChange with ⟨e, he⟩
  apply le_antisymm
  · intro y hy
    let eTgtSq :=
      ideal_equiv_cotangent_of_square_zero (RingHom.ker qB) hSqB
    have htransport :=
      targetKernel_mem_map_of_baseChangeCotangentEquiv
        (g := g) (qA := qA) (qB := qB) (f := f) hcomm hSqB (e := e) he
    have heInv :
        e (e.symm (Ideal.toCotangent (RingHom.ker qB) ⟨y, hy⟩)) =
          Ideal.toCotangent (RingHom.ker qB) ⟨y, hy⟩ := by
      exact e.apply_symm_apply _
    -- Evaluate the transported common-model description on the cotangent class of `y`.
    have hyrepr :
        eTgtSq.symm (Ideal.toCotangent (RingHom.ker qB) ⟨y, hy⟩) = ⟨y, hy⟩ := by
      simpa [eTgtSq] using
        ideal_equiv_cotangent_of_square_zero_symm_toCotangent
          (RingHom.ker qB) hSqB ⟨y, hy⟩
    have hyrepr_coe :
        (((eTgtSq.symm (Ideal.toCotangent (RingHom.ker qB) ⟨y, hy⟩) : RingHom.ker qB) :
            Bprime)) =
          y := by
      exact congrArg (fun t : RingHom.ker qB ↦ (t : Bprime)) hyrepr
    have hmem :
        (((eTgtSq.symm (Ideal.toCotangent (RingHom.ker qB) ⟨y, hy⟩) : RingHom.ker qB) :
            Bprime)) ∈
          Ideal.map g (RingHom.ker qA) := by
      simpa [heInv] using
        htransport (e.symm (Ideal.toCotangent (RingHom.ker qB) ⟨y, hy⟩))
    exact hyrepr_coe ▸ hmem
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    -- Every generator `g x` of the mapped ideal is killed by `qB` because `x ∈ ker qA`.
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have hx0 : qA x = 0 := hx
    have hpoint := congrArg (fun h : Aprime →+* B ↦ h x) hcomm
    simpa [RingHom.comp_apply, hx0] using hpoint

/-- Chap10 Lemma 10 143 11: in a commutative square of surjective ring maps
`Aprime ⟶ Bprime` over `A ⟶ B`, if `A → B` is étale, both quotient kernels are square-zero, and
the canonical base-change comparison from the source kernel cotangent to the target kernel
cotangent along the induced map `(Aprime ⧸ ker qA) → (Bprime ⧸ ker qB)` is an isomorphism, then
`Aprime → Bprime` is étale. This quotient-level tensor formulation is the local API for the
source condition `J = I ⊗_A B`. -/
@[stacks 05YT]
theorem etale_of_surjective_of_ker_eq_map_of_square_zero
    (hcomm : qB.comp g = f.comp qA)
    (hEtale : f.Etale)
    (hSurjA : Function.Surjective qA)
    (hSurjB : Function.Surjective qB)
    (hSqA : (ker qA) ^ 2 = ⊥)
    (hSqB : (ker qB) ^ 2 = ⊥)
    (hBaseChange :
      letI : Algebra Aprime Bprime := g.toAlgebra
      let hker : RingHom.ker qA ≤ Ideal.comap (algebraMap Aprime Bprime) (RingHom.ker qB) := by
        intro x hx
        rw [RingHom.mem_ker] at hx
        change qB ((algebraMap Aprime Bprime) x) = 0
        have hpoint := congrArg (fun h : Aprime →+* B ↦ h x) hcomm
        simpa [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, hx] using hpoint
      letI : Algebra (Aprime ⧸ RingHom.ker qA) (Bprime ⧸ RingHom.ker qB) :=
        Ideal.Quotient.algebraQuotientOfLEComap hker
      ∃ e :
        ((Bprime ⧸ RingHom.ker qB) ⊗[Aprime ⧸ RingHom.ker qA] (RingHom.ker qA).Cotangent) ≃ₗ[Bprime ⧸
          RingHom.ker qB] (RingHom.ker qB).Cotangent,
        ∀ x : RingHom.ker qA,
          e (1 ⊗ₜ[Aprime ⧸ RingHom.ker qA] Ideal.toCotangent (RingHom.ker qA) x) =
            Ideal.toCotangent (RingHom.ker qB) ⟨g x, by
              have hx : qA x = 0 := by
                exact x.2
              have hpoint := congrArg (fun h : Aprime →+* B ↦ h x) hcomm
              simpa [RingHom.comp_apply, hx] using hpoint⟩) :
    g.Etale := by
  letI : Algebra Aprime A := qA.toAlgebra
  let qAAlg : Aprime →ₐ[Aprime] A :=
    { toRingHom := qA
      commutes' := fun r ↦ rfl }
  let eA : (Aprime ⧸ RingHom.ker qA) ≃ₐ[Aprime] A :=
    @Ideal.quotientKerAlgEquivOfSurjective Aprime Aprime A _ _ _ _ _ qAAlg hSurjA
  letI : Algebra (Aprime ⧸ RingHom.ker qA) A := eA.toAlgHom.toAlgebra
  letI : Algebra (Aprime ⧸ RingHom.ker qA) B :=
    RingHom.toAlgebra (f.comp (algebraMap (Aprime ⧸ RingHom.ker qA) A))
  have hqAEtale : (algebraMap (Aprime ⧸ RingHom.ker qA) A).Etale := by
    -- The quotient identification `Aprime ⧸ ker qA ≃ A` is bijective, hence étale.
    simpa [RingHom.algebraMap_toAlgebra] using
      (RingHom.Etale.of_bijective eA.bijective :
        (eA.toRingHom : (Aprime ⧸ RingHom.ker qA) →+* A).Etale)
  have hEtaleQuot : (algebraMap (Aprime ⧸ RingHom.ker qA) B).Etale := by
    have hqAUnram : (algebraMap (Aprime ⧸ RingHom.ker qA) A).FormallyUnramified :=
      hqAEtale.formallyUnramified
    have hqASmooth : (algebraMap (Aprime ⧸ RingHom.ker qA) A).Smooth :=
      (RingHom.etale_iff_formallyUnramified_and_smooth _).mp hqAEtale |>.2
    have hfUnram : f.FormallyUnramified := hEtale.formallyUnramified
    have hfSmooth : f.Smooth :=
      (RingHom.etale_iff_formallyUnramified_and_smooth _).mp hEtale |>.2
    -- Transport étaleness of `f : A → B` across the quotient identification of `A`.
    rw [RingHom.etale_iff_formallyUnramified_and_smooth]
    refine ⟨?_, ?_⟩
    · simpa [RingHom.algebraMap_toAlgebra] using RingHom.FormallyUnramified.comp hqAUnram hfUnram
    · simpa [RingHom.algebraMap_toAlgebra] using RingHom.Smooth.comp hqASmooth hfSmooth
  letI : Algebra.Etale (Aprime ⧸ RingHom.ker qA) B := by
    simpa [RingHom.etale_algebraMap] using hEtaleQuot
  have hEtaleLift :
      ∃ (C : Type _) (_ : CommRing C) (_ : Algebra Aprime C) (_ : Algebra.Etale Aprime C),
        Nonempty ((C ⧸ Ideal.map (algebraMap Aprime C) (RingHom.ker qA)) ≃ₐ[Aprime ⧸ RingHom.ker qA] B) :=
    Algebra.exists_etale_lift_of_quotient (RingHom.ker qA)
  obtain ⟨C, _instC, _algC, _etC, hCquot⟩ := hEtaleLift
  let c : Aprime →+* C := algebraMap Aprime C
  let eC : (C ⧸ Ideal.map c (RingHom.ker qA)) ≃ₐ[Aprime ⧸ RingHom.ker qA] B :=
    Classical.choice hCquot
  let qC : C →+* B := eC.toRingHom.comp (Ideal.Quotient.mk (Ideal.map c (RingHom.ker qA)))
  have hLiftedQuot :
      Function.Surjective qC ∧ RingHom.ker qC = Ideal.map c (RingHom.ker qA) := by
    simpa [qC] using lifted_quotient_map_ker_eq_map qA c eC.toRingEquiv
  have hSurjC : Function.Surjective qC := by
    -- The quotient map followed by the chosen reduction equivalence is still surjective.
    exact hLiftedQuot.1
  have hSrc : RingHom.ker qC = Ideal.map c (RingHom.ker qA) := by
    -- The chosen quotient comparison has the expected source kernel.
    exact hLiftedQuot.2
  have hcEtale : c.Etale := by
    -- The lifted algebra `C` is étale over `Aprime`.
    simpa [c, RingHom.etale_algebraMap] using (inferInstance : Algebra.Etale Aprime C)
  have hcSmooth : c.Smooth :=
    (RingHom.etale_iff_formallyUnramified_and_smooth c).mp hcEtale |>.2
  letI : Algebra.FormallySmooth Aprime C :=
    (RingHom.formallySmooth_algebraMap).mp <| by
      -- We use formal smoothness of the lifted étale source to lift `qC : C → B`.
      simpa [c] using hcSmooth.formallySmooth
  have hnilB : IsNilpotent (RingHom.ker qB) :=
    isNilpotent_of_square_zero (RingHom.ker qB) hSqB
  letI : Algebra Aprime B := RingHom.toAlgebra (f.comp qA)
  letI : Algebra Aprime Bprime := g.toAlgebra
  have hqCbase : qC.comp c = f.comp qA := by
    ext r
    -- The chosen quotient equivalence `eC` is linear over `Aprime ⧸ ker qA`.
    simpa [qC, c, RingHom.comp_apply, RingHom.algebraMap_toAlgebra] using
      eC.commutes' (Ideal.Quotient.mk (RingHom.ker qA) r)
  let qCAlg : C →ₐ[Aprime] B :=
    { toRingHom := qC
      commutes' := fun r ↦ congrArg (fun h : Aprime →+* B ↦ h r) hqCbase }
  let qBAlg : Bprime →ₐ[Aprime] B :=
    { toRingHom := qB
      commutes' := fun r ↦ congrArg (fun h : Aprime →+* B ↦ h r) hcomm }
  let φAlg : C →ₐ[Aprime] Bprime :=
    Algebra.FormallySmooth.liftOfSurjective qCAlg qBAlg hSurjB hnilB
  have hqAlg : qBAlg.comp φAlg = qCAlg :=
    Algebra.FormallySmooth.comp_liftOfSurjective qCAlg qBAlg hSurjB hnilB
  have hq : qB.comp φAlg.toRingHom = qC := by
    -- The chosen comparison map is a lift of `qC` through the quotient `qB`.
    ext x
    exact congrArg (fun h : C →ₐ[Aprime] B ↦ h x) hqAlg
  have hcomp : φAlg.toRingHom.comp c = g := by
    -- As an `Aprime`-algebra map, `φAlg` commutes with the base map `g`.
    ext r
    exact φAlg.commutes' r
  have hSqSrc : (Ideal.map c (RingHom.ker qA)) ^ 2 = ⊥ := by
    -- Transport square-zero of `ker qA` along the lifted étale source map `c`.
    simpa [c, Ideal.map_pow] using congrArg (Ideal.map c) hSqA
  have hTgt :
      RingHom.ker qB = Ideal.map g (RingHom.ker qA) := by
    exact targetKernel_eq_map_of_baseChangeCotangentEquiv
      (g := g) (qA := qA) (qB := qB) (f := f) hcomm hSqB hBaseChange
  have hSurjφ : Function.Surjective φAlg.toRingHom := by
    -- Once the target kernel is normalized to `Ideal.map g (ker qA)`, surjectivity is the square-zero
    -- ideal-lifting statement proved above.
    exact comparisonSurjectiveOfSquareZeroLift hSurjC hq hcomp hTgt hSqA
  have hInjφ : Function.Injective φAlg.toRingHom := by
    -- The remaining injectivity step is delegated to the generic étale-lift comparison package.
    exact comparisonInjectiveOfEtaleLift
      hcEtale hSurjC hSurjB hq hcomp hSqA hSrc hTgt hBaseChange
  have hEtaleφ : φAlg.toRingHom.Etale := by
    -- Bijective ring maps are étale, so the comparison identifies `Bprime` with the chosen étale
    -- lift `C`.
    exact RingHom.Etale.of_bijective ⟨hInjφ, hSurjφ⟩
  have hCompEtale : (φAlg.toRingHom.comp c).Etale := by
    have hφUnram : φAlg.toRingHom.FormallyUnramified := hEtaleφ.formallyUnramified
    have hφSmooth : φAlg.toRingHom.Smooth :=
      (RingHom.etale_iff_formallyUnramified_and_smooth _).mp hEtaleφ |>.2
    -- Compose the étale source lift with the étale comparison isomorphism.
    rw [RingHom.etale_iff_formallyUnramified_and_smooth]
    exact ⟨RingHom.FormallyUnramified.comp hcEtale.formallyUnramified hφUnram,
      RingHom.Smooth.comp hcSmooth hφSmooth⟩
  -- Compose the étale source lift with the étale comparison isomorphism to recover `g`.
  exact hcomp ▸ hCompEtale

end

end RingHom
