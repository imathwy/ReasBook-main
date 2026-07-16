import stacks_proof.stacks_project.Chap10.Lemma_10_99_11.StageKernelFiltration

open CategoryTheory.Limits IsLocalRing
open scoped TensorProduct Pointwise

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/-- Helper for Lemma 10.99.11: localizing an `S`-linear equivalence at a prime ideal of `S`
again gives an `S`-linear equivalence. -/
noncomputable def localized_linearEquiv_atPrime
    {X : Type*} {Y : Type*} [AddCommMonoid X] [AddCommMonoid Y] [Module S X] [Module S Y]
    (q : PrimeSpectrum S) (e : X ≃ₗ[S] Y) :
    LocalizedModule.AtPrime q.asIdeal X ≃ₗ[S] LocalizedModule.AtPrime q.asIdeal Y := by
  refine LinearEquiv.ofLinear
    (LocalizedModule.map q.asIdeal.primeCompl e.toLinearMap)
    (LocalizedModule.map q.asIdeal.primeCompl e.symm.toLinearMap)
    ?_ ?_
  · -- Proof comment: after precomposing with the canonical localization map on `X`, both
    -- composites reduce to the identity because `e ∘ e.symm = id`.
    apply IsLocalizedModule.linearMap_ext q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl Y)
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl Y)
    ext y
    simp [LinearMap.comp_apply]
  · -- Proof comment: the same computation on generators shows `e ∘ e.symm = id` after
    -- localization on `X`.
    apply IsLocalizedModule.linearMap_ext q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl X)
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl X)
    ext x
    simp [LinearMap.comp_apply]

/-- Helper for Lemma 10.99.11: after localizing the `S`-module factor at `q` and the `R`-module
factor at the under-prime `q ∩ R`, tensoring over `R` agrees with localizing the tensor product at
`q`. -/
noncomputable def localized_tensorProduct_right_localized_linearEquiv
    {N : Type*} [AddCommMonoid N] [Module S N] [Module R N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P]
    (q : PrimeSpectrum S) :
    LocalizedModule.AtPrime q.asIdeal N ⊗[R] LocalizedModule.AtPrime (q.asIdeal.under R) P
      ≃ₗ[R] LocalizedModule.AtPrime q.asIdeal (N ⊗[R] P) := by
  let p : Ideal R := q.asIdeal.under R
  -- Proof comment: first rewrite the localized `R`-module as `R_p ⊗[R] P`.
  let e₁ :
      LocalizedModule.AtPrime q.asIdeal N ⊗[R] LocalizedModule.AtPrime p P
        ≃ₗ[R] LocalizedModule.AtPrime q.asIdeal N ⊗[R]
          (Localization.AtPrime p ⊗[R] P) :=
    TensorProduct.congr (LinearEquiv.refl R _)
      (LinearEquiv.restrictScalars R (LocalizedModule.equivTensorProduct p.primeCompl P))
  -- Proof comment: reassociate so that the localized base ring sits next to `N_q`.
  let e₂ :
      LocalizedModule.AtPrime q.asIdeal N ⊗[R] (Localization.AtPrime p ⊗[R] P)
        ≃ₗ[R] (LocalizedModule.AtPrime q.asIdeal N ⊗[R] Localization.AtPrime p) ⊗[R] P :=
    (TensorProduct.assoc R (LocalizedModule.AtPrime q.asIdeal N) (Localization.AtPrime p) P).symm
  -- Proof comment: cancel the redundant `R_p` tensor factor because `N_q` is already an
  -- `R_p`-module through the local ring map.
  let eLeft :
      LocalizedModule.AtPrime q.asIdeal N ⊗[R] Localization.AtPrime p
        ≃ₗ[R] LocalizedModule.AtPrime q.asIdeal N :=
    (TensorProduct.comm R (LocalizedModule.AtPrime q.asIdeal N) (Localization.AtPrime p)).trans
      (LinearEquiv.restrictScalars R <|
        IsLocalization.moduleLid (S := p.primeCompl) (A := Localization.AtPrime p)
          (M₁ := LocalizedModule.AtPrime q.asIdeal N))
  let e₃ :
      (LocalizedModule.AtPrime q.asIdeal N ⊗[R] Localization.AtPrime p) ⊗[R] P
        ≃ₗ[R] LocalizedModule.AtPrime q.asIdeal N ⊗[R] P :=
    TensorProduct.congr eLeft (LinearEquiv.refl R P)
  -- Proof comment: the last step is the canonical localization/tensor comparison from
  -- Lemma `10.39.18`.
  let e₄ :
      LocalizedModule.AtPrime q.asIdeal N ⊗[R] P
        ≃ₗ[R] LocalizedModule.AtPrime q.asIdeal (N ⊗[R] P) :=
    LinearEquiv.restrictScalars R <|
      localized_tensor_right_equiv (R := R) (A := S) (X := N) q.asIdeal.primeCompl P
  exact e₁.trans <| e₂.trans <| e₃.trans e₄

/-- Helper for Lemma 10.99.11: localizing the ideal `I` at the under-prime `q ∩ R` identifies
with its extended ideal inside `R_(q ∩ R)` as an `R`-module. -/
noncomputable def localized_under_ideal_linearEquiv_mapped_ideal
    (I : Ideal R) (q : PrimeSpectrum S) :
    LocalizedModule.AtPrime (q.asIdeal.under R) I ≃ₗ[R]
      Ideal.map (algebraMap R (Localization.AtPrime (q.asIdeal.under R))) I :=
  IsLocalizedModule.linearEquiv (q.asIdeal.under R).primeCompl
    (LocalizedModule.mkLinearMap (q.asIdeal.under R).primeCompl I)
    (Algebra.idealMap I (S := Localization.AtPrime (q.asIdeal.under R)))

/-- Helper for Lemma 10.99.11: the ideal-localization comparison sends the class of an element of
`I` to its image in the extended ideal of `R_(q ∩ R)`. -/
@[simp] theorem localized_under_ideal_linearEquiv_mapped_ideal_apply_mk
    (I : Ideal R) (q : PrimeSpectrum S) (x : I) :
    localized_under_ideal_linearEquiv_mapped_ideal (R := R) (S := S) I q
        (LocalizedModule.mkLinearMap (q.asIdeal.under R).primeCompl I x) =
      Algebra.idealMap I (S := Localization.AtPrime (q.asIdeal.under R)) x := by
  -- Proof comment: both sides are the canonical images of `x` under the two localization models.
  simpa [localized_under_ideal_linearEquiv_mapped_ideal] using
    (IsLocalizedModule.linearEquiv_apply (q.asIdeal.under R).primeCompl
      (LocalizedModule.mkLinearMap (q.asIdeal.under R).primeCompl I)
      (Algebra.idealMap I (S := Localization.AtPrime (q.asIdeal.under R))) x)

/-- Helper for Lemma 10.99.11: the canonical bridge
`I ⊗[R] M → (IS) ⊗[S] M` sends the source `I^n`-power filtration into the corresponding
filtration by `(IS)^n`. -/
lemma mapped_ideal_tensor_map_mem_pow_smul_top
    (I : Ideal R) (n : ℕ) {x : I ⊗[R] M}
    (hx : x ∈ I ^ n • (⊤ : Submodule R (I ⊗[R] M))) :
    mapped_ideal_tensor_map (A := R) (B := S) (N := M) I x ∈
      (Ideal.map (algebraMap R S) I) ^ n •
        (⊤ : Submodule S (Ideal.map (algebraMap R S) I ⊗[S] M)) := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  -- Proof comment: unfold membership in the source `I^n`-power filtration and transport the
  -- generators through the tensor bridge one scalar at a time.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y hy
    have hrJ : algebraMap R S r ∈ J ^ n := by
      simpa [J, Ideal.map_pow] using Ideal.mem_map_of_mem (algebraMap R S) hr
    have hyTop :
        mapped_ideal_tensor_map (A := R) (B := S) (N := M) I y ∈
          (⊤ : Submodule S (J ⊗[S] M)) := by
      simp
    -- Proof comment: the bridge is `R`-linear, so the scalar from `I^n` turns into its image in
    -- `(IS)^n` and hence lands in the target power-smul submodule.
    simpa [J, Algebra.smul_def] using
      (Submodule.smul_mem_smul hrJ hyTop :
        algebraMap R S r • mapped_ideal_tensor_map (A := R) (B := S) (N := M) I y ∈
          J ^ n • (⊤ : Submodule S (J ⊗[S] M)))
  · intro y z hy hz
    simpa [map_add] using add_mem hy hz

/-- Helper for Lemma 10.99.11: the kernel of the mapped-ideal multiplication map
`(IS) ⊗[S] M → M` satisfies the same power filtration as the source kernel. -/
lemma mapped_ideal_tensor_kernel_le_pow_smul_top
    (I : Ideal R) (hflat : FlatQuotientsByIdealPowers M I) (n : ℕ) :
    LinearMap.ker
        (TensorProduct.lift
          ((LinearMap.lsmul S M).comp (Ideal.map (algebraMap R S) I).subtype)) ≤
      (Ideal.map (algebraMap R S) I) ^ n •
        (⊤ : Submodule S (Ideal.map (algebraMap R S) I ⊗[S] M)) := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let φ : I ⊗[R] M →ₗ[R] J ⊗[S] M :=
    mapped_ideal_tensor_map (A := R) (B := S) (N := M) I
  let μR : I ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  let μS : J ⊗[S] M →ₗ[S] M :=
    TensorProduct.lift ((LinearMap.lsmul S M).comp J.subtype)
  intro x hx
  rcases mapped_ideal_tensor_map_surjective (A := R) (B := S) (N := M) I x with ⟨y, rfl⟩
  have hy_zero : μR y = 0 := by
    -- Proof comment: the source and mapped multiplication maps commute with the tensor bridge, so
    -- any preimage of a mapped-kernel element already lies in the source kernel.
    have hcompare :=
      mapped_ideal_tensor_to_module_comp (A := R) (B := S) (N := M) I
    have hx_zero : μS (φ y) = 0 := by
      exact LinearMap.mem_ker.mp hx
    calc
      μR y = (μS.restrictScalars R) (φ y) := by
        simpa [LinearMap.comp_apply, φ, μR, μS] using
          (congrArg (fun f ↦ f y) hcompare).symm
      _ = 0 := hx_zero
  have hy_mem :
      y ∈ I ^ n • (⊤ : Submodule R (I ⊗[R] M)) := by
    exact tensor_kernel_le_pow_smul_top_stage (R := R) (M := M) I hflat n
      (show y ∈ LinearMap.ker μR by simpa [μR, LinearMap.mem_ker] using hy_zero)
  -- Proof comment: transport the already proved source filtration through the bridge to the
  -- genuinely localizable mapped-ideal tensor owner.
  exact mapped_ideal_tensor_map_mem_pow_smul_top
    (R := R) (S := S) (M := M) I n hy_mem

/-- Helper for Lemma 10.99.11: after localizing at a prime `q` containing `IS`, the kernel of the
mapped-ideal multiplication map `(IS) ⊗[S] M → M` vanishes. -/
lemma localized_mapped_ideal_tensor_kernel_eq_bot_at_prime
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflat : FlatQuotientsByIdealPowers M I) :
    (LinearMap.ker
        (TensorProduct.lift
          ((LinearMap.lsmul S M).comp (Ideal.map (algebraMap R S) I).subtype))).localized
        q.asIdeal.primeCompl = ⊥ := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let K : Submodule S (J ⊗[S] M) :=
    LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul S M).comp J.subtype))
  let Sq := Localization.AtPrime q.asIdeal
  have hpow :
      ∀ n : ℕ, K ≤ J ^ n • (⊤ : Submodule S (J ⊗[S] M)) := by
    intro n
    simpa [J, K] using
      mapped_ideal_tensor_kernel_le_pow_smul_top
        (R := R) (S := S) (M := M) I hflat n
  have hmap :
      Ideal.map (algebraMap S Sq) J ≤ Ideal.jacobson (⊥ : Ideal Sq) := by
    calc
      Ideal.map (algebraMap S Sq) J ≤ Ideal.map (algebraMap S Sq) q.asIdeal :=
        Ideal.map_mono hq
      _ = IsLocalRing.maximalIdeal Sq := by
        simpa [Sq] using Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal)
      _ ≤ Ideal.jacobson (⊥ : Ideal Sq) :=
        IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal Sq)
  have hlocal :
      (⨅ n : ℕ, (Ideal.map (algebraMap S Sq) J) ^ n • ⊤ :
        Submodule Sq (LocalizedModule.AtPrime q.asIdeal (J ⊗[S] M))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson
      (I := Ideal.map (algebraMap S Sq) J)
      (M := LocalizedModule.AtPrime q.asIdeal (J ⊗[S] M))
      hmap
  have hle :
      K.localized q.asIdeal.primeCompl ≤
        (⨅ n : ℕ, (Ideal.map (algebraMap S Sq) J) ^ n • ⊤ :
          Submodule Sq (LocalizedModule.AtPrime q.asIdeal (J ⊗[S] M))) := by
    refine le_iInf fun n ↦ ?_
    change
      K.localized' Sq q.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (J ⊗[S] M)) ≤
        (Ideal.map (algebraMap S Sq) J) ^ n •
          (⊤ : Submodule Sq (LocalizedModule.AtPrime q.asIdeal (J ⊗[S] M)))
    refine le_trans
      ((Submodule.localized'gi Sq q.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (J ⊗[S] M))).gc.monotone_l
        (hpow n)) ?_
    rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Ideal.map_pow, Submodule.localized'_top]
  rw [hlocal] at hle
  simpa [K] using hle

/-- Helper for Lemma 10.99.11: if `q` contains `IS`, then the localized base ideal `I R_(q ∩ R)`
is proper. -/
lemma localized_under_ideal_ne_top_at_prime
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal) :
    Ideal.map (algebraMap R (Localization.AtPrime (q.asIdeal.under R))) I ≠ ⊤ := by
  have hp : I ≤ q.asIdeal.under R := by
    intro x hx
    change algebraMap R S x ∈ q.asIdeal
    exact hq (Ideal.mem_map_of_mem (algebraMap R S) hx)
  have hle :
      Ideal.map (algebraMap R (Localization.AtPrime (q.asIdeal.under R))) I ≤
        maximalIdeal (Localization.AtPrime (q.asIdeal.under R)) := by
    calc
      Ideal.map (algebraMap R (Localization.AtPrime (q.asIdeal.under R))) I ≤
          Ideal.map (algebraMap R (Localization.AtPrime (q.asIdeal.under R))) (q.asIdeal.under R) :=
        Ideal.map_mono hp
      _ = maximalIdeal (Localization.AtPrime (q.asIdeal.under R)) := by
        simpa using Localization.AtPrime.map_eq_maximalIdeal (I := q.asIdeal.under R)
  intro htop
  have hmax_top :
      maximalIdeal (Localization.AtPrime (q.asIdeal.under R)) = ⊤ :=
    le_antisymm le_top (by simpa [htop] using hle)
  exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime (q.asIdeal.under R))).ne_top
    hmax_top

/-- Helper for Lemma 10.99.11: after localizing at `q`, the mapped-ideal multiplication map
`(IS) ⊗[S] M → M` becomes injective. -/
lemma localized_mapped_ideal_tensor_multiplication_injective_at_prime
    (I : Ideal R) (q : PrimeSpectrum S) (hq : I.map (algebraMap R S) ≤ q.asIdeal)
    (hflat : FlatQuotientsByIdealPowers M I) :
    Function.Injective
      (LocalizedModule.map q.asIdeal.primeCompl
        (TensorProduct.lift
          ((LinearMap.lsmul S M).comp (Ideal.map (algebraMap R S) I).subtype))) := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let μS : J ⊗[S] M →ₗ[S] M :=
    TensorProduct.lift ((LinearMap.lsmul S M).comp J.subtype)
  have hker_bot :
      (LinearMap.ker μS).localized q.asIdeal.primeCompl = ⊥ := by
    -- Proof comment: the Artin-Rees/Krull-intersection argument above already kills the localized
    -- mapped-ideal kernel at primes over `IS`.
    simpa [J, μS] using
      localized_mapped_ideal_tensor_kernel_eq_bot_at_prime
        (R := R) (S := S) (M := M) I q hq hflat
  have hsub :
      Subsingleton (LocalizedModule q.asIdeal.primeCompl (LinearMap.ker μS)) := by
    -- Proof comment: convert the localized kernel equality `K_q = 0` into a subsingleton owner
    -- using the canonical localization equivalence for submodules.
    let _ : Subsingleton ↥((LinearMap.ker μS).localized q.asIdeal.primeCompl) :=
      (Submodule.subsingleton_iff_eq_bot).2 hker_bot
    exact (LinearMap.ker μS).localizedEquiv q.asIdeal.primeCompl |>.symm.injective.subsingleton
  -- Proof comment: Lemma `10.79.2` packages exactly the implication from localized-kernel
  -- subsingleton to injectivity of the localized map.
  exact
    (localized_map_injective_iff_subsingleton_ker μS q.asIdeal.primeCompl).2 hsub

/-- Helper for Lemma 10.99.11: kernel vanishing for the ideal-tensor multiplication map forces
vanishing of the corresponding quotient `Tor₁`. -/
lemma tor_one_module_quotient_vanishes_of_ker_eq_bot
    {A : Type u} [CommRing A] {J : Ideal A} {N : Type u} [AddCommGroup N] [Module A N]
    (hker :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul A N).comp J.subtype)) = ⊥) :
    IsZero (Tor₁[A](N, A ⧸ J)) := by
  let μ : J ⊗[A] N →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp J.subtype)
  have hkerSubsingleton : Subsingleton (LinearMap.ker μ) := by
    -- Proof comment: the assumed kernel equality identifies the kernel with the zero submodule.
    exact (Submodule.subsingleton_iff_eq_bot).2 (by simpa [μ] using hker)
  let e :
      Tor₁[A](N, A ⧸ J) ≃ₗ[A] LinearMap.ker μ :=
    tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (R := A) (M := N) J
  have hsub :
      Subsingleton (Tor₁[A](N, A ⧸ J)) := by
    refine ⟨fun x y ↦ ?_⟩
    apply e.injective
    exact Subsingleton.elim _ _
  -- Proof comment: Remark `10.75.9` identifies this Tor owner with the zero kernel.
  exact (ModuleCat.isZero_iff_subsingleton).2 hsub

/-- Helper for Lemma 10.99.11: a commuting square of linear equivalences transports injectivity
across the horizontal maps. -/
lemma injective_of_ladder_linearEquiv
    {A : Type u} [CommRing A]
    {P : Type v} [AddCommGroup P] [Module A P]
    {Q : Type w} [AddCommGroup Q] [Module A Q]
    {P' : Type v} [AddCommGroup P'] [Module A P']
    {Q' : Type w} [AddCommGroup Q'] [Module A Q']
    {f : P →ₗ[A] Q} {g : P' →ₗ[A] Q'}
    {eP : P ≃ₗ[A] P'} {eQ : Q ≃ₗ[A] Q'}
    (h : g.comp eP.toLinearMap = eQ.toLinearMap.comp f)
    (hf : Function.Injective f) :
    Function.Injective g := by
  intro x y hxy
  apply eP.symm.injective
  apply hf
  apply eQ.injective
  -- Proof comment: evaluate the commuting square on `eP.symm x` and `eP.symm y`.
  calc
    eQ (f (eP.symm x)) = g x := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun h (eP.symm x)).symm
    _ = g y := hxy
    _ = eQ (f (eP.symm y)) := by
      simpa [LinearMap.comp_apply] using LinearMap.congr_fun h (eP.symm y)

/-- Helper for Lemma 10.99.11: package the source-owner transport
`LocalizedModule.AtPrime q (I ⊗[R] M) ≃ J ⊗[Rp] Mq` once, so the remaining work only needs a
generator-level conjugation check. -/
noncomputable def localized_source_tensor_owner_equiv_under_ideal_tensor
    (I : Ideal R) (q : PrimeSpectrum S) :
    let p : Ideal R := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    letI : Algebra Rp Sq := f.toAlgebra
    letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[R] J ⊗[Rp] Mq := by
  let p : Ideal R := q.asIdeal.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q.asIdeal
  let J : Ideal Rp := Ideal.map (algebraMap R Rp) I
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
  letI : Algebra Rp Sq := f.toAlgebra
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  let eComm :
      LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[R]
        LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    -- Proof comment: first localize the tensor swap `I ⊗ M ≃ M ⊗ I`.
    LinearEquiv.restrictScalars R <|
      localized_linearEquiv_atPrime (S := S) q
        ((TensorProduct.comm R I M).toAddEquiv.linearEquiv S)
  let eTensor :
      Mq ⊗[R] LocalizedModule.AtPrime p I ≃ₗ[R]
        LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    -- Proof comment: then rewrite the localized tensor product by localizing only the right
    -- tensor factor at the under-prime `p = q ∩ R`.
    LinearEquiv.restrictScalars R <|
      localized_tensorProduct_right_localized_linearEquiv
        (R := R) (S := S) (N := M) (P := I) q
  let eIdeal :
      Mq ⊗[R] LocalizedModule.AtPrime p I ≃ₗ[R] Mq ⊗[R] J :=
    -- Proof comment: replace the localized ideal by the mapped ideal `J = I Rp`.
    LinearEquiv.restrictScalars R <|
      TensorProduct.congr
        (LinearEquiv.refl R Mq)
        (localized_under_ideal_linearEquiv_mapped_ideal (R := R) (S := S) I q)
  let eLidJ :
      Rp ⊗[R] J ≃ₗ[Rp] J :=
    IsLocalization.moduleLid (S := p.primeCompl) (A := Rp) (M₁ := J)
  let eBase :
      Mq ⊗[R] J ≃ₗ[R] Mq ⊗[Rp] J :=
    -- Proof comment: cancel the redundant `Rp` base change on the ideal factor.
    (LinearEquiv.restrictScalars R <|
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R Rp Rp Mq J).symm.trans
        (TensorProduct.congr (LinearEquiv.refl Rp Mq) eLidJ))
  let eCommRp : Mq ⊗[Rp] J ≃ₗ[R] J ⊗[Rp] Mq :=
    LinearEquiv.restrictScalars R (TensorProduct.comm Rp Mq J)
  exact eComm.trans <| eTensor.symm.trans <| eIdeal.trans <| eBase.trans eCommRp

/-- Helper for Lemma 10.99.11: before extending the ideal to `R_(q ∩ R)`, the localized source
owner `(I ⊗[R] M)_q` identifies with the simpler source tensor owner `I ⊗[R] M_q`. -/
noncomputable def localized_source_tensor_owner_equiv_source_ideal_tensor
    (I : Ideal R) (q : PrimeSpectrum S) :
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[R] I ⊗[R] Mq := by
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  let eComm :
      LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[R]
        LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    -- Proof comment: first localize the tensor swap `I ⊗ M ≃ M ⊗ I`.
    LinearEquiv.restrictScalars R <|
      localized_linearEquiv_atPrime (S := S) q
        ((TensorProduct.comm R I M).toAddEquiv.linearEquiv S)
  let eTensor :
      Mq ⊗[R] I ≃ₗ[R] LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    -- Proof comment: then use the standard localization-tensor comparison on the right factor.
    LinearEquiv.restrictScalars R <|
      localized_tensor_right_equiv (R := R) (A := S) (X := M) q.asIdeal.primeCompl I
  let eCommRq : Mq ⊗[R] I ≃ₗ[R] I ⊗[R] Mq :=
    TensorProduct.comm R Mq I
  exact eComm.trans <| eTensor.symm.trans eCommRq

/-- Helper for Lemma 10.99.11: the localized source tensor owner also identifies with
`I ⊗[R] M_q` as an `S`-module through the localized module factor. -/
noncomputable def localized_source_tensor_owner_linearEquiv_source_ideal_tensor
    (I : Ideal R) (q : PrimeSpectrum S) :
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    let _ : Module S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).isScalarTower (A := S)
    LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[S] I ⊗[R] Mq := by
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  letI : Module S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).isScalarTower (A := S)
  let eComm :
      LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[S]
        LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    localized_linearEquiv_atPrime (S := S) q
      ((TensorProduct.comm R I M).toAddEquiv.linearEquiv S)
  let eTensor :
      Mq ⊗[R] I ≃ₗ[S] LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    localized_tensor_right_equiv (R := R) (A := S) (X := M) q.asIdeal.primeCompl I
  let eCommSq : I ⊗[R] Mq ≃ₗ[S] Mq ⊗[R] I :=
    (TensorProduct.comm R I Mq).toAddEquiv.linearEquiv S
  exact eComm.trans <| eTensor.symm.trans eCommSq.symm

/-- Helper for Lemma 10.99.11: the simpler source-owner comparison sends a localized source pure
tensor to the corresponding pure tensor in `I ⊗[R] M_q`. -/
@[simp] theorem localized_source_tensor_owner_equiv_source_ideal_tensor_apply_mk_tmul
    (I : Ideal R) (q : PrimeSpectrum S) (a : I) (m : M) :
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    localized_source_tensor_owner_equiv_source_ideal_tensor
      (R := R) (S := S) (M := M) I q
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M) (a ⊗ₜ[R] m)) =
        a ⊗ₜ[R] (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M m) := by
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  let eComm :
      LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[R]
        LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    LinearEquiv.restrictScalars R <|
      localized_linearEquiv_atPrime (S := S) q
        ((TensorProduct.comm R I M).toAddEquiv.linearEquiv S)
  let eTensor :
      Mq ⊗[R] I ≃ₗ[R] LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    LinearEquiv.restrictScalars R <|
      localized_tensor_right_equiv (R := R) (A := S) (X := M) q.asIdeal.primeCompl I
  have hComm :
      eComm (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M) (a ⊗ₜ[R] m)) =
        LocalizedModule.mkLinearMap q.asIdeal.primeCompl (M ⊗[R] I) (m ⊗ₜ[R] a) := by
    -- Proof comment: localizing the tensor swap keeps the tensor generator unchanged up to the
    -- expected order reversal.
    simpa [eComm, localized_linearEquiv_atPrime] using
      (LocalizedModule.map_mk (S := q.asIdeal.primeCompl)
        (((TensorProduct.comm R I M).toAddEquiv.linearEquiv S).toLinearMap)
        (a ⊗ₜ[R] m) (1 : q.asIdeal.primeCompl))
  have hTensor :
      eTensor.symm
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (M ⊗[R] I) (m ⊗ₜ[R] a)) =
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M m) ⊗ₜ[R] a := by
    -- Proof comment: the localization-tensor equivalence is normalized so the localized tensor
    -- generator comes from localizing only the module factor.
    simpa [eTensor, localized_tensor_right_equiv] using
      (IsLocalizedModule.linearEquiv_symm_apply
        (S := q.asIdeal.primeCompl)
        (f := TensorProduct.AlgebraTensorModule.rTensor R I
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M))
        (g := LocalizedModule.mkLinearMap q.asIdeal.primeCompl (M ⊗[R] I))
        (x := m ⊗ₜ[R] a))
  -- Proof comment: combine the swap computation and the localization-tensor computation, then
  -- swap the two tensor factors back to the source order.
  rw [localized_source_tensor_owner_equiv_source_ideal_tensor]
  simp only [LinearEquiv.trans_apply]
  rw [hComm, hTensor]
  simp

/-- Helper for Lemma 10.99.11: the `S`-linear source-owner comparison sends a localized source
pure tensor to the corresponding pure tensor in `I ⊗[R] M_q`. -/
@[simp] theorem localized_source_tensor_owner_linearEquiv_source_ideal_tensor_apply_mk_tmul
    (I : Ideal R) (q : PrimeSpectrum S) (a : I) (m : M) :
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    let _ : Module S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).isScalarTower (A := S)
    localized_source_tensor_owner_linearEquiv_source_ideal_tensor
      (R := R) (S := S) (M := M) I q
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M) (a ⊗ₜ[R] m)) =
        a ⊗ₜ[R] (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M m) := by
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  letI : Module S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).isScalarTower (A := S)
  let eComm :
      LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[S]
        LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    localized_linearEquiv_atPrime (S := S) q
      ((TensorProduct.comm R I M).toAddEquiv.linearEquiv S)
  let eTensor :
      Mq ⊗[R] I ≃ₗ[S] LocalizedModule.AtPrime q.asIdeal (M ⊗[R] I) :=
    localized_tensor_right_equiv (R := R) (A := S) (X := M) q.asIdeal.primeCompl I
  have hComm :
      eComm (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M) (a ⊗ₜ[R] m)) =
        LocalizedModule.mkLinearMap q.asIdeal.primeCompl (M ⊗[R] I) (m ⊗ₜ[R] a) := by
    -- Proof comment: localizing the tensor swap keeps the tensor generator unchanged up to the
    -- expected order reversal.
    simpa [eComm, localized_linearEquiv_atPrime] using
      (LocalizedModule.map_mk (S := q.asIdeal.primeCompl)
        (((TensorProduct.comm R I M).toAddEquiv.linearEquiv S).toLinearMap)
        (a ⊗ₜ[R] m) (1 : q.asIdeal.primeCompl))
  have hTensor :
      eTensor.symm
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (M ⊗[R] I) (m ⊗ₜ[R] a)) =
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M m) ⊗ₜ[R] a := by
    -- Proof comment: the localization-tensor equivalence is normalized so the localized tensor
    -- generator comes from localizing only the module factor.
    simpa [eTensor, localized_tensor_right_equiv] using
      (IsLocalizedModule.linearEquiv_symm_apply
        (S := q.asIdeal.primeCompl)
        (f := TensorProduct.AlgebraTensorModule.rTensor R I
          (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M))
        (g := LocalizedModule.mkLinearMap q.asIdeal.primeCompl (M ⊗[R] I))
        (x := m ⊗ₜ[R] a))
  -- Proof comment: combine the swap computation and the localization-tensor computation, then
  -- swap the two tensor factors back to the source order.
  rw [localized_source_tensor_owner_linearEquiv_source_ideal_tensor]
  simp only [LinearEquiv.trans_apply]
  rw [hComm, hTensor]
  simp

/-- Helper for Lemma 10.99.11: under the simpler source-owner comparison
`(I ⊗[R] M)_q ≃ I ⊗[R] M_q`, the localized source multiplication map becomes the canonical
source multiplication map `I ⊗[R] M_q → M_q`. -/
lemma localized_source_tensor_map_conjugates_to_source_ideal_multiplication
    (I : Ideal R) (q : PrimeSpectrum S) :
    let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    let _ : Module S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).isScalarTower (A := S)
    let eSource :
        LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[R] I ⊗[R] Mq :=
      (localized_source_tensor_owner_linearEquiv_source_ideal_tensor
        (R := R) (S := S) (M := M) I q).restrictScalars R
    let μRq : I ⊗[R] Mq →ₗ[R] Mq :=
      TensorProduct.lift ((LinearMap.lsmul R Mq).comp I.subtype)
    μRq.comp eSource.toLinearMap =
      (LocalizedModule.map q.asIdeal.primeCompl
        (source_tensor_to_module (R := R) (S := S) (M := M) I)).restrictScalars R := by
  let Mq : Type (max v w) := LocalizedModule.AtPrime q.asIdeal M
  let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  let _ : Module S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).toAddEquiv.module S
  let _ : IsScalarTower R S (I ⊗[R] Mq) := (TensorProduct.comm R I Mq).isScalarTower (A := S)
  let eSource :
      LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[R] I ⊗[R] Mq :=
    (localized_source_tensor_owner_linearEquiv_source_ideal_tensor
      (R := R) (S := S) (M := M) I q).restrictScalars R
  let μRq : I ⊗[R] Mq →ₗ[R] Mq :=
    TensorProduct.lift ((LinearMap.lsmul R Mq).comp I.subtype)
  let eSourceS :
      LocalizedModule.AtPrime q.asIdeal (I ⊗[R] M) ≃ₗ[S] I ⊗[R] Mq :=
    localized_source_tensor_owner_linearEquiv_source_ideal_tensor
      (R := R) (S := S) (M := M) I q
  let μSq : I ⊗[R] Mq →ₗ[S] Mq :=
    source_tensor_to_module (R := R) (S := S) (M := Mq) I
  have hS :
      μSq.comp eSourceS.toLinearMap =
        LocalizedModule.map q.asIdeal.primeCompl
          (source_tensor_to_module (R := R) (S := S) (M := M) I) := by
    dsimp [eSourceS, μSq]
    apply IsLocalizedModule.linearMap_ext q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M))
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
    apply LinearMap.restrictScalars_injective R
    apply TensorProduct.ext'
    intro a m
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]
    have howner :
        localized_source_tensor_owner_linearEquiv_source_ideal_tensor
            (R := R) (S := S) (M := M) I q
            ((LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M)) (a ⊗ₜ[R] m)) =
          a ⊗ₜ[R] (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M m) := by
      simpa using
        localized_source_tensor_owner_linearEquiv_source_ideal_tensor_apply_mk_tmul
          (R := R) (S := S) (M := M) I q a m
    change
      (source_tensor_to_module (R := R) (S := S) (M := Mq) I)
          ((localized_source_tensor_owner_linearEquiv_source_ideal_tensor
              (R := R) (S := S) (M := M) I q)
            ((LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M)) (a ⊗ₜ[R] m))) =
        ((LocalizedModule.map q.asIdeal.primeCompl)
          (source_tensor_to_module (R := R) (S := S) (M := M) I))
            ((LocalizedModule.mkLinearMap q.asIdeal.primeCompl (I ⊗[R] M)) (a ⊗ₜ[R] m))
    rw [howner]
    rw [LocalizedModule.mkLinearMap_apply]
    rw [LocalizedModule.mkLinearMap_apply]
    rw [LocalizedModule.map_mk]
    simp [source_tensor_to_module, TensorProduct.AlgebraTensorModule.rid_tmul]
    simpa using
      (LocalizedModule.smul'_mk (S := q.asIdeal.primeCompl)
        (r := algebraMap R S (a : R)) (s := 1) (m := m))
  calc
    μRq.comp eSource.toLinearMap =
        (μSq.comp eSourceS.toLinearMap).restrictScalars R := by
      have hμ : μSq.restrictScalars R = μRq := by
        apply TensorProduct.ext'
        intro a x
        simp [μSq, μRq, source_tensor_to_module, TensorProduct.AlgebraTensorModule.rid_tmul]
      rw [← hμ]
      rfl
    _ = (LocalizedModule.map q.asIdeal.primeCompl
          (source_tensor_to_module (R := R) (S := S) (M := M) I)).restrictScalars R := by
      simpa using congrArg (LinearMap.restrictScalars R) hS

end
