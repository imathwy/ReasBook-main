import Mathlib
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.DirectLimitFG

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_65_3 (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-
Domain triage: this item lies in commutative algebra of associated primes under flat base change.
The source-facing exact-annihilator set is `associatedPrimesOfModule`, while the Noetherian owner
abstraction is mathlib's `associatedPrimes`; this file stays at the source-facing layer, and any
Noetherian owner-form restatement should be obtained downstream via
`associatedPrimesOfModule_eq_associatedPrimes`. The quotient module `N / pN` is already exposed in
Lemma 10.65.1 as `relativeAssassinPrimeQuotient`, so this file reuses that chapter-level name
instead of keeping a parallel local definition.
-/

/-- Helper for Lemma 10.65.3: reducing `N` modulo `pS` is the same `S`-module as tensoring `N`
with the quotient ring `R ⧸ p`. -/
private noncomputable def relativeAssassinPrimeQuotient_tensorQuotient_linearEquiv
    (p : Ideal R) :
    relativeAssassinPrimeQuotient R S N p ≃ₗ[S] N ⊗[R] (R ⧸ p) :=
  (TensorProduct.quotTensorEquivQuotSMul N (p.map (algebraMap R S))).symm.trans <|
    (TensorProduct.congr (Ideal.qoutMapEquivTensorQout (R := R) (S := S) (I := p))
      (LinearEquiv.refl S N)).trans <|
    (TensorProduct.comm S _ N).trans <|
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N (R ⧸ p)

/-- Helper for Lemma 10.65.3: after localizing `N` at `q` and `M` at `q ∩ R`, tensoring over `R`
still gives the localization of `N ⊗[R] M`. This avoids the more delicate over/under tensor
transport and is the comparison used in the regular-element contradiction. -/
private noncomputable def localized_tensorProduct_right_localized_linearEquiv
    (q : PrimeSpectrum S) :
    LocalizedModule.AtPrime q.asIdeal N ⊗[R] LocalizedModule.AtPrime (q.asIdeal.under R) M
      ≃ₗ[R] LocalizedModule.AtPrime q.asIdeal (N ⊗[R] M) := by
  let p : Ideal R := q.asIdeal.under R
  -- First rewrite `M_p` as `R_p ⊗[R] M`.
  let e₁ :
      LocalizedModule.AtPrime q.asIdeal N ⊗[R] LocalizedModule.AtPrime p M
        ≃ₗ[R] LocalizedModule.AtPrime q.asIdeal N ⊗[R]
          (Localization.AtPrime p ⊗[R] M) :=
    TensorProduct.congr (LinearEquiv.refl R _)
      (LinearEquiv.restrictScalars R (LocalizedModule.equivTensorProduct p.primeCompl M))
  -- Then reassociate so the localized base ring sits next to `N_q`.
  let e₂ :
      LocalizedModule.AtPrime q.asIdeal N ⊗[R] (Localization.AtPrime p ⊗[R] M)
        ≃ₗ[R] (LocalizedModule.AtPrime q.asIdeal N ⊗[R] Localization.AtPrime p) ⊗[R] M :=
    (TensorProduct.assoc R (LocalizedModule.AtPrime q.asIdeal N) (Localization.AtPrime p) M).symm
  -- Cancel the redundant `R_p` tensor factor using that `N_q` is already an `R_p`-module.
  let eLeft :
      LocalizedModule.AtPrime q.asIdeal N ⊗[R] Localization.AtPrime p
        ≃ₗ[R] LocalizedModule.AtPrime q.asIdeal N :=
    (TensorProduct.comm R (LocalizedModule.AtPrime q.asIdeal N) (Localization.AtPrime p)).trans
      (LinearEquiv.restrictScalars R <|
        IsLocalization.moduleLid (S := p.primeCompl) (A := Localization.AtPrime p)
          (M₁ := LocalizedModule.AtPrime q.asIdeal N))
  let e₃ :
      (LocalizedModule.AtPrime q.asIdeal N ⊗[R] Localization.AtPrime p) ⊗[R] M
        ≃ₗ[R] LocalizedModule.AtPrime q.asIdeal N ⊗[R] M :=
    TensorProduct.congr eLeft (LinearEquiv.refl R M)
  -- Finally identify `N_q ⊗[R] M` with the localization of `N ⊗[R] M` at `q`.
  let e₄ :
      LocalizedModule.AtPrime q.asIdeal N ⊗[R] M
        ≃ₗ[R] LocalizedModule.AtPrime q.asIdeal (N ⊗[R] M) :=
    LinearEquiv.restrictScalars R <|
      localized_tensor_right_equiv (R := R) (A := S) (X := N) q.asIdeal.primeCompl M
  exact e₁.trans <| e₂.trans <| e₃.trans e₄

/-- Helper for Lemma 10.65.3: if `q` is associated to an `S`-module, then after localizing at
`q` the unique prime above it is the maximal ideal of `S_q`. -/
private theorem maximalIdeal_mem_associatedPrimesOfModule_atPrime_of_mem
    {X : Type*} [AddCommGroup X] [Module S X] {q : Ideal S} [q.IsPrime]
    (hq : q ∈ associatedPrimesOfModule S X) :
    IsLocalRing.maximalIdeal (Localization.AtPrime q) ∈
      associatedPrimesOfModule (Localization.AtPrime q) (LocalizedModule.AtPrime q X) := by
  have hrange :
      q ∈ Set.range (Ideal.comap (algebraMap S (Localization.AtPrime q))) := by
    refine ⟨IsLocalRing.maximalIdeal (Localization.AtPrime q), ?_⟩
    simpa using (Localization.AtPrime.comap_maximalIdeal (R := S) (I := q))
  have hloc :
      q ∈ associatedPrimesOfModule S (LocalizedModule.AtPrime q X) :=
    associatedPrimesOfModule_inter_localization_range_subset
      (R := S) (S := q.primeCompl) (M := X) ⟨hq, hrange⟩
  have himage :
      q ∈ Ideal.comap (algebraMap S (Localization.AtPrime q)) ''
        associatedPrimesOfModule (Localization.AtPrime q) (LocalizedModule.AtPrime q X) := by
    rw [associatedPrimesOfModule_localizedModule_eq_image_comap
      (R := S) (S := q.primeCompl) (M := X)]
    exact hloc
  rcases himage with ⟨J, hJ, hJcomap⟩
  have hJmax : J = IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    exact (Localization.AtPrime.eq_maximalIdeal_iff_comap_eq (R := S) (I := q)).mp hJcomap
  simpa [hJmax] using hJ

/-- Helper for Lemma 10.65.3: if the maximal ideal of `R_p` is associated to `M_p`, then `p`
was already associated to `M`. This is the source descent step obtained by combining the chapter's
localization descriptions of associated primes. -/
private theorem mem_associatedPrimesOfModule_of_maximalIdeal_mem_atPrime
    [IsNoetherianRing R] [Module.Finite R M]
    {p : Ideal R} [p.IsPrime]
    (hp :
      IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) :
    p ∈ associatedPrimesOfModule R M := by
  have hp_loc :
      p ∈ associatedPrimesOfModule R (LocalizedModule.AtPrime p M) := by
    have himage :
        p ∈ Ideal.comap (algebraMap R (Localization.AtPrime p)) ''
          associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
      refine ⟨IsLocalRing.maximalIdeal (Localization.AtPrime p), hp, ?_⟩
      simpa using (Localization.AtPrime.comap_maximalIdeal (R := R) (I := p))
    rw [associatedPrimesOfModule_localizedModule_eq_image_comap
      (R := R) (S := p.primeCompl) (M := M)] at himage
    exact himage
  have hp_pair :
      p ∈ associatedPrimesOfModule R M ∩
        Set.range (Ideal.comap (algebraMap R (Localization.AtPrime p))) := by
    rw [associatedPrimesOfModule_inter_localization_range_eq
      (R := R) (S := p.primeCompl) (M := M)]
    exact hp_loc
  exact hp_pair.1

/-- Helper for Lemma 10.65.3: if a localized element in the maximal ideal of `R_p` is regular on
`M_p`, then some numerator lying in `p` is already regular for the restricted `R`-action on
`M_p`. This is the bridge from the local regular-element criterion to the tensor comparison above.
-/
private theorem exists_mem_isSMulRegular_atPrime_numerator
    {p : Ideal R} [p.IsPrime] {x : Localization.AtPrime p}
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (hreg : IsSMulRegular (LocalizedModule.AtPrime p M) x) :
    ∃ r ∈ p, IsSMulRegular (LocalizedModule.AtPrime p M) r := by
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  have hrp : r ∈ p := by
    exact (IsLocalization.AtPrime.mk'_mem_maximal_iff
      (S := Localization.AtPrime p) (I := p) r s).mp hx
  have hsreg :
      IsSMulRegular (LocalizedModule.AtPrime p M)
        (algebraMap R (Localization.AtPrime p) (s : R)) :=
    (IsLocalization.map_units (Localization.AtPrime p) s).isSMulRegular _
  have hmap :
      IsSMulRegular (LocalizedModule.AtPrime p M)
        (algebraMap R (Localization.AtPrime p) r) := by
    -- Multiply the regular localized element by the unit coming from the denominator to recover
    -- the numerator in the localized ring.
    rw [← (IsLocalization.mk'_spec (M := p.primeCompl) (S := Localization.AtPrime p) r s)]
    exact hreg.mul hsreg
  refine ⟨r, hrp, ?_⟩
  exact (isSMulRegular_algebraMap_iff
    (A := Localization.AtPrime p) (M := LocalizedModule.AtPrime p M) (r := r)).mp hmap

/-- Lemma 10.65.3 (1): if `N` is flat over `R`, then every associated prime of some quotient
`N / pN` with `p ∈ Ass_R(M)` is an associated prime of `M ⊗[R] N` over `S`. In Lean this tensor
product is represented by the canonically `S`-linear model `N ⊗[R] M`. -/
-- Proof sketch: for `p ∈ associatedPrimesOfModule R M`, choose an injection `R ⧸ p ↪ M` and
-- tensor it with the flat `R`-module `N`. Identify `(R ⧸ p) ⊗[R] N` with `N / pN`, then apply
-- `associatedPrimes.subset_of_injective` over `S`.
theorem associatedPrimesOfModule_iUnion_primeQuotients_subset_tensorProduct [Module.Flat R N] :
    (⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M,
      associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p)) ⊆
      associatedPrimesOfModule S (N ⊗[R] M) := by
  intro q hq
  rcases Set.mem_iUnion.mp hq with ⟨p, hq⟩
  rcases Set.mem_iUnion.mp hq with ⟨hp, hq⟩
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hp
  rcases hp with ⟨_, m, hm⟩
  let φ₀ : R →ₗ[R] M := (LinearMap.lsmul R M).flip m
  have hker_le : p ≤ LinearMap.ker φ₀ := by
    intro r hr
    simpa [φ₀, hm, Ideal.mem_torsionOf_iff] using hr
  let φ : R ⧸ p →ₗ[R] M := p.liftQ φ₀ hker_le
  have hker_eq : LinearMap.ker φ₀ = p := by
    ext r
    simpa [φ₀, hm, Ideal.mem_torsionOf_iff]
  have hφ_injective : Function.Injective φ := by
    apply LinearMap.ker_eq_bot.mp
    simpa [φ] using Submodule.ker_liftQ_eq_bot' p φ₀ hker_eq.symm
  let φTensor : N ⊗[R] (R ⧸ p) →ₗ[S] N ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.lTensor S N φ
  have hφTensor_injective : Function.Injective φTensor := by
    simpa [φTensor] using
      Module.Flat.lTensor_preserves_injective_linearMap (M := N) φ hφ_injective
  have hqTensor :
      q ∈ associatedPrimesOfModule S (N ⊗[R] (R ⧸ p)) := by
    -- Rewrite the quotient module into the standard tensor presentation before tensoring the
    -- cyclic injection into `M`.
    simpa [LinearEquiv.associatedPrimesOfModule_eq (R := S)
      (M := relativeAssassinPrimeQuotient R S N p)
      (M' := N ⊗[R] (R ⧸ p))
      (relativeAssassinPrimeQuotient_tensorQuotient_linearEquiv
        (R := R) (S := S) (N := N) p)] using hq
-- Flatness keeps the cyclic inclusion injective after tensoring, so associated primes ascend.
  exact associatedPrimesOfModule.subset_of_injective
    (R := S) (f := φTensor) hφTensor_injective hqTensor

/-- Helper for Lemma 10.65.3: an injective linear map preserves the exact torsion ideal of a
chosen witness element. -/
private theorem torsionOf_map_eq_of_injective
    {A : Type*} [CommRing A] {X : Type*} [AddCommGroup X] [Module A X]
    {Y : Type*} [AddCommGroup Y] [Module A Y]
    {f : X →ₗ[A] Y} (hf : Function.Injective f) (x : X) :
    Ideal.torsionOf A Y (f x) = Ideal.torsionOf A X x := by
  -- Compare membership in the two annihilator ideals pointwise through injectivity of `f`.
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  constructor
  · intro ha
    apply hf
    simpa using ha
  · intro ha
    simpa using congrArg f ha

/-- Helper for Lemma 10.65.3: the union of prime-quotient contributions grows monotonically under
an injective map on the indexing `R`-module. -/
private theorem iUnion_primeQuotients_subset_of_injective
    {M' : Type*} [AddCommGroup M'] [Module R M']
    {f : M' →ₗ[R] M} (hf : Function.Injective f) :
    (⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M',
      associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p)) ⊆
      (⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M,
        associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p)) := by
  intro q hq
  rcases Set.mem_iUnion.mp hq with ⟨p, hq⟩
  rcases Set.mem_iUnion.mp hq with ⟨hp, hq⟩
  -- Only the indexing set changes: associated primes of the smaller module inject into those of
  -- the larger module.
  refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨?_, hq⟩⟩
  exact associatedPrimesOfModule.subset_of_injective hf hp

/-- Helper for Lemma 10.65.3: every associated-prime witness in `N ⊗[R] M` already comes from a
finite `R`-submodule of `M`. -/
private theorem associatedPrime_tensorProduct_exists_finite_submodule [Module.Flat R N]
    {q : Ideal S} (hq : q ∈ associatedPrimesOfModule S (N ⊗[R] M)) :
    ∃ (M' : Submodule R M) (_ : Module.Finite R M'),
      q ∈ associatedPrimesOfModule S (N ⊗[R] M') := by
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hq
  rcases hq with ⟨hqPrime, x, hx⟩
  obtain ⟨M', hM'finite, hx_range⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite
      (R := R) (M := N) (N := M) ({x} : Set (N ⊗[R] M)) (Set.toFinite _)
  let inclusionTensor : N ⊗[R] M' →ₗ[S] N ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.lTensor S N M'.subtype
  have hx_mem_range : x ∈ LinearMap.range inclusionTensor := by
    simpa [inclusionTensor] using hx_range (by simp)
  rcases hx_mem_range with ⟨x', rfl⟩
  refine ⟨M', hM'finite, ?_⟩
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf]
  have hsubtype_tensor_injective : Function.Injective inclusionTensor := by
    simpa [inclusionTensor] using
      Module.Flat.lTensor_preserves_injective_linearMap (M := N) M'.subtype
        (Submodule.injective_subtype M')
  -- Pull the associated-prime witness back along the injective tensor map from the finite
  -- submodule, preserving its exact torsion ideal.
  refine ⟨hqPrime, x', ?_⟩
  calc
    q = Ideal.torsionOf S (N ⊗[R] M) (inclusionTensor x') := by
      simpa [hx, inclusionTensor]
    _ = Ideal.torsionOf S (N ⊗[R] M') x' :=
      torsionOf_map_eq_of_injective (f := inclusionTensor) hsubtype_tensor_injective x'

/-- Helper for Lemma 10.65.3: tensoring the right-factor scalar-multiplication map is the same as
scalar multiplication on the tensor product. -/
private theorem localized_lTensor_lsmul_eq_lsmul
    (q : PrimeSpectrum S) (r : R) :
    (TensorProduct.AlgebraTensorModule.lTensor (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal N)
        (LinearMap.lsmul R (LocalizedModule.AtPrime (q.asIdeal.under R) M) r)).restrictScalars R =
      LinearMap.lsmul R
        (LocalizedModule.AtPrime q.asIdeal N ⊗[R]
          LocalizedModule.AtPrime (q.asIdeal.under R) M) r := by
  -- On pure tensors, moving the scalar to the right factor is exactly the tensor relation.
  ext x y
  simp [LinearMap.lsmul_apply, TensorProduct.smul_tmul', TensorProduct.tmul_smul]

/-- Helper for Lemma 10.65.3: in the finite Noetherian case, an associated prime of
`N ⊗[R] M` contracts to an associated prime of `M`. -/
private theorem under_mem_associatedPrimesOfModule_of_mem_tensorProduct_of_finite
    [Module.Flat R N] [IsNoetherianRing R] [Module.Finite R M]
    {q : Ideal S} [q.IsPrime]
    (hq : q ∈ associatedPrimesOfModule S (N ⊗[R] M)) :
    q.under R ∈ associatedPrimesOfModule R M := by
  let q' : PrimeSpectrum S := ⟨q, inferInstance⟩
  let p : Ideal R := q.under R
  letI : p.IsPrime := Ideal.IsPrime.under (A := R) q
  have hq_local :
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ∈
        associatedPrimesOfModule (Localization.AtPrime q)
          (LocalizedModule.AtPrime q (N ⊗[R] M)) :=
    maximalIdeal_mem_associatedPrimesOfModule_atPrime_of_mem
      (S := S) (X := N ⊗[R] M) hq
  by_contra hp_not
  have hp_local_not_text :
      IsLocalRing.maximalIdeal (Localization.AtPrime p) ∉
        associatedPrimesOfModule (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
    intro hp_local
    exact hp_not <|
      mem_associatedPrimesOfModule_of_maximalIdeal_mem_atPrime
        (R := R) (M := M) hp_local
  have hp_local_not :
      IsLocalRing.maximalIdeal (Localization.AtPrime p) ∉
        associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
    simpa [associatedPrimesOfModule_eq_associatedPrimes] using hp_local_not_text
  have hmax_not_le :
      ∀ J ∈ associatedPrimes (Localization.AtPrime p) (LocalizedModule.AtPrime p M),
        ¬ IsLocalRing.maximalIdeal (Localization.AtPrime p) ≤ J := by
    intro J hJ hle
    letI : J.IsPrime := hJ.1
    have hJ_le :
        J ≤ IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
      IsLocalRing.le_maximalIdeal_of_isPrime J
    exact hp_local_not (le_antisymm hJ_le hle ▸ hJ)
  obtain ⟨x, hxmax, hreg_x⟩ :=
    (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes
      (R := Localization.AtPrime p)
      (M := LocalizedModule.AtPrime p M)
      (I := IsLocalRing.maximalIdeal (Localization.AtPrime p))).2 hmax_not_le
  obtain ⟨r, hrp, hreg_r⟩ :=
    exists_mem_isSMulRegular_atPrime_numerator
      (R := R) (M := M) (p := p) hxmax hreg_x
  have hNq_flat :
      Module.Flat R (LocalizedModule.AtPrime q N) :=
    flat_localizedModule_of_flat (R := R) (A := S) (M := N) q.primeCompl inferInstance
  letI : Module.Flat R (LocalizedModule.AtPrime q N) := hNq_flat
  have hreg_tensor :
      IsSMulRegular
        (LocalizedModule.AtPrime q N ⊗[R] LocalizedModule.AtPrime p M) r := by
    have hTensor_inj :
        Function.Injective
          ((TensorProduct.AlgebraTensorModule.lTensor (Localization.AtPrime q)
              (LocalizedModule.AtPrime q N)
              (LinearMap.lsmul R (LocalizedModule.AtPrime p M) r)).restrictScalars R) := by
      simpa using
        Module.Flat.lTensor_preserves_injective_linearMap
          (M := LocalizedModule.AtPrime q N)
          (LinearMap.lsmul R (LocalizedModule.AtPrime p M) r) hreg_r
    rw [localized_lTensor_lsmul_eq_lsmul (R := R) (S := S) (M := M) (N := N) q' r] at hTensor_inj
    exact hTensor_inj
  have hreg_localized :
      IsSMulRegular (LocalizedModule.AtPrime q (N ⊗[R] M)) r := by
    -- Transport regularity from the explicit tensor-localized model to the actual localization.
    exact
      ((localized_tensorProduct_right_localized_linearEquiv
          (R := R) (S := S) (M := M) (N := N) q').isSMulRegular_congr r).1 hreg_tensor
  have hreg_localized_sq :
      IsSMulRegular (LocalizedModule.AtPrime q (N ⊗[R] M))
        (algebraMap R (Localization.AtPrime q) r) := by
    exact
      (isSMulRegular_algebraMap_iff
        (A := Localization.AtPrime q)
        (M := LocalizedModule.AtPrime q (N ⊗[R] M))).2 hreg_localized
  have hr_mem_max :
      algebraMap R (Localization.AtPrime q) r ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    -- Because `r ∈ q ∩ R`, its image lands in the maximal ideal of `S_q`.
    simpa [p, Ideal.under_def, IsScalarTower.algebraMap_eq R S (Localization.AtPrime q)] using
      (IsLocalization.AtPrime.to_map_mem_maximal_iff
        (Localization.AtPrime q) q (algebraMap R S r)).2 hrp
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hq_local
  rcases hq_local with ⟨hqmax_prime, z, hz⟩
  have hr_torsion :
      algebraMap R (Localization.AtPrime q) r ∈
        Ideal.torsionOf (Localization.AtPrime q) (LocalizedModule.AtPrime q (N ⊗[R] M)) z := by
    simpa [hz] using hr_mem_max
  have hsmul_zero :
      (algebraMap R (Localization.AtPrime q) r) • z = 0 := by
    simpa [Ideal.mem_torsionOf_iff] using hr_torsion
  have hz_zero : z = 0 := by
    apply hreg_localized_sq
    simpa using hsmul_zero
  have htop : IsLocalRing.maximalIdeal (Localization.AtPrime q) = ⊤ := by
    rw [hz, hz_zero, Ideal.torsionOf_zero]
  exact hqmax_prime.ne_top htop

/-- Helper for Lemma 10.65.3: tensoring a prime-cyclic filtration with a flat module preserves the
source proof's exact filtration argument, so every associated prime of the tensor of the last stage
comes from one prime-quotient factor. -/
private theorem associatedPrimesOfModule_tensorProduct_subset_primeFactorQuotients_of_filtration
    [Module.Flat R N] (s : PrimeCyclicFiltration R M) (hs₀ : s.head = ⊥) :
    associatedPrimesOfModule S (N ⊗[R] s.last) ⊆
      (⋃ p : PrimeSpectrum R, ⋃ _ : p ∈ PrimeCyclicFiltration.primeFactors (R := R) (M := M) s,
        associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p.asIdeal)) := by
  revert hs₀
  induction s using RelSeries.inductionOn' with
  | singleton K =>
      intro hs₀ q hq
      have hK : K = ⊥ := hs₀
      subst hK
      -- The initial stage is the zero module, so it has no associated primes.
      change q ∈ associatedPrimesOfModule S (N ⊗[R] (⊥ : Submodule R M)) at hq
      rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hq
      rcases hq with ⟨hqPrime, z, hz⟩
      letI : Subsingleton (N ⊗[R] (⊥ : Submodule R M)) := inferInstance
      have hz_zero : z = 0 := Subsingleton.elim _ _
      have htop : q = ⊤ := by
        rw [hz, hz_zero, Ideal.torsionOf_zero]
      exact (hqPrime.ne_top htop).elim
  | snoc s K hrel ih =>
      rcases hrel with ⟨hle, p, hp⟩
      intro hs₀ q hq
      let f : N ⊗[R] (s.last.submoduleOf K) →ₗ[S] N ⊗[R] K :=
        TensorProduct.AlgebraTensorModule.lTensor S N (s.last.submoduleOf K).subtype
      let g : N ⊗[R] K →ₗ[S] N ⊗[R] (K ⧸ s.last.submoduleOf K) :=
        TensorProduct.AlgebraTensorModule.lTensor S N ((s.last.submoduleOf K).mkQ)
      have hf : Function.Injective f := by
        -- Flatness keeps the inclusion of the previous stage injective after tensoring.
        simpa [f] using
          Module.Flat.lTensor_preserves_injective_linearMap (M := N)
            (s.last.submoduleOf K).subtype
            (Submodule.injective_subtype (s.last.submoduleOf K))
      have hfg : Function.Exact f g := by
        -- The tensorized snoc step is still the exact sequence
        -- `0 → N ⊗ s.last → N ⊗ K → N ⊗ (K / s.last)`.
        simpa [f, g] using
          (lTensor_exact N (LinearMap.exact_subtype_mkQ (s.last.submoduleOf K))
            (Submodule.mkQ_surjective (s.last.submoduleOf K)))
      have hsubset :
          associatedPrimesOfModule S (N ⊗[R] K) ⊆
            associatedPrimesOfModule S (N ⊗[R] (s.last.submoduleOf K)) ∪
              associatedPrimesOfModule S (N ⊗[R] (K ⧸ s.last.submoduleOf K)) :=
        associatedPrimesOfModule.subset_union_of_exact
          (R := S) (f := f) (g := g) hf hfg
      have hqK : q ∈ associatedPrimesOfModule S (N ⊗[R] K) := by
        rw [RelSeries.last_snoc] at hq
        exact hq
      rcases hsubset hqK with hq_prev | hq_last
      · -- Earlier prime factors persist after adjoining one more quotient step.
        have hq_prev_last : q ∈ associatedPrimesOfModule S (N ⊗[R] s.last) := by
          simpa [LinearEquiv.associatedPrimesOfModule_eq (R := S)
            (M := N ⊗[R] (s.last.submoduleOf K))
            (M' := N ⊗[R] s.last)
            (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S N)
              (Submodule.submoduleOfEquivOfLe hle))] using hq_prev
        rcases Set.mem_iUnion.mp (ih hs₀ hq_prev_last) with ⟨p', hp'⟩
        rcases Set.mem_iUnion.mp hp' with ⟨hp'factor, hq'⟩
        exact Set.mem_iUnion.mpr ⟨p', Set.mem_iUnion.mpr
          ⟨PrimeCyclicFiltration.primeFactors_subset_snoc (s := s) ⟨hle, p, hp⟩ hp'factor, hq'⟩⟩
      · rcases hp with ⟨e⟩
        have hq_tensor_quotient :
            q ∈ associatedPrimesOfModule S (N ⊗[R] (R ⧸ p.asIdeal)) := by
          -- Rewrite the last tensor quotient through the chosen prime-cyclic quotient isomorphism.
          simpa [LinearEquiv.associatedPrimesOfModule_eq (R := S)
            (M := N ⊗[R] (K ⧸ s.last.submoduleOf K))
            (M' := N ⊗[R] (R ⧸ p.asIdeal))
            (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S N) e)] using hq_last
        have hq_prime_quotient :
            q ∈ associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p.asIdeal) := by
          -- The source quotient branch is exactly the standard module `N / pN`.
          simpa [LinearEquiv.associatedPrimesOfModule_eq (R := S)
            (M := relativeAssassinPrimeQuotient R S N p.asIdeal)
            (M' := N ⊗[R] (R ⧸ p.asIdeal))
            (relativeAssassinPrimeQuotient_tensorQuotient_linearEquiv
              (R := R) (S := S) (N := N) p.asIdeal)] using hq_tensor_quotient
        exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr
          ⟨PrimeCyclicFiltration.mem_primeFactors_snoc_last (s := s) hle (show Nonempty
              ((↥K ⧸ s.last.submoduleOf K) ≃ₗ[R] R ⧸ p.asIdeal) from ⟨e⟩), hq_prime_quotient⟩⟩

/-- Helper for Lemma 10.65.3: the converse inclusion after reducing to a finite `R`-module. -/
private theorem associatedPrimesOfModule_tensorProduct_subset_iUnion_primeQuotients_of_isNoetherianRing_of_finite
    [Module.Flat R N] [IsNoetherianRing R] [Module.Finite R M] :
    associatedPrimesOfModule S (N ⊗[R] M) ⊆
      (⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M,
        associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p)) := by
  intro q hq
  letI : q.IsPrime := hq.1
  have hunder :
      q.under R ∈ associatedPrimesOfModule R M :=
    under_mem_associatedPrimesOfModule_of_mem_tensorProduct_of_finite
      (R := R) (S := S) (M := M) (N := N) hq
  obtain ⟨s, hs₀, hs_top⟩ :=
    IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime (A := R) (M := M)
  let eTop : s.last ≃ₗ[R] M :=
    (LinearEquiv.ofEq _ _ hs_top).trans Submodule.topEquiv
  have hq_last : q ∈ associatedPrimesOfModule S (N ⊗[R] s.last) := by
    -- Route correction: instead of forcing the final `iUnion` directly, first move the witness to
    -- the last stage of a prime-cyclic filtration and then isolate one quotient branch.
    simpa [LinearEquiv.associatedPrimesOfModule_eq (R := S)
      (M := N ⊗[R] s.last)
      (M' := N ⊗[R] M)
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S N) eTop)] using hq
  rcases Set.mem_iUnion.mp
      (associatedPrimesOfModule_tensorProduct_subset_primeFactorQuotients_of_filtration
        (R := R) (S := S) (M := M) (N := N) s hs₀ hq_last) with ⟨p, hp⟩
  rcases Set.mem_iUnion.mp hp with ⟨hp_factor, hq_branch⟩
  have hq_tensor_quotient :
      q ∈ associatedPrimesOfModule S (N ⊗[R] (R ⧸ p.asIdeal)) := by
    simpa [LinearEquiv.associatedPrimesOfModule_eq (R := S)
      (M := relativeAssassinPrimeQuotient R S N p.asIdeal)
      (M' := N ⊗[R] (R ⧸ p.asIdeal))
      (relativeAssassinPrimeQuotient_tensorQuotient_linearEquiv
        (R := R) (S := S) (N := N) p.asIdeal)] using hq_branch
  have hunder_branch :
      q.under R ∈ associatedPrimesOfModule R (R ⧸ p.asIdeal) :=
    under_mem_associatedPrimesOfModule_of_mem_tensorProduct_of_finite
      (R := R) (S := S) (M := R ⧸ p.asIdeal) (N := N) hq_tensor_quotient
  have hunder_eq : q.under R = p.asIdeal := by
    rw [associatedPrimesOfModule_quotient_prime_eq_singleton (R := R) p, Set.mem_singleton_iff] at hunder_branch
    exact hunder_branch
  -- The chosen branch must therefore be the quotient indexed by the contracted associated prime.
  exact Set.mem_iUnion.mpr ⟨q.under R, Set.mem_iUnion.mpr ⟨hunder, by
    exact hunder_eq.symm ▸ hq_branch⟩⟩

/-- Lemma 10.65.3 (2): if `R` is Noetherian and `N` is flat over `R`, then the associated primes
of `M ⊗[R] N` over `S` are exactly the associated primes of the quotients `N / pN` for
`p ∈ Ass_R(M)`. In Lean the tensor product is written in the canonically `S`-linear order
`N ⊗[R] M`. -/
-- Proof sketch: the previous theorem gives the inclusion from right to left. For the converse,
-- reduce to the finitely generated case by writing `M` as a directed union of finite submodules.
-- For finite `M`, choose a prime-quotient filtration and tensor it with `N`; flatness preserves
-- exactness, and `associatedPrimes.subset_union_of_exact` reduces an associated prime of
-- `M ⊗[R] N` to one of the subquotients `N / pN`.
theorem associatedPrimesOfModule_tensorProduct_eq_iUnion_primeQuotients_of_isNoetherianRing
    [Module.Flat R N] [IsNoetherianRing R] :
    associatedPrimesOfModule S (N ⊗[R] M) =
      (⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M,
        associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p)) := by
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨M', hM'finite, hq'⟩ :=
      associatedPrime_tensorProduct_exists_finite_submodule
        (R := R) (S := S) (M := M) (N := N) hq
    have hq_finite :
        q ∈ ⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M',
          associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) :=
      associatedPrimesOfModule_tensorProduct_subset_iUnion_primeQuotients_of_isNoetherianRing_of_finite
        (R := R) (S := S) (M := M') (N := N) hq'
    -- Reduce the arbitrary-module case to the finite submodule carrying the chosen witness, then
    -- enlarge the indexing union along the inclusion `M' ↪ M`.
    exact iUnion_primeQuotients_subset_of_injective
      (R := R) (S := S) (M := M) (N := N)
      (f := M'.subtype) (Submodule.injective_subtype M') hq_finite
  · -- The easy inclusion is exactly the flat-base-change injection proved above.
    exact associatedPrimesOfModule_iUnion_primeQuotients_subset_tensorProduct
      (R := R) (S := S) (M := M) (N := N)

end

/-! ### Lemma_10_65_4 (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped TensorProduct nonZeroDivisors

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

local notation "R⁰" => nonZeroDivisors R
local notation "K" => FractionRing R
local notation "T" => Algebra.algebraMapSubmonoid S R⁰
local notation "Sₖ" => Localization T
local notation "Nₖ" => LocalizedModule T N

local instance instIsNoetherianRingBaseChange [IsNoetherianRing S] : IsNoetherianRing Sₖ :=
  IsLocalization.isNoetherianRing T Sₖ inferInstance

/- Domain triage:
- primary domain: commutative algebra of associated primes under localization/base change;
- `source-facing`: the exact-annihilator set `associatedPrimesOfModule`;
- `core/canonical`: the localization owner `LocalizedModule T N` together with mathlib's
  Noetherian owner set `associatedPrimes`;
- `bridge/view`: the tensor-base-change realization `(S ⊗[R] K) ⊗[S] N` and the textbook tensor
  model `N ⊗[R] K`.

In this file, `Nₖ` is the localization owner itself, so the public equalities reuse Lemmas
`10.63.16` and `10.63.17` directly. The only remaining private bridge passes from that owner to
the tensor-base-change and textbook tensor presentations.
-/

private noncomputable def localizedModuleFractionRingBaseChangeEquiv :
    Nₖ ≃ₗ[S] (S ⊗[R] K) ⊗[S] N :=
  IsLocalizedModule.iso T (TensorProduct.mk S (S ⊗[R] K) N 1)

private noncomputable def fractionRingTensorLinearEquiv : Nₖ ≃ₗ[S] N ⊗[R] K :=
  localizedModuleFractionRingBaseChangeEquiv ≪≫ₗ TensorProduct.comm S (S ⊗[R] K) N ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N K

/-- Lemma 10.65.4, first equality in canonical owner form: for an `S`-module `N` that is flat
over `R`, the associated primes of `N` over `S` agree with those of the canonical localization
owner `Nₖ = LocalizedModule T N`. -/
-- Proof sketch: this is the `R⁰` specialization of Lemma `10.63.17`, applied to the image of
-- `R⁰` in `S`; flatness over `R` says exactly that every nonzero element of `R` acts regularly on
-- `N`.
theorem associatedPrimesOfModule_eq_fractionRingBaseChange_as_SModule [Module.Flat R N] :
    associatedPrimesOfModule S N = associatedPrimesOfModule S Nₖ := by
  refine associatedPrimesOfModule_eq_associatedPrimesOfModule_localizedModule T ?_
  intro s
  rcases s.2 with ⟨r, hr, hs⟩
  simpa [hs] using
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hr).map
      (algebraMap R S) fun m ↦ by simp

/- The textbook tensor model `N ⊗[R] K` and the canonical localization owner `Nₖ` are the same
`S`-module up to the standard fraction-ring base-change equivalence, so they have the same textbook associated
primes over `S`. -/
theorem associatedPrimesOfModule_baseChange_to_fractionRing_eq_canonicalBaseChange :
    associatedPrimesOfModule S (N ⊗[R] K) =
      associatedPrimesOfModule S Nₖ := by
  let e : Nₖ ≃ₗ[S] N ⊗[R] K := fractionRingTensorLinearEquiv
  exact
    (show associatedPrimesOfModule S (N ⊗[R] K) = associatedPrimesOfModule S Nₖ from
      (LinearEquiv.associatedPrimesOfModule_eq S Nₖ e).symm)

/-- Textbook tensor-model reformulation of the first equality of Lemma 10.65.4. -/
-- Proof sketch: first apply the canonical owner-level equality
-- `associatedPrimesOfModule_eq_fractionRingBaseChange_as_SModule`, then rewrite along the standard
-- tensor equivalence
-- `associatedPrimesOfModule_baseChange_to_fractionRing_eq_canonicalBaseChange`.
theorem associatedPrimesOfModule_eq_associatedPrimesOfModule_baseChange_to_fractionRing
    [Module.Flat R N] :
    associatedPrimesOfModule S N =
      associatedPrimesOfModule S (N ⊗[R] K) := by
  calc
    associatedPrimesOfModule S N = associatedPrimesOfModule S Nₖ :=
      associatedPrimesOfModule_eq_fractionRingBaseChange_as_SModule
    _ = associatedPrimesOfModule S (N ⊗[R] K) :=
      associatedPrimesOfModule_baseChange_to_fractionRing_eq_canonicalBaseChange.symm

/-- Noetherian specialization of the canonical owner form of the first equality of Lemma 10.65.4
in mathlib's `associatedPrimes` API. -/
theorem associatedPrimes_eq_fractionRingBaseChange_as_SModule
    [Module.Flat R N] [IsNoetherianRing S] :
    associatedPrimes S N = associatedPrimes S Nₖ := by
  rw [← associatedPrimesOfModule_eq_associatedPrimes S N,
    ← associatedPrimesOfModule_eq_associatedPrimes S Nₖ]
  exact associatedPrimesOfModule_eq_fractionRingBaseChange_as_SModule

/-- Noetherian specialization of the textbook tensor-model reformulation of the first equality of
Lemma 10.65.4 in mathlib's `associatedPrimes` API. -/
theorem associatedPrimes_eq_associatedPrimes_baseChange_to_fractionRing
    [Module.Flat R N] [IsNoetherianRing S] :
    associatedPrimes S N =
      associatedPrimes S (N ⊗[R] K) := by
  calc
    associatedPrimes S N = associatedPrimes S Nₖ :=
      associatedPrimes_eq_fractionRingBaseChange_as_SModule
    _ = associatedPrimes S (N ⊗[R] K) := by
      let e : Nₖ ≃ₗ[S] N ⊗[R] K := fractionRingTensorLinearEquiv
      simpa using LinearEquiv.AssociatedPrimes.eq e

/-
Lemma 10.65.4, second equality: the associated primes of the canonical base-change
`Nₖ` over `S` are exactly the contractions of its associated primes over `Sₖ`.
-/
-- Proof sketch: apply the textbook contraction statement for associated primes under restriction
-- of scalars along `S → Sₖ` to the localization owner from Lemma `10.63.16`.
omit [Module R N] [IsScalarTower R S N] in
theorem associatedPrimesOfModule_baseChange_to_fractionRing_eq_image_comap :
    associatedPrimesOfModule S Nₖ =
      Ideal.comap (algebraMap S Sₖ) '' associatedPrimesOfModule Sₖ Nₖ := by
  simpa using
    (associatedPrimesOfModule_localizedModule_eq_image_comap T).symm

/-- Rewriting the second equality of Lemma 10.65.4 through the standard identification of the
textbook tensor model with the canonical base-change model. -/
theorem associatedPrimesOfModule_baseChange_to_fractionRing_textbook_eq_image_comap :
    associatedPrimesOfModule S (N ⊗[R] K) =
      Ideal.comap (algebraMap S Sₖ) '' associatedPrimesOfModule Sₖ Nₖ := by
  rw [associatedPrimesOfModule_baseChange_to_fractionRing_eq_canonicalBaseChange]
  exact associatedPrimesOfModule_baseChange_to_fractionRing_eq_image_comap

/- Noetherian specialization of the textbook formulation of the second equality of
Lemma 10.65.4, obtained from the canonical base-change statement via the standard `S`-linear
identification of the two tensor models. -/
theorem associatedPrimes_baseChange_to_fractionRing_textbook_eq_image_comap
    [IsNoetherianRing S] :
    associatedPrimes S (N ⊗[R] K) =
      Ideal.comap (algebraMap S Sₖ) '' associatedPrimes Sₖ Nₖ := by
  let _ : IsNoetherianRing Sₖ := inferInstance
  simpa [associatedPrimesOfModule_eq_associatedPrimes] using
    (associatedPrimesOfModule_baseChange_to_fractionRing_textbook_eq_image_comap :
      associatedPrimesOfModule S (N ⊗[R] K) =
        Ideal.comap (algebraMap S Sₖ) '' associatedPrimesOfModule Sₖ Nₖ)

end

/-! ### Lemma_10_65_5 (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/- Domain triage:
* primary domain: associated primes under flat base change along `R → S`;
* source-facing layer: the chapter owner `relativeAssassin R S N` together with the textbook
  exact-annihilator set `associatedPrimesOfModule`;
* core/canonical layer: mathlib's Noetherian owner `associatedPrimes`;
* bridge/view: the contraction description of the fiberwise union coming from Lemma 10.65.1 and
  Remark 10.18.5.

This item stays at the source-facing layer. The Noetherian equality is stated for
`associatedPrimesOfModule`, and any owner-form restatement via `associatedPrimes` belongs in a
later bridge file.
-/

/-- Helper for Lemma 10.65.5: reducing `N` modulo `pS` agrees with tensoring `N` by the prime
quotient `R ⧸ p`, viewed as an `S`-module. -/
noncomputable def relativeAssassinPrimeQuotientTensorQuotientLinearEquiv (p : Ideal R) :
    relativeAssassinPrimeQuotient R S N p ≃ₗ[S] N ⊗[R] (R ⧸ p) :=
  (TensorProduct.quotTensorEquivQuotSMul N (p.map (algebraMap R S))).symm.trans <|
    (TensorProduct.congr (Ideal.qoutMapEquivTensorQout (R := R) (S := S) (I := p))
      (LinearEquiv.refl S N)).trans <|
    (TensorProduct.comm S _ N).trans <|
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N (R ⧸ p)

/-- Helper for Lemma 10.65.5: for a flat `R`-module `N`, any associated prime of the prime
quotient module `N / pN` contracts back to the fixed prime `p`. -/
theorem under_eq_of_mem_associated_primes_relative_assassin_prime_quotient_of_flat
    [Module.Flat R N] {p : PrimeSpectrum R} {q : PrimeSpectrum S}
    (hq : q.asIdeal ∈ associatedPrimesOfModule S
      (relativeAssassinPrimeQuotient R S N p.asIdeal)) :
    q.asIdeal.under R = p.asIdeal := by
  let I : Ideal S := p.asIdeal.map (algebraMap R S)
  -- Read the associated-prime witness through the quotient model `N / pN`.
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hq
  rcases hq with ⟨hqPrime, m, hm⟩
  have hp_le : p.asIdeal ≤ q.asIdeal.under R := by
    have hqbar_mem :
        q.asIdeal ∈ Ideal.comap (Ideal.Quotient.mk I) ''
          associatedPrimesOfModule (S ⧸ I)
            (relativeAssassinPrimeQuotient R S N p.asIdeal) := by
      -- The quotient presentation forces every associated prime of `N / pN` to contain `pS`.
      rw [associatedPrimesOfModule_quotient_image_comap_eq
        (R := S) (I := I) (M := relativeAssassinPrimeQuotient R S N p.asIdeal)]
      exact ⟨hqPrime, m, hm⟩
    rcases hqbar_mem with ⟨qbar, hqbar, hcomap⟩
    intro r hr
    rw [Ideal.under_def, Ideal.mem_comap]
    rw [← hcomap, Ideal.mem_comap]
    have hzero : Ideal.Quotient.mk I (algebraMap R S r) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    have hzero_mem : (0 : S ⧸ I) ∈ qbar := by
      simp
    simpa [hzero] using hzero_mem
  have hunder_le : q.asIdeal.under R ≤ p.asIdeal := by
    intro r hr
    by_contra hr_not_mem
    have hrbar_ne_zero : (Ideal.Quotient.mk p.asIdeal r : R ⧸ p.asIdeal) ≠ 0 := by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hr_not_mem
    have hrbar_nz :
        (Ideal.Quotient.mk p.asIdeal r : R ⧸ p.asIdeal) ∈ nonZeroDivisors (R ⧸ p.asIdeal) :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hrbar_ne_zero
    let _ : Module.Flat (R ⧸ p.asIdeal) ((R ⧸ p.asIdeal) ⊗[R] N) :=
      Module.Flat.baseChange (R := R) (S := R ⧸ p.asIdeal) (M := N)
    have hreg_left_bar :
        IsSMulRegular
          ((R ⧸ p.asIdeal) ⊗[R] N) (Ideal.Quotient.mk p.asIdeal r : R ⧸ p.asIdeal) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors hrbar_nz
    have hreg_left :
        IsSMulRegular ((R ⧸ p.asIdeal) ⊗[R] N) r :=
      hreg_left_bar.of_map (Ideal.Quotient.mk p.asIdeal) fun _ ↦ rfl
    have hreg_tensor :
        IsSMulRegular (N ⊗[R] (R ⧸ p.asIdeal)) r := by
      -- Move to the tensor model that exposes the `R ⧸ p`-regularity directly.
      exact ((TensorProduct.comm R (R ⧸ p.asIdeal) N).isSMulRegular_congr r).1 hreg_left
    have hreg_quot :
        IsSMulRegular (relativeAssassinPrimeQuotient R S N p.asIdeal) r := by
      -- Route correction: read regularity on `N / pN` through the quotient-tensor comparison
      -- before applying the associated-prime witness.
      exact
        ((LinearEquiv.restrictScalars R
          (relativeAssassinPrimeQuotientTensorQuotientLinearEquiv
            (R := R) (S := S) (N := N) p.asIdeal)).isSMulRegular_congr r).2 hreg_tensor
    have hr_torsion :
        algebraMap R S r ∈ Ideal.torsionOf S
          (relativeAssassinPrimeQuotient R S N p.asIdeal) m := by
      simpa [Ideal.under_def, hm] using hr
    have hsmul_zero : (algebraMap R S r) • m = 0 := by
      simpa [Ideal.mem_torsionOf_iff] using hr_torsion
    have hm_zero : m = 0 := hreg_quot <| by
      simpa using hsmul_zero
    have htop : q.asIdeal = ⊤ := by
      rw [hm, hm_zero, Ideal.torsionOf_zero]
    exact hqPrime.ne_top htop
  exact le_antisymm hunder_le hp_le

-- Proof sketch: rewrite the fiberwise union from the source as
-- `relativeAssassin R S N ∩ {q | q.asIdeal.under R ∈ associatedPrimesOfModule R M}` using
-- Lemma 10.65.1 together with the fiber-spectrum identification from Remark 10.18.5, then apply
-- Lemma 10.65.3(1) to the contracted prime quotient modules `N / pN`.
/-- Lemma 10.65.5 (1): if `N` is flat over `R`, then every associated prime of a fiber module
`κ(𝔭) ⊗[R] N`, viewed as a prime of `S` by the canonical map
`Spec (κ(𝔭) ⊗[R] S) → Spec S`, for `𝔭 ∈ Ass_R(M)`, is an associated prime of the base-changed
module `M ⊗[R] N`. In Lean the canonically `S`-linear tensor model is written `N ⊗[R] M`. -/
theorem fiberAssociatedPrimes_subset_associatedPrimesOfModule_tensorProduct
    [Module.Flat R N] :
    relativeAssassin R S N ∩
        { q : PrimeSpectrum S | q.asIdeal.under R ∈ associatedPrimesOfModule R M } ⊆
      { q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M) } := by
  intro q hq
  rcases hq with ⟨hqA, hqM⟩
  -- Rewrite the fiberwise condition through the fixed contracted-prime quotient from Lemma 10.65.1.
  have hqAfin : q ∈ relativeAssassinAfin R S N := by
    rw [← relativeAssassinA_eq_relativeAssassinAfin_of_flat (R := R) (S := S) (N := N)]
    exact hqA
  have hqQuot :
      q.asIdeal ∈ associatedPrimesOfModule S
        (relativeAssassinPrimeQuotient R S N (q.asIdeal.under R)) := by
    simpa using hqAfin
  -- Insert the contracted prime `q ∩ R` into the union from Lemma 10.65.3(1).
  have hqUnion :
      q.asIdeal ∈ ⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M,
        associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) := by
    exact Set.mem_iUnion.mpr ⟨q.asIdeal.under R, Set.mem_iUnion.mpr ⟨hqM, hqQuot⟩⟩
  exact
    associatedPrimesOfModule_iUnion_primeQuotients_subset_tensorProduct
      (R := R) (S := S) (M := M) (N := N) hqUnion

-- Proof sketch: combine the source-facing inclusion above with the Noetherian converse furnished
-- by Lemma 10.65.3(2), again rewriting the fiberwise union through the contraction description
-- from Lemma 10.65.1 and Remark 10.18.5.
/-- Lemma 10.65.5 (2): if `R` is Noetherian and `N` is flat over `R`, then the associated primes
of `M ⊗[R] N` over `S` are exactly the fiberwise associated primes over those
`𝔭 ∈ Ass_R(M)`, viewed inside `Spec S` by the canonical maps from the fiber spectra. In Lean this
is expressed by equality with
`relativeAssassin R S N ∩ { q | q.asIdeal.under R ∈ associatedPrimesOfModule R M }`. -/
theorem associatedPrimesOfModule_tensorProduct_eq_fiberAssociatedPrimes_of_isNoetherianRing
    [Module.Flat R N] [IsNoetherianRing R] :
    { q : PrimeSpectrum S | q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] M) } =
      relativeAssassin R S N ∩
        { q : PrimeSpectrum S | q.asIdeal.under R ∈ associatedPrimesOfModule R M } := by
  ext q
  constructor
  · intro hq
    -- Expand the Noetherian equality from Lemma 10.65.3(2) to recover a prime-quotient witness.
    have hqUnion :
        q.asIdeal ∈ ⋃ p : Ideal R, ⋃ _ : p ∈ associatedPrimesOfModule R M,
          associatedPrimesOfModule S (relativeAssassinPrimeQuotient R S N p) := by
      rw [← associatedPrimesOfModule_tensorProduct_eq_iUnion_primeQuotients_of_isNoetherianRing
        (R := R) (S := S) (M := M) (N := N)]
      exact hq
    rcases Set.mem_iUnion.mp hqUnion with ⟨p, hqUnion⟩
    rcases Set.mem_iUnion.mp hqUnion with ⟨hp_assoc, hqQuot⟩
    have hp_assoc' : p ∈ associatedPrimesOfModule R M := hp_assoc
    have hp_prime : p.IsPrime := by
      rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hp_assoc
      exact hp_assoc.1
    let pSpec : PrimeSpectrum R := ⟨p, hp_prime⟩
    -- Force the branch index to be the contraction `q ∩ R`.
    have hunder :
        q.asIdeal.under R = pSpec.asIdeal := by
      exact under_eq_of_mem_associated_primes_relative_assassin_prime_quotient_of_flat
        (R := R) (S := S) (N := N) (p := pSpec) (q := q) hqQuot
    -- Rewrite the same witness back into the defining condition for `relativeAssassin`.
    have hqAfin : q ∈ relativeAssassinAfin R S N := by
      rw [mem_relativeAssassinAfin_iff, hunder]
      simpa [pSpec] using hqQuot
    have hqA : q ∈ relativeAssassin R S N := by
      rw [relativeAssassinA_eq_relativeAssassinAfin_of_flat (R := R) (S := S) (N := N)]
      exact hqAfin
    refine ⟨hqA, ?_⟩
    simpa [Set.mem_setOf_eq, pSpec] using (hunder.symm ▸ hp_assoc')
  · intro hq
    exact
      fiberAssociatedPrimes_subset_associatedPrimesOfModule_tensorProduct
        (R := R) (S := S) (M := M) (N := N) hq

end

/-! ### Remark_10_65_6 (from Chap10) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open Ideal.Quotient (eq_zero_iff_mem)
open scoped TensorProduct nonZeroDivisors

universe u v w

section

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime]
variable [AddCommGroup N] [Module S N]

local notation "Sbar" => S ⧸ p.map (algebraMap R S)
local notation "Rbar" => R ⧸ p
local notation "Rbar⁰" => nonZeroDivisors Rbar
local notation "T" => Algebra.algebraMapSubmonoid Sbar Rbar⁰
local notation "Nfiber" => (p.Fiber S) ⊗[S] N

-- Elements of `pS` vanish in `κ(p) ⊗[R] S`.
private lemma algebraMap_fiber_eq_zero_of_mem_map {x : S} (hx : x ∈ p.map (algebraMap R S)) :
    algebraMap S (p.Fiber S) x = 0 := by
  let φ : (R ⧸ p) ⊗[R] S →+* p.Fiber S :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField)
      (AlgHom.id R S)).toRingHom
  have hquot :
      (Ideal.Quotient.mk (p.map (algebraMap R S)) x : S ⧸ p.map (algebraMap R S)) = 0 :=
    eq_zero_iff_mem.mpr hx
  have htmul : (1 : R ⧸ p) ⊗ₜ[R] x = 0 := by
    let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p
    have : e (Ideal.Quotient.mk (p.map (algebraMap R S)) x) = (1 : R ⧸ p) ⊗ₜ[R] x := rfl
    rw [← this, hquot]
    simp [e]
  have hφ : φ ((1 : R ⧸ p) ⊗ₜ[R] x) = 0 := by
    rw [htmul, map_zero]
  simpa [φ] using hφ

private noncomputable instance :
    Algebra Sbar (p.Fiber S) :=
  (Ideal.Quotient.liftₐ (p.map (algebraMap R S)) (Algebra.ofId S (p.Fiber S))
    fun _ hx ↦ algebraMap_fiber_eq_zero_of_mem_map p hx).toRingHom.toAlgebra

/-- Helper for Remark 10.65.6: the underlying ring equivalence from the quotient-base-changed
fiber presentation to the standard fiber ring. -/
private noncomputable def fiber_tensor_over_quotient_ring_equiv :
    Sbar ⊗[Rbar] p.ResidueField ≃+* p.Fiber S :=
  (Algebra.TensorProduct.commRight Rbar Sbar p.ResidueField).toRingEquiv.trans
    ((Algebra.TensorProduct.congr
        (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField] p.ResidueField)
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p)).trans
      (Algebra.TensorProduct.cancelBaseChange R Rbar p.ResidueField p.ResidueField S)).toRingEquiv

/-- Helper for Remark 10.65.6: the quotient generator `s mod pS` maps to the pure tensor
`1 ⊗ s`, so the ring bridge respects the `S / pS`-algebra structures. -/
private theorem algebraMap_quotient_to_fiber_mk (s : S) :
    algebraMap Sbar (p.Fiber S) (Ideal.Quotient.mk (p.map (algebraMap R S)) s) = 1 ⊗ₜ[R] s :=
  rfl

/-- Helper for Remark 10.65.6: the quotient generator `s mod pS` maps to the pure tensor
`1 ⊗ s`, so the ring bridge respects the `S / pS`-algebra structures. -/
private theorem fiber_tensor_over_quotient_ring_equiv_commutes (x : Sbar) :
    fiber_tensor_over_quotient_ring_equiv (R := R) (S := S) (p := p)
      (algebraMap Sbar (Sbar ⊗[Rbar] p.ResidueField) x) =
    algebraMap Sbar (p.Fiber S) x := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa [fiber_tensor_over_quotient_ring_equiv, algebraMap_quotient_to_fiber_mk,
    Algebra.TensorProduct.cancelBaseChange_tmul]

/-- Helper for Remark 10.65.6: the quotient presentation `S / pS` tensored with `κ(p)` over
`R / p` recovers the fiber ring `κ(p) ⊗[R] S` as an `S / pS`-algebra. -/
private noncomputable def fiber_tensor_over_quotient_alg_equiv :
    Sbar ⊗[Rbar] p.ResidueField ≃ₐ[Sbar] p.Fiber S :=
  { toRingEquiv := fiber_tensor_over_quotient_ring_equiv (R := R) (S := S) (p := p)
    commutes' := fiber_tensor_over_quotient_ring_equiv_commutes
      (R := R) (S := S) (p := p) }

/-- Helper for Remark 10.65.6: the fiber ring is the localization of `S / pS` at the image of
the nonzerodivisors of `R / p`. -/
private noncomputable def fiber_quotient_localization_alg_equiv :
    Localization T ≃ₐ[Sbar] p.Fiber S :=
  ((Localization.tensorLeftAlgEquiv Rbar⁰ Sbar).symm.trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : Sbar ≃ₐ[Sbar] Sbar)
        (IsLocalization.algEquiv Rbar⁰ (Localization Rbar⁰) p.ResidueField))).trans
    (fiber_tensor_over_quotient_alg_equiv (R := R) (S := S) (p := p))

/-- Helper for Remark 10.65.6: after viewing the fiber ring as a localization of `S / pS`, the
associated primes of the fiber module over `S / pS` are exactly the contractions of its associated
primes over the fiber ring. -/
private theorem associatedPrimesOfModule_over_quotient_eq_image_comap_over_fiber :
    Ideal.comap (algebraMap Sbar (p.Fiber S)) '' associatedPrimesOfModule (p.Fiber S) Nfiber =
      associatedPrimesOfModule Sbar Nfiber := by
  letI : IsLocalization T (Localization T) := Localization.isLocalization (M := T)
  letI : IsLocalization T (p.Fiber S) :=
    IsLocalization.isLocalization_of_algEquiv T
      (fiber_quotient_localization_alg_equiv (p := p))
  -- Route correction: once the fiber ring is recognized as a localization of `S / pS`, the
  -- reverse inclusion is the same annihilator-localization argument as in Lemma 10.63.16 (1).
  refine Set.Subset.antisymm associatedPrimesOfModule_image_comap_subset ?_
  intro p0 hp0
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hp0
  rcases hp0 with ⟨hp0, m, hm⟩
  let q : Ideal (p.Fiber S) := Ideal.torsionOf (p.Fiber S) Nfiber m
  have hcomap : Ideal.comap (algebraMap Sbar (p.Fiber S)) q = p0 := by
    ext x
    rw [hm, Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
    simp [algebraMap_smul]
  have hq_ne_top : q ≠ ⊤ := by
    intro hq_top
    apply hp0.ne_top
    simpa [hq_top] using hcomap.symm
  have hq : q.IsPrime := by
    refine (IsLocalization.isPrime_iff_isPrime_disjoint T (p.Fiber S) q).2 ?_
    refine ⟨by simpa [hcomap] using hp0, ?_⟩
    simpa [hcomap] using
      (IsLocalization.disjoint_comap_iff T (p.Fiber S) q).2 hq_ne_top
  refine ⟨q, ?_, hcomap⟩
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf]
  exact ⟨hq, m, rfl⟩

/- Domain triage:
* `source-facing`: the two equalities in Remark 10.65.6 for associated primes of the fiber module.
* `core/canonical`: the owner theorem
  `associatedPrimesOfModule_quotient_image_comap_eq` for contraction along a quotient map.
* `bridge/view`: the local `Sbar`-algebra structure on `p.Fiber S`, used only to state the
  source-facing fiber comparison for the canonical tensor model `Nfiber`.
-/

/- Remark 10.65.6, first equality: for the canonical fiber module modeling
`N ⊗_R κ(p)`, the comparison between associated primes over `S` and over `S ⧸ pS` is exactly the
specialization of the owner theorem
`associatedPrimesOfModule_quotient_image_comap_eq` to the ideal `pS = p.map (algebraMap R S)` and
the `S`-module `Nfiber`. -/
#check
  (associatedPrimesOfModule_quotient_image_comap_eq (p.map (algebraMap R S)) :
    Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap R S))) ''
        associatedPrimesOfModule Sbar Nfiber =
      associatedPrimesOfModule S Nfiber)

/-- Remark 10.65.6, second equality: for the same fiber module, the textbook associated primes
over `S ⧸ pS` agree with those over the fiber ring `κ(p) ⊗[R] S` after transporting them back to
ideals of `S`. -/
theorem associatedPrimesOfModule_fiberTensor_over_quotient_eq_over_fiber :
    Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap R S))) ''
        associatedPrimesOfModule Sbar Nfiber =
      Ideal.comap (algebraMap S (p.Fiber S)) ''
        associatedPrimesOfModule (p.Fiber S) Nfiber := by
  -- First rewrite the `S / pS`-level associated primes through the localization comparison.
  rw [← associatedPrimesOfModule_over_quotient_eq_image_comap_over_fiber
    (R := R) (S := S) (N := N) (p := p)]
  -- Then contract once more along `S → S / pS`, which composes to the original map `S → κ(p) ⊗ S`.
  ext I
  constructor
  · rintro ⟨K, ⟨J, hJ, rfl⟩, hKI⟩
    refine ⟨J, hJ, ?_⟩
    simpa [Ideal.comap_comap] using hKI
  · rintro ⟨J, hJ, hJmap⟩
    refine ⟨Ideal.comap (algebraMap Sbar (p.Fiber S)) J, ⟨J, hJ, rfl⟩, ?_⟩
    simpa using hJmap

end
