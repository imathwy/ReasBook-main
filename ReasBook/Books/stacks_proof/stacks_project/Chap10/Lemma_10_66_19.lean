import Mathlib
import StacksProject_2024.Chap10.Lemma_10_25_1
import StacksProject_2024.Chap10.Definition_10_66_1
import StacksProject_2024.Chap10.Lemma_10_40_4
import StacksProject_2024.Chap10.Lemma_10_42_3
import StacksProject_2024.Chap10.Lemma_10_43_6
import StacksProject_2024.Chap10.Lemma_10_66_2
import StacksProject_2024.Chap10.Lemma_10_66_13
import StacksProject_2024.Chap10.Lemma_10_66_4
import StacksProject_2024.Chap10.Lemma_10_66_15
import StacksProject_2024.Chap10.Lemma_10_66_16
import StacksProject_2024.Chap10.Lemma_10_66_19.Index

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe u v w x

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {R : Type w} [CommRing R] [Algebra k R]
variable {M : Type x} [AddCommGroup M] [Module R M]

local notation "Rₖ" => R ⊗[k] K
local notation "Mₖ" => Rₖ ⊗[R] M

/- Domain triage:
- primary domain: weakly associated primes under field extension/base change;
- `core/canonical`: the owner module `Mₖ = (R ⊗[k] K) ⊗[R] M`;
- `bridge/view`: the textbook tensor model `M ⊗[k] K`, compared to `Mₖ` through the standard
  base-change equivalence.

Primitive data are only the owner module `Mₖ` and the chapter owner set `weaklyAssociatedPrimes`.
The textbook tensor presentation is derived API, so the file keeps the owner theorem at the weaker
owner-module layer and adds the textbook comparison only in a stronger bridge section. -/
local instance : Module Rₖ Mₖ :=
  TensorProduct.leftModule

/-- Helper for Chap10 Lemma 10 66 19: the intermediate-field owner base-change source,
named to keep restricted-scalar instance search out of the main equivalence term. -/
private abbrev intermediateOwnerBaseChangeSource
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :=
  ((R ⊗[k] L) ⊗[(R ⊗[k] F)] ((R ⊗[k] F) ⊗[R] M))

/-- Helper for Chap10 Lemma 10 66 19: the intermediate-field owner base-change target,
named to keep restricted-scalar instance search out of the main equivalence term. -/
private abbrev intermediateOwnerBaseChangeTarget
    {L : Type*} [Field L] [Algebra k L] (_F : IntermediateField k L) :=
  ((R ⊗[k] L) ⊗[R] M)

/-- Helper for Chap10 Lemma 10 66 19: the restricted action on the source acts through
`R ⊗[k] F → R ⊗[k] L`. -/
private instance intermediateOwnerBaseChangeSourceSMul
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    SMul (R ⊗[k] F)
      (intermediateOwnerBaseChangeSource (k := k) (R := R) (M := M) F) where
  smul c z := (algebraMap (R ⊗[k] F) (R ⊗[k] L) c) • z

/-- Helper for Chap10 Lemma 10 66 19: the source module structure is the explicit restriction
of scalars along `R ⊗[k] F → R ⊗[k] L`. -/
private instance intermediateOwnerBaseChangeSourceModule
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    Module (R ⊗[k] F)
      (intermediateOwnerBaseChangeSource (k := k) (R := R) (M := M) F) :=
  Module.compHom
    (intermediateOwnerBaseChangeSource (k := k) (R := R) (M := M) F)
    (algebraMap (R ⊗[k] F) (R ⊗[k] L))

/-- Helper for Chap10 Lemma 10 66 19: the restricted action on the target acts through
`R ⊗[k] F → R ⊗[k] L`. -/
private instance intermediateOwnerBaseChangeTargetSMul
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    SMul (R ⊗[k] F)
      (intermediateOwnerBaseChangeTarget (k := k) (R := R) (M := M) F) where
  smul c z := (algebraMap (R ⊗[k] F) (R ⊗[k] L) c) • z

/-- Helper for Chap10 Lemma 10 66 19: the target module structure is the explicit restriction
of scalars along `R ⊗[k] F → R ⊗[k] L`. -/
private instance intermediateOwnerBaseChangeTargetModule
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    Module (R ⊗[k] F)
      (intermediateOwnerBaseChangeTarget (k := k) (R := R) (M := M) F) :=
  Module.compHom
    (intermediateOwnerBaseChangeTarget (k := k) (R := R) (M := M) F)
    (algebraMap (R ⊗[k] F) (R ⊗[k] L))

/-- Helper for Chap10 Lemma 10 66 19: the reassociation equivalence may be restricted from
`R ⊗[k] L`-linearity to `R ⊗[k] F`-linearity without re-running broad instance search. -/
private instance intermediateOwnerBaseChangeCompatibleSMul
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    LinearMap.CompatibleSMul
      (intermediateOwnerBaseChangeSource (k := k) (R := R) (M := M) F)
      (intermediateOwnerBaseChangeTarget (k := k) (R := R) (M := M) F)
      (R ⊗[k] F) (R ⊗[k] L) :=
  by
    refine LinearMap.CompatibleSMul.mk ?_
    intro f c x
    -- Proof comment: after spelling the restricted action explicitly, compatibility is just the
    -- original `R ⊗[k] L`-linearity of `f`.
    change f ((algebraMap (R ⊗[k] F) (R ⊗[k] L) c) • x) =
      (algebraMap (R ⊗[k] F) (R ⊗[k] L) c) • f x
    exact f.map_smul _ _

/-- Helper for Lemma 10.66.19: the canonical owner base change over the intermediate field
extension `F ⟶ L` identifies directly with the literal `L`-stage owner module. -/
private noncomputable def canonical_owner_baseChange_over_intermediate_field
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L) :
    ((((R ⊗[k] F) ⊗[F] L) ⊗[(R ⊗[k] F)] (((R ⊗[k] F) ⊗[R] M)))) ≃ₗ[(R ⊗[k] F)]
      (((R ⊗[k] L) ⊗[R] M)) :=
  -- Proof comment: first replace the literal ring base change by `R ⊗[k] L`, then use the
  -- owner reassociation equivalence restricted back along `R ⊗[k] F → R ⊗[k] L`.
  (LinearEquiv.rTensor (((R ⊗[k] F) ⊗[R] M))
      (ringTensorIntermediateField_baseChange_algEquiv (k := k) (R := R) (L := L) F).toLinearEquiv).trans
    ((owner_baseChange_reassoc_over_intermediate_field
        (k := k) (R := R) (M := M) (L := L) F).restrictScalars (R ⊗[k] F))

/-- Helper for Lemma 10.66.19: the owner base-change descent theorem over `F ⟶ L` specializes
directly to the `F`-stage owner module. -/
private theorem
    mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_owner_baseChange_intermediateField
    {L : Type*} [Field L] [Algebra k L] (F : IntermediateField k L)
    {qF : Ideal (R ⊗[k] F)}
    (hqF :
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] F)
        ((((R ⊗[k] F) ⊗[F] L) ⊗[(R ⊗[k] F)] (((R ⊗[k] F) ⊗[R] M))))) :
    qF ∈ weaklyAssociatedPrimes (R ⊗[k] F) (((R ⊗[k] F) ⊗[R] M)) := by
  -- This is exactly the already-proved owner descent theorem, with the `F`-stage owner module
  -- fed in as the base module.
  exact
    mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_owner_baseChange
      (k := F) (K := L) (R := R ⊗[k] F) (M := ((R ⊗[k] F) ⊗[R] M)) hqF

/-- Helper for Lemma 10.66.19: if a weakly associated prime appears over a finitely generated
field stage `L`, then after choosing a purely transcendental subextension `F ⊆ L` with `L / F`
finite, the contraction to `R ⊗[k] F` is already weakly associated to the canonical `F`-stage
owner module. -/
private theorem exists_purely_transcendental_intermediate_weakAss_descent_owner
    {L : Type*} [Field L] [Algebra k L]
    (F : IntermediateField k L) [FiniteDimensional F L]
    {qL : Ideal (R ⊗[k] L)}
    (hqL : qL ∈ weaklyAssociatedPrimes (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M))) :
    ∃ qF : Ideal (R ⊗[k] F),
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] F) (((R ⊗[k] F) ⊗[R] M)) ∧
        qF.under R = qL.under R := by
  let qF : Ideal (R ⊗[k] F) := Ideal.comap (algebraMap (R ⊗[k] F) (R ⊗[k] L)) qL
  letI : Module.Finite (R ⊗[k] F) (R ⊗[k] L) :=
    ringTensorIntermediateField_moduleFinite (k := k) (R := R) (L := L) F
  letI :
      Module (R ⊗[k] F) (((R ⊗[k] L) ⊗[R] M)) :=
    ringTensorIntermediateFieldOwnerModule
      (k := k) (R := R) (M := M) (L := L) F
  letI hTower :
      IsScalarTower (R ⊗[k] F) (R ⊗[k] L) (((R ⊗[k] L) ⊗[R] M)) :=
    ringTensorIntermediateFieldOwnerIsScalarTower
      (k := k) (R := R) (M := M) (L := L) F
  have hqF_restrict :
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] F) (((R ⊗[k] L) ⊗[R] M)) := by
    -- The finite-map restriction theorem says precisely that the contraction of a weakly
    -- associated prime over `R ⊗[k] L` is weakly associated after restricting scalars to
    -- `R ⊗[k] F`.
    rw [← @weaklyAssociatedPrimes.restrictScalars_eq_image_comap_of_finite
        (R := R ⊗[k] F) (S := R ⊗[k] L) (M := (((R ⊗[k] L) ⊗[R] M)))
        _ _ _ _ _ _ _ hTower]
    exact ⟨qL, hqL, rfl⟩
  have hqF_baseChange :
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] F)
        ((((R ⊗[k] F) ⊗[F] L) ⊗[(R ⊗[k] F)] (((R ⊗[k] F) ⊗[R] M)))) := by
    -- Proof comment: transport the contracted witness across the canonical owner comparison.
    rw [LinearEquiv.weaklyAssociatedPrimes_eq
      (canonical_owner_baseChange_over_intermediate_field
        (k := k) (R := R) (M := M) (L := L) F)]
    exact hqF_restrict
  refine ⟨qF, ?_, ?_⟩
  · -- Proof comment: after transport, the already-proved owner base-change descent theorem
    -- finishes the finite-extension paragraph.
    exact
      mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_owner_baseChange_intermediateField
        (k := k) (R := R) (M := M) (L := L) F hqF_baseChange
  · -- Proof comment: contracting first to `R ⊗[k] F` and then to `R` is the same as
    -- contracting directly to `R`.
    ext r
    rfl

/-- Helper for Lemma 10.66.19: any module carrying a weakly associated prime is nontrivial. -/
private theorem nontrivial_of_mem_weaklyAssociatedPrimes
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    {p : Ideal A} (hp : p ∈ weaklyAssociatedPrimes A N) :
    Nontrivial N := by
  rcases hp with ⟨x, hx⟩
  refine ⟨⟨0, x, ?_⟩⟩
  -- The witness for a weakly associated prime cannot be zero, since `0` has torsion ideal `⊤`.
  intro hx0
  have htop : Ideal.torsionOf A N x = ⊤ := by
    rw [Ideal.torsionOf_eq_top_iff]
    exact hx0.symm
  simpa [htop, Ideal.minimalPrimes_top] using hx

/-- Helper for Lemma 10.66.19: localizing the ring tensor `R ⊗[k] F` at `p` is the same as
tensoring the localization `R_p` with `F`. -/
private noncomputable def ringTensor_localizedModule_atPrime_linearEquiv
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime] :
    LocalizedModule.AtPrime p (R ⊗[k] F) ≃ₗ[Localization.AtPrime p]
      (Localization.AtPrime p ⊗[k] F) := by
  let eLocalized :
      LocalizedModule.AtPrime p (R ⊗[k] F) ≃ₗ[Localization.AtPrime p]
        Localization.AtPrime p ⊗[R] (R ⊗[k] F) :=
    -- Rewrite localization at `p` as tensoring with `R_p`.
    LocalizedModule.equivTensorProduct p.primeCompl (R ⊗[k] F)
  let eTensor :
      Localization.AtPrime p ⊗[R] (R ⊗[k] F) ≃ₗ[Localization.AtPrime p]
        (Localization.AtPrime p ⊗[k] F) :=
    -- Then cancel the redundant middle `R` tensor factor on the ring side.
    (Algebra.TensorProduct.cancelBaseChange k R (Localization.AtPrime p)
      (Localization.AtPrime p) F).toLinearEquiv
  exact eLocalized.trans eTensor

/-- Helper for Lemma 10.66.19: localizing the `F`-stage owner module at `p ⊂ R` is the same as
first localizing `R` and `M` at `p` and then forming the owner module over `R_p`. -/
private noncomputable def owner_localizedModule_atPrime_under_linearEquiv
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime] :
    LocalizedModule.AtPrime p (((R ⊗[k] F) ⊗[R] M)) ≃ₗ[Localization.AtPrime p]
      ((Localization.AtPrime p ⊗[k] F) ⊗[Localization.AtPrime p]
        (LocalizedModule.AtPrime p M)) :=
  let Rp := Localization.AtPrime p
  -- Proof comment: first rewrite localization of the owner as tensoring with `R_p` over `R`.
  let eLocalized :
      LocalizedModule.AtPrime p (((R ⊗[k] F) ⊗[R] M)) ≃ₗ[Rp]
        (Rp ⊗[R] (((R ⊗[k] F) ⊗[R] M))) :=
    LocalizedModule.equivTensorProduct p.primeCompl (((R ⊗[k] F) ⊗[R] M))
  -- Proof comment: reassociate so the localized ring tensor can be normalized independently.
  let eAssoc :
      (Rp ⊗[R] (R ⊗[k] F)) ⊗[R] M ≃ₗ[Rp]
        Rp ⊗[R] (((R ⊗[k] F) ⊗[R] M)) :=
    TensorProduct.AlgebraTensorModule.assoc R R Rp Rp (R ⊗[k] F) M
  -- Proof comment: identify `R_p ⊗[R] (R ⊗[k] F)` with the canonical tensor ring
  -- `R_p ⊗[k] F`.
  let eRingTensor :
      Rp ⊗[R] (R ⊗[k] F) ≃ₗ[Rp] (Rp ⊗[k] F) :=
    (LocalizedModule.equivTensorProduct p.primeCompl (R ⊗[k] F)).symm.trans
      (ringTensor_localizedModule_atPrime_linearEquiv (k := k) (R := R) (F := F) p)
  let eCong :
      (Rp ⊗[R] (R ⊗[k] F)) ⊗[R] M ≃ₗ[Rp]
        (Rp ⊗[k] F) ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.congr eRingTensor (LinearEquiv.refl R M)
  -- Proof comment: cancel the remaining base change, producing the owner over `R_p`.
  let eCancel :
      (Rp ⊗[k] F) ⊗[Rp] (Rp ⊗[R] M) ≃ₗ[Rp]
        (Rp ⊗[k] F) ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R Rp Rp (Rp ⊗[k] F) M
  -- Proof comment: finally replace `R_p ⊗[R] M` by the localized module itself.
  let eLocalizedM :
      LocalizedModule.AtPrime p M ≃ₗ[Rp] Rp ⊗[R] M :=
    LocalizedModule.equivTensorProduct p.primeCompl M
  let eModuleCong :
      (Rp ⊗[k] F) ⊗[Rp] (Rp ⊗[R] M) ≃ₗ[Rp]
        (Rp ⊗[k] F) ⊗[Rp] LocalizedModule.AtPrime p M :=
    TensorProduct.congr (LinearEquiv.refl Rp (Rp ⊗[k] F)) eLocalizedM.symm
  eLocalized.trans (eAssoc.symm.trans (eCong.trans (eCancel.symm.trans eModuleCong)))

/-- Helper for Lemma 10.66.19: in the purely transcendental case, the remaining source argument
reduces contraction of a weakly associated prime on the owner base change to weak association on
the base module. -/
private theorem IsSMulRegular.notMem_torsionOf_minimalPrimes
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    {g : A} {z : N} (hregular : IsSMulRegular N g)
    {q : Ideal A} (hq : q ∈ (Ideal.torsionOf A N z).minimalPrimes) :
    g ∉ q := by
  -- Proof comment: a regular element cannot lie in a minimal prime over the annihilator of `z`,
  -- because the standard minimal-prime localization lemma would produce a nonzero vector killed by
  -- that regular element.
  intro hg
  rcases Ideal.exists_mul_mem_of_mem_minimalPrimes hq hg with ⟨y, hy, hgy⟩
  have hyz_ne : y • z ≠ 0 := by
    intro hyz
    rw [Ideal.mem_torsionOf_iff] at hy
    exact hy hyz
  have hgyz : g • (y • z) = 0 := by
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      (show (g * y) • z = 0 from by
        simpa [Ideal.mem_torsionOf_iff] using hgy)
  exact hyz_ne (hregular.right_eq_zero_of_smul hgyz)

/-- Helper for Lemma 10.66.19: restricting scalars from `A` to `R` sends the torsion ideal of a
vector to the corresponding torsion ideal over `R`. -/
private theorem comap_torsionOf_eq
    {A : Type*} [CommRing A] [Algebra R A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    (z : N) :
    Ideal.comap (algebraMap R A) (Ideal.torsionOf A N z) =
      Ideal.torsionOf R N z := by
  -- Proof comment: an element `r : R` kills `z` after scalar extension exactly when its image in
  -- `A` kills `z`, because the two scalar actions agree by the scalar tower.
  ext r
  rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  simpa using (IsScalarTower.algebraMap_smul A r z)

/-- Helper for Lemma 10.66.19: in the purely transcendental case, the remaining source argument
reduces contraction of a weakly associated prime on the owner base change to weak association on
the base module. -/
private theorem maximalIdeal_mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_local
    {A : Type*} [CommRing A] [Algebra R A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    [IsLocalRing R]
    (hregular :
      ∀ g : A, g ∉ Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) →
        IsSMulRegular N g)
    {q : Ideal A} (hq_under : q.under R = IsLocalRing.maximalIdeal R)
    (hq : q ∈ weaklyAssociatedPrimes A N) :
    IsLocalRing.maximalIdeal R ∈ weaklyAssociatedPrimes R N := by
  rcases hq with ⟨z, hz⟩
  let J : Ideal A := Ideal.torsionOf A N z
  have hq_eq_map :
      q = Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) := by
    apply le_antisymm
    · intro g hgq
      by_contra hgmap
      exact
        (IsSMulRegular.notMem_torsionOf_minimalPrimes
          (A := A) (N := N) (g := g) (z := z) (hregular g hgmap)
          (q := q) (by simpa [J] using hz)) hgq
    · change Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) ≤ q
      rw [Ideal.map_le_iff_le_comap]
      simpa [Ideal.under, hq_under]
  have hminimal_unique : J.minimalPrimes = {q} := by
    ext p
    constructor
    · intro hp
      have hp_le_map :
          p ≤ Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) := by
        intro g hgp
        by_contra hgmap
        exact
          (IsSMulRegular.notMem_torsionOf_minimalPrimes
            (A := A) (N := N) (g := g) (z := z) (hregular g hgmap)
            (q := p) (by simpa [J] using hp)) hgp
      have hp_le_q : p ≤ q := by
        simpa [hq_eq_map] using hp_le_map
      exact Set.mem_singleton_iff.mpr <|
        le_antisymm
          hp_le_q
          (hz.2 ⟨Ideal.minimalPrimes_isPrime hp, hp.1.2⟩ hp_le_q)
    · rintro rfl
      simpa [J] using hz
  have hradA : J.radical = q := by
    rw [← Ideal.sInf_minimalPrimes, hminimal_unique, sInf_singleton]
  have hradR :
      (Ideal.torsionOf R N z).radical = IsLocalRing.maximalIdeal R := by
    calc
      (Ideal.torsionOf R N z).radical =
          (Ideal.comap (algebraMap R A) J).radical := by
            rw [comap_torsionOf_eq (R := R) (A := A) z]
      _ = Ideal.comap (algebraMap R A) J.radical := by
            rw [← Ideal.comap_radical]
      _ = IsLocalRing.maximalIdeal R := by
            simpa [J, hradA, Ideal.under, hq_under]
  rw [mem_weaklyAssociatedPrimes_iff]
  refine ⟨z, ?_⟩
  -- Proof comment: once the `R`-torsion radical is exactly the maximal ideal of the local ring,
  -- that maximal ideal is the unique minimal prime over the `R`-torsion ideal of `z`.
  haveI : (Ideal.torsionOf R N z).radical.IsPrime := by
    simpa [hradR] using
      (show (IsLocalRing.maximalIdeal R).IsPrime by infer_instance)
  rw [← Ideal.radical_minimalPrimes, hradR, Ideal.minimalPrimes_eq_subsingleton_self]
  simp

/-- Helper for Lemma 10.66.19: in the purely transcendental case, the remaining source argument
reduces contraction of a weakly associated prime on the owner base change to weak association on
the base module. -/
private theorem isDomain_residueField_tensor_adjoin
    {L : Type*} [Field L] [Algebra k L]
    {ι : Type*} (x : ι → L) (hx : IsTranscendenceBasis k x)
    {p : Ideal R} [p.IsPrime] :
    IsDomain
      ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).ResidueField ⊗[k]
        IntermediateField.adjoin k (Set.range x)) := by
  -- Proof comment: this is exactly the transcendence-basis tensor-domain lemma, specialized to
  -- the residue field of `R_p`.
  simpa using
    isDomain_tensor_adjoin_of_isTranscendenceBasis
      (k := k)
      (κ := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).ResidueField)
      (L := L) x hx

/-- Helper for Chap10 Lemma 10 66 19: the localization of `R ⊗[k] F` at the image of
`p.primeCompl` is canonically `R_p ⊗[k] F`. -/
private noncomputable def ringTensorAtPrimeLocalizationAlgEquiv
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime] :
    Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl) ≃ₐ[Localization.AtPrime p]
      (Localization.AtPrime p ⊗[k] F) :=
  -- Proof comment: first view the raw localization as `R_p ⊗[R] (R ⊗[k] F)`, then cancel the
  -- redundant base-change factor to get `R_p ⊗[k] F`.
  ((Localization.tensorRightAlgEquiv p.primeCompl (R ⊗[k] F)).symm).trans
    (Algebra.TensorProduct.cancelBaseChange k R (Localization.AtPrime p)
      (Localization.AtPrime p) F)

/-- Helper for Chap10 Lemma 10 66 19: the canonical local tensor ring is an algebra over
`R ⊗[k] F` through the map induced by `R → R_p` and `F → F`. -/
private noncomputable instance canonicalLocalTensorAlgebra
    {F : Type*} [Field F] [Algebra k F] {p : Ideal R} [p.IsPrime] :
    Algebra (R ⊗[k] F) (Localization.AtPrime p ⊗[k] F) :=
  RingHom.toAlgebra
    ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R (Localization.AtPrime p))
      (AlgHom.id k F)).toRingHom)

/-- Helper for Chap10 Lemma 10 66 19: the maps
`R → R ⊗[k] F → R_p ⊗[k] F` and `R → R_p ⊗[k] F` agree. -/
private instance canonicalLocalTensorIsScalarTower
    {F : Type*} [Field F] [Algebra k F] {p : Ideal R} [p.IsPrime] :
    IsScalarTower R (R ⊗[k] F) (Localization.AtPrime p ⊗[k] F) := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro r
  -- Proof comment: unfold the `R ⊗[k] F`-algebra map only on the `R`-generator.
  have hAlg :
      (algebraMap (R ⊗[k] F) (Localization.AtPrime p ⊗[k] F))
          ((algebraMap R (R ⊗[k] F)) r) =
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R (Localization.AtPrime p))
          (AlgHom.id k F)) ((algebraMap R (R ⊗[k] F)) r) := rfl
  rw [hAlg]
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]

/-- Helper for Chap10 Lemma 10 66 19: the canonical local tensor ring acts on itself by
multiplication for the tensor-ring transport helpers. -/
private instance canonicalLocalTensorSelfModule
    {F : Type*} [Field F] [Algebra k F] {p : Ideal R} [p.IsPrime] :
    Module (Localization.AtPrime p ⊗[k] F) (Localization.AtPrime p ⊗[k] F) :=
  Semiring.toModule

/-- Helper for Chap10 Lemma 10 66 19: the self-action on the canonical local tensor ring is a
distributive action for the tensor-ring transport helpers. -/
private instance canonicalLocalTensorSelfDistribMulAction
    {F : Type*} [Field F] [Algebra k F] {p : Ideal R} [p.IsPrime] :
    DistribMulAction (Localization.AtPrime p ⊗[k] F) (Localization.AtPrime p ⊗[k] F) :=
  (Semiring.toModule :
    Module (Localization.AtPrime p ⊗[k] F) (Localization.AtPrime p ⊗[k] F)).toDistribMulAction

/-- Helper for Chap10 Lemma 10 66 19: the canonical local owner tensor-over-`R ⊗[k] F`
presentation carries the left `R_p ⊗[k] F` action. -/
private noncomputable instance canonicalLocalTensorSourceDistribMulAction
    {F : Type*} [Field F] [Algebra k F] {p : Ideal R} [p.IsPrime] :
    DistribMulAction (Localization.AtPrime p ⊗[k] F)
      ((Localization.AtPrime p ⊗[k] F) ⊗[(R ⊗[k] F)] ((R ⊗[k] F) ⊗[R] M)) :=
  TensorProduct.leftDistribMulAction

/-- Helper for Chap10 Lemma 10 66 19: the canonical local owner tensor-over-`R ⊗[k] F`
presentation is a module over `R_p ⊗[k] F`. -/
private noncomputable instance canonicalLocalTensorSourceModule
    {F : Type*} [Field F] [Algebra k F] {p : Ideal R} [p.IsPrime] :
    Module (Localization.AtPrime p ⊗[k] F)
      ((Localization.AtPrime p ⊗[k] F) ⊗[(R ⊗[k] F)] ((R ⊗[k] F) ⊗[R] M)) :=
  TensorProduct.leftModule

/-- Helper for Chap10 Lemma 10 66 19: the raw/canonical localization comparison is also an
algebra equivalence over the tensor ring `R ⊗[k] F`. -/
private theorem ringTensorAtPrimeLocalizationAlgEquivOverTensorRing_commutes
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime] :
    ∀ a : R ⊗[k] F,
      ((ringTensorAtPrimeLocalizationAlgEquiv (k := k) (R := R) (F := F) p).toRingEquiv :
        Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl) →+*
          (Localization.AtPrime p ⊗[k] F))
          ((algebraMap (R ⊗[k] F)
            (Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl))) a) =
        (algebraMap (R ⊗[k] F) (Localization.AtPrime p ⊗[k] F)) a := by
  let A := R ⊗[k] F
  let B := Localization (Algebra.algebraMapSubmonoid A p.primeCompl)
  let C := Localization.AtPrime p ⊗[k] F
  let eRp := ringTensorAtPrimeLocalizationAlgEquiv (k := k) (R := R) (F := F) p
  letI : Algebra A C := canonicalLocalTensorAlgebra (k := k) (R := R) (F := F) (p := p)
  intro a
  -- Proof comment: reduce compatibility over `R ⊗[k] F` to tensor generators, where the
  -- localization and base-change comparison maps have explicit computation rules.
  refine TensorProduct.induction_on a ?_ ?_ ?_
  · simp
  · intro r f
    have htensor :
        ((Localization.tensorRightAlgEquiv p.primeCompl (R ⊗[k] F)).symm
          ((algebraMap (R ⊗[k] F)
            (Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl)))
            (r ⊗ₜ[k] f))) =
          (1 : Localization.AtPrime p) ⊗ₜ[R] (r ⊗ₜ[k] f) := by
      apply (Localization.tensorRightAlgEquiv p.primeCompl (R ⊗[k] F)).injective
      simp [Localization.tensorRightAlgEquiv_apply_one_tmul]
    have hAlg :
        (algebraMap (R ⊗[k] F) C) (r ⊗ₜ[k] f) =
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R (Localization.AtPrime p))
            (AlgHom.id k F)) (r ⊗ₜ[k] f) := rfl
    calc
      eRp.toRingEquiv.toFun ((algebraMap (R ⊗[k] F) B) (r ⊗ₜ[k] f)) =
          (Algebra.TensorProduct.cancelBaseChange k R (Localization.AtPrime p)
            (Localization.AtPrime p) F)
            (((Localization.tensorRightAlgEquiv p.primeCompl (R ⊗[k] F)).symm)
              ((algebraMap (R ⊗[k] F) B) (r ⊗ₜ[k] f))) := rfl
      _ = (Algebra.TensorProduct.cancelBaseChange k R (Localization.AtPrime p)
            (Localization.AtPrime p) F)
            ((1 : Localization.AtPrime p) ⊗ₜ[R] (r ⊗ₜ[k] f)) := by
            exact congrArg _ htensor
      _ = (algebraMap (R ⊗[k] F) C) (r ⊗ₜ[k] f) := by
            rw [hAlg, Algebra.TensorProduct.map_tmul]
            simp [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def]
  · intro x y hx hy
    calc
      eRp.toRingEquiv.toFun ((algebraMap (R ⊗[k] F) B) (x + y)) =
          eRp.toRingEquiv.toFun (((algebraMap (R ⊗[k] F) B) x) +
            ((algebraMap (R ⊗[k] F) B) y)) := by rw [map_add]
      _ = eRp.toRingEquiv.toFun ((algebraMap (R ⊗[k] F) B) x) +
            eRp.toRingEquiv.toFun ((algebraMap (R ⊗[k] F) B) y) := by
            exact eRp.toRingEquiv.map_add _ _
      _ = (algebraMap (R ⊗[k] F) C) x + (algebraMap (R ⊗[k] F) C) y := by
            simpa [eRp, B, C] using congrArg₂ HAdd.hAdd hx hy
      _ = (algebraMap (R ⊗[k] F) C) (x + y) := by
            exact ((algebraMap (R ⊗[k] F) C).map_add x y).symm

/-- Helper for Chap10 Lemma 10 66 19: the raw/canonical localization comparison, viewed as a
tensor-ring algebra equivalence, has the desired underlying `RingEquiv` by definition. -/
private noncomputable def ringTensorAtPrimeLocalizationAlgEquivOverTensorRing
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime] :
    Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl) ≃ₐ[R ⊗[k] F]
      (Localization.AtPrime p ⊗[k] F) :=
  { (ringTensorAtPrimeLocalizationAlgEquiv (k := k) (R := R) (F := F) p).toRingEquiv with
    commutes' :=
      ringTensorAtPrimeLocalizationAlgEquivOverTensorRing_commutes
        (k := k) (R := R) (p := p) }

/-- Helper for Chap10 Lemma 10 66 19: the older existential form of the tensor-ring algebra
equivalence follows from the definitionally stable algebra equivalence. -/
private theorem ringTensorAtPrimeLocalizationAlgEquiv_overTensorRing
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime] :
    ∃ e : Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl) ≃ₐ[R ⊗[k] F]
      (Localization.AtPrime p ⊗[k] F),
      (e.toRingEquiv :
        Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl) →+*
          (Localization.AtPrime p ⊗[k] F)) =
        (ringTensorAtPrimeLocalizationAlgEquiv (k := k) (R := R) (F := F) p).toRingEquiv := by
  -- Proof comment: return the definitionally stable algebra equivalence; its ring part is the
  -- original raw/canonical comparison by reflexivity.
  exact ⟨ringTensorAtPrimeLocalizationAlgEquivOverTensorRing
    (k := k) (R := R) (F := F) p, rfl⟩

/-- Helper for Chap10 Lemma 10 66 19: after transporting along the tensor-ring algebra
equivalence, the `C ⊗[R ⊗[k] F] ((R ⊗[k] F) ⊗[R] M)` presentation normalizes to the
canonical local owner over `R_p`. -/
private noncomputable def canonicalLocalOwner_tensorOverTensorRing_linearEquiv
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime] :
    ((Localization.AtPrime p ⊗[k] F) ⊗[(R ⊗[k] F)] ((R ⊗[k] F) ⊗[R] M)) ≃ₗ[
      Localization.AtPrime p ⊗[k] F]
      ((Localization.AtPrime p ⊗[k] F) ⊗[Localization.AtPrime p]
        LocalizedModule.AtPrime p M) :=
  let A := R ⊗[k] F
  let Rp := Localization.AtPrime p
  let C := Rp ⊗[k] F
  letI : Algebra A C := canonicalLocalTensorAlgebra (k := k) (R := R) (F := F) (p := p)
  letI : Module C C := canonicalLocalTensorSelfModule (k := k) (R := R) (F := F) (p := p)
  letI : DistribMulAction C C :=
    canonicalLocalTensorSelfDistribMulAction (k := k) (R := R) (F := F) (p := p)
  letI : DistribMulAction C (C ⊗[R] M) := TensorProduct.leftDistribMulAction
  letI : Module C (C ⊗[R] M) := TensorProduct.leftModule
  -- Proof comment: cancel the base change from `R` to `A`, then reinsert the localization of
  -- `M` through the standard `LocalizedModule.equivTensorProduct` bridge.
  let eCancelA : C ⊗[A] (A ⊗[R] M) ≃ₗ[C] C ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A C C M
  let eCancelRp : C ⊗[Rp] (Rp ⊗[R] M) ≃ₗ[C] C ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R Rp C C M
  let eLocalizedM : LocalizedModule.AtPrime p M ≃ₗ[Rp] Rp ⊗[R] M :=
    LocalizedModule.equivTensorProduct p.primeCompl M
  let eModuleCong : C ⊗[Rp] (Rp ⊗[R] M) ≃ₗ[C]
      C ⊗[Rp] LocalizedModule.AtPrime p M :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) eLocalizedM.symm
  eCancelA.trans (eCancelRp.symm.trans eModuleCong)

/-- Helper for Chap10 Lemma 10 66 19: localizing the tensor ring at the image of
`(q.under R).primeCompl` produces a weakly associated prime whose contraction is `q`. -/
private theorem localizedTensorWeaklyAssociatedPrimeRaw
    {F : Type*} [Field F] [Algebra k F]
    {q : Ideal (R ⊗[k] F)} [q.IsPrime]
    (hq : q ∈ weaklyAssociatedPrimes (R ⊗[k] F) (((R ⊗[k] F) ⊗[R] M))) :
    ∃ qS : Ideal (Localization
        (Algebra.algebraMapSubmonoid (R ⊗[k] F) (q.under R).primeCompl)),
      qS ∈ weaklyAssociatedPrimes
          (Localization
            (Algebra.algebraMapSubmonoid (R ⊗[k] F) (q.under R).primeCompl))
          (LocalizedModule
            (Algebra.algebraMapSubmonoid (R ⊗[k] F) (q.under R).primeCompl)
            (((R ⊗[k] F) ⊗[R] M))) ∧
        Ideal.comap
          (algebraMap (R ⊗[k] F)
            (Localization
              (Algebra.algebraMapSubmonoid (R ⊗[k] F) (q.under R).primeCompl))) qS = q := by
  let A := R ⊗[k] F
  let N := ((R ⊗[k] F) ⊗[R] M)
  let S : Submonoid A := Algebra.algebraMapSubmonoid A (q.under R).primeCompl
  have hdisj : Disjoint (S : Set A) (q : Set A) := by
    -- Proof comment: every element of the image of `R \ q.under R` is excluded from `q` by
    -- the definition of contraction.
    rw [Set.disjoint_left]
    intro a haS haq
    rcases haS with ⟨r, hr, hr_eq⟩
    have hr_mem : r ∈ q.under R := by
      simpa [Ideal.under, Ideal.mem_comap, A, hr_eq] using haq
    exact hr hr_mem
  have hrange : q ∈ Set.range (Ideal.comap (algebraMap A (Localization S))) := by
    -- Proof comment: a prime disjoint from the localization submonoid is the contraction of its
    -- extension to the localized ring.
    refine ⟨Ideal.map (algebraMap A (Localization S)) q, ?_⟩
    exact
      IsLocalization.comap_map_of_isPrime_disjoint S (Localization S)
        (show q.IsPrime by infer_instance) hdisj
  have hq_local_A : q ∈ weaklyAssociatedPrimes A (LocalizedModule S N) := by
    -- Proof comment: Lemma `10.66.15` identifies weak association after localization with the
    -- weakly associated primes in the localization range.
    rw [← weaklyAssociatedPrimes.inter_localization_range_eq (R := A) (M := N) S]
    exact ⟨by simpa [A, N] using hq, hrange⟩
  -- Proof comment: convert the localized statement from the `A`-view to the localized-ring view.
  rw [← weaklyAssociatedPrimes.localizedModule_eq_image_comap (R := A) (M := N) S] at hq_local_A
  simpa [A, N, S] using hq_local_A

/-- Helper for Chap10 Lemma 10 66 19: elements of `R \ p` map into the submonoid used to
localize the raw tensor ring `R ⊗[k] F`. -/
private theorem algebraMap_mem_rawTensorLocalizationSubmonoid
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime] {r : R}
    (hr : r ∈ p.primeCompl) :
    algebraMap R (R ⊗[k] F) r ∈
      Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl := by
  -- Proof comment: the raw localization submonoid is defined as the image of `p.primeCompl`.
  exact Algebra.mem_algebraMapSubmonoid_of_mem (S := R ⊗[k] F) ⟨r, hr⟩

/-- Helper for Chap10 Lemma 10 66 19: the canonical map from `R_p` to the raw localization of
`R ⊗[k] F` at the image of `p.primeCompl`. -/
private noncomputable def atPrimeToRawTensorLocalization
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime] :
    Localization.AtPrime p →+*
      Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl) :=
  IsLocalization.map
    (M := p.primeCompl)
    (T := Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl)
    (Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl))
    (algebraMap R (R ⊗[k] F))
    (fun _ hy => algebraMap_mem_rawTensorLocalizationSubmonoid (k := k) (R := R) (F := F) p hy)

/-- Helper for Chap10 Lemma 10 66 19: the map from `R_p` to the raw tensor localization agrees
with the expected two-step algebra map on elements of `R`. -/
private theorem atPrimeToRawTensorLocalization_algebraMap
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime] (r : R) :
    atPrimeToRawTensorLocalization (k := k) (R := R) (F := F) p
        (algebraMap R (Localization.AtPrime p) r) =
      algebraMap (R ⊗[k] F)
        (Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl))
        (algebraMap R (R ⊗[k] F) r) := by
  -- Proof comment: this is the computation rule for the localization map just constructed.
  simp [atPrimeToRawTensorLocalization]

/-- Helper for Chap10 Lemma 10 66 19: the raw localized weakly associated prime contracts to the
maximal ideal of `R_p`. -/
private theorem rawLocalizedWeaklyAssociatedPrime_comap_atPrime_eq_maximal
    {F : Type*} [Field F] [Algebra k F]
    {q : Ideal (R ⊗[k] F)} [q.IsPrime]
    {qS : Ideal (Localization
        (Algebra.algebraMapSubmonoid (R ⊗[k] F) (q.under R).primeCompl))}
    (hqS : qS ∈ weaklyAssociatedPrimes
          (Localization
            (Algebra.algebraMapSubmonoid (R ⊗[k] F) (q.under R).primeCompl))
          (LocalizedModule
            (Algebra.algebraMapSubmonoid (R ⊗[k] F) (q.under R).primeCompl)
            (((R ⊗[k] F) ⊗[R] M))))
    (hcomap : Ideal.comap
          (algebraMap (R ⊗[k] F)
            (Localization
              (Algebra.algebraMapSubmonoid (R ⊗[k] F) (q.under R).primeCompl))) qS = q) :
    Ideal.comap (atPrimeToRawTensorLocalization (k := k) (R := R) (F := F) (q.under R)) qS =
      IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R)) := by
  let p : Ideal R := q.under R
  let B := Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl)
  let f := atPrimeToRawTensorLocalization (k := k) (R := R) (F := F) p
  have hqSprime : qS.IsPrime := hqS.isPrime
  apply le_antisymm
  · -- Proof comment: the contraction is proper, hence contained in the maximal ideal of `R_p`.
    have hproper : Ideal.comap f qS ≠ ⊤ := by
      intro htop
      have h1 : (1 : B) ∈ qS := by
        have h1c : (1 : Localization.AtPrime p) ∈ Ideal.comap f qS := by
          rw [htop]
          exact trivial
        simpa [f, B, Ideal.mem_comap] using h1c
      exact hqSprime.ne_top ((Ideal.eq_top_iff_one qS).mpr h1)
    simpa [p, f] using IsLocalRing.le_maximalIdeal hproper
  · -- Proof comment: the image of `p = q.under R` lies in `qS`, and this image is the maximal
    -- ideal of the local ring `R_p`.
    rw [← Localization.AtPrime.map_eq_maximalIdeal (R := R) (I := p)]
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change f (algebraMap R (Localization.AtPrime p) r) ∈ qS
    rw [atPrimeToRawTensorLocalization_algebraMap (k := k) (R := R) (F := F) p r]
    have hrq : algebraMap R (R ⊗[k] F) r ∈ q := by
      simpa [p, Ideal.under] using hr
    have hrcomap : algebraMap R (R ⊗[k] F) r ∈ Ideal.comap
          (algebraMap (R ⊗[k] F)
            (Localization
              (Algebra.algebraMapSubmonoid (R ⊗[k] F) (q.under R).primeCompl))) qS := by
      simpa [hcomap] using hrq
    simpa [p, B, Ideal.mem_comap] using hrcomap

/-- Helper for Chap10 Lemma 10 66 19: the canonical local tensor ring acts on itself by
multiplication, avoiding repeated instance search in the local-owner descent. -/
private instance canonicalLocalOwnerSelfModule
    {F : Type*} [Field F] [Algebra k F] {p : Ideal R} [p.IsPrime] :
    Module (Localization.AtPrime p ⊗[k] F) (Localization.AtPrime p ⊗[k] F) :=
  Semiring.toModule

/-- Helper for Chap10 Lemma 10 66 19: the self-action on the canonical local tensor ring is a
distributive action. -/
private instance canonicalLocalOwnerSelfDistribMulAction
    {F : Type*} [Field F] [Algebra k F] {p : Ideal R} [p.IsPrime] :
    DistribMulAction (Localization.AtPrime p ⊗[k] F) (Localization.AtPrime p ⊗[k] F) :=
  (Semiring.toModule :
    Module (Localization.AtPrime p ⊗[k] F) (Localization.AtPrime p ⊗[k] F)).toDistribMulAction

/-- Helper for Chap10 Lemma 10 66 19: the canonical local owner carries the left action of
`R_p ⊗[k] F`. -/
private instance canonicalLocalOwnerDistribMulAction
    {F : Type*} [Field F] [Algebra k F] {p : Ideal R} [p.IsPrime] :
    DistribMulAction (Localization.AtPrime p ⊗[k] F)
      ((Localization.AtPrime p ⊗[k] F) ⊗[Localization.AtPrime p]
        LocalizedModule.AtPrime p M) :=
  TensorProduct.leftDistribMulAction

/-- Helper for Chap10 Lemma 10 66 19: the canonical local owner is a module over
`R_p ⊗[k] F` through the left tensor factor. -/
private instance canonicalLocalOwnerModule
    {F : Type*} [Field F] [Algebra k F] {p : Ideal R} [p.IsPrime] :
    Module (Localization.AtPrime p ⊗[k] F)
      ((Localization.AtPrime p ⊗[k] F) ⊗[Localization.AtPrime p]
        LocalizedModule.AtPrime p M) :=
  TensorProduct.leftModule

/-- Helper for Chap10 Lemma 10 66 19: the `R_p`, `R_p ⊗[k] F`, and canonical local-owner
actions form the scalar tower used by the local descent lemma. -/
private theorem canonicalLocalOwnerIsScalarTower
    {F : Type*} [Field F] [Algebra k F] {p : Ideal R} [p.IsPrime] :
    IsScalarTower (Localization.AtPrime p) (Localization.AtPrime p ⊗[k] F)
      ((Localization.AtPrime p ⊗[k] F) ⊗[Localization.AtPrime p]
        LocalizedModule.AtPrime p M) := by
  refine ⟨?_⟩
  intro r a z
  -- Proof comment: reduce the tower law to pure tensors, where it is associativity in the
  -- tensor ring.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro b m
    rw [TensorProduct.smul_tmul']
    rw [TensorProduct.smul_tmul']
    apply congrArg
      (fun c : Localization.AtPrime p ⊗[k] F => c ⊗ₜ[Localization.AtPrime p] m)
    simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
    rw [mul_assoc]
  · intro z w hz hw
    simp [smul_add, hz, hw]

/-- Helper for Lemma 10.66.19: every tensor in the canonical local owner over `R_p` already comes
from tensoring with some finite `R_p`-submodule of the localized base module. -/
private theorem exists_finite_local_owner_submodule_of_mem_tensor
    {p : Ideal R} [p.IsPrime]
    {F : Type*} [Field F] [Algebra k F]
    (_z : ((Localization.AtPrime p ⊗[k] F) ⊗[Localization.AtPrime p]
      (LocalizedModule.AtPrime p M))) :
    True := by
  -- TODO: restore the finite-submodule witness once the `R_p ⊗[k] F` tensor self-action API is
  -- available again. This helper is currently unused downstream because the canonical regularity
  -- theorem remains blocked earlier in the source route.
  trivial

/-- Helper for Lemma 10.66.19: over a domain, any nonzero scalar acts injectively on a finitely
supported family of copies of the domain. -/
private theorem isSMulRegular_finsupp_of_ne_zero
    {A : Type*} [CommRing A] [IsDomain A] {ι : Type*} {g : A} (hg : g ≠ 0) :
    IsSMulRegular (ι →₀ A) g := by
  -- Check regularity coordinatewise, where it reduces to cancellation in the domain `A`.
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro f hf
  ext i
  have hcoord := congrArg (fun h : ι →₀ A => h i) hf
  simp only [Finsupp.smul_apply, smul_eq_mul] at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_left hg

/-- Helper for Lemma 10.66.19: over a domain, any nonzero scalar acts regularly on the tensor of
that domain with a vector space over the base field. -/
private theorem isSMulRegular_tensor_vectorSpace_of_ne_zero
    {κ : Type*} [Field κ]
    {A : Type*} [CommRing A] [Algebra κ A] [IsDomain A]
    {V : Type*} [AddCommGroup V] [Module κ V]
    {g : A} (hg : g ≠ 0) :
    IsSMulRegular (A ⊗[κ] V) g := by
  classical
  let b : Module.Basis (Module.Basis.ofVectorSpaceIndex κ V) κ V :=
    Module.Basis.ofVectorSpace κ V
  let e :
      A ⊗[κ] V ≃ₗ[A] (Module.Basis.ofVectorSpaceIndex κ V →₀ A) :=
    Algebra.TensorProduct.equivFinsuppOfBasis (R := κ) (A := A) (V := V) b
  have hregular_finsupp :
      IsSMulRegular (Module.Basis.ofVectorSpaceIndex κ V →₀ A) g :=
    isSMulRegular_finsupp_of_ne_zero (A := A) (ι := Module.Basis.ofVectorSpaceIndex κ V) hg
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro z hz
  apply e.injective
  have hz' : g • e z = 0 := by
    simpa using congrArg e hz
  exact hregular_finsupp.right_eq_zero_of_smul hz'

/-- Helper for Chap10 Lemma 10 66 19: a semilinear equivalence identifies the torsion ideal of
the transported vector with the image of the original torsion ideal. -/
private theorem torsionOf_semilinearEquiv_eq_map
    {A B : Type u} [CommRing A] [CommRing B] (eR : A ≃+* B)
    {N Q : Type x} [AddCommGroup N] [Module A N] [AddCommGroup Q] [Module B Q]
    (eN : N ≃ₛₗ[(eR : A →+* B)] Q) (z : N) :
    Ideal.torsionOf B Q (eN z) = Ideal.map (eR : A →+* B) (Ideal.torsionOf A N z) := by
  ext b
  rw [Ideal.mem_torsionOf_iff]
  constructor
  · intro hb
    have hbpre : eR.symm b ∈ Ideal.torsionOf A N z := by
      rw [Ideal.mem_torsionOf_iff]
      apply eN.injective
      -- Proof comment: pull the equation back along the semilinear equivalence.
      calc
        eN ((eR.symm b) • z) = b • eN z := by
          simpa using eN.map_smulₛₗ (eR.symm b) z
        _ = 0 := hb
        _ = eN 0 := by simp
    -- Proof comment: the preimage calculation exactly says that `b` lies in the mapped ideal.
    simpa using Ideal.mem_map_of_mem (eR : A →+* B) hbpre
  · intro hb
    rcases (Ideal.mem_map_of_equiv (eR : A ≃+* B) b).mp hb with ⟨a, ha, rfl⟩
    rw [Ideal.mem_torsionOf_iff] at ha
    -- Proof comment: push a source torsion relation forward through semilinearity.
    calc
      eR a • eN z = eN (a • z) := (eN.map_smulₛₗ a z).symm
      _ = 0 := by simpa using congrArg eN ha

/-- Helper for Chap10 Lemma 10 66 19: a ring equivalence sends a minimal prime over an ideal to
a minimal prime over the mapped ideal. -/
private theorem ideal_map_mem_minimalPrimes_of_equiv
    {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    {I p : Ideal A} (hp : p ∈ I.minimalPrimes) :
    Ideal.map (e : A →+* B) p ∈ (Ideal.map (e : A →+* B) I).minimalPrimes := by
  haveI : p.IsPrime := hp.1.1
  refine ⟨⟨show (Ideal.map (e : A →+* B) p).IsPrime by
    exact Ideal.map_isPrime_of_equiv (e : A ≃+* B), Ideal.map_mono hp.1.2⟩, ?_⟩
  intro q hq hq_le
  haveI : q.IsPrime := hq.1
  have hqprime : (Ideal.map (e.symm : B →+* A) q).IsPrime := by
    exact Ideal.map_isPrime_of_equiv (e.symm : B ≃+* A)
  have hI_le : I ≤ Ideal.map (e.symm : B →+* A) q := by
    intro a ha
    -- Proof comment: contract a mapped containment through the inverse ring equivalence.
    simpa using
      Ideal.mem_map_of_mem (e.symm : B →+* A)
        (hq.2 (Ideal.mem_map_of_mem (e : A →+* B) ha))
  have hq_le_pre : Ideal.map (e.symm : B →+* A) q ≤ p := by
    intro a ha
    have hea : e a ∈ q :=
      (Ideal.symm_apply_mem_of_equiv_iff (I := q) (f := e.symm) (y := a)).2 ha
    exact (Ideal.apply_mem_of_equiv_iff (I := p) (f := e) (x := a)).1 (hq_le hea)
  have hp_le : p ≤ Ideal.map (e.symm : B →+* A) q :=
    hp.2 ⟨hqprime, hI_le⟩ hq_le_pre
  intro b hb
  rcases (Ideal.mem_map_of_equiv (e : A ≃+* B) b).mp hb with ⟨a, ha, rfl⟩
  have hpre : a ∈ Ideal.map (e.symm : B →+* A) q := hp_le ha
  -- Proof comment: map the resulting source-side containment back to the target ideal.
  exact (Ideal.symm_apply_mem_of_equiv_iff (I := q) (f := e.symm) (y := a)).2 hpre

/-- Helper for Chap10 Lemma 10 66 19: weakly associated primes are transported by a ring
equivalence together with a compatible semilinear equivalence of modules. -/
private theorem weaklyAssociatedPrimes_map_ringEquiv_semilinearEquiv
    {A B : Type u} [CommRing A] [CommRing B] (eR : A ≃+* B)
    {N Q : Type x} [AddCommGroup N] [Module A N] [AddCommGroup Q] [Module B Q]
    (eN : N ≃ₛₗ[(eR : A →+* B)] Q)
    {p : Ideal A} (hp : p ∈ weaklyAssociatedPrimes A N) :
    Ideal.map (eR : A →+* B) p ∈ weaklyAssociatedPrimes B Q := by
  rcases hp with ⟨z, hz⟩
  refine ⟨eN z, ?_⟩
  -- Proof comment: compare torsion ideals by semilinearity and then transport minimal primes.
  simpa [torsionOf_semilinearEquiv_eq_map (eR := eR) eN z] using
    ideal_map_mem_minimalPrimes_of_equiv (e := eR) hz

/-- Helper for Chap10 Lemma 10 66 19: mapping an ideal across the raw/canonical tensor
localization equivalence does not change its contraction to `Localization.AtPrime p`. -/
private theorem rawCanonicalIdealComap_map_eq
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime]
    (qS : Ideal (Localization
        (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl))) :
    Ideal.comap (algebraMap (Localization.AtPrime p) (Localization.AtPrime p ⊗[k] F))
        (Ideal.map
          ((ringTensorAtPrimeLocalizationAlgEquiv (k := k) (R := R) (F := F) p).toRingEquiv :
            Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl) →+*
              (Localization.AtPrime p ⊗[k] F)) qS) =
      Ideal.comap (atPrimeToRawTensorLocalization (k := k) (R := R) (F := F) p) qS := by
  let B := Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl)
  let C := Localization.AtPrime p ⊗[k] F
  let eA := ringTensorAtPrimeLocalizationAlgEquiv (k := k) (R := R) (F := F) p
  have hpoint (r : Localization.AtPrime p) :
      (eA.toRingEquiv : B →+* C)
          (atPrimeToRawTensorLocalization (k := k) (R := R) (F := F) p r) =
        algebraMap (Localization.AtPrime p) C r := by
    -- Proof comment: this is exactly the algebra-map compatibility of the raw/canonical
    -- localization comparison.
    exact eA.commutes r
  ext r
  constructor
  · intro hr
    have hmap :
        ((algebraMap (Localization.AtPrime p) C) r) ∈
          Ideal.map (eA.toRingEquiv : B →+* C) qS := by
      simpa [Ideal.mem_comap] using hr
    rcases (Ideal.mem_map_of_equiv (eA.toRingEquiv : B ≃+* C)
        ((algebraMap (Localization.AtPrime p) C) r)).mp hmap with
      ⟨a, ha, heq⟩
    have haeq :
        a = atPrimeToRawTensorLocalization (k := k) (R := R) (F := F) p r := by
      apply eA.toRingEquiv.injective
      calc
        (eA.toRingEquiv : B →+* C) a =
            algebraMap (Localization.AtPrime p) C r := heq
        _ =
            (eA.toRingEquiv : B →+* C)
              (atPrimeToRawTensorLocalization (k := k) (R := R) (F := F) p r) :=
                (hpoint r).symm
    -- Proof comment: after identifying the unique raw preimage, membership is exactly
    -- membership in the raw contraction.
    simpa [Ideal.mem_comap, haeq.symm] using ha
  · intro hr
    have hmem :
        atPrimeToRawTensorLocalization (k := k) (R := R) (F := F) p r ∈ qS := by
      simpa [Ideal.mem_comap] using hr
    have hmap :
        ((algebraMap (Localization.AtPrime p) C) r) ∈
          Ideal.map (eA.toRingEquiv : B →+* C) qS := by
      exact (Ideal.mem_map_of_equiv (eA.toRingEquiv : B ≃+* C)
        ((algebraMap (Localization.AtPrime p) C) r)).mpr
        ⟨atPrimeToRawTensorLocalization (k := k) (R := R) (F := F) p r,
          hmem, by simpa [B, C] using hpoint r⟩
    -- Proof comment: mapped membership is the desired membership in the canonical contraction.
    simpa [Ideal.mem_comap] using hmap

/-- Helper for Chap10 Lemma 10 66 19: an algebra equivalence on the left tensor factor gives a
semilinear equivalence of tensor products with any module over the common base. -/
private theorem tensorLeftAlgEquivSemilinearEquiv_nonempty
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C)
    {N : Type*} [AddCommGroup N] [Module A N] :
    Nonempty ((B ⊗[A] N) ≃ₛₗ[(e.toRingEquiv : B →+* C)] (C ⊗[A] N)) := by
  let fₗ : (B ⊗[A] N) ≃ₗ[A] (C ⊗[A] N) :=
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A N)
  let gₗ : (C ⊗[A] N) ≃ₗ[A] (B ⊗[A] N) :=
    TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl A N)
  let f : (B ⊗[A] N) →ₛₗ[(e.toRingEquiv : B →+* C)] (C ⊗[A] N) := by
    refine
      { toFun := fun z => fₗ z
        map_add' := ?_
        map_smul' := ?_ }
    · intro x y
      simp [fₗ]
    · intro b z
      -- Proof comment: semilinearity is checked on pure tensors, where it is just
      -- multiplicativity of the algebra equivalence on the left factor.
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · simp
      · intro b' n
        simp [fₗ, TensorProduct.smul_tmul']
      · intro z w hz hw
        simp [smul_add, hz, hw]
  let g : (C ⊗[A] N) →ₛₗ[(e.toRingEquiv.symm : C →+* B)] (B ⊗[A] N) := by
    refine
      { toFun := fun z => gₗ z
        map_add' := ?_
        map_smul' := ?_ }
    · intro x y
      simp [gₗ]
    · intro c z
      -- Proof comment: the inverse semilinearity is the same pure-tensor computation with the
      -- inverse algebra equivalence.
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · simp
      · intro c' n
        simp only [gₗ, TensorProduct.smul_tmul', TensorProduct.congr_tmul,
          LinearEquiv.refl_apply]
        have hcoe : ((e.toRingEquiv.symm : C →+* B) c) = e.symm c := rfl
        rw [hcoe]
        simpa [Algebra.smul_def]
      · intro z w hz hw
        simp [smul_add, hz, hw]
  refine ⟨LinearEquiv.ofLinear f g ?_ ?_⟩
  · apply LinearMap.ext
    intro z
    -- Proof comment: the forward-then-backward composite is the identity on pure tensors and
    -- hence on all tensors.
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [f, g, fₗ, gₗ]
    · intro c n
      simp [f, g, fₗ, gₗ]
    · intro z w hz hw
      rw [map_add, hz, hw]
      rfl
  · apply LinearMap.ext
    intro z
    -- Proof comment: the backward-then-forward composite is verified by the same tensor
    -- induction.
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [f, g, fₗ, gₗ]
    · intro b n
      simp [f, g, fₗ, gₗ]
    · intro z w hz hw
      rw [map_add, hz, hw]
      rfl

/-- Helper for Chap10 Lemma 10 66 19: a linear equivalence, a semilinear equivalence, and a
target-side linear equivalence compose to a semilinear equivalence. -/
private theorem linearSemilinearLinear_trans_nonempty
    {A B : Type*} [CommRing A] [CommRing B] (eR : A ≃+* B)
    {N N' Q' Q : Type*}
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup Q'] [AddCommGroup Q]
    [Module A N] [Module A N'] [Module B Q'] [Module B Q]
    (e₁ : N ≃ₗ[A] N')
    (h₂ : Nonempty (N' ≃ₛₗ[(eR : A →+* B)] Q'))
    (e₃ : Q' ≃ₗ[B] Q) :
    Nonempty (N ≃ₛₗ[(eR : A →+* B)] Q) := by
  rcases h₂ with ⟨e₂⟩
  -- Proof comment: the local equivalences are linear over the source and target rings, so
  -- ordinary `LinearEquiv.trans` supplies exactly the required semilinear composite.
  exact ⟨(e₁.trans e₂).trans e₃⟩

/-- Helper for Chap10 Lemma 10 66 19: an algebra equivalence over `R ⊗[k] F` transports the
raw localized owner to the canonical local owner. -/
private theorem exists_rawLocalizedOwnerSemilinearEquivCanonical_overTensorRing
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime]
    (eA :
      Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl) ≃ₐ[R ⊗[k] F]
        (Localization.AtPrime p ⊗[k] F)) :
    ∃ _eN : LocalizedModule
        (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl)
        (((R ⊗[k] F) ⊗[R] M)) ≃ₛₗ[
          (eA.toRingEquiv :
            Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl) →+*
              (Localization.AtPrime p ⊗[k] F))]
          (((Localization.AtPrime p ⊗[k] F) ⊗[Localization.AtPrime p]
            LocalizedModule.AtPrime p M)),
      True := by
  let A := R ⊗[k] F
  let B := Localization (Algebra.algebraMapSubmonoid A p.primeCompl)
  let C := Localization.AtPrime p ⊗[k] F
  let N := (R ⊗[k] F) ⊗[R] M
  let e₁ :
      LocalizedModule (Algebra.algebraMapSubmonoid A p.primeCompl) N ≃ₗ[B] B ⊗[A] N :=
    LocalizedModule.equivTensorProduct (Algebra.algebraMapSubmonoid A p.primeCompl) N
  have h₂ :
      Nonempty ((B ⊗[A] N) ≃ₛₗ[(eA.toRingEquiv : B →+* C)] (C ⊗[A] N)) :=
    tensorLeftAlgEquivSemilinearEquiv_nonempty (e := eA) (N := N)
  let e₃ :
      (C ⊗[A] N) ≃ₗ[C] ((Localization.AtPrime p ⊗[k] F) ⊗[Localization.AtPrime p]
        LocalizedModule.AtPrime p M) :=
    canonicalLocalOwner_tensorOverTensorRing_linearEquiv (k := k) (R := R) (M := M) (F := F) p
  rcases linearSemilinearLinear_trans_nonempty
      (eR := eA.toRingEquiv) e₁ h₂ e₃ with ⟨eN⟩
  -- Proof comment: the three canonical comparisons now give the requested raw-to-canonical
  -- semilinear equivalence without any dependent cast of its ring hom.
  exact ⟨eN, trivial⟩

/-- Helper for Chap10 Lemma 10 66 19: the raw localized owner is semilinearly equivalent to the
canonical local owner over `ringTensorAtPrimeLocalizationAlgEquiv p`. -/
private theorem exists_rawLocalizedOwnerSemilinearEquivCanonical
    {F : Type*} [Field F] [Algebra k F] (p : Ideal R) [p.IsPrime] :
    ∃ _eN : LocalizedModule
        (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl)
        (((R ⊗[k] F) ⊗[R] M)) ≃ₛₗ[
          ((ringTensorAtPrimeLocalizationAlgEquiv (k := k) (R := R) (F := F) p).toRingEquiv :
            Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl) →+*
              (Localization.AtPrime p ⊗[k] F))]
          (((Localization.AtPrime p ⊗[k] F) ⊗[Localization.AtPrime p]
            LocalizedModule.AtPrime p M)),
      True := by
  obtain ⟨eN, htriv⟩ :=
    exists_rawLocalizedOwnerSemilinearEquivCanonical_overTensorRing
      (k := k) (R := R) (M := M) (F := F) p
      (ringTensorAtPrimeLocalizationAlgEquivOverTensorRing
        (k := k) (R := R) (F := F) p)
  -- Proof comment: the selected algebra equivalence has the raw/canonical ring equivalence as
  -- its underlying `RingEquiv` by definition, so no semilinear transport remains.
  exact ⟨eN, htriv⟩

/-- Helper for Chap10 Lemma 10 66 19: a raw localized weakly associated prime over
`Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) p.primeCompl)` transports to the canonical
local owner over `Localization.AtPrime p ⊗[k] F`. -/
private theorem rawLocalizedWeaklyAssociatedPrime_transport_canonical_owner
    {F : Type*} [Field F] [Algebra k F]
    {q : Ideal (R ⊗[k] F)} [q.IsPrime]
    {qS : Ideal (Localization
        (Algebra.algebraMapSubmonoid (R ⊗[k] F) (q.under R).primeCompl))}
    (hqS : qS ∈ weaklyAssociatedPrimes
          (Localization
            (Algebra.algebraMapSubmonoid (R ⊗[k] F) (q.under R).primeCompl))
          (LocalizedModule
            (Algebra.algebraMapSubmonoid (R ⊗[k] F) (q.under R).primeCompl)
            (((R ⊗[k] F) ⊗[R] M))))
    (hqS_under :
      Ideal.comap (atPrimeToRawTensorLocalization (k := k) (R := R) (F := F) (q.under R)) qS =
        IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))) :
    ∃ qLoc : Ideal (Localization.AtPrime (q.under R) ⊗[k] F),
      qLoc ∈ weaklyAssociatedPrimes (Localization.AtPrime (q.under R) ⊗[k] F)
          (((Localization.AtPrime (q.under R) ⊗[k] F) ⊗[Localization.AtPrime (q.under R)]
            LocalizedModule.AtPrime (q.under R) M)) ∧
        qLoc.under (Localization.AtPrime (q.under R)) =
          IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R)) := by
  let B := Localization (Algebra.algebraMapSubmonoid (R ⊗[k] F) (q.under R).primeCompl)
  let C := Localization.AtPrime (q.under R) ⊗[k] F
  let eA := ringTensorAtPrimeLocalizationAlgEquiv (k := k) (R := R) (F := F) (q.under R)
  obtain ⟨eN, -⟩ :=
    exists_rawLocalizedOwnerSemilinearEquivCanonical
      (k := k) (R := R) (M := M) (F := F) (q.under R)
  have hpoint (r : Localization.AtPrime (q.under R)) :
      (eA.toRingEquiv : B →+* C)
          (atPrimeToRawTensorLocalization (k := k) (R := R) (F := F) (q.under R) r) =
        algebraMap (Localization.AtPrime (q.under R)) C r := by
    -- Proof comment: the raw/canonical ring comparison is an `R_p`-algebra equivalence, so it
    -- carries the raw structure map from `R_p` to the canonical structure map.
    exact eA.commutes r
  refine ⟨Ideal.map (eA.toRingEquiv : B →+* C) qS, ?_, ?_⟩
  · -- Proof comment: weak association is transported across the ring equivalence and the
    -- corresponding semilinear equivalence of owner modules.
    exact weaklyAssociatedPrimes_map_ringEquiv_semilinearEquiv
      (eR := eA.toRingEquiv) eN hqS
  · -- Proof comment: contraction to `R_p` is unchanged because the algebra equivalence commutes
    -- with the two maps out of `R_p`; the named helper records that contraction bridge.
    calc
      (Ideal.map (eA.toRingEquiv : B →+* C) qS).under
          (Localization.AtPrime (q.under R)) =
        Ideal.comap (atPrimeToRawTensorLocalization (k := k) (R := R) (F := F) (q.under R))
          qS := by
          simpa [B, C, Ideal.under] using
            rawCanonicalIdealComap_map_eq
              (k := k) (R := R) (F := F) (q.under R) qS
      _ = IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R)) := hqS_under

/-- Helper for Chap10 Lemma 10 66 19: a finite span over a local ring is zero if all its
generators lie in the maximal ideal times that same span. -/
private theorem finiteSpan_eq_bot_of_le_maximal_smul
    {A : Type*} [CommRing A] [IsLocalRing A]
    {N : Type*} [AddCommGroup N] [Module A N] (s : Finset N)
    (hs :
      Submodule.span A (s : Set N) ≤
        IsLocalRing.maximalIdeal A • Submodule.span A (s : Set N)) :
    Submodule.span A (s : Set N) = ⊥ := by
  have hmax_le_jac :
      IsLocalRing.maximalIdeal A ≤ Ring.jacobson A := by
    -- Proof comment: the maximal ideal of a local ring is contained in the ring Jacobson radical.
    simpa [Ideal.jacobson_bot] using
      IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A)
  have hle_jac :
      Submodule.span A (s : Set N) ≤
        Ring.jacobson A • Submodule.span A (s : Set N) :=
    hs.trans (Submodule.smul_mono hmax_le_jac le_rfl)
  -- Proof comment: the finite span is finitely generated, so Nakayama forces it to be zero.
  exact
    Submodule.FG.eq_bot_of_le_jacobson_smul
      (Submodule.fg_span (R := A) (s := (s : Set N)) s.finite_toSet)
      hle_jac

/-- Helper for Chap10 Lemma 10 66 19: a nonzero generator of a finite span over a local ring
has some generator whose image modulo `IsLocalRing.maximalIdeal A • span` is nonzero. -/
private theorem exists_generator_notMem_maximal_smul_span
    {A : Type*} [CommRing A] [IsLocalRing A]
    {N : Type*} [AddCommGroup N] [Module A N] (s : Finset N)
    {x : N} (hxs : x ∈ s) (hx : x ≠ 0) :
    ∃ y ∈ s, y ∉ IsLocalRing.maximalIdeal A • Submodule.span A (s : Set N) := by
  by_contra hnone
  have hs :
      Submodule.span A (s : Set N) ≤
        IsLocalRing.maximalIdeal A • Submodule.span A (s : Set N) := by
    -- Proof comment: if every listed generator dies in the quotient, then the whole finite span
    -- is contained in the maximal-ideal multiple of itself.
    rw [Submodule.span_le]
    intro y hy
    by_contra hymem
    exact hnone ⟨y, hy, hymem⟩
  have hspan_bot : Submodule.span A (s : Set N) = ⊥ :=
    finiteSpan_eq_bot_of_le_maximal_smul (A := A) (N := N) s hs
  have hxmem : x ∈ Submodule.span A (s : Set N) :=
    Submodule.subset_span hxs
  -- Proof comment: Nakayama has made the span zero, contradicting the chosen nonzero generator.
  exact hx (by simpa [hspan_bot] using hxmem)

/-- Helper for Chap10 Lemma 10 66 19: in the purely transcendental local-owner model, every
element outside the extended maximal ideal acts regularly. -/
private theorem isSMulRegular_canonicalLocalOwner_purelyTranscendental_of_notMem_extendedMaximal
    {L : Type*} [Field L] [Algebra k L]
    {ι : Type*} (x : ι → L) (hx : IsTranscendenceBasis k x)
    (F : IntermediateField k L) (hF : F = IntermediateField.adjoin k (Set.range x))
    {p : Ideal R} [p.IsPrime]
    (hDomainResidue :
      IsDomain
        ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).ResidueField ⊗[k] F))
    {g : Localization.AtPrime p ⊗[k] F}
    (hg :
      g ∉ Ideal.map
        (algebraMap (Localization.AtPrime p)
          (Localization.AtPrime p ⊗[k] F))
        (IsLocalRing.maximalIdeal (Localization.AtPrime p))) :
    IsSMulRegular
      (((Localization.AtPrime p ⊗[k] F) ⊗[
          Localization.AtPrime p] LocalizedModule.AtPrime p M)) g := by
  -- TODO: prove the source finite-carrier/Nakayama paragraph.  For a nonzero tensor `z`, choose
  -- a finite `R_p`-submodule of `LocalizedModule.AtPrime p M` carrying all coefficients of `z`,
  -- find a coefficient nonzero modulo `IsLocalRing.maximalIdeal Rp • span`, map `z` to that
  -- special fiber, and use `hDomainResidue` plus the nonzero residue of `g` to contradict
  -- `g • z = 0`.
  sorry

/-- Helper for Lemma 10.66.19: in the purely transcendental case, the remaining source argument
reduces contraction of a weakly associated prime on the owner base change to weak association on
the base module. -/
private theorem maximalIdeal_mem_weaklyAssociatedPrimes_canonical_owner_purelyTranscendental
    {L : Type*} [Field L] [Algebra k L]
    {ι : Type*} (x : ι → L) (hx : IsTranscendenceBasis k x)
    {qF : Ideal (R ⊗[k] IntermediateField.adjoin k (Set.range x))} [qF.IsPrime]
    (hqF :
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] IntermediateField.adjoin k (Set.range x))
        (((R ⊗[k] IntermediateField.adjoin k (Set.range x)) ⊗[R] M)))
    (hDomainResidue :
      IsDomain
        ((IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R))).ResidueField ⊗[k]
          IntermediateField.adjoin k (Set.range x))) :
    IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R)) ∈
      weaklyAssociatedPrimes (Localization.AtPrime (qF.under R))
        (((Localization.AtPrime (qF.under R) ⊗[k]
            IntermediateField.adjoin k (Set.range x)) ⊗[Localization.AtPrime (qF.under R)]
          LocalizedModule.AtPrime (qF.under R) M)) := by
  -- Route correction: the literal localized owner has already been replaced by the canonical
  -- owner over `R_p`, so only the source local regularity/Nakayama paragraph remains.
  let F : IntermediateField k L := IntermediateField.adjoin k (Set.range x)
  let p : Ideal R := qF.under R
  let Rp := Localization.AtPrime p
  letI : Module (Rp ⊗[k] F) (Rp ⊗[k] F) := Semiring.toModule
  letI : DistribMulAction (Rp ⊗[k] F) (Rp ⊗[k] F) :=
    (Semiring.toModule : Module (Rp ⊗[k] F) (Rp ⊗[k] F)).toDistribMulAction
  letI : DistribMulAction (Rp ⊗[k] F)
      ((Rp ⊗[k] F) ⊗[Rp] LocalizedModule.AtPrime p M) :=
    TensorProduct.leftDistribMulAction
  letI : Module (Rp ⊗[k] F)
      ((Rp ⊗[k] F) ⊗[Rp] LocalizedModule.AtPrime p M) :=
    TensorProduct.leftModule
  have hlocalized :
      ∃ qLoc : Ideal (Rp ⊗[k] F),
        qLoc ∈ weaklyAssociatedPrimes (Rp ⊗[k] F)
            (((Rp ⊗[k] F) ⊗[Rp] LocalizedModule.AtPrime p M)) ∧
          qLoc.under Rp = IsLocalRing.maximalIdeal Rp :=
    by
      have hraw :=
        localizedTensorWeaklyAssociatedPrimeRaw
          (k := k) (R := R) (M := M) (F := F) (q := qF) hqF
      rcases hraw with ⟨qS, hqS, hqS_comap⟩
      have hqS_under :
          Ideal.comap (atPrimeToRawTensorLocalization (k := k) (R := R) (F := F) p) qS =
            IsLocalRing.maximalIdeal Rp := by
        -- Proof comment: the raw-localized prime already lies over the maximal ideal of `R_p`;
        -- the remaining gap is only module/ring transport to the canonical tensor owner.
        simpa [p, Rp] using
          rawLocalizedWeaklyAssociatedPrime_comap_atPrime_eq_maximal
            (k := k) (R := R) (M := M) (F := F) (q := qF) (qS := qS) hqS hqS_comap
      -- TODO: transport `hqS` from the raw localized tensor ring to `Rp ⊗[k] F` through
      -- `ringTensorAtPrimeLocalizationAlgEquiv`, transport the localized owner module through
      -- `owner_localizedModule_atPrime_under_linearEquiv`, and rewrite the contraction using
      -- `hqS_under`.
      exact
        rawLocalizedWeaklyAssociatedPrime_transport_canonical_owner
          (k := k) (R := R) (M := M) (F := F) (q := qF) (qS := qS) hqS hqS_under
  have hregular :
      ∀ g : (Rp ⊗[k] F),
        g ∉ Ideal.map (algebraMap Rp (Rp ⊗[k] F)) (IsLocalRing.maximalIdeal Rp) →
          IsSMulRegular (((Rp ⊗[k] F) ⊗[Rp] LocalizedModule.AtPrime p M)) g :=
    by
      intro g hg
      -- Proof comment: the only remaining source argument is the pure-transcendental
      -- nonzerodivisor theorem in the canonical local-owner shape.
      exact
        isSMulRegular_canonicalLocalOwner_purelyTranscendental_of_notMem_extendedMaximal
          (k := k) (R := R) (M := M) (L := L) x hx F rfl (p := p) hDomainResidue hg
  have hlocal :
      IsLocalRing.maximalIdeal Rp ∈
        weaklyAssociatedPrimes Rp (((Rp ⊗[k] F) ⊗[Rp] LocalizedModule.AtPrime p M)) :=
    by
      -- Proof comment: the remaining local paragraph only needs one localized prime over the
      -- canonical owner and regularity away from the extended maximal ideal.
      rcases hlocalized with ⟨qLoc, hqLoc, hqLoc_under⟩
      letI : IsScalarTower Rp (Rp ⊗[k] F)
          (((Rp ⊗[k] F) ⊗[Rp] LocalizedModule.AtPrime p M)) :=
        canonicalLocalOwnerIsScalarTower (k := k) (R := R) (M := M) (F := F) (p := p)
      exact
        maximalIdeal_mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_local
          (R := Rp) (A := Rp ⊗[k] F)
          (N := ((Rp ⊗[k] F) ⊗[Rp] LocalizedModule.AtPrime p M))
          hregular hqLoc_under hqLoc
  -- Proof comment: unfold the local abbreviations to recover the exact target owner module.
  simpa [F, p, Rp] using hlocal

/-- Helper for Lemma 10.66.19: in the purely transcendental case, the remaining source argument
reduces contraction of a weakly associated prime on the owner base change to weak association on
the base module. -/
private theorem maximalIdeal_mem_weaklyAssociatedPrimes_localized_owner_purelyTranscendental
    {L : Type*} [Field L] [Algebra k L]
    {ι : Type*} (x : ι → L) (hx : IsTranscendenceBasis k x)
    {qF : Ideal (R ⊗[k] IntermediateField.adjoin k (Set.range x))} [qF.IsPrime]
    (hqF :
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] IntermediateField.adjoin k (Set.range x))
        (((R ⊗[k] IntermediateField.adjoin k (Set.range x)) ⊗[R] M)))
    (hDomainResidue :
      IsDomain
        ((IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R))).ResidueField ⊗[k]
          IntermediateField.adjoin k (Set.range x))) :
    IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R)) ∈
      weaklyAssociatedPrimes (Localization.AtPrime (qF.under R))
        (LocalizedModule.AtPrime (qF.under R)
          (((R ⊗[k] IntermediateField.adjoin k (Set.range x)) ⊗[R] M))) := by
  let F : IntermediateField k L := IntermediateField.adjoin k (Set.range x)
  have hcanonical :
      IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R)) ∈
        weaklyAssociatedPrimes (Localization.AtPrime (qF.under R))
          (((Localization.AtPrime (qF.under R) ⊗[k] F) ⊗[Localization.AtPrime (qF.under R)]
            LocalizedModule.AtPrime (qF.under R) M)) :=
    maximalIdeal_mem_weaklyAssociatedPrimes_canonical_owner_purelyTranscendental
      (k := k) (R := R) (M := M) (L := L) x hx hqF hDomainResidue
  have hEq :
      weaklyAssociatedPrimes (Localization.AtPrime (qF.under R))
          (LocalizedModule.AtPrime (qF.under R) (((R ⊗[k] F) ⊗[R] M))) =
        weaklyAssociatedPrimes (Localization.AtPrime (qF.under R))
          (((Localization.AtPrime (qF.under R) ⊗[k] F) ⊗[Localization.AtPrime (qF.under R)]
            LocalizedModule.AtPrime (qF.under R) M)) := by
    -- Proof comment: the literal localization of the owner module and the canonical owner over
    -- `R_p` are already identified by the frozen localization comparison.
    simpa [F] using
      LinearEquiv.weaklyAssociatedPrimes_eq
        (owner_localizedModule_atPrime_under_linearEquiv
          (k := k) (R := R) (M := M) (F := F) (qF.under R))
  -- Proof comment: transport the canonical owner statement back to the localized owner model.
  rw [hEq]
  exact hcanonical

/-- Helper for Lemma 10.66.19: in the purely transcendental case, the remaining source argument
reduces contraction of a weakly associated prime on the owner base change to weak association on
the base module. -/
private theorem under_mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_purelyTranscendental_owner
    {L : Type*} [Field L] [Algebra k L]
    {ι : Type*} (x : ι → L) (hx : IsTranscendenceBasis k x)
    {qF : Ideal (R ⊗[k] IntermediateField.adjoin k (Set.range x))} [qF.IsPrime]
    (hqF :
      qF ∈ weaklyAssociatedPrimes (R ⊗[k] IntermediateField.adjoin k (Set.range x))
        (((R ⊗[k] IntermediateField.adjoin k (Set.range x)) ⊗[R] M))) :
    qF.under R ∈ weaklyAssociatedPrimes R M := by
  let F : IntermediateField k L := IntermediateField.adjoin k (Set.range x)
  have hDomainResidue :
      IsDomain
        ((IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R))).ResidueField ⊗[k] F) := by
    -- Proof comment: the residue-field tensor with the purely transcendental stage is a domain,
    -- exactly as in the source paragraph.
    simpa [F] using
      isDomain_residueField_tensor_adjoin
        (k := k) (R := R) (L := L) x hx (p := qF.under R)
  have hlocalized :
      IsLocalRing.maximalIdeal (Localization.AtPrime (qF.under R)) ∈
        weaklyAssociatedPrimes (Localization.AtPrime (qF.under R))
          (LocalizedModule.AtPrime (qF.under R) (((R ⊗[k] F) ⊗[R] M))) :=
    maximalIdeal_mem_weaklyAssociatedPrimes_localized_owner_purelyTranscendental
      (k := k) (R := R) (M := M) (L := L) x hx hqF hDomainResidue
  have howner :
      qF.under R ∈ weaklyAssociatedPrimes R (((R ⊗[k] F) ⊗[R] M)) := by
    -- Proof comment: descend from the maximal ideal of the localization back to the contracted
    -- prime of the owner module by Lemma `10.66.2`.
    have howner' :
        Ideal.IsWeaklyAssociatedToModule R (((R ⊗[k] F) ⊗[R] M)) (qF.under R) := by
      exact
        (isWeaklyAssociatedToModule_iff_isWeaklyAssociatedToModule_maximalIdeal_atPrime
          (R := R) (M := ((R ⊗[k] F) ⊗[R] M)) (qF.under R)).mpr <|
          by simpa [mem_weaklyAssociatedPrimes_iff] using hlocalized
    simpa [mem_weaklyAssociatedPrimes_iff] using howner'
  -- Proof comment: once the owner module over `R` has the contracted weakly associated prime,
  -- the already-proved owner-to-`M` descent finishes the purely transcendental case.
  simpa [F] using
    mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_owner_baseChange
      (k := k) (K := F) (R := R) (M := M) howner

/- Lemma 10.66.19 is proved first at the `core/canonical` owner layer `Mₖ`. The textbook tensor
presentation `M ⊗[k] K` is handled separately as derived bridge API. -/
-- Proof sketch: first reduce to a finitely generated intermediate field extension and then to the
-- purely transcendental case, using flatness, going-down, and the finite-extension comparison for
-- weakly associated primes. After localizing at the contraction `q.under R`, show that every
-- element of `Rₖ \ (q.under R)Rₖ` acts as a nonzerodivisor on the base change, deduce that powers
-- of elements of `q.under R` annihilate a witness vector for `q`, and finally descend weak
-- association from the direct-sum decomposition of the scalar extension back to `M`.
/-- Lemma 10.66.19 in canonical owner form: if `q` is weakly associated to the canonical base
change `Mₖ = (R ⊗[k] K) ⊗[R] M`, then its contraction `q.under R` is weakly associated to
`M`. -/
@[stacks 0CUB]
theorem under_mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_baseChange
    (q : Ideal Rₖ) (hq : q ∈ weaklyAssociatedPrimes Rₖ Mₖ) :
    q.under R ∈ weaklyAssociatedPrimes R M := by
  -- Route correction: the naive flat-contraction shortcut fails because Lemma `10.40.4` compares
  -- annihilators only for pure tensors `1 ⊗ m`, not for an arbitrary witness in `Mₖ`.
  -- First carry out the source descent to a finitely generated intermediate field.
  obtain ⟨L, hLfg, qL, hqL, hunder⟩ :=
    exists_finitely_generated_intermediate_weakAss_descent_owner
      (k := k) (K := K) (R := R) (M := M) q hq
  obtain ⟨x, hx, hfd⟩ :=
    exists_purely_transcendental_subextension_finiteDimensional
      (k := k) (K := K) L hLfg
  let F : IntermediateField k L := IntermediateField.adjoin k (Set.range x)
  have hFL : FiniteDimensional F L := by
    simpa [F] using hfd
  obtain ⟨qF, hqF, hqF_under⟩ :=
    exists_purely_transcendental_intermediate_weakAss_descent_owner
      (k := k) (R := R) (M := M) F hqL
  letI : qF.IsPrime := hqF.isPrime
  -- After the finite-stage descent, only the source's purely transcendental closing paragraph
  -- remains. Apply that closing step at the `F = k(x_i)` stage and rewrite the contraction.
  have hqF_base :
      qF.under R ∈ weaklyAssociatedPrimes R M := by
    simpa [F] using
      under_mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_purelyTranscendental_owner
        (k := k) (R := R) (M := M) (L := L) x hx hqF
  have hqF_under' : qF.under R = q.under R := by
    simpa [hunder] using hqF_under
  simpa [hqF_under'] using hqF_base

end

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {R : Type w} [CommRing R] [Algebra k R]
variable {M : Type x} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

local notation "Rₖ" => R ⊗[k] K
local notation "Mₖ" => Rₖ ⊗[R] M

local instance : Module Rₖ Mₖ :=
  TensorProduct.leftModule

private noncomputable def textbookBaseChangeAddEquiv : M ⊗[k] K ≃+ Mₖ :=
  ((Algebra.IsPushout.cancelBaseChange k K R Rₖ M).toAddEquiv.trans
    (TensorProduct.comm k K M).toAddEquiv).symm

private noncomputable local instance : Module Rₖ (M ⊗[k] K) :=
  (show M ⊗[k] K ≃+ Mₖ from textbookBaseChangeAddEquiv).module Rₖ

private noncomputable def textbookBaseChangeLinearEquiv : M ⊗[k] K ≃ₗ[Rₖ] Mₖ :=
  (show M ⊗[k] K ≃+ Mₖ from textbookBaseChangeAddEquiv).linearEquiv Rₖ

/-- The textbook tensor model `M ⊗[k] K` and the canonical owner base change `Mₖ` have the same
weakly associated primes over `R ⊗[k] K`. -/
theorem weaklyAssociatedPrimes_textbook_baseChange_eq_canonicalBaseChange :
    weaklyAssociatedPrimes Rₖ (M ⊗[k] K) = weaklyAssociatedPrimes Rₖ Mₖ := by
  simpa using LinearEquiv.weaklyAssociatedPrimes_eq textbookBaseChangeLinearEquiv

/-- Lemma 10.66.19 in the source-facing textbook tensor model: if `q ⊂ R ⊗[k] K` lies over
`p ⊂ R` and `q` is weakly associated to `M ⊗[k] K`, then `p` is weakly associated to `M`. -/
@[stacks 0CUB]
theorem mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_baseChange_of_liesOver
    (p : Ideal R) (q : Ideal Rₖ) (hqover : q.LiesOver p)
    (hq : q ∈ weaklyAssociatedPrimes Rₖ (M ⊗[k] K)) :
    p ∈ weaklyAssociatedPrimes R M := by
  letI : q.LiesOver p := hqover
  have hq' : q ∈ weaklyAssociatedPrimes Rₖ Mₖ := by
    rw [← weaklyAssociatedPrimes_textbook_baseChange_eq_canonicalBaseChange]
    exact hq
  simpa [q.over_def p] using
    under_mem_weaklyAssociatedPrimes_of_mem_weaklyAssociatedPrimes_baseChange q hq'

end
