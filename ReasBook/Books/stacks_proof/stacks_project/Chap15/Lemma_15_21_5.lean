import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import StacksProject_2024.Chap10.Lemma_10_36_17
import StacksProject_2024.Chap10.Lemma_10_39_8
import StacksProject_2024.Chap10.Lemma_10_101_5
import StacksProject_2024.Chap15.Lemma_15_16_1
import StacksProject_2024.Chap15.Lemma_15_21_3
import StacksProject_2024.Chap15.Lemma_15_21_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open PrimeSpectrum
open scoped TensorProduct BigOperators

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [Module.Finite R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: flatness descent for modules under finite injective base change over Noetherian
  rings;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `flat_of_nilpotent_ideal_of_injective_algebraMap_of_flat_mod_ideal_and_flat_baseChange`,
  `flat_of_isArtinianRing_of_injective_algebraMap_of_flat_tensorProduct`,
  `Module.Flat.of_flat_tensorProduct`;
- best owner abstraction: the canonical flatness predicate `Module.Flat`, with the Chapter 10
  nilpotent-ideal descent criterion as the upstream owner theorem in the minimal dependency
  closure;
- primitive data: the Noetherian base ring `R`, the finite `R`-algebra `S`, the injective algebra
  map `R → S`, and the `R`-module `M`;
- derived API: flatness of the base-changed module `S ⊗[R] M`, expressed in the canonical Lean
  model of base change rather than through a parallel wrapper or renamed tensor-product owner.

Layering:
- this item is `source-facing`: it is the Noetherian finite-extension descent statement from the
  source text;
- `core/canonical`: `Module.Flat` and the Chapter 10 owner theorem
  `flat_of_nilpotent_ideal_of_injective_algebraMap_of_flat_mod_ideal_and_flat_baseChange`;
- companion source-facing specialization already upstream:
  `flat_of_isArtinianRing_of_injective_algebraMap_of_flat_tensorProduct`;
- no separate `bridge/view` declaration is warranted here.
-/

omit [IsNoetherianRing R] in
/-- Helper for Lemma 15.21.5: a finite free injective algebra map is faithfully flat. -/
lemma algebraMap_faithfullyFlat_of_injective_moduleFinite_moduleFree
    {R' : Type*} [CommRing R'] [Algebra R R']
    [Module.Finite R R'] [Module.Free R R']
    (hinj : Function.Injective (algebraMap R R')) :
    (algebraMap R R').FaithfullyFlat := by
  have hIntegral : (algebraMap R R').IsIntegral := by
    rw [algebraMap_isIntegral_iff]
    infer_instance
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  constructor
  · -- Free modules are flat, so the algebra map is flat.
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · -- Integral extensions with injective structure map are surjective on spectra.
    simpa using RingHom.IsIntegral.comap_surjective hIntegral hinj

/-- Helper for Lemma 15.21.5: if an ideal cuts out all of `Spec R`, then it is nilpotent in the
Noetherian ring `R`. -/
lemma isNilpotent_of_zeroLocus_eq_univ_of_isNoetherian
    (I : Ideal R) (hzero : zeroLocus (I : Set R) = Set.univ) :
    IsNilpotent I := by
  -- The zero-locus criterion places the ideal inside the nilradical.
  have hle : I ≤ nilradical R := (zeroLocus_eq_univ_iff (I : Set R)).1 hzero
  -- In a Noetherian ring every ideal is finitely generated, so containment in the nilradical
  -- upgrades to nilpotence.
  exact (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian I)).2 hle

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.5: an algebra map from `S` to `R ⧸ I` should turn flatness of
`S ⊗[R] M` into flatness of the quotient module `M / IM`. -/
lemma ideal_isFlatQuotient_of_algebraMap_to_quotient
    (I : Ideal R) (Φ : S →ₐ[R] R ⧸ I)
    (hflat : Module.Flat S (S ⊗[R] M)) :
    Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) := by
  let _ : Algebra S (R ⧸ I) := Φ.toAlgebra
  let _ : Module.Flat S (S ⊗[R] M) := hflat
  have hbase : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[S] (S ⊗[R] M)) := by
    -- First base change the given flat `S`-module along `Φ : S → R ⧸ I`.
    simpa using (Module.Flat.baseChange (R := S) (S := R ⧸ I) (M := S ⊗[R] M))
  let eCancel :
      ((R ⧸ I) ⊗[S] (S ⊗[R] M)) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] M) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S (R ⧸ I) (R ⧸ I) M
  let f :
      (R ⧸ I) →ₗ[R ⧸ I] M →ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
    (LinearMap.ringLmapEquivSelf (R ⧸ I) (R ⧸ I)
      (M →ₗ[R] M ⧸ (I • (⊤ : Submodule R M)))).symm
      ((I • (⊤ : Submodule R M)).mkQ)
  let e₀ : ((R ⧸ I) ⊗[R] M) →ₗ[R ⧸ I] M ⧸ (I • (⊤ : Submodule R M)) :=
    TensorProduct.AlgebraTensorModule.lift f
  have e₀_apply (y : M) :
      e₀ ((1 : R ⧸ I) ⊗ₜ[R] y) = (I • (⊤ : Submodule R M)).mkQ y := by
    -- On the canonical tensor generator, the lifted map is the quotient projection.
    simp [e₀, f]
  have e₀_restrictScalars :
      e₀.restrictScalars R = (TensorProduct.quotTensorEquivQuotSMul M I).toLinearMap := by
    -- Compare the quotient model with the standard `R`-linear tensor/quotient equivalence.
    apply TensorProduct.ext'
    intro q y
    refine Quotient.inductionOn q ?_
    intro a
    change e₀ (Ideal.Quotient.mk I a ⊗ₜ[R] y) =
      TensorProduct.quotTensorEquivQuotSMul M I (Ideal.Quotient.mk I a ⊗ₜ[R] y)
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    simp [e₀, f]
    simpa using (algebraMap_smul (R ⧸ I) a (Submodule.Quotient.mk y))
  have hbij :
      Function.Bijective e₀ := by
    constructor
    · intro u v huv
      have huv' : e₀.restrictScalars R u = e₀.restrictScalars R v := huv
      rw [e₀_restrictScalars] at huv'
      exact (TensorProduct.quotTensorEquivQuotSMul M I).injective huv'
    · intro z
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) z
      exact ⟨(1 : R ⧸ I) ⊗ₜ[R] y, e₀_apply y⟩
  let eQuot :
      ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] M ⧸ (I • (⊤ : Submodule R M)) :=
    LinearEquiv.ofBijective e₀ hbij
  let _ : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[S] (S ⊗[R] M)) := hbase
  have hquot : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) := by
    -- Then transport flatness through the canonical base-change cancellation and quotient model.
    exact Module.Flat.of_linearEquiv (eCancel.trans eQuot).symm
  exact hquot

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.5: flatness of `S ⊗[R] M` over `S` survives the finite free base
change `R → R'`, after rewriting the tensor object into the source-facing order. -/
lemma flat_baseChange_tensorProduct_of_flat_tensorProduct
    {R' : Type*} [CommRing R'] [Algebra R R']
    (hflat : Module.Flat S (S ⊗[R] M)) :
    Module.Flat (R' ⊗[R] S) ((R' ⊗[R] S) ⊗[R'] (R' ⊗[R] M)) := by
  let S' := R' ⊗[R] S
  let _ : Module.Flat S (S ⊗[R] M) := hflat
  have hbase : Module.Flat S' (S' ⊗[S] (S ⊗[R] M)) := by
    -- Base change the flat `S`-module along the right tensor inclusion `S → S'`.
    simpa [S'] using (Module.Flat.baseChange (R := S) (S := S') (M := S ⊗[R] M))
  let eLeft : S' ⊗[S] (S ⊗[R] M) ≃ₗ[S'] S' ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M
  let eRight : S' ⊗[R'] (R' ⊗[R] M) ≃ₗ[S'] S' ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R R' S' S' M
  let _ : Module.Flat S' (S' ⊗[S] (S ⊗[R] M)) := hbase
  -- Both tensor presentations identify with `S' ⊗[R] M`, so flatness transfers to the
  -- source-facing `R'`-tensor order needed later in the split-presentation argument.
  exact Module.Flat.of_linearEquiv (eRight.trans eLeft.symm)

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.5: after evaluating at the tuple `α(·, k ·)`, every element of
`ker θ` maps to zero in the evaluation-image quotient. -/
lemma eval_aeval_quotient_eq_zero_of_mem_kernel
    {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S']
    {n : ℕ} {d : Fin n → ℕ} {α : ∀ i : Fin n, Fin (d i) → R'}
    (θ : MvPolynomial (Fin n) R' →ₐ[R'] S')
    (k : ∀ i : Fin n, Fin (d i))
    {p : MvPolynomial (Fin n) R'}
    (hp : p ∈ RingHom.ker θ.toRingHom) :
    MvPolynomial.aeval
        (fun i ↦
          Ideal.Quotient.mk
            (Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) (RingHom.ker θ.toRingHom))
            (α i (k i))) p = 0 := by
  let evk : MvPolynomial (Fin n) R' →ₐ[R'] R' := MvPolynomial.aeval fun i ↦ α i (k i)
  let Jk : Ideal R' := Ideal.map evk (RingHom.ker θ.toRingHom)
  -- Evaluating in the quotient is the same as evaluating in `R'` and then taking the quotient
  -- class, so membership in the mapped ideal forces the result to vanish.
  have hEval :
      MvPolynomial.aeval
        (fun i ↦
          Ideal.Quotient.mk
            (Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) (RingHom.ker θ.toRingHom))
            (α i (k i))) p =
        Ideal.Quotient.mk Jk (evk p) := by
    simpa [evk, Jk] using
      (MvPolynomial.aeval_algebraMap_apply (R := R') (A := R') (B := R' ⧸ Jk)
        (x := fun i ↦ α i (k i)) (p := p))
  rw [hEval]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem evk hp)

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.5: the evaluation map descends through the canonical quotient
presentation `A ⧸ ker θ ≃ S'` to an `R'`-algebra map `S' → R' ⧸ Jₖ`. -/
noncomputable abbrev evaluation_quotient_algHom_of_surjective_kernel_presentation
    {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S']
    {n : ℕ} {d : Fin n → ℕ} {α : ∀ i : Fin n, Fin (d i) → R'}
    (θ : MvPolynomial (Fin n) R' →ₐ[R'] S')
    (hθsurj : Function.Surjective θ)
    (k : ∀ i : Fin n, Fin (d i)) :
    S' →ₐ[R']
      R' ⧸ Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) (RingHom.ker θ.toRingHom) :=
  let K := RingHom.ker θ.toRingHom
  let evk : MvPolynomial (Fin n) R' →ₐ[R'] R' := MvPolynomial.aeval fun i ↦ α i (k i)
  let evkBar :
      (MvPolynomial (Fin n) R' ⧸ K) →ₐ[R'] R' ⧸ Ideal.map evk K :=
    Ideal.Quotient.liftₐ K ((Ideal.Quotient.mkₐ R' (Ideal.map evk K)).comp evk) (by
      intro f hf
      -- The quotient by the image ideal kills every evaluation of an element of `K`.
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem evk hf))
  let eK : (MvPolynomial (Fin n) R' ⧸ K) ≃ₐ[R'] S' :=
    Ideal.quotientKerAlgEquivOfSurjective hθsurj
  -- Compose the descended evaluation map with the canonical quotient-kernel presentation.
  evkBar.comp eK.symm

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.5: flatness over `S'` descends to flatness modulo every evaluation
image ideal coming from the kernel presentation. -/
lemma evaluation_image_isFlatQuotient_of_surjective_kernel_presentation
    {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S']
    {n : ℕ} {d : Fin n → ℕ} {α : ∀ i : Fin n, Fin (d i) → R'}
    {N : Type*} [AddCommGroup N] [Module R' N]
    (θ : MvPolynomial (Fin n) R' →ₐ[R'] S')
    (hθsurj : Function.Surjective θ)
    (k : ∀ i : Fin n, Fin (d i))
    (hflatTensor : Module.Flat S' (S' ⊗[R'] N)) :
    Module.Flat
      (R' ⧸ Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) (RingHom.ker θ.toRingHom))
      (N ⧸
        (Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) (RingHom.ker θ.toRingHom) •
          (⊤ : Submodule R' N))) := by
  -- Use the descended evaluation map as the quotient-valued algebra map required by the
  -- general quotient-flatness descent lemma.
  simpa using
    ideal_isFlatQuotient_of_algebraMap_to_quotient
      (R := R') (S := S') (M := N)
      (I := Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) (RingHom.ker θ.toRingHom))
      (evaluation_quotient_algHom_of_surjective_kernel_presentation
        (θ := θ) (hθsurj := hθsurj) (α := α) k)
      hflatTensor

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.5: the quotient by the top ideal is flat because the quotient module is
trivial. -/
lemma flat_quotient_top
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N] :
    Module.Flat (A ⧸ (⊤ : Ideal A))
      (N ⧸ ((⊤ : Ideal A) • (⊤ : Submodule A N))) := by
  -- The quotient by `⊤ • ⊤ = ⊤` is the zero module, hence flat over the zero quotient ring.
  let _ : Subsingleton (N ⧸ ((⊤ : Ideal A) • (⊤ : Submodule A N))) :=
    Submodule.Quotient.subsingleton_iff.mpr
      (Submodule.top_smul (R := A) (N := (⊤ : Submodule A N)))
  infer_instance

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.5: quotient-flatness is preserved under binary ideal intersections. -/
lemma flat_quotient_inf_of_flat_quotients
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (I J : Ideal A)
    (hI : Module.Flat (A ⧸ I) (N ⧸ (I • (⊤ : Submodule A N))))
    (hJ : Module.Flat (A ⧸ J) (N ⧸ (J • (⊤ : Submodule A N)))) :
    Module.Flat (A ⧸ (I ⊓ J)) (N ⧸ ((I ⊓ J) • (⊤ : Submodule A N))) :=
by
  -- Route correction: reuse the earlier chapter owner theorem for binary intersections of
  -- flat-quotient ideals instead of rebuilding its reduced-case proof locally in this file.
  simpa [Ideal.IsFlatQuotient] using
    (Ideal.IsFlatQuotient.inf (R := A) (M := N) (I₁ := I) (I₂ := J) hI hJ)

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.5: a finite intersection of quotient-flat ideals again gives a flat
quotient module over the quotient ring by that intersection. -/
lemma flat_quotient_iInf_finset
    {ι : Type*} {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (s : Finset ι) (J : ι → Ideal A)
    (hJ : ∀ i, Module.Flat (A ⧸ J i) (N ⧸ (J i • (⊤ : Submodule A N)))) :
    Module.Flat (A ⧸ (⨅ i ∈ s, J i)) (N ⧸ ((⨅ i ∈ s, J i) • (⊤ : Submodule A N))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty intersection is `⊤`, whose quotient module is zero.
      have hempty : ((⨅ i ∈ (∅ : Finset ι), J i) : Ideal A) = ⊤ := by
        simp
      rw [hempty]
      simpa using (flat_quotient_top (A := A) (N := N))
  | insert a s ha ih =>
      -- Peel off one branch and apply the canonical binary intersection theorem.
      have hinsert :
          ((⨅ i ∈ insert a s, J i) : Ideal A) = J a ⊓ ⨅ i ∈ s, J i := by
        rw [Finset.iInf_insert]
      rw [hinsert]
      exact
        flat_quotient_inf_of_flat_quotients (A := A) (N := N) (I := J a)
          (J := ⨅ i ∈ s, J i) (hJ a) ih

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.5: for a finite index type, the full infimum of flat-quotient ideals
again gives a flat quotient. -/
lemma flat_quotient_iInf_of_finite
    {ι : Type*} [Finite ι] {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (J : ι → Ideal A)
    (hJ : ∀ i, Module.Flat (A ⧸ J i) (N ⧸ (J i • (⊤ : Submodule A N)))) :
    Module.Flat (A ⧸ (⨅ i, J i)) (N ⧸ ((⨅ i, J i) • (⊤ : Submodule A N))) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  -- Rewrite the infinite notation to a finite fold over `Finset.univ`.
  have huniv : ((⨅ i ∈ (Finset.univ : Finset ι), J i) : Ideal A) = ⨅ i, J i := by
    simp
  rw [← huniv]
  exact flat_quotient_iInf_finset (N := N) (s := Finset.univ) J hJ

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.5: the finite family of evaluation-image ideals has flat quotient after
combining the branchwise quotient-flatness statements. -/
lemma evaluation_image_iInf_isFlatQuotient_of_surjective_kernel_presentation
    {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S']
    {n : ℕ} {d : Fin n → ℕ} {α : ∀ i : Fin n, Fin (d i) → R'}
    {N : Type*} [AddCommGroup N] [Module R' N]
    (θ : MvPolynomial (Fin n) R' →ₐ[R'] S')
    (hθsurj : Function.Surjective θ)
    (hflatTensor : Module.Flat S' (S' ⊗[R'] N)) :
    let Jk : (∀ i : Fin n, Fin (d i)) → Ideal R' :=
      fun k ↦ Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) (RingHom.ker θ.toRingHom)
    let I : Ideal R' := ⨅ k, Jk k
    Module.Flat (R' ⧸ I) (N ⧸ (I • (⊤ : Submodule R' N))) := by
  classical
  let Jk : (∀ i : Fin n, Fin (d i)) → Ideal R' :=
    fun k ↦ Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) (RingHom.ker θ.toRingHom)
  let I : Ideal R' := ⨅ k, Jk k
  have hbranch :
      ∀ k, Module.Flat (R' ⧸ Jk k) (N ⧸ (Jk k • (⊤ : Submodule R' N))) := by
    intro k
    -- Each branch is exactly the quotient-flatness statement proved from the descended
    -- evaluation algebra map.
    simpa [Jk] using
      (evaluation_image_isFlatQuotient_of_surjective_kernel_presentation
        (R' := R') (S' := S') (N := N) (θ := θ) (hθsurj := hθsurj)
        (d := d) (α := α) k hflatTensor)
  have hI : Module.Flat (R' ⧸ I) (N ⧸ (I • (⊤ : Submodule R' N))) := by
    -- The index type is finite, so the previous finite-intersection lemma applies.
    simpa [I, Jk] using flat_quotient_iInf_of_finite (N := N) Jk hbranch
  simpa [I]

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.5: the evaluation-image intersection cuts out all of `Spec R'` after a
surjective split polynomial presentation. -/
lemma zeroLocus_iInf_evaluationImage_eq_univ_of_surjective_kernel_presentation
    {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S'] [Module.Finite R' S']
    {n : ℕ} {d : Fin n → ℕ} {α : ∀ i : Fin n, Fin (d i) → R'}
    (θ : MvPolynomial (Fin n) R' →ₐ[R'] S')
    (hθsurj : Function.Surjective θ)
    (hrel : ∀ i : Fin n,
      ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)) ∈
        RingHom.ker θ.toRingHom)
    (hinjTensor : Function.Injective (algebraMap R' S')) :
    zeroLocus
      ((⨅ k : ∀ i : Fin n, Fin (d i),
        Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) (RingHom.ker θ.toRingHom) :
          Ideal R') : Set R') = Set.univ := by
  classical
  let K : Ideal (MvPolynomial (Fin n) R') := RingHom.ker θ.toRingHom
  let eK : (MvPolynomial (Fin n) R' ⧸ K) ≃ₐ[R'] S' :=
    Ideal.quotientKerAlgEquivOfSurjective hθsurj
  have hrangeK :
      Set.range (PrimeSpectrum.comap (algebraMap R' (MvPolynomial (Fin n) R' ⧸ K))) =
        zeroLocus
          ((⨅ k : ∀ i : Fin n, Fin (d i),
            Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) K : Ideal R') : Set R') := by
    -- Lemma `15.21.4` computes the spectrum image for the quotient by `K = ker θ`.
    simpa [K] using
      range_comap_polynomial_quotient_eq_zeroLocus_iInf_evaluationImage
        (R := R') (d := d) K α hrel
  have hbase :
      (algebraMap R' S') =
        eK.toRingHom.comp (algebraMap R' (MvPolynomial (Fin n) R' ⧸ K)) := by
    -- The quotient-kernel equivalence preserves scalars by construction.
    ext r
    exact (eK.commutes r).symm
  have hsurjSpec : Function.Surjective (PrimeSpectrum.comap eK.toRingHom) := by
    -- Spectrum contraction along a ring equivalence is surjective.
    exact
      (PrimeSpectrum.isHomeomorph_comap_of_bijective eK.toRingEquiv.bijective).bijective.surjective
  have hrangeS' :
      Set.range (PrimeSpectrum.comap (algebraMap R' S')) =
        zeroLocus
          ((⨅ k : ∀ i : Fin n, Fin (d i),
            Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) K : Ideal R') : Set R') := by
    -- Rewrite the image through `A ⧸ K ≃ S'`, then drop the surjective spectrum automorphism.
    calc
      Set.range (PrimeSpectrum.comap (algebraMap R' S')) =
          Set.range
            ((PrimeSpectrum.comap (algebraMap R' (MvPolynomial (Fin n) R' ⧸ K))).comp
              (PrimeSpectrum.comap eK.toRingHom)) := by
                rw [hbase, PrimeSpectrum.comap_comp]
      _ = Set.range (PrimeSpectrum.comap (algebraMap R' (MvPolynomial (Fin n) R' ⧸ K))) := by
            rw [Set.range_comp, Set.range_eq_univ.2 hsurjSpec, Set.image_univ]
      _ = zeroLocus
            ((⨅ k : ∀ i : Fin n, Fin (d i),
              Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) K : Ideal R') : Set R') := hrangeK
  have hIntegral : (algebraMap R' S').IsIntegral := by
    rw [algebraMap_isIntegral_iff]
    infer_instance
  have hrangeUniv :
      Set.range (PrimeSpectrum.comap (algebraMap R' S')) = Set.univ := by
    exact Set.range_eq_univ.2 (RingHom.IsIntegral.comap_surjective hIntegral hinjTensor)
  simpa [K] using hrangeS'.symm.trans hrangeUniv

-- Proof sketch: after a finite locally free base change reducing to the split polynomial-quotient
-- case of Lemmas `15.21.3` and `15.21.4`, one obtains a nilpotent ideal `I ⊆ R` such that
-- `M / IM` is flat over `R ⧸ I`. Then apply the nilpotent-ideal descent criterion
-- `10.101.5`, using injectivity of `R → S` and the assumed flatness of `S ⊗[R] M`.
/-- Lemma 15.21.5: let `R → S` be a finite injective homomorphism of Noetherian rings, and let
`M` be an `R`-module. If the base change `S ⊗[R] M` is flat over `S`, then `M` is flat over `R`.
This is the canonical Lean form of the textbook statement for `M ⊗_R S`, and it remains a
source-facing Chapter 15 theorem rather than a renamed wrapper around the Chapter 10 owner
criterion. -/
@[stacks 0533]
theorem flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct
    (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat S (S ⊗[R] M)) :
    Module.Flat R M := by
  classical
  obtain ⟨n, R', hR'Comm, hR'Alg, hinj', hR'finite, hR'free, d, α, φ, hφsurj⟩ :=
    exists_finiteFree_baseChange_surjective_splitPolynomialQuotient (R := R) (S := S)
  letI : CommRing R' := hR'Comm
  letI : Algebra R R' := hR'Alg
  letI : Module.Finite R R' := hR'finite
  letI : Module.Free R R' := hR'free
  letI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  have hff : (algebraMap R R').FaithfullyFlat :=
    algebraMap_faithfullyFlat_of_injective_moduleFinite_moduleFree
      (R := R) (R' := R') hinj'
  let _ : Module.FaithfullyFlat R R' := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  -- By faithfully flat descent it suffices to prove flatness after the finite free base change.
  suffices hflat' : Module.Flat R' (R' ⊗[R] M) by
    exact (Module.Flat.iff_flat_tensorProduct (R := R) (M := M) R').mp hflat'
  let S' := R' ⊗[R] S
  let J : Ideal (MvPolynomial (Fin n) R') :=
    Ideal.span
      (Set.range fun i ↦
        ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)))
  let θ : MvPolynomial (Fin n) R' →ₐ[R'] S' :=
    φ.comp (Ideal.Quotient.mkₐ R' J)
  have hθsurj : Function.Surjective θ := by
    intro z
    rcases hφsurj z with ⟨x, rfl⟩
    rcases Ideal.Quotient.mkₐ_surjective R' J x with ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  have hrel :
      ∀ i : Fin n,
        ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)) ∈
          RingHom.ker θ.toRingHom := by
    intro i
    rw [RingHom.mem_ker]
    have hJ :
        ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)) ∈ J := by
      exact Ideal.subset_span ⟨i, rfl⟩
    have hmk :
        Ideal.Quotient.mk J
            (∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j))) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.2 hJ
    simpa [θ] using congrArg φ hmk
  have hinjTensor : Function.Injective (algebraMap R' S') := by
    -- The left tensor inclusion is injective because `R'` is free, hence flat, over `R`.
    simpa [S'] using
      (Algebra.TensorProduct.includeLeft_injective (S := R) (A := R') (B := S) hinj)
  have hflatTensor :
      Module.Flat S' (S' ⊗[R'] (R' ⊗[R] M)) :=
    flat_baseChange_tensorProduct_of_flat_tensorProduct
      (R := R) (S := S) (M := M) (R' := R') hflat
  -- Route correction: the quotient-presentation transport is now isolated in the helper
  -- `evaluation_quotient_algHom_of_surjective_kernel_presentation`, and the zero-locus/nilpotent
  -- half of the source route is now explicit below. The only remaining gap is the finite
  -- intersection flat-quotient package from Lemma `15.16.1`.
  let I : Ideal R' :=
    ⨅ k : ∀ i : Fin n, Fin (d i),
      Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) (RingHom.ker θ.toRingHom)
  have hzero : zeroLocus (I : Set R') = Set.univ := by
    -- Lemma `15.21.4` identifies the spectrum image with `V(I)`, and integrality makes that
    -- image all of `Spec(R')`.
    simpa [I] using
      zeroLocus_iInf_evaluationImage_eq_univ_of_surjective_kernel_presentation
        (R' := R') (S' := S') (θ := θ) (hθsurj := hθsurj)
        (d := d) (α := α) hrel hinjTensor
  have hnil : IsNilpotent I :=
    isNilpotent_of_zeroLocus_eq_univ_of_isNoetherian (R := R') I hzero
  have hflat' : Module.Flat R' (R' ⊗[R] M) := by
    have hflat_mod_I :
        Module.Flat (R' ⧸ I) ((R' ⊗[R] M) ⧸ (I • (⊤ : Submodule R' (R' ⊗[R] M)))) := by
      -- Fold the branchwise quotient-flatness statements over the finite evaluation family.
      simpa [I] using
        (evaluation_image_iInf_isFlatQuotient_of_surjective_kernel_presentation
          (R' := R') (S' := S') (N := R' ⊗[R] M)
          (θ := θ) (hθsurj := hθsurj) (d := d) (α := α) hflatTensor)
    exact
      flat_of_nilpotent_ideal_of_injective_algebraMap_of_flat_mod_ideal_and_flat_baseChange
        (R := R') (R' := S') (M := R' ⊗[R] M) hnil hinjTensor hflat_mod_I hflatTensor
  exact hflat'

end
