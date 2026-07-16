import StacksProject_2024.stacks_project.Chap10.Lemma_10_77_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_77_8
import StacksProject_2024.stacks_project.Chap10.Theorem_10_95_6
import StacksProject_2024.stacks_project.Chap15.Lemma_15_21_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_21_5

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped TensorProduct

universe u v w u₁

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [Module.Finite R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

open PrimeSpectrum

/- Domain triage:
- primary domain: descent of projective modules under finite injective base change over
  Noetherian commutative rings;
- sampled owner declarations of the same kind:
  `Module.Projective`,
  `Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated`,
  `Module.Flat.of_projective`,
  `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`,
  `projective_of_projective_quotient_of_isNilpotent_of_flat`;
- best owner abstraction: the canonical owner predicate `Module.Projective R M`;
- primitive data: the Noetherian base ring `R`, the finite `R`-algebra `S`, the injective
  algebra map `R → S`, and the `R`-module `M`;
- derived API: the descended projectivity of `M`, stated directly in terms of the owner predicate
  rather than via a parallel wrapper for the textbook module `M ⊗_R S`.

Layering:
- this numbered item is `source-facing`: it is the textbook finite-injective descent statement;
- `core/canonical`: `Module.Projective`, together with the flatness owner
  `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`, the
  projective-to-flat bridge `Module.Flat.of_projective`, and the Chapter 10 nilpotent-thickening
  descent theorem
  `projective_of_projective_quotient_of_isNilpotent_of_flat`;
- no separate `bridge/view` owner is warranted here: the source-facing statement already lands
  directly in the canonical owner predicate `Module.Projective`.
-/

-- Proof sketch: projective modules are flat, so
-- `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`
-- descends flatness of `M` from `hproj`. After the same finite locally free reduction used in
-- Lemmas `15.21.3` and `15.21.4`, one gets a nilpotent ideal `I` such that `M / IM` is
-- projective over `R ⧸ I`; the Chapter 10 projective descent theorem
-- `projective_of_projective_quotient_of_isNilpotent_of_flat` then finishes.
/-- Helper for Lemma 15.21.7: the prime-spectrum map of an integral algebra extension is
surjective. -/
lemma primeSpectrum_comap_surjective_of_isIntegral
    [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) := by
  have hintegral : (algebraMap R S).IsIntegral := by
    intro s
    exact Algebra.IsIntegral.isIntegral s
  -- This is the standard lying-over surjectivity statement packaged for the canonical algebra map.
  simpa using hintegral.comap_surjective hinj

/-- Helper for Lemma 15.21.7: an injective finite free algebra map is faithfully flat. -/
lemma faithfullyFlat_of_injective_finiteFree_algebraMap
    {R' : Type (max u v)} [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R'))
    [Module.Finite R R'] [Module.Free R R'] :
    Module.FaithfullyFlat R R' := by
  letI : Algebra.IsIntegral R R' := Algebra.IsIntegral.of_finite R R'
  -- Finite free modules are flat, and integral extensions are surjective on spectra.
  have howner : RingHom.FaithfullyFlat (algebraMap R R') := by
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    have hflat : Module.Flat R R' := Module.Flat.of_free
    refine ⟨RingHom.flat_algebraMap_iff.mpr hflat,
      primeSpectrum_comap_surjective_of_isIntegral (R := R) (S := R') hinj⟩
  exact RingHom.faithfullyFlat_algebraMap_iff.mp howner

/-- Helper for Lemma 15.21.7: once the finite free base change from Lemma `15.21.3` yields a
projective base-changed module, faithfully flat descent along that base change returns a
projective `R`-module. -/
lemma projective_of_projective_tensorProduct_of_injective_finiteFree_baseChange
    {R' : Type (max u v)} [CommRing R'] [Algebra R R']
    [Module.Finite R R'] [Module.Free R R']
    (hinj : Function.Injective (algebraMap R R'))
    (hproj : Module.Projective R' (R' ⊗[R] M)) :
    Module.Projective R M := by
  letI : Module.FaithfullyFlat R R' :=
    faithfullyFlat_of_injective_finiteFree_algebraMap (R := R) (R' := R') hinj
  letI : Module.Projective R' (R' ⊗[R] M) := hproj
  -- The Chapter 10 faithfully flat descent theorem closes the reduction.
  exact Module.Projective.of_projective_tensorProduct_of_faithfullyFlat R'

/-- Helper for Lemma 15.21.7: after base change to `R'`, the projective `S`-module
`S ⊗[R] M` remains projective over the split extension `R' ⊗[R] S` in the tensor order used by
the source proof. -/
lemma projective_baseChange_tensorProduct_of_projective_tensorProduct
    {R' : Type (max u v)} [CommRing R'] [Algebra R R']
    (hproj : Module.Projective S (S ⊗[R] M)) :
    Module.Projective (R' ⊗[R] S) ((R' ⊗[R] S) ⊗[R'] (R' ⊗[R] M)) := by
  let S' := R' ⊗[R] S
  letI : Module.Projective S (S ⊗[R] M) := hproj
  letI : Module.Projective S' (S' ⊗[S] (S ⊗[R] M)) := Module.Projective.tensorProduct
  let eLeft : S' ⊗[S] (S ⊗[R] M) ≃ₗ[S'] S' ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M
  let eRight : S' ⊗[R'] (R' ⊗[R] M) ≃ₗ[S'] S' ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R R' S' S' M
  -- Both tensor presentations are the same `S'`-module up to the canonical cancellation maps.
  exact Module.Projective.of_equiv (eLeft.trans eRight.symm)

/-- Helper for Lemma 15.21.7: in the split kernel presentation, the branch-intersection ideal
cuts out all of `Spec R'`, hence is nilpotent in the Noetherian ring `R'`. -/
lemma split_presentation_evaluationInf_isNilpotent
    {R' : Type*} [CommRing R'] [IsNoetherianRing R']
    {S' : Type*} [CommRing S'] [Algebra R' S'] [Module.Finite R' S']
    {n : ℕ} (d : Fin n → ℕ) (α : ∀ i : Fin n, Fin (d i) → R')
    (θ : MvPolynomial (Fin n) R' →ₐ[R'] S') (hθsurj : Function.Surjective θ)
    (hrel :
      ∀ i : Fin n,
        ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)) ∈
          RingHom.ker θ.toRingHom)
    (hinj : Function.Injective (algebraMap R' S')) :
    IsNilpotent
      (⨅ k : ∀ i : Fin n, Fin (d i),
        Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) (RingHom.ker θ.toRingHom)) := by
  -- Route correction: work with the actual kernel `ker θ`, not the original split ideal, so the
  -- zero-locus computation from Lemma `15.21.4` matches the source proof exactly.
  have hzero :
      zeroLocus
        ((⨅ k : ∀ i : Fin n, Fin (d i),
          Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) (RingHom.ker θ.toRingHom) :
            Ideal R') : Set R') = Set.univ := by
    -- Lemma `15.21.5` already packages the spectrum-image computation for the quotient by
    -- `ker θ`; reuse that exact source-faithful zero-locus statement here.
    simpa using
      zeroLocus_iInf_evaluationImage_eq_univ_of_surjective_kernel_presentation
        (R' := R') (S' := S') (θ := θ) (hθsurj := hθsurj)
        (d := d) (α := α) hrel hinj
  -- Once the branch intersection cuts out all of `Spec R'`, Noetherianity upgrades that to
  -- nilpotence.
  exact
    isNilpotent_of_zeroLocus_eq_univ_of_isNoetherian
      (R := R')
      (⨅ k : ∀ i : Fin n, Fin (d i),
        Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) (RingHom.ker θ.toRingHom))
      hzero

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.7: after quotienting by `I₁ ⊓ I₂`, the images of `I₁` and `I₂`
have trivial intersection. -/
lemma map_inf_quotient_intersection_eq_bot
    {I₁ I₂ : Ideal R} :
    Ideal.map (Ideal.Quotient.mk (I₁ ⊓ I₂)) I₁ ⊓
      Ideal.map (Ideal.Quotient.mk (I₁ ⊓ I₂)) I₂ =
        (⊥ : Ideal (R ⧸ (I₁ ⊓ I₂))) := by
  -- Check membership in the intersection by lifting representatives through the quotient map.
  refine bot_unique ?_
  intro x hx
  rcases (Ideal.mem_inf.mp hx) with ⟨hx₁, hx₂⟩
  obtain ⟨a₁, ha₁I₁, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (I₁ ⊓ I₂))
      Ideal.Quotient.mk_surjective).1 hx₁
  obtain ⟨a₂, ha₂I₂, ha₂eq⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (I₁ ⊓ I₂))
      Ideal.Quotient.mk_surjective).1 hx₂
  -- The two representatives differ by an element of `I₁ ⊓ I₂`, so the first representative
  -- already belongs to both ideals.
  have hsub :
      (Ideal.Quotient.mk (I₁ ⊓ I₂)) (a₁ - a₂) = 0 := by
    simpa [ha₂eq] using sub_eq_zero.mp rfl
  have hsub_mem : a₁ - a₂ ∈ I₁ ⊓ I₂ :=
    (Ideal.Quotient.eq_zero_iff_mem).1 hsub
  have ha₁I₂ : a₁ ∈ I₂ := by
    have hadd : (a₁ - a₂) + a₂ ∈ I₂ := I₂.add_mem (Ideal.mem_inf.mp hsub_mem).2 ha₂I₂
    simpa [sub_eq_add_neg, add_assoc] using hadd
  have ha₁K : a₁ ∈ I₁ ⊓ I₂ := Ideal.mem_inf.mpr ⟨ha₁I₁, ha₁I₂⟩
  simpa using (Ideal.Quotient.eq_zero_iff_mem).2 ha₁K

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.7: quotienting `M / KM` again by the image of `J`
recovers `M / JM` as an `R`-linear quotient-of-quotient equivalence. -/
noncomputable def quotient_quotient_smul_top_equiv
    {K J : Ideal R} (hKJ : K ≤ J) :
    ((M ⧸ (K • (⊤ : Submodule R M))) ⧸
      ((((Ideal.map (Ideal.Quotient.mk K) J) •
          (⊤ : Submodule (R ⧸ K) (M ⧸ (K • (⊤ : Submodule R M))))) :
            Submodule (R ⧸ K) (M ⧸ (K • (⊤ : Submodule R M)))).restrictScalars R)) ≃ₗ[R]
      M ⧸ (J • (⊤ : Submodule R M)) := by
  let Ksm : Submodule R M := K • (⊤ : Submodule R M)
  let Jsm : Submodule R M := J • (⊤ : Submodule R M)
  have hden :
      ((((Ideal.map (Ideal.Quotient.mk K) J) •
          (⊤ : Submodule (R ⧸ K) (M ⧸ Ksm))) :
            Submodule (R ⧸ K) (M ⧸ Ksm)).restrictScalars R) =
        Jsm.map Ksm.mkQ := by
    -- Rewrite the quotient-ring action back to the original `R`-action and then identify the
    -- image of `JM` in the first quotient.
    calc
      ((((Ideal.map (Ideal.Quotient.mk K) J) •
          (⊤ : Submodule (R ⧸ K) (M ⧸ Ksm))) :
            Submodule (R ⧸ K) (M ⧸ Ksm)).restrictScalars R) =
          J • (⊤ : Submodule R (M ⧸ Ksm)) := by
            simpa [Ksm] using
              (Ideal.smul_restrictScalars (R := R) (S := R ⧸ K)
                (M := M ⧸ Ksm) J (⊤ : Submodule (R ⧸ K) (M ⧸ Ksm)))
      _ = Jsm.map Ksm.mkQ := by
            simpa [Jsm] using
              (Submodule.map_smul'' (f := Ksm.mkQ) J (⊤ : Submodule R M))
  -- After identifying the denominator, the standard third isomorphism theorem gives the target
  -- quotient.
  exact
    (Submodule.quotEquivOfEq _ _ hden).trans
      (Submodule.quotientQuotientEquivQuotient Ksm Jsm (Submodule.smul_mono hKJ le_rfl))

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.7: projectivity over `R ⧸ J` transports across the standard
quotient-of-quotient ring equivalence. -/
lemma projective_transport_to_double_quotient
    {K J : Ideal R} (hKJ : K ≤ J)
    (hproj : Module.Projective (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))) :
    let _ :
        Module ((R ⧸ K) ⧸ Ideal.map (Ideal.Quotient.mk K) J)
          (M ⧸ (J • (⊤ : Submodule R M))) :=
      Module.compHom (M ⧸ (J • (⊤ : Submodule R M)))
        (DoubleQuot.quotQuotEquivQuotOfLE (R := R) (I := K) (J := J) hKJ).toRingHom
    Module.Projective
      ((R ⧸ K) ⧸ Ideal.map (Ideal.Quotient.mk K) J)
      (M ⧸ (J • (⊤ : Submodule R M))) := by
  -- TODO: transport `hproj` along `DoubleQuot.quotQuotEquivQuotOfLE` by exhibiting the quotient
  -- module `M / JM` with the `Module.compHom` structure as the same additive group equipped with
  -- scalars pulled back through the ring equivalence, then apply `Module.Projective.of_equiv`.
  sorry

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.7: projectivity modulo two ideals descends to projectivity modulo
their intersection by gluing over the quotient by `I₁ ⊓ I₂`. -/
lemma projective_of_projective_quotients_inf
    {I₁ I₂ : Ideal R}
    (hproj₁ : Module.Projective (R ⧸ I₁) (M ⧸ (I₁ • (⊤ : Submodule R M))))
    (hproj₂ : Module.Projective (R ⧸ I₂) (M ⧸ (I₂ • (⊤ : Submodule R M)))) :
    Module.Projective (R ⧸ (I₁ ⊓ I₂)) (M ⧸ ((I₁ ⊓ I₂) • (⊤ : Submodule R M))) := by
  -- TODO: work over `R ⧸ (I₁ ⊓ I₂)`, use `map_inf_quotient_intersection_eq_bot` for the `⊥`
  -- hypothesis, transport `hproj₁` and `hproj₂` with
  -- `projective_transport_to_double_quotient`, identify the resulting modules with the
  -- quotient-of-quotient branches via `quotient_quotient_smul_top_equiv`, and then apply
  -- `projective_of_projective_quotients_of_inf_eq_bot`.
  sorry

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.7: projective branch quotients glue to projectivity modulo the finite
intersection ideal. -/
lemma projective_of_projective_quotients_iInf_fintype
    {κ : Type u₁} [Finite κ]
    (J : κ → Ideal R)
    (hproj : ∀ k, Module.Projective (R ⧸ J k) (M ⧸ (J k • (⊤ : Submodule R M)))) :
    Module.Projective (R ⧸ (⨅ k, J k)) (M ⧸ ((⨅ k, J k) • (⊤ : Submodule R M))) := by
  -- TODO: use `Fintype.induction_empty_option`. The empty case is the quotient by `⊤`, and the
  -- `Option` step reduces the new family to `projective_of_projective_quotients_inf` applied to
  -- the `none` branch and the intersection of the tail ideals.
  sorry

omit [IsNoetherianRing R] [Module.Finite R S] in
/-- Helper for Lemma 15.21.7: an algebra map `S → R ⧸ I` transports projectivity of
`S ⊗[R] M` to projectivity of the quotient module `M / IM`. -/
lemma ideal_isProjectiveQuotient_of_algebraMap_to_quotient
    (I : Ideal R) (Φ : S →ₐ[R] R ⧸ I)
    (hproj : Module.Projective S (S ⊗[R] M)) :
    Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) := by
  let _ : Algebra S (R ⧸ I) := Φ.toAlgebra
  let _ : Module.Projective S (S ⊗[R] M) := hproj
  have hbase : Module.Projective (R ⧸ I) ((R ⧸ I) ⊗[S] (S ⊗[R] M)) := by
    -- First base change the projective `S`-module along `Φ : S → R ⧸ I`.
    simpa using
      (Module.Projective.tensorProduct
        (R := R ⧸ I) (R₀ := S) (M := R ⧸ I) (N := S ⊗[R] M))
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
    -- On tensor generators, the lifted map is the quotient projection.
    simp [e₀, f]
  have e₀_restrictScalars :
      e₀.restrictScalars R = (TensorProduct.quotTensorEquivQuotSMul M I).toLinearMap := by
    -- Compare the `R ⧸ I`-linear quotient map with the standard `R`-linear tensor/quotient
    -- equivalence, so injectivity comes from the owner theorem.
    apply TensorProduct.ext'
    intro q y
    refine Quotient.inductionOn q ?_
    intro a
    change e₀ (Ideal.Quotient.mk I a ⊗ₜ[R] y) =
      TensorProduct.quotTensorEquivQuotSMul M I (Ideal.Quotient.mk I a ⊗ₜ[R] y)
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    simp [e₀, f]
    simpa using (algebraMap_smul (R ⧸ I) a (Submodule.Quotient.mk y))
  have hbij : Function.Bijective e₀ := by
    constructor
    · intro u v huv
      have huv' : e₀.restrictScalars R u = e₀.restrictScalars R v := huv
      rw [e₀_restrictScalars] at huv'
      exact (TensorProduct.quotTensorEquivQuotSMul M I).injective huv'
    · intro z
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) z
      exact ⟨(1 : R ⧸ I) ⊗ₜ[R] y, e₀_apply y⟩
  let eQuot : ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] M ⧸ (I • (⊤ : Submodule R M)) :=
    LinearEquiv.ofBijective e₀ hbij
  let _ : Module.Projective (R ⧸ I) ((R ⧸ I) ⊗[S] (S ⊗[R] M)) := hbase
  -- Transport projectivity across base-change cancellation and the quotient model.
  exact Module.Projective.of_equiv' (eCancel.trans eQuot)

/-- Helper for Lemma 15.21.7: after choosing the split polynomial presentation from
Lemma `15.21.3`, the remaining source-faithful step is to prove projectivity of the base-changed
module `R' ⊗[R] M` over `R'` by combining Lemma `15.21.4` with projective descent across the
resulting nilpotent ideal. -/
lemma projective_tensorProduct_of_split_baseChange_presentation
    {R' : Type (max u v)} [CommRing R'] [Algebra R R']
    [Module.Finite R R'] [Module.Free R R']
    (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat R M)
    (hproj : Module.Projective S (S ⊗[R] M))
    {n : ℕ} (d : Fin n → ℕ) (α : ∀ i, Fin (d i) → R')
    (φ :
      (MvPolynomial (Fin n) R' ⧸
        Ideal.span
          (Set.range fun i ↦
            ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)))) →ₐ[R']
        (R' ⊗[R] S))
    (hφ : Function.Surjective φ) :
    Module.Projective R' (R' ⊗[R] M) := by
  classical
  let S' := R' ⊗[R] S
  have hprojTensor :
      Module.Projective S' (S' ⊗[R'] (R' ⊗[R] M)) :=
    projective_baseChange_tensorProduct_of_projective_tensorProduct
      (R := R) (S := S) (M := M) (R' := R') hproj
  let Jsplit : Ideal (MvPolynomial (Fin n) R') :=
    Ideal.span
      (Set.range fun i ↦
        ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)))
  let θ : MvPolynomial (Fin n) R' →ₐ[R'] S' :=
    φ.comp (Ideal.Quotient.mkₐ R' Jsplit)
  have hθsurj : Function.Surjective θ := by
    intro z
    rcases hφ z with ⟨x, rfl⟩
    rcases Ideal.Quotient.mkₐ_surjective R' Jsplit x with ⟨p, rfl⟩
    exact ⟨p, rfl⟩
  let K : Ideal (MvPolynomial (Fin n) R') := RingHom.ker θ.toRingHom
  let Jk : (∀ i : Fin n, Fin (d i)) → Ideal R' :=
    fun k ↦ Ideal.map (MvPolynomial.eval fun i ↦ α i (k i)) K
  have hbranch :
      ∀ k : ∀ i : Fin n, Fin (d i),
        Module.Projective (R' ⧸ Jk k)
          ((R' ⊗[R] M) ⧸ (Jk k • (⊤ : Submodule R' (R' ⊗[R] M)))) := by
    intro k
    let ξk : S' →ₐ[R'] R' ⧸ Jk k :=
      evaluation_quotient_algHom_of_surjective_kernel_presentation
        (θ := θ) (hθsurj := hθsurj) (k := k)
    -- Each evaluation branch turns the projective tensor module into the corresponding quotient.
    exact
      ideal_isProjectiveQuotient_of_algebraMap_to_quotient
        (R := R') (S := S') (M := R' ⊗[R] M) (I := Jk k) ξk hprojTensor
  have hrel :
      ∀ i : Fin n,
        ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)) ∈ K := by
    intro i
    rw [RingHom.mem_ker]
    have hJsplit :
        ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)) ∈ Jsplit := by
      exact Ideal.subset_span ⟨i, rfl⟩
    have hmk :
        Ideal.Quotient.mk Jsplit
            (∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j))) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.2 hJsplit
    simpa [θ, Jsplit] using congrArg φ hmk
  letI : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hnil :
      IsNilpotent (⨅ k : ∀ i : Fin n, Fin (d i), Jk k) := by
    -- The split presentation forces the branch ideals to cover all primes of `R'`.
    simpa [Jk, K] using
      split_presentation_evaluationInf_isNilpotent
        (R' := R') (S' := S') (d := d) (α := α) θ hθsurj hrel
        (Algebra.TensorProduct.includeLeft_injective (S := R) (A := R') (B := S) hinj)
  have hprojQuot :
      Module.Projective
        (R' ⧸ (⨅ k : ∀ i : Fin n, Fin (d i), Jk k))
        ((R' ⊗[R] M) ⧸
          ((⨅ k : ∀ i : Fin n, Fin (d i), Jk k) •
            (⊤ : Submodule R' (R' ⊗[R] M)))) := by
    -- Glue the projective branch quotients across the finite family of evaluation ideals.
    simpa [Jk] using
      projective_of_projective_quotients_iInf_fintype
        (R := R') (M := R' ⊗[R] M) Jk hbranch
  have hflatBase : Module.Flat R' (R' ⊗[R] M) := by
    letI : Module.Flat R M := hflat
    -- Flatness survives the finite free base change `R → R'`.
    simpa using (Module.Flat.baseChange (R := R) (S := R') (M := M))
  -- With projectivity modulo the nilpotent branch intersection and flatness in hand, the Chapter
  -- 10 nilpotent-thickening descent theorem finishes the source proof over `R'`.
  exact
    projective_of_projective_quotient_of_isNilpotent_of_flat
      (R := R') (I := ⨅ k : ∀ i : Fin n, Fin (d i), Jk k) (M := R' ⊗[R] M)
      hnil hprojQuot

/-- Helper for Lemma 15.21.7: the flatness input needed for the nilpotent-thickening step is the
projective-to-flat specialization of Lemma `15.21.5`. -/
lemma flat_of_projective_tensorProduct_of_injective_moduleFinite
    (hinj : Function.Injective (algebraMap R S))
    (hproj : Module.Projective S (S ⊗[R] M)) :
    Module.Flat R M := by
  letI : Module.Projective S (S ⊗[R] M) := hproj
  have hflatTensor : Module.Flat S (S ⊗[R] M) := Module.Flat.of_projective
  -- Reuse the already-established flatness descent theorem from Lemma `15.21.5`.
  exact
    flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct
      (R := R) (S := S) (M := M) hinj hflatTensor

/-- Lemma 15.21.7: let `R → S` be a finite injective homomorphism of Noetherian rings, and let
`M` be an `R`-module. If the base change `S ⊗[R] M` is projective over `S`, then `M` is
projective over `R`. This is the canonical Lean form of the textbook statement for
`M ⊗_R S`, and it remains a source-facing Chapter 15 theorem rather than a renamed wrapper around
an upstream owner theorem with different hypotheses. -/
theorem projective_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_projective_tensorProduct
    (hinj : Function.Injective (algebraMap R S))
    (hproj : Module.Projective S (S ⊗[R] M)) :
    Module.Projective R M := by
  -- First descend flatness from the projective tensor module.
  have hflat : Module.Flat R M :=
    flat_of_projective_tensorProduct_of_injective_moduleFinite (R := R) (S := S) (M := M) hinj hproj
  -- Next choose the finite free split base change supplied by Lemma `15.21.3`.
  obtain ⟨n, R', hR'Comm, hR'Alg, hinjR', hR'finite, hR'free, d, α, φ, hφ⟩ :=
    exists_finiteFree_baseChange_surjective_splitPolynomialQuotient (R := R) (S := S)
  letI : CommRing R' := hR'Comm
  letI : Algebra R R' := hR'Alg
  letI : Module.Finite R R' := hR'finite
  letI : Module.Free R R' := hR'free
  -- Route correction: isolate the genuinely open split-presentation argument over `R'`, and keep
  -- the faithfully-flat descent back to `R` as a separate verified step.
  have hprojBase : Module.Projective R' (R' ⊗[R] M) :=
    projective_tensorProduct_of_split_baseChange_presentation
      (R := R) (S := S) (M := M) (R' := R') hinj hflat hproj d α φ hφ
  -- Once the base-changed module is projective over `R'`, descend it along the finite free
  -- faithfully flat extension `R → R'`.
  exact
    projective_of_projective_tensorProduct_of_injective_finiteFree_baseChange
      (R := R) (M := M) (R' := R') hinjR' hprojBase

end
