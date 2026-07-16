import stacks_proof.stacks_project.Chap10.Lemma_10_118_3.PolynomialLocalization

universe u v w

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M]

open GenericFlatness

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.118.3: if `T⁻¹N` is finitely presented over `T⁻¹A`, then it is the
localization of a finitely presented `A`-module mapping to `N`. -/
theorem exists_finitePresentation_module_with_localizedLinearEquiv
    {A : Type v} [CommRing A] (T : Submonoid A)
    {N : Type w} [AddCommGroup N] [Module A N]
    [Module.FinitePresentation (Localization T) (LocalizedModule T N)] :
    ∃ (N' : Type v) (_ : AddCommGroup N') (_ : Module A N') (_ : Module.FinitePresentation A N')
      (f : N' →ₗ[A] N)
      (e : LocalizedModule T N' ≃ₗ[Localization T] LocalizedModule T N),
      e.toLinearMap = LocalizedModule.map T f := by
  classical
  let _ : Module.Finite (Localization T) (LocalizedModule T N) := inferInstance
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := Localization T) (M := LocalizedModule T N)
  choose yt ht using
    fun i : Fin n ↦ IsLocalizedModule.mk'_surjective T (LocalizedModule.mkLinearMap T N) (x i)
  let y : Fin n → N := fun i ↦ (yt i).1
  let t : Fin n → T := fun i ↦ (yt i).2
  let N0 : Submodule A N := Submodule.span A (Set.range y)
  have hN0_finite : Module.Finite A N0 := by
    -- The chosen numerators generate `N0`.
    rw [Module.Finite.iff_fg]
    simpa [N0] using Submodule.fg_span (Set.finite_range y)
  have hN0_top : N0.localized T = ⊤ := by
    -- The localized numerators already span the given localized generators.
    apply top_le_iff.mp
    rw [← hx]
    rw [show N0.localized T =
      Submodule.span (Localization T)
        ((LocalizedModule.mkLinearMap T N) '' Set.range y) by
          simpa [N0] using
            (Submodule.localized'_span (Localization T) T (LocalizedModule.mkLinearMap T N)
              (Set.range y))]
    refine Submodule.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨i, rfl⟩
    rw [SetLike.mem_coe, ← IsLocalization.smul_mem_iff (s := t i)]
    rw [← (IsLocalizedModule.mk'_eq_iff (f := LocalizedModule.mkLinearMap T N)).mp (ht i)]
    exact Submodule.subset_span ⟨y i, ⟨i, rfl⟩, rfl⟩
  obtain ⟨m, π0, hπ0⟩ := Module.Finite.exists_fin' A N0
  let π : (Fin m → A) →ₗ[A] N := N0.subtype ∘ₗ π0
  have hN0_surj : Function.Surjective (LocalizedModule.map T N0.subtype) := by
    -- Localizing the inclusion of `N0` is surjective because `N0.localized T = ⊤`.
    exact LinearMap.range_eq_top.1
      (localized_subtype_range_eq_top_of_top_localized (T := T) N0 hN0_top)
  have hπ0_surj : Function.Surjective (LocalizedModule.map T π0) :=
    LocalizedModule.map_surjective T π0 hπ0
  have hπ_surj : Function.Surjective (LocalizedModule.map T π) := by
    -- Surjectivity survives composition after localizing the free cover of `N0`.
    intro z
    obtain ⟨z0, hz0⟩ := hN0_surj z
    obtain ⟨w, hw⟩ := hπ0_surj z0
    refine ⟨w, ?_⟩
    calc
      (LocalizedModule.map T π) w
          = (LocalizedModule.map T N0.subtype) ((LocalizedModule.map T π0) w) := by
              simpa [π] using
                LinearMap.congr_fun
                  (IsLocalizedModule.map_comp'
                    (S := T)
                    (f₀ := LocalizedModule.mkLinearMap T (Fin m → A))
                    (f₁ := LocalizedModule.mkLinearMap T N0)
                    (f₂ := LocalizedModule.mkLinearMap T N)
                    π0 N0.subtype)
                  w
      _ = (LocalizedModule.map T N0.subtype) z0 := by rw [hw]
      _ = z := hz0
  let _ : Module.Finite (Localization T) (LocalizedModule T (Fin m → A)) := inferInstance
  obtain ⟨Ksub, hKsub_finite, hKsub_top⟩ :=
    exists_finite_kernel_submodule_with_top_localized (T := T) (π := π) hπ_surj
  let K0 : Submodule A (Fin m → A) := Ksub.map (LinearMap.ker π).subtype
  let fbar : (Fin m → A) ⧸ K0 →ₗ[A] N :=
    K0.liftQ π (kernel_submodule_image_le_ker (π := π) Ksub)
  have hfbar : fbar.comp (Submodule.mkQ K0) = π := by
    -- The descended quotient map is defined to agree with `π` on generators.
    simpa [fbar] using K0.liftQ_mkQ π (kernel_submodule_image_le_ker (π := π) Ksub)
  have hK0_fg : K0.FG := by
    let _ : Module.Finite A Ksub := hKsub_finite
    have hKsub_fg : Ksub.FG :=
      Submodule.FG.of_finite (R := A) (M := LinearMap.ker π) (N := Ksub)
    -- Finite generation is preserved when we map the descended relation module into the free one.
    simpa [K0] using
      Submodule.FG.map (LinearMap.ker π).subtype hKsub_fg
  let _ : Module.FinitePresentation A ((Fin m → A) ⧸ K0) :=
    Module.finitePresentation_of_surjective (Submodule.mkQ K0) (Submodule.mkQ_surjective _) <| by
      -- The kernel of the quotient map is exactly the relation submodule `K0`.
      change (LinearMap.ker (Submodule.mkQ K0)).FG
      simpa using hK0_fg
  have hK0 :
      K0.localized T = (LinearMap.ker π).localized' (Localization T) T
        (LocalizedModule.mkLinearMap T (Fin m → A)) := by
    -- Localizing the descended relation submodule recovers the localized kernel of `π`.
    simpa [K0] using
      kernel_image_localized_eq_localized_kernel (T := T) (π := π) Ksub hKsub_top
  obtain ⟨e, he⟩ :=
    localized_quotient_equiv_of_surjective_and_kernel_match
      (T := T) (π := π) (K0 := K0) fbar hπ_surj hfbar hK0
  -- The quotient by the descended finite relation module is the desired finitely presented source.
  exact ⟨(Fin m → A) ⧸ K0, inferInstance, inferInstance, inferInstance, fbar, e, he⟩

/-- Helper for Lemma 10.118.3: a finite module over `R[x_1, \dots, x_n]` admits a finitely
presented surjective model whose generic fiber agrees with the original module. -/
theorem exists_finitely_presented_polynomial_surjective_model_with_generic_fiber_linearEquiv
    {n : ℕ}
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [Module.Finite (MvPolynomial (Fin n) R) N] :
    ∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module (MvPolynomial (Fin n) R) N')
      (_ : Module.FinitePresentation (MvPolynomial (Fin n) R) N')
      (f : N' →ₗ[MvPolynomial (Fin n) R] N) (_ : Function.Surjective f)
      (e : LocalizedModule
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) N' ≃ₗ[
            Localization
              (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R))]
            LocalizedModule
              (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) N),
      e.toLinearMap = LocalizedModule.map
        (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) f := by
  let P := MvPolynomial (Fin n) R
  let T : Submonoid P := Algebra.algebraMapSubmonoid P (nonZeroDivisors R)
  have hfp_genericFiber : Module.FinitePresentation (Localization T) (LocalizedModule T N) := by
    -- Proof comment: the generic fiber over the fraction field is finitely presented because
    -- `P = R[x_1, \dots, x_n]` is finite type over the fraction field and therefore Noetherian.
    simpa [P, T] using
      (fractionRing_localized_module_finitePresentation (R := R) (S := P) (M := N))
  let _ : Module.FinitePresentation (Localization T) (LocalizedModule T N) := hfp_genericFiber
  -- Proof comment: now apply the general finitely presented approximation theorem at the generic
  -- fiber denominator submonoid.
  simpa [P, T] using
    (exists_finitePresentation_surjective_model_with_localizedLinearEquiv
      (A := P) (T := T) (N := N))

/-- Helper for Lemma 10.118.3: a finite type algebra admits a surjective presentation by a
multivariable polynomial ring on finitely many generators. -/
theorem exists_surjective_mvPolynomial_presentation :
    ∃ n : ℕ, ∃ π : MvPolynomial (Fin n) R →ₐ[R] S, Function.Surjective π := by
  -- Proof comment: unpack the standard finite-type owner theorem into the concrete polynomial
  -- presentation used in the source proof.
  simpa using
    (Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType R S))

/-- Helper for Lemma 10.118.3: after inverting all nonzero elements of the domain, the generic
fiber of any restricted `R`-module is a free module over the fraction field. -/
lemma fractionRing_localized_restrictScalars_module_free
    {N : Type*} [AddCommGroup N] [Module R N] :
    Module.Free (Localization (nonZeroDivisors R))
      (LocalizedModule (nonZeroDivisors R) N) := by
  -- Proof comment: `Localization (nonZeroDivisors R)` is the fraction field of `R`, and every
  -- module over a field is free.
  infer_instance

/-- Helper for Lemma 10.118.3: a finitely presented polynomial module becomes free after
inverting one nonzero polynomial in the source ring. -/
lemma exists_nonzero_away_polynomial_free_of_finitely_presented_module
    {n : ℕ}
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) N] :
    ∃ g : MvPolynomial (Fin n) R, g ≠ 0 ∧
      Module.Free (Localization.Away g) (LocalizedModule.Away g N) := by
  let P := MvPolynomial (Fin n) R
  letI : Module.Free (Localization (nonZeroDivisors P))
      (LocalizedModule (nonZeroDivisors P) N) := by
    -- Proof comment: over the fraction field of the polynomial domain, every module is free.
    infer_instance
  -- Proof comment: apply the generic localization lemma over the polynomial ring itself.
  simpa [P] using
    (exists_nonzero_away_free_of_localized_finitePresentation (R := P) (N := N))

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 118 3: a surjective polynomial-module map remains surjective after
coefficient-away localization. -/
lemma coeffAway_localized_map_surjective
    {n : ℕ} {f : R}
    {N' N : Type*} [AddCommGroup N'] [Module (MvPolynomial (Fin n) R) N']
    [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (φ : N' →ₗ[MvPolynomial (Fin n) R] N) (hφ : Function.Surjective φ) :
    Function.Surjective
      (LocalizedModule.map (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) φ) := by
  -- Proof comment: localization is an exact base-change operation on the level of surjectivity.
  exact LocalizedModule.map_surjective (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) φ hφ

/-- Helper for Chap10 Lemma 10 118 3: the coefficient-localized polynomial action on an
away-localized polynomial module extends the original polynomial-ring action. -/
theorem away_polynomial_module_isScalarTower_over_source
    {n : ℕ} (f : R)
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N] :
    let A := MvPolynomial (Fin n) (Localization.Away f)
    letI : Module A (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
      away_polynomial_module_over_coeff_localization (R := R) (n := n) f
    IsScalarTower (MvPolynomial (Fin n) R) A
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  dsimp
  let P := MvPolynomial (Fin n) R
  let A := MvPolynomial (Fin n) (Localization.Away f)
  let B := Localization.Away (MvPolynomial.C (σ := Fin n) f)
  let e : A ≃ₐ[P] B := (away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm
  letI : Module A (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
    away_polynomial_module_over_coeff_localization (R := R) (n := n) f
  refine ⟨?_⟩
  intro p a x
  -- Proof comment: rewrite the `A`-action through the direct away-localization ring `B`.
  change e (algebraMap P A p * a) • x = p • (e a • x)
  rw [map_mul]
  rw [e.commutes]
  -- Proof comment: the remaining comparison is the ordinary scalar tower
  -- `P → B → LocalizedModule.Away (C f) N`.
  calc
    (algebraMap P B p * e a) • x = algebraMap P B p • (e a • x) := by
      exact mul_smul (algebraMap P B p) (e a) x
    _ = p • (e a • x) := by
      exact IsScalarTower.algebraMap_smul B p (e a • x)

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 118 3: once the coefficient-away localization of a presentation map
is injective, surjectivity promotes it to a linear equivalence over the direct away ring. -/
noncomputable abbrev coeffAway_localizedLinearEquivOfInjective
    {n : ℕ} {f : R}
    {N' N : Type*} [AddCommGroup N'] [Module (MvPolynomial (Fin n) R) N']
    [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (φ : N' →ₗ[MvPolynomial (Fin n) R] N) (hφ : Function.Surjective φ)
    (hinj : Function.Injective
      (LocalizedModule.map (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) φ)) :
    LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N' ≃ₗ[
      Localization.Away (MvPolynomial.C (σ := Fin n) f)]
      LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N :=
  LinearEquiv.ofBijective
    (LocalizedModule.map (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) φ)
    ⟨hinj, coeffAway_localized_map_surjective (R := R) (n := n) (f := f) φ hφ⟩

/-- Helper for Chap10 Lemma 10 118 3: an injective coefficient-away localized map gives an
`R_f[x]`-linear equivalence between the coefficient-localized polynomial modules. -/
noncomputable abbrev coeffAway_localizedCoeffLinearEquivOfInjective
    {n : ℕ} {f : R}
    {N' N : Type*} [AddCommGroup N'] [Module (MvPolynomial (Fin n) R) N']
    [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (φ : N' →ₗ[MvPolynomial (Fin n) R] N) (hφ : Function.Surjective φ)
    (hinj : Function.Injective
      (LocalizedModule.map (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) φ)) :
    LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N' ≃ₗ[
      MvPolynomial (Fin n) (Localization.Away f)]
      LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N :=
  let P := MvPolynomial (Fin n) R
  let U : Submonoid P := Submonoid.powers (MvPolynomial.C (σ := Fin n) f)
  let A := MvPolynomial (Fin n) (Localization.Away f)
  letI : IsLocalization U A := away_mvPolynomial_C_isLocalization (R := R) (n := n) f
  letI : Module A (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N') :=
    away_polynomial_module_over_coeff_localization (R := R) (n := n) f
  letI : Module A (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
    away_polynomial_module_over_coeff_localization (R := R) (n := n) f
  letI : IsScalarTower P A (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N') :=
    away_polynomial_module_isScalarTower_over_source (R := R) (n := n) f
  letI : IsScalarTower P A (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
    away_polynomial_module_isScalarTower_over_source (R := R) (n := n) f
  (LinearEquiv.restrictScalars P
    (coeffAway_localizedLinearEquivOfInjective (R := R) (n := n) (f := f) φ hφ hinj)
      ).extendScalarsOfIsLocalization U A

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 118 3: the direct-away equivalence obtained from injectivity has
underlying map equal to the localized presentation map. -/
@[simp] theorem coeffAway_localizedLinearEquivOfInjective_toLinearMap
    {n : ℕ} {f : R}
    {N' N : Type*} [AddCommGroup N'] [Module (MvPolynomial (Fin n) R) N']
    [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    (φ : N' →ₗ[MvPolynomial (Fin n) R] N) (hφ : Function.Surjective φ)
    (hinj : Function.Injective
      (LocalizedModule.map (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) φ)) :
    (coeffAway_localizedLinearEquivOfInjective (R := R) (n := n) (f := f) φ hφ hinj).toLinearMap =
      LocalizedModule.map (Submonoid.powers (MvPolynomial.C (σ := Fin n) f)) φ := by
  -- Proof comment: `LinearEquiv.ofBijective` keeps the supplied linear map as its forward map.
  rfl

/-- Helper for Lemma 10.118.3: localizing a finitely presented polynomial module away from `C f`
preserves finite presentation over the direct localized source ring `R[x_1, \dots, x_n]_(C f)`. -/
lemma away_polynomial_module_finitePresentation_over_direct_localization
    {n : ℕ} (f : R)
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) N] :
    Module.FinitePresentation (Localization.Away (MvPolynomial.C (σ := Fin n) f))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  -- Proof comment: finite presentation localizes directly along the powers of `C f`.
  infer_instance

/-- Helper for Lemma 10.118.3: finite presentation transfers across a ring equivalence after
restricting scalars along that equivalence. -/
lemma module_finitePresentation_compHom_of_ringEquiv
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    {N : Type*} [AddCommGroup N] [Module B N] [Module.FinitePresentation B N] :
    let _ : Algebra A B := e.toRingHom.toAlgebra
    let _ : Module A N := Module.compHom N e.toRingHom
    let _ : IsScalarTower A B N := RestrictScalars.isScalarTower A B N
    Module.FinitePresentation A N := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  let _ : Module A N := Module.compHom N e.toRingHom
  let _ : IsScalarTower A B N := RestrictScalars.isScalarTower A B N
  have hB : Module.FinitePresentation A B := by
    -- Proof comment: via the ring equivalence, `B` is just the free rank-one `A`-module.
    exact Module.FinitePresentation.of_equiv (Module.compHom.toLinearEquiv e)
  let _ : Module.FinitePresentation A B := hB
  -- Proof comment: once the target ring is finitely presented over the source, transitivity
  -- upgrades finite presentation of the module through the transported scalar tower.
  exact Module.FinitePresentation.trans (R := A) (S := B) (M := N)

/-- Helper for Lemma 10.118.3: after transporting scalars across the canonical equivalence
`R[x_1, \dots, x_n]_(C f) ≃ R_f[x_1, \dots, x_n]`, the away-localized polynomial module is
finitely presented over the normalized coefficient-localized polynomial ring. -/
lemma away_polynomial_module_finitePresentation_over_coeff_localization
    {n : ℕ} (f : R)
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) N] :
    let A := MvPolynomial (Fin n) (Localization.Away f)
    let _ : Module A (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
      Module.compHom (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N)
        ((away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm.toRingHom)
    Module.FinitePresentation A
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) := by
  dsimp
  let A := MvPolynomial (Fin n) (Localization.Away f)
  let B := Localization.Away (MvPolynomial.C (σ := Fin n) f)
  let e : A ≃+* B := (away_mvPolynomial_C_algEquiv (R := R) (n := n) f).symm.toRingEquiv
  letI : Module.FinitePresentation B
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
    away_polynomial_module_finitePresentation_over_direct_localization
      (R := R) (n := n) f
  -- Proof comment: the only remaining step is the generic ring-equivalence transport from the
  -- direct localization ring to the normalized coefficient-localized polynomial ring.
  simpa [A, B, e] using
    (module_finitePresentation_compHom_of_ringEquiv
      (A := A)
      (B := B)
      e
      (N := LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N))

/-- Helper for Lemma 10.118.3: freeness over `R_f` transports across a linear equivalence from the
canonical away-localized polynomial model to the target coefficient-localized module. -/
lemma away_polynomial_model_free_over_base_of_linearEquiv
    {n : ℕ} (f : R)
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    {T : Type*} [AddCommGroup T] [Module (Localization.Away f) T]
    [Module (MvPolynomial (Fin n) (Localization.Away f)) T]
    [IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f)) T]
    [Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N)]
    (e : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N ≃ₗ[
      MvPolynomial (Fin n) (Localization.Away f)] T) :
    Module.Free (Localization.Away f) T := by
  let _ : Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
    away_polynomial_module_over_coeff_localization (R := R) (n := n) f
  let _ : Module (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
    away_polynomial_module_over_base_localization (R := R) (n := n) f
  let _ : IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
    away_polynomial_module_isScalarTower_over_coeff_localization (R := R) (n := n) f
  -- Proof comment: restrict the polynomial-linear equivalence to `R_f` and transport the free
  -- basis from the canonical source model.
  exact Module.Free.of_equiv' inferInstance <|
    LinearEquiv.restrictScalars (Localization.Away f) e

/-- Helper for Lemma 10.118.3: finite presentation over `R_f[x_1, \dots, x_n]` transports across a
linear equivalence from the canonical away-localized polynomial model. -/
lemma away_polynomial_model_finitePresentation_over_coeff_localization_of_linearEquiv
    {n : ℕ} (f : R)
    {N : Type*} [AddCommGroup N] [Module (MvPolynomial (Fin n) R) N]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) N]
    {T : Type*} [AddCommGroup T]
    [Module (MvPolynomial (Fin n) (Localization.Away f)) T]
    (e : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N ≃ₗ[
      MvPolynomial (Fin n) (Localization.Away f)] T) :
    Module.FinitePresentation (MvPolynomial (Fin n) (Localization.Away f)) T := by
  let _ : Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
    away_polynomial_module_over_coeff_localization (R := R) (n := n) f
  let _ : Module.FinitePresentation
      (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) N) :=
    away_polynomial_module_finitePresentation_over_coeff_localization
      (R := R) (n := n) f
  -- Proof comment: the owner finite-presentation structure is already on the canonical source
  -- model, so this is a direct transport across the linear equivalence.
  exact Module.FinitePresentation.of_equiv e

/-- Helper for Lemma 10.118.3: once `S_f` and `M_f` are finitely presented over the localized
polynomial ring and free over `R_f`, the owner condition `LocalizationCondition R S M f` follows
by finite-presentation transitivity and finite algebra change of scalars. -/
theorem localizationCondition_of_localized_mvPolynomial_module_conditions
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))]
    [Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    [IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))]
    [IsScalarTower (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    [Module.FinitePresentation (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))]
    [Module.FinitePresentation (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    [Module.Free (Localization.Away f) (Localization.Away (algebraMap R S f))]
    [Module.Free (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M)] :
    LocalizationCondition R S M f := by
  let A := MvPolynomial (Fin n) (Localization.Away f)
  letI : Algebra.FinitePresentation (Localization.Away f) A := inferInstance
  letI : Algebra.FinitePresentation A (Localization.Away (algebraMap R S f)) :=
    Algebra.FinitePresentation.of_finitePresentation
      A
      (Localization.Away (algebraMap R S f))
  letI : Algebra.FinitePresentation (Localization.Away f)
      (Localization.Away (algebraMap R S f)) :=
    Algebra.FinitePresentation.trans
      (Localization.Away f)
      A
      (Localization.Away (algebraMap R S f))
  letI : Module.Finite A (Localization.Away (algebraMap R S f)) := inferInstance
  letI : Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) :=
    (Module.FinitePresentation.iff_of_finite_finitePresentation
      (R := A)
      (S := Localization.Away (algebraMap R S f))
      (M := LocalizedModule.Away (algebraMap R S f) M)).1 inferInstance
  -- Proof comment: the localized polynomial presentation already gives algebra finite
  -- presentation of `S_f`, and the finite algebra change-of-scalars bridge turns the localized
  -- polynomial finite presentation of `M_f` into the desired `S_f`-module finite presentation.
  infer_instance

/-- Helper for Lemma 10.118.3: the localized target module action by the coefficient-localized
polynomial ring is automatically compatible with the ambient `R_f`-module structure coming from
the localized target ring. -/
theorem localized_target_module_isScalarTower_over_coeff_localization
    {n : ℕ} (f : R)
    [Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))]
    [Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    [IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))]
    [IsScalarTower (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M)] :
    IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M) := by
  let _ : IsScalarTower (Localization.Away f)
      (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) :=
    IsScalarTower.of_compHom
      (Localization.Away f)
      (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M)
  refine IsScalarTower.of_algebraMap_smul ?_
  intro r x
  calc
    (algebraMap (Localization.Away f) (MvPolynomial (Fin n) (Localization.Away f)) r) • x
        =
          (algebraMap
            (MvPolynomial (Fin n) (Localization.Away f))
            (Localization.Away (algebraMap R S f))
            (algebraMap (Localization.Away f) (MvPolynomial (Fin n) (Localization.Away f)) r)) • x := by
          symm
          exact IsScalarTower.algebraMap_smul
            (Localization.Away (algebraMap R S f))
            (algebraMap (Localization.Away f) (MvPolynomial (Fin n) (Localization.Away f)) r) x
    _ = (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)) r) • x := by
          simp [RingHom.comp_apply, IsScalarTower.algebraMap_eq
            (Localization.Away f)
            (MvPolynomial (Fin n) (Localization.Away f))
            (Localization.Away (algebraMap R S f))]
    _ = r • x := by
          simpa using
            (IsScalarTower.algebraMap_smul
              (Localization.Away (algebraMap R S f))
              r x)

/-- Helper for Lemma 10.118.3: once the away-localized polynomial models are already free over
`R_f`, finitely presented over `R_f[x_1, \dots, x_n]`, and identified with the target
away-localizations by polynomial-linear equivalences, the owner condition follows formally. -/
theorem localizationCondition_of_localized_mvPolynomial_model_linearEquivs
    {n : ℕ} (f : R)
    {S' : Type*} [AddCommGroup S'] [Module (MvPolynomial (Fin n) R) S']
    {M' : Type*} [AddCommGroup M'] [Module (MvPolynomial (Fin n) R) M']
    [Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))]
    [Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    [IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))]
    [IsScalarTower (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M)]
    [Module.FinitePresentation (MvPolynomial (Fin n) R) S']
    [Module.FinitePresentation (MvPolynomial (Fin n) R) M']
    [Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S')]
    [Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M')]
    (eS : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S' ≃ₗ[
      MvPolynomial (Fin n) (Localization.Away f)]
        Localization.Away (algebraMap R S f))
    (eM : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M' ≃ₗ[
      MvPolynomial (Fin n) (Localization.Away f)]
        LocalizedModule.Away (algebraMap R S f) M) :
    LocalizationCondition R S M f := by
  -- Route correction: the proof route is to use the canonical coefficient-localized polynomial
  -- module structures from `away_polynomial_module_over_coeff_localization`, transport finite
  -- presentation across `eS` and `eM`, and then package the resulting instances with
  -- `localizationCondition_of_localized_mvPolynomial_module_conditions`.
  let _ : Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S') :=
    away_polynomial_module_over_coeff_localization (R := R) (n := n) f
  let _ : Module (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S') :=
    away_polynomial_module_over_base_localization (R := R) (n := n) f
  let _ : IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S') :=
    away_polynomial_module_isScalarTower_over_coeff_localization (R := R) (n := n) f
  let _ : Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M') :=
    away_polynomial_module_over_coeff_localization (R := R) (n := n) f
  let _ : Module (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M') :=
    away_polynomial_module_over_base_localization (R := R) (n := n) f
  let _ : IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M') :=
    away_polynomial_module_isScalarTower_over_coeff_localization (R := R) (n := n) f
  let _ : Module.FinitePresentation
      (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) :=
    away_polynomial_model_finitePresentation_over_coeff_localization_of_linearEquiv
      (R := R) (n := n) (N := S') f eS
  let _ : Module.FinitePresentation
      (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M) :=
    away_polynomial_model_finitePresentation_over_coeff_localization_of_linearEquiv
      (R := R) (n := n) (N := M') f eM
  let _ : Module.Free (Localization.Away f)
      (Localization.Away (algebraMap R S f)) :=
    away_polynomial_model_free_over_base_of_linearEquiv
      (R := R) (n := n) (N := S') f eS
  let _ : IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M) :=
    localized_target_module_isScalarTower_over_coeff_localization
      (R := R) (S := S) (M := M) (n := n) f
  let _ : Module.Free (Localization.Away f)
      (LocalizedModule.Away (algebraMap R S f) M) :=
    away_polynomial_model_free_over_base_of_linearEquiv
      (R := R) (n := n) (N := M') f eM
  -- Proof comment: with the two transported finite-presentation instances and the two transported
  -- freeness instances in place, the owner localization condition is exactly the packaged theorem
  -- for the localized polynomial presentation.
  exact localizationCondition_of_localized_mvPolynomial_module_conditions
    (R := R) (S := S) (M := M) (n := n) f


end
