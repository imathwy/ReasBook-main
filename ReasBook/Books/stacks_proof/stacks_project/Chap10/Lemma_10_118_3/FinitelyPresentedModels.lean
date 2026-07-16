import stacks_proof.stacks_project.Chap10.Lemma_10_118_3.GenericFiber

universe u v w

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M]

open GenericFlatness

/-- Helper for Lemma 10.118.3: if a localization `T⁻¹M` is finite over `T⁻¹A`, then some finite
submodule of `M` already localizes to all of `T⁻¹M`. -/
theorem exists_finite_submodule_with_top_localized
    {A : Type v} [CommRing A] (T : Submonoid A)
    {N : Type w} [AddCommGroup N] [Module A N]
    [Module.Finite (Localization T) (LocalizedModule T N)] :
    ∃ N' : Submodule A N,
      Module.Finite A N' ∧
        N'.localized T = ⊤ := by
  classical
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := Localization T) (M := LocalizedModule T N)
  choose yt ht using
    fun i : Fin n ↦ IsLocalizedModule.mk'_surjective T (LocalizedModule.mkLinearMap T N) (x i)
  let y : Fin n → N := fun i ↦ (yt i).1
  let t : Fin n → T := fun i ↦ (yt i).2
  let N' : Submodule A N := Submodule.span A (Set.range y)
  refine ⟨N', ?_, ?_⟩
  · -- The chosen numerators generate `N'`, so `N'` is finite over `A`.
    rw [Module.Finite.iff_fg]
    exact Submodule.fg_span (Set.finite_range y)
  · -- The localized numerators span the localized generators, hence all of `T⁻¹N`.
    apply top_le_iff.mp
    rw [← hx]
    rw [show N'.localized T =
      Submodule.span (Localization T)
        ((LocalizedModule.mkLinearMap T N) '' Set.range y) by
          simpa [N'] using
            (Submodule.localized'_span (Localization T) T (LocalizedModule.mkLinearMap T N)
              (Set.range y))]
    refine Submodule.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨i, rfl⟩
    rw [SetLike.mem_coe, ← IsLocalization.smul_mem_iff (s := t i)]
    rw [← (IsLocalizedModule.mk'_eq_iff (f := LocalizedModule.mkLinearMap T N)).mp (ht i)]
    exact Submodule.subset_span ⟨y i, ⟨i, rfl⟩, rfl⟩

/-- Helper for Lemma 10.118.3: after localizing a surjective presentation, its kernel is finite
because it sits in a short exact sequence with finite middle term and finitely presented cokernel. -/
lemma localized_kernel_finite_of_surjective_presentation
    {A : Type v} [CommRing A] (T : Submonoid A)
    {N : Type w} [AddCommGroup N] [Module A N]
    {P : Type*} [AddCommGroup P] [Module A P]
    (π : P →ₗ[A] N)
    (hπ : Function.Surjective (LocalizedModule.map T π))
    [Module.Finite (Localization T) (LocalizedModule T P)]
    [Module.FinitePresentation (Localization T) (LocalizedModule T N)] :
    Module.Finite (Localization T) (LinearMap.ker (LocalizedModule.map T π)) := by
  -- The localized kernel-subtype map is exact with the localized presentation map.
  have hExact :
      Function.Exact (LinearMap.ker (LocalizedModule.map T π)).subtype
        (LocalizedModule.map T π) := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
  exact Module.Finite.of_exact_of_finitePresentation
    (LinearMap.ker (LocalizedModule.map T π)).subtype
    (LocalizedModule.map T π)
    (Submodule.injective_subtype _)
    hπ
    hExact

/-- Helper for Lemma 10.118.3: if a submodule localizes to the whole localized module, then the
localized inclusion map is surjective. -/
lemma localized_subtype_range_eq_top_of_top_localized
    {A : Type v} [CommRing A] (T : Submonoid A)
    {P : Type*} [AddCommGroup P] [Module A P]
    (N : Submodule A P)
    (hN : N.localized T = ⊤) :
    LinearMap.range (LocalizedModule.map T N.subtype) = ⊤ := by
  -- Rewrite the target as surjectivity and pull a localized numerator back through `hN`.
  exact LinearMap.range_eq_top.2 <| by
    intro z
    have hz : z ∈ N.localized T := by
      simpa [hN] using
        (show z ∈ (⊤ : Submodule (Localization T) (LocalizedModule T P)) from trivial)
    rcases (Submodule.mem_localized'
        (S := Localization T) (p := T) (f := LocalizedModule.mkLinearMap T P) (M' := N) z).mp hz
      with ⟨x, hx, s, rfl⟩
    refine ⟨LocalizedModule.mk ⟨x, hx⟩ s, ?_⟩
    simpa [IsLocalizedModule.mk_eq_mk'] using
      (LocalizedModule.map_mk (S := T) N.subtype ⟨x, hx⟩ s)

/-- Helper for Lemma 10.118.3: if `N` already localizes to the whole source, then localizing the
image of `N` under a linear map recovers the full localized image. -/
lemma localized_image_of_top_localized_submodule
    {A : Type v} [CommRing A] (T : Submonoid A)
    {P : Type*} [AddCommGroup P] [Module A P]
    {Q : Type*} [AddCommGroup Q] [Module A Q]
    (ι : P →ₗ[A] Q)
    (N : Submodule A P)
    (hN : N.localized T = ⊤) :
    (N.map ι).localized T = LinearMap.range (LocalizedModule.map T ι) := by
  apply le_antisymm
  · -- Every localized image element comes from a localized source element in `N`.
    intro z hz
    rcases (Submodule.mem_localized'
        (S := Localization T) (p := T) (f := LocalizedModule.mkLinearMap T Q) (M' := N.map ι) z).mp
        hz with ⟨x, hx, s, rfl⟩
    rcases hx with ⟨y, hy, rfl⟩
    refine ⟨LocalizedModule.mk y s, ?_⟩
    simpa [IsLocalizedModule.mk_eq_mk'] using
      (LocalizedModule.map_mk (S := T) ι y s)
  · -- Conversely, use `hN` to rewrite any localized source element with numerator in `N`.
    rintro z ⟨y, rfl⟩
    have hy : y ∈ N.localized T := by
      simpa [hN] using (show y ∈ (⊤ : Submodule (Localization T) (LocalizedModule T P)) from trivial)
    rcases (Submodule.mem_localized'
        (S := Localization T) (p := T) (f := LocalizedModule.mkLinearMap T P) (M' := N) y).mp hy
      with ⟨x, hx, s, hs⟩
    rw [← hs]
    exact (Submodule.mem_localized'
      (S := Localization T) (p := T) (f := LocalizedModule.mkLinearMap T Q) (M' := N.map ι)
      (((LocalizedModule.map T) ι) (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap T P) x s))).2
      ⟨ι x, ⟨x, hx, rfl⟩, s, by
        exact
          (IsLocalizedModule.map_mk'
            (S := T)
            (f := LocalizedModule.mkLinearMap T P)
            (g := LocalizedModule.mkLinearMap T Q)
            ι x s).symm⟩

/-- Helper for Lemma 10.118.3: if a finite submodule of the kernel localizes to all of the
localized kernel module, then its image in the ambient module localizes to the localized kernel
submodule of the presentation. -/
lemma kernel_image_localized_eq_localized_kernel
    {A : Type v} [CommRing A] (T : Submonoid A)
    {N : Type w} [AddCommGroup N] [Module A N]
    {P : Type*} [AddCommGroup P] [Module A P]
    (π : P →ₗ[A] N)
    (Ksub : Submodule A (LinearMap.ker π))
    (hKsub : Ksub.localized T = ⊤) :
    (Ksub.map (LinearMap.ker π).subtype).localized T = (LinearMap.ker π).localized' (Localization T)
      T (LocalizedModule.mkLinearMap T P) := by
  -- First localize the finite kernel submodule inside the ambient free module.
  calc
    (Ksub.map (LinearMap.ker π).subtype).localized T =
        LinearMap.range (LocalizedModule.map T (LinearMap.ker π).subtype) := by
      simpa using
        localized_image_of_top_localized_submodule
          (T := T) (LinearMap.ker π).subtype Ksub hKsub
    _ = (LinearMap.ker π).localized' (Localization T) T (LocalizedModule.mkLinearMap T P) := by
      -- Then identify that localized range with the localized kernel by taking `N = ⊤`.
      symm
      simpa [Submodule.localized, Submodule.map_top, Submodule.range_subtype] using
        localized_image_of_top_localized_submodule
          (T := T) (LinearMap.ker π).subtype (⊤ : Submodule A (LinearMap.ker π))
          (by simp [Submodule.localized])

/-- Helper for Lemma 10.118.3: the inverse of `localizedQuotientEquiv` sends a localized quotient
generator to the quotient class of the localized numerator. -/
lemma localized_quotient_equiv_symm_apply_mk
    {A : Type v} [CommRing A] (T : Submonoid A)
    {P : Type*} [AddCommGroup P] [Module A P]
    (K0 : Submodule A P) (x : P) :
    (localizedQuotientEquiv T K0).symm
      (LocalizedModule.mkLinearMap T (P ⧸ K0) (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap T P x) := by
  -- The canonical localization equivalence is characterized by its action on quotient generators.
  simpa [localizedQuotientEquiv, Submodule.toLocalizedQuotient] using
    (IsLocalizedModule.linearEquiv_symm_apply
      (S := T)
      (f := K0.toLocalizedQuotient T)
      (g := LocalizedModule.mkLinearMap T (P ⧸ K0))
      (x := Submodule.Quotient.mk x))

/-- Helper for Lemma 10.118.3: the full quotient-comparison composite sends each localized quotient
generator to the corresponding localized image under the presentation map. -/
lemma localized_quotient_comparison_apply_mk
    {A : Type v} [CommRing A] (T : Submonoid A)
    {N : Type w} [AddCommGroup N] [Module A N]
    {P : Type*} [AddCommGroup P] [Module A P]
    (π : P →ₗ[A] N)
    (K0 : Submodule A P)
    (hkerloc : K0.localized T = LinearMap.ker (LocalizedModule.map T π))
    (hπ : Function.Surjective (LocalizedModule.map T π))
    (x : P) :
    (((localizedQuotientEquiv T K0).symm ≪≫ₗ
        Submodule.quotEquivOfEq _ _ hkerloc ≪≫ₗ
        (LocalizedModule.map T π).quotKerEquivOfSurjective hπ)
      (LocalizedModule.mkLinearMap T (P ⧸ K0) (Submodule.Quotient.mk x))) =
        LocalizedModule.mkLinearMap T N (π x) := by
  -- Route correction: compute the whole quotient comparison on generators before comparing maps.
  simp only [LinearEquiv.trans_apply]
  rw [localized_quotient_equiv_symm_apply_mk]
  rw [Submodule.quotEquivOfEq_mk]
  simpa using
    (LinearMap.quotKerEquivOfSurjective_apply_mk
      (f := LocalizedModule.map T π)
      (hf := hπ)
      (x := LocalizedModule.mkLinearMap T P x))

/-- Helper for Lemma 10.118.3: if the localized relation submodule agrees with the localized
kernel of a presentation, then the induced map on the quotient becomes an isomorphism after
localization. -/
lemma localized_quotient_equiv_of_surjective_and_kernel_match
    {A : Type v} [CommRing A] (T : Submonoid A)
    {N : Type w} [AddCommGroup N] [Module A N]
    {P : Type*} [AddCommGroup P] [Module A P]
    (π : P →ₗ[A] N)
    (K0 : Submodule A P)
    (fbar : P ⧸ K0 →ₗ[A] N)
    (hπ : Function.Surjective (LocalizedModule.map T π))
    (hfbar : fbar.comp (Submodule.mkQ K0) = π)
    (hK0 : K0.localized T = (LinearMap.ker π).localized' (Localization T) T
      (LocalizedModule.mkLinearMap T P)) :
    ∃ e : LocalizedModule T (P ⧸ K0) ≃ₗ[Localization T] LocalizedModule T N,
      e.toLinearMap = LocalizedModule.map T fbar := by
  have hkerloc : K0.localized T = LinearMap.ker (LocalizedModule.map T π) := by
    -- Rewrite the localized relation module into the actual kernel of the localized presentation.
    calc
      K0.localized T = (LinearMap.ker π).localized' (Localization T) T
          (LocalizedModule.mkLinearMap T P) := hK0
      _ = LinearMap.ker (LocalizedModule.map T π) := by
        simpa using
          (LinearMap.localized'_ker_eq_ker_localizedMap
            (S := Localization T)
            (p := T)
            (f := LocalizedModule.mkLinearMap T P)
            (f' := LocalizedModule.mkLinearMap T N)
            (g := π))
  let e : LocalizedModule T (P ⧸ K0) ≃ₗ[Localization T] LocalizedModule T N :=
    (localizedQuotientEquiv T K0).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hkerloc ≪≫ₗ
      (LocalizedModule.map T π).quotKerEquivOfSurjective hπ
  refine ⟨e, ?_⟩
  have hcomp :
      e.toLinearMap.restrictScalars A ∘ₗ LocalizedModule.mkLinearMap T (P ⧸ K0) =
        (LocalizedModule.map T fbar).restrictScalars A ∘ₗ LocalizedModule.mkLinearMap T (P ⧸ K0) := by
    ext x
    -- Compare both maps on the quotient generators coming from `P`.
    change e (LocalizedModule.mkLinearMap T (P ⧸ K0) (Submodule.Quotient.mk x)) =
      (LocalizedModule.map T fbar) (LocalizedModule.mkLinearMap T (P ⧸ K0) (Submodule.Quotient.mk x))
    rw [localized_quotient_comparison_apply_mk
      (T := T) (π := π) (K0 := K0) (hkerloc := hkerloc) (hπ := hπ) (x := x)]
    have hfbar_apply : fbar (Submodule.Quotient.mk x) = π x := by
      exact LinearMap.congr_fun hfbar x
    simpa [hfbar_apply] using
      (IsLocalizedModule.map_apply
        (S := T)
        (f := LocalizedModule.mkLinearMap T (P ⧸ K0))
        (g := LocalizedModule.mkLinearMap T N)
        (h := fbar)
        (x := Submodule.Quotient.mk x))
  have hEqA :
      e.toLinearMap.restrictScalars A = (LocalizedModule.map T fbar).restrictScalars A := by
    exact IsLocalizedModule.linearMap_ext
      (S := T)
      (LocalizedModule.mkLinearMap T (P ⧸ K0))
      (LocalizedModule.mkLinearMap T N)
      hcomp
  -- Equality after restricting scalars already determines the localized linear map.
  ext x
  exact LinearMap.congr_fun hEqA x

/-- Helper for Lemma 10.118.3: if the localized presentation map is surjective and its localized
kernel is finite, then the localization of the source-side kernel is finite as well. -/
lemma source_kernel_localized_finite_of_surjective_presentation
    {A : Type v} [CommRing A] (T : Submonoid A)
    {N : Type w} [AddCommGroup N] [Module A N]
    {P : Type*} [AddCommGroup P] [Module A P]
    (π : P →ₗ[A] N)
    (hπ : Function.Surjective (LocalizedModule.map T π))
    [Module.Finite (Localization T) (LocalizedModule T P)]
    [Module.FinitePresentation (Localization T) (LocalizedModule T N)] :
    Module.Finite (Localization T) (LocalizedModule T (LinearMap.ker π)) := by
  let κ : LinearMap.ker π →ₗ[A] LinearMap.ker (LocalizedModule.map T π) :=
    LinearMap.toKerIsLocalized
      (p := T)
      (f := LocalizedModule.mkLinearMap T P)
      (f' := LocalizedModule.mkLinearMap T N)
      π
  let _ : IsLocalizedModule T κ :=
    LinearMap.toKerLocalized_isLocalizedModule
      (S := Localization T)
      (p := T)
      (f := LocalizedModule.mkLinearMap T P)
      (f' := LocalizedModule.mkLinearMap T N)
      π
  let _ : Module.Finite (Localization T) (LinearMap.ker (LocalizedModule.map T π)) :=
    localized_kernel_finite_of_surjective_presentation (T := T) π hπ
  -- Transfer finiteness back across the canonical localization equivalence on kernels.
  exact Module.Finite.equiv
    (LinearEquiv.extendScalarsOfIsLocalization
      (S := T)
      (A := Localization T)
      (IsLocalizedModule.iso T κ)).symm

/-- Helper for Lemma 10.118.3: the kernel of the source presentation contains a finite submodule
whose localization is the entire localized kernel module. -/
lemma exists_finite_kernel_submodule_with_top_localized
    {A : Type v} [CommRing A] (T : Submonoid A)
    {N : Type w} [AddCommGroup N] [Module A N]
    {P : Type*} [AddCommGroup P] [Module A P]
    (π : P →ₗ[A] N)
    (hπ : Function.Surjective (LocalizedModule.map T π))
    [Module.Finite (Localization T) (LocalizedModule T P)]
    [Module.FinitePresentation (Localization T) (LocalizedModule T N)] :
    ∃ Ksub : Submodule A (LinearMap.ker π),
      Module.Finite A Ksub ∧
        Ksub.localized T = ⊤ := by
  let _ : Module.Finite (Localization T) (LocalizedModule T (LinearMap.ker π)) :=
    source_kernel_localized_finite_of_surjective_presentation (T := T) π hπ
  -- Apply the finite-submodule localization theorem to the source kernel module itself.
  exact exists_finite_submodule_with_top_localized (T := T) (N := LinearMap.ker π)

/-- Helper for Lemma 10.118.3: the image of a submodule of `ker π` still lies in `ker π`, so the
presentation map descends to the quotient by that image. -/
lemma kernel_submodule_image_le_ker
    {A : Type v} [CommRing A]
    {N : Type w} [AddCommGroup N] [Module A N]
    {P : Type*} [AddCommGroup P] [Module A P]
    (π : P →ₗ[A] N)
    (Ksub : Submodule A (LinearMap.ker π)) :
    Ksub.map (LinearMap.ker π).subtype ≤ LinearMap.ker π := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.2

/-- Helper for Lemma 10.118.3: when `N` is already finite over `A`, the localized finitely
presented approximation can be chosen with a surjective comparison map, matching the source
presentation-quotient construction. -/
theorem exists_finitePresentation_surjective_model_with_localizedLinearEquiv
    {A : Type v} [CommRing A] (T : Submonoid A)
    {N : Type w} [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.FinitePresentation (Localization T) (LocalizedModule T N)] :
    ∃ (N' : Type v) (_ : AddCommGroup N') (_ : Module A N') (_ : Module.FinitePresentation A N')
      (f : N' →ₗ[A] N) (_ : Function.Surjective f)
      (e : LocalizedModule T N' ≃ₗ[Localization T] LocalizedModule T N),
      e.toLinearMap = LocalizedModule.map T f := by
  classical
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' A N
  have hπ_surj : Function.Surjective (LocalizedModule.map T π) :=
    -- The chosen finite presentation of `N` stays surjective after localization.
    LocalizedModule.map_surjective T π hπ
  let _ : Module.Finite (Localization T) (LocalizedModule T (Fin m → A)) := inferInstance
  obtain ⟨Ksub, hKsub_finite, hKsub_top⟩ :=
    exists_finite_kernel_submodule_with_top_localized (T := T) (π := π) hπ_surj
  let K0 : Submodule A (Fin m → A) := Ksub.map (LinearMap.ker π).subtype
  let fbar : (Fin m → A) ⧸ K0 →ₗ[A] N :=
    K0.liftQ π (kernel_submodule_image_le_ker (π := π) Ksub)
  have hfbar : fbar.comp (Submodule.mkQ K0) = π := by
    -- By construction, the descended quotient map agrees with the original surjection.
    simpa [fbar] using K0.liftQ_mkQ π (kernel_submodule_image_le_ker (π := π) Ksub)
  have hfbar_surj : Function.Surjective fbar := by
    intro y
    rcases hπ y with ⟨x, rfl⟩
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    exact LinearMap.congr_fun hfbar x
  have hK0_fg : K0.FG := by
    let _ : Module.Finite A Ksub := hKsub_finite
    have hKsub_fg : Ksub.FG :=
      Submodule.FG.of_finite (R := A) (M := LinearMap.ker π) (N := Ksub)
    -- The finite relation module stays finitely generated after mapping into the free source.
    simpa [K0] using
      Submodule.FG.map (LinearMap.ker π).subtype hKsub_fg
  let _ : Module.FinitePresentation A ((Fin m → A) ⧸ K0) :=
    Module.finitePresentation_of_surjective (Submodule.mkQ K0) (Submodule.mkQ_surjective _) <| by
      -- The quotient relations are exactly `K0`.
      change (LinearMap.ker (Submodule.mkQ K0)).FG
      simpa using hK0_fg
  have hK0 :
      K0.localized T = (LinearMap.ker π).localized' (Localization T) T
        (LocalizedModule.mkLinearMap T (Fin m → A)) := by
    -- Localizing the chosen finite relation module recovers the full localized kernel.
    simpa [K0] using
      kernel_image_localized_eq_localized_kernel (T := T) (π := π) Ksub hKsub_top
  obtain ⟨e, he⟩ :=
    localized_quotient_equiv_of_surjective_and_kernel_match
      (T := T) (π := π) (K0 := K0) fbar hπ_surj hfbar hK0
  -- This is the source-faithful quotient model: finitely presented, surjective onto `N`, and
  -- equal to `N` after localizing at `T`.
  exact
    ⟨(Fin m → A) ⧸ K0, inferInstance, inferInstance, inferInstance, fbar, hfbar_surj, e, he⟩

/-- Helper for Lemma 10.118.3: a finitely presented module that is already free after localizing at
all nonzero elements of the domain becomes free after inverting one nonzero element. -/
lemma exists_nonzero_away_free_of_localized_finitePresentation
    {N : Type w} [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R N]
    [Module.Free (Localization (nonZeroDivisors R))
      (LocalizedModule (nonZeroDivisors R) N)] :
    ∃ f : R, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule.Away f N) := by
  obtain ⟨f, hf, hfree, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (S := nonZeroDivisors R)
    (f := LocalizedModule.mkLinearMap (nonZeroDivisors R) N)
    (Rₛ := Localization (nonZeroDivisors R))
  -- Mathlib already spreads freeness from the total localization to one away localization.
  exact ⟨f, mem_nonZeroDivisors_iff_ne_zero.mp hf, hfree⟩

/-- Helper for Chap10 Lemma 10 118 3: a finitely presented module over the domain becomes free
after inverting one nonzero coefficient. -/
lemma exists_nonzero_away_free_of_finitelyPresented_module_over_domain
    {N : Type w} [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R N] :
    ∃ f : R, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule.Away f N) := by
  let _ : Module.Free (Localization (nonZeroDivisors R))
      (LocalizedModule (nonZeroDivisors R) N) := by
    -- Proof comment: over the fraction field of `R`, every localized module is a vector space.
    infer_instance
  -- Proof comment: mathlib spreads a free generic fiber of a finitely presented module to one
  -- principal open subset of the domain.
  exact exists_nonzero_away_free_of_localized_finitePresentation (R := R) (N := N)

/-- Helper for Lemma 10.118.3: a torsion-free module over a domain embeds into any localization
whose denominators are non-zero-divisors. -/
lemma localizedModule_mkLinearMap_injective_of_le_nonZeroDivisors
    {A : Type v} [CommRing A] [IsDomain A]
    {T : Submonoid A}
    {N : Type w} [AddCommGroup N] [Module A N]
    [Module.IsTorsionFree A N]
    (hT : T ≤ nonZeroDivisors A) :
    Function.Injective (LocalizedModule.mkLinearMap T N) := by
  intro x y hxy
  -- Proof comment: move the equality to the kernel of the localization map, then clear the
  -- denominator using torsion-freeness because every element of `T` is regular.
  rw [← sub_eq_zero]
  have hzero : LocalizedModule.mkLinearMap T N (x - y) = 0 := by
    simpa [map_sub] using sub_eq_zero.mpr hxy
  rw [← LinearMap.mem_ker, LocalizedModule.mem_ker_mkLinearMap_iff] at hzero
  rcases hzero with ⟨s, hs, hsxy⟩
  exact (smul_eq_zero_iff_right
    (mem_nonZeroDivisors_iff_ne_zero.mp (hT hs))).mp hsxy

/-- Helper for Lemma 10.118.3: a free module over a domain embeds into any localization whose
denominators are non-zero-divisors. -/
lemma localizedModule_mkLinearMap_injective_of_free
    {A : Type v} [CommRing A] [IsDomain A]
    {T : Submonoid A}
    {N : Type w} [AddCommGroup N] [Module A N]
    [Module.Free A N]
    (hT : T ≤ nonZeroDivisors A) :
    Function.Injective (LocalizedModule.mkLinearMap T N) := by
  let _ : Module.IsTorsionFree A N := inferInstance
  -- Proof comment: free modules are torsion-free over a domain, so the previous localization
  -- injectivity criterion applies directly.
  exact localizedModule_mkLinearMap_injective_of_le_nonZeroDivisors
    (A := A) (T := T) (N := N) hT


end
