import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_5_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]
variable (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: choose finitely many elements of `M` whose images generate `LocalizedModule S M`
-- over `Localization S`, and let `M'` be the submodule they generate. Then the localized
-- submodule `M'.localized S` is all of `LocalizedModule S M`.
/-- Lemma 10.126.4 (1): if the localization `S⁻¹M` is finite over `S⁻¹R`, then some finitely
generated submodule of `M` has the same localization as `M`. -/
@[stacks 05N6]
theorem exists_finite_submodule_with_top_localized
    [Module.Finite (Localization S) (LocalizedModule S M)] :
    ∃ M' : Submodule R M,
      Module.Finite R M' ∧
        M'.localized S = ⊤ := by
  classical
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := Localization S) (M := LocalizedModule S M)
  choose yt ht using
    fun i : Fin n ↦ IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) (x i)
  let y : Fin n → M := fun i ↦ (yt i).1
  let t : Fin n → S := fun i ↦ (yt i).2
  let M' : Submodule R M := Submodule.span R (Set.range y)
  refine ⟨M', ?_, ?_⟩
  · -- The chosen numerators generate `M'`, so `M'` is finite over `R`.
    rw [Module.Finite.iff_fg]
    exact Submodule.fg_span (Set.finite_range y)
  · -- The localized numerators span the localized generators, hence all of `S⁻¹M`.
    apply top_le_iff.mp
    rw [← hx]
    rw [show M'.localized S =
      Submodule.span (Localization S)
        ((LocalizedModule.mkLinearMap S M) '' Set.range y) by
          simpa [M'] using
            (Submodule.localized'_span (Localization S) S (LocalizedModule.mkLinearMap S M)
              (Set.range y))]
    refine Submodule.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨i, rfl⟩
    rw [SetLike.mem_coe, ← IsLocalization.smul_mem_iff (s := t i)]
    rw [← (IsLocalizedModule.mk'_eq_iff (f := LocalizedModule.mkLinearMap S M)).mp (ht i)]
    exact Submodule.subset_span ⟨y i, ⟨i, rfl⟩, rfl⟩

/-- Helper for Lemma 10.126.4: after localizing a surjective presentation, its kernel is finite
because it sits in a short exact sequence with finite middle term and finitely presented cokernel. -/
lemma localized_kernel_finite_of_surjective_presentation
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (hπ : Function.Surjective (LocalizedModule.map S π))
    [Module.Finite (Localization S) (LocalizedModule S F)]
    [Module.FinitePresentation (Localization S) (LocalizedModule S M)] :
    Module.Finite (Localization S) (LinearMap.ker (LocalizedModule.map S π)) := by
  -- The localized kernel-subtype map is exact with the localized presentation map.
  have hExact :
      Function.Exact (LinearMap.ker (LocalizedModule.map S π)).subtype
        (LocalizedModule.map S π) := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
  exact Module.Finite.of_exact_of_finitePresentation
    (LinearMap.ker (LocalizedModule.map S π)).subtype
    (LocalizedModule.map S π)
    (Submodule.injective_subtype _)
    hπ
    hExact

/-- Helper for Lemma 10.126.4: if a submodule localizes to the whole localized module, then the
localized inclusion map is surjective. -/
lemma localized_subtype_range_eq_top_of_top_localized
    {K : Type*} [AddCommGroup K] [Module R K]
    (N : Submodule R K)
    (hN : N.localized S = ⊤) :
    LinearMap.range (LocalizedModule.map S N.subtype) = ⊤ := by
  -- Rewrite the target as surjectivity and pull a localized numerator back through `hN`.
  exact LinearMap.range_eq_top.2 <| by
    intro z
    have hz : z ∈ N.localized S := by
      simpa [hN] using
        (show z ∈ (⊤ : Submodule (Localization S) (LocalizedModule S K)) from trivial)
    rcases (Submodule.mem_localized'
        (S := Localization S) (p := S) (f := LocalizedModule.mkLinearMap S K) (M' := N) z).mp hz
      with ⟨x, hx, s, rfl⟩
    refine ⟨LocalizedModule.mk ⟨x, hx⟩ s, ?_⟩
    simpa [IsLocalizedModule.mk_eq_mk'] using
      (LocalizedModule.map_mk (S := S) N.subtype ⟨x, hx⟩ s)

/-- Helper for Lemma 10.126.4: if `N` already localizes to the whole source, then localizing the
image of `N` under a linear map recovers the full localized image. -/
lemma localized_image_of_top_localized_submodule
    {K : Type*} [AddCommGroup K] [Module R K]
    {F : Type*} [AddCommGroup F] [Module R F]
    (ι : K →ₗ[R] F)
    (N : Submodule R K)
    (hN : N.localized S = ⊤) :
    (N.map ι).localized S = LinearMap.range (LocalizedModule.map S ι) := by
  apply le_antisymm
  · -- Every localized image element comes from a localized source element in `N`.
    intro z hz
    rcases (Submodule.mem_localized'
        (S := Localization S) (p := S) (f := LocalizedModule.mkLinearMap S F) (M' := N.map ι) z).mp
        hz with ⟨x, hx, s, rfl⟩
    rcases hx with ⟨y, hy, rfl⟩
    refine ⟨LocalizedModule.mk y s, ?_⟩
    simpa [IsLocalizedModule.mk_eq_mk'] using
      (LocalizedModule.map_mk (S := S) ι y s)
  · -- Conversely, use `hN` to rewrite any localized source element with numerator in `N`.
    rintro z ⟨y, rfl⟩
    have hy : y ∈ N.localized S := by
      simpa [hN] using (show y ∈ (⊤ : Submodule (Localization S) (LocalizedModule S K)) from trivial)
    rcases (Submodule.mem_localized'
        (S := Localization S) (p := S) (f := LocalizedModule.mkLinearMap S K) (M' := N) y).mp hy
      with ⟨x, hx, s, hs⟩
    rw [← hs]
    exact (Submodule.mem_localized'
      (S := Localization S) (p := S) (f := LocalizedModule.mkLinearMap S F) (M' := N.map ι)
      (((LocalizedModule.map S) ι) (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S K) x s))).2
      ⟨ι x, ⟨x, hx, rfl⟩, s, by
        exact
          (IsLocalizedModule.map_mk'
            (S := S)
            (f := LocalizedModule.mkLinearMap S K)
            (g := LocalizedModule.mkLinearMap S F)
            ι x s).symm⟩

/-- Helper for Lemma 10.126.4: if a finite submodule of the kernel localizes to all of the
localized kernel module, then its image in the ambient module localizes to the localized kernel
submodule of the presentation. -/
lemma kernel_image_localized_eq_localized_kernel
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (Ksub : Submodule R (LinearMap.ker π))
    (hKsub : Ksub.localized S = ⊤) :
    (Ksub.map (LinearMap.ker π).subtype).localized S = (LinearMap.ker π).localized' (Localization S)
      S (LocalizedModule.mkLinearMap S F) := by
  -- First localize the finite kernel submodule inside the ambient free module.
  calc
    (Ksub.map (LinearMap.ker π).subtype).localized S =
        LinearMap.range (LocalizedModule.map S (LinearMap.ker π).subtype) := by
      simpa using
        localized_image_of_top_localized_submodule
          (S := S) (LinearMap.ker π).subtype Ksub hKsub
    _ = (LinearMap.ker π).localized' (Localization S) S (LocalizedModule.mkLinearMap S F) := by
      -- Then identify that localized range with the localized kernel by taking `N = ⊤`.
      symm
      simpa [Submodule.localized, Submodule.map_top, Submodule.range_subtype] using
        localized_image_of_top_localized_submodule
          (S := S) (LinearMap.ker π).subtype (⊤ : Submodule R (LinearMap.ker π))
          (by simp [Submodule.localized])

/-- Helper for Lemma 10.126.4: the inverse of `localizedQuotientEquiv` sends a localized quotient
generator to the quotient class of the localized numerator. -/
lemma localized_quotient_equiv_symm_apply_mk
    {F : Type*} [AddCommGroup F] [Module R F]
    (K0 : Submodule R F) (x : F) :
    (localizedQuotientEquiv S K0).symm
      (LocalizedModule.mkLinearMap S (F ⧸ K0) (Submodule.Quotient.mk x)) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap S F x) := by
  -- The canonical localization equivalence is characterized by its action on quotient generators.
  simpa [localizedQuotientEquiv, Submodule.toLocalizedQuotient] using
    (IsLocalizedModule.linearEquiv_symm_apply
      (S := S)
      (f := K0.toLocalizedQuotient S)
      (g := LocalizedModule.mkLinearMap S (F ⧸ K0))
      (x := Submodule.Quotient.mk x))

/-- Helper for Lemma 10.126.4: the full quotient-comparison composite sends each localized quotient
generator to the corresponding localized image under the presentation map. -/
lemma localized_quotient_comparison_apply_mk
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (K0 : Submodule R F)
    (hkerloc : K0.localized S = LinearMap.ker (LocalizedModule.map S π))
    (hπ : Function.Surjective (LocalizedModule.map S π))
    (x : F) :
    (((localizedQuotientEquiv S K0).symm ≪≫ₗ
        Submodule.quotEquivOfEq _ _ hkerloc ≪≫ₗ
        (LocalizedModule.map S π).quotKerEquivOfSurjective hπ)
      (LocalizedModule.mkLinearMap S (F ⧸ K0) (Submodule.Quotient.mk x))) =
        LocalizedModule.mkLinearMap S M (π x) := by
  -- Route correction: compute the whole quotient comparison on generators before comparing maps.
  simp only [LinearEquiv.trans_apply]
  rw [localized_quotient_equiv_symm_apply_mk]
  rw [Submodule.quotEquivOfEq_mk]
  simpa using
    (LinearMap.quotKerEquivOfSurjective_apply_mk
      (f := LocalizedModule.map S π)
      (hf := hπ)
      (x := LocalizedModule.mkLinearMap S F x))

/-- Helper for Lemma 10.126.4: if the localized relation submodule agrees with the localized
kernel of a presentation, then the induced map on the quotient becomes an isomorphism after
localization. -/
lemma localized_quotient_equiv_of_surjective_and_kernel_match
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (K0 : Submodule R F)
    (fbar : F ⧸ K0 →ₗ[R] M)
    (hπ : Function.Surjective (LocalizedModule.map S π))
    (hfbar : fbar.comp (Submodule.mkQ K0) = π)
    (hK0 : K0.localized S = (LinearMap.ker π).localized' (Localization S) S
      (LocalizedModule.mkLinearMap S F)) :
    ∃ e : LocalizedModule S (F ⧸ K0) ≃ₗ[Localization S] LocalizedModule S M,
      e.toLinearMap = LocalizedModule.map S fbar := by
  have hkerloc : K0.localized S = LinearMap.ker (LocalizedModule.map S π) := by
    -- Rewrite the localized relation module into the actual kernel of the localized presentation.
    calc
      K0.localized S = (LinearMap.ker π).localized' (Localization S) S
          (LocalizedModule.mkLinearMap S F) := hK0
      _ = LinearMap.ker (LocalizedModule.map S π) := by
        simpa using
          (LinearMap.localized'_ker_eq_ker_localizedMap
            (S := Localization S)
            (p := S)
            (f := LocalizedModule.mkLinearMap S F)
            (f' := LocalizedModule.mkLinearMap S M)
            (g := π))
  let e : LocalizedModule S (F ⧸ K0) ≃ₗ[Localization S] LocalizedModule S M :=
    (localizedQuotientEquiv S K0).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hkerloc ≪≫ₗ
      (LocalizedModule.map S π).quotKerEquivOfSurjective hπ
  refine ⟨e, ?_⟩
  have hcomp :
      e.toLinearMap.restrictScalars R ∘ₗ LocalizedModule.mkLinearMap S (F ⧸ K0) =
        (LocalizedModule.map S fbar).restrictScalars R ∘ₗ LocalizedModule.mkLinearMap S (F ⧸ K0) := by
    ext x
    -- Compare both maps on the quotient generators coming from `F`.
    change e (LocalizedModule.mkLinearMap S (F ⧸ K0) (Submodule.Quotient.mk x)) =
      (LocalizedModule.map S fbar) (LocalizedModule.mkLinearMap S (F ⧸ K0) (Submodule.Quotient.mk x))
    rw [localized_quotient_comparison_apply_mk
      (S := S) (π := π) (K0 := K0) (hkerloc := hkerloc) (hπ := hπ) (x := x)]
    have hfbar_apply : fbar (Submodule.Quotient.mk x) = π x := by
      exact LinearMap.congr_fun hfbar x
    simpa [hfbar_apply] using
      (IsLocalizedModule.map_apply
        (S := S)
        (f := LocalizedModule.mkLinearMap S (F ⧸ K0))
        (g := LocalizedModule.mkLinearMap S M)
        (h := fbar)
        (x := Submodule.Quotient.mk x))
  have hEqR :
      e.toLinearMap.restrictScalars R = (LocalizedModule.map S fbar).restrictScalars R := by
    exact IsLocalizedModule.linearMap_ext
      (S := S)
      (LocalizedModule.mkLinearMap S (F ⧸ K0))
      (LocalizedModule.mkLinearMap S M)
      hcomp
  -- Equality after restricting scalars already determines the localized linear map.
  ext x
  exact LinearMap.congr_fun hEqR x

/-- Helper for Lemma 10.126.4: if the localized presentation map is surjective and its localized
kernel is finite, then the localization of the source-side kernel is finite as well. -/
lemma source_kernel_localized_finite_of_surjective_presentation
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (hπ : Function.Surjective (LocalizedModule.map S π))
    [Module.Finite (Localization S) (LocalizedModule S F)]
    [Module.FinitePresentation (Localization S) (LocalizedModule S M)] :
    Module.Finite (Localization S) (LocalizedModule S (LinearMap.ker π)) := by
  let κ : LinearMap.ker π →ₗ[R] LinearMap.ker (LocalizedModule.map S π) :=
    LinearMap.toKerIsLocalized
      (p := S)
      (f := LocalizedModule.mkLinearMap S F)
      (f' := LocalizedModule.mkLinearMap S M)
      π
  let _ : IsLocalizedModule S κ :=
    LinearMap.toKerLocalized_isLocalizedModule
      (S := Localization S)
      (p := S)
      (f := LocalizedModule.mkLinearMap S F)
      (f' := LocalizedModule.mkLinearMap S M)
      π
  let _ : Module.Finite (Localization S) (LinearMap.ker (LocalizedModule.map S π)) :=
    localized_kernel_finite_of_surjective_presentation (S := S) π hπ
  -- Transfer finiteness back across the canonical localization equivalence on kernels.
  exact Module.Finite.equiv
    (LinearEquiv.extendScalarsOfIsLocalization
      (S := S)
      (A := Localization S)
      (IsLocalizedModule.iso S κ)).symm

/-- Helper for Lemma 10.126.4: the kernel of the source presentation contains a finite submodule
whose localization is the entire localized kernel module. -/
lemma exists_finite_kernel_submodule_with_top_localized
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (hπ : Function.Surjective (LocalizedModule.map S π))
    [Module.Finite (Localization S) (LocalizedModule S F)]
    [Module.FinitePresentation (Localization S) (LocalizedModule S M)] :
    ∃ Ksub : Submodule R (LinearMap.ker π),
      Module.Finite R Ksub ∧
        Ksub.localized S = ⊤ := by
  let _ : Module.Finite (Localization S) (LocalizedModule S (LinearMap.ker π)) :=
    source_kernel_localized_finite_of_surjective_presentation (S := S) π hπ
  -- Apply part (1) to the source kernel module itself.
  exact exists_finite_submodule_with_top_localized (S := S) (M := LinearMap.ker π)

/-- Helper for Lemma 10.126.4: the image of a submodule of `ker π` still lies in `ker π`, so the
presentation map descends to the quotient by that image. -/
lemma kernel_submodule_image_le_ker
    {F : Type*} [AddCommGroup F] [Module R F]
    (π : F →ₗ[R] M)
    (Ksub : Submodule R (LinearMap.ker π)) :
    Ksub.map (LinearMap.ker π).subtype ≤ LinearMap.ker π := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.2

-- Proof sketch: choose generators `x₁, ..., xₙ` of `LocalizedModule S M`, let
-- `Rⁿ → M` send the standard basis to these elements, and localize its kernel. By the finite case,
-- replace that localized kernel by a finite submodule `K'` of the original kernel with the same
-- localization. Then take `M' := (Fin n → R) ⧸ K'`; this module is finitely presented and its map
-- to `M` becomes a linear equivalence after localizing at `S`.
/-- Lemma 10.126.4 (2): if the localization `S⁻¹M` is finitely presented over `S⁻¹R`, then it is
the localization of a finitely presented `R`-module mapping to `M`. -/
@[stacks 05N6]
theorem exists_finitePresentation_module_with_localizedLinearEquiv
    [Module.FinitePresentation (Localization S) (LocalizedModule S M)] :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module R M') (_ : Module.FinitePresentation R M')
      (f : M' →ₗ[R] M)
      (e : LocalizedModule S M' ≃ₗ[Localization S] LocalizedModule S M),
      e.toLinearMap = LocalizedModule.map S f := by
  classical
  let _ : Module.Finite (Localization S) (LocalizedModule S M) := inferInstance
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := Localization S) (M := LocalizedModule S M)
  choose yt ht using
    fun i : Fin n ↦ IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) (x i)
  let y : Fin n → M := fun i ↦ (yt i).1
  let t : Fin n → S := fun i ↦ (yt i).2
  let M0 : Submodule R M := Submodule.span R (Set.range y)
  have hM0_finite : Module.Finite R M0 := by
    -- The chosen numerators generate `M0`.
    rw [Module.Finite.iff_fg]
    simpa [M0] using Submodule.fg_span (Set.finite_range y)
  have hM0_top : M0.localized S = ⊤ := by
    -- The localized numerators already span the given localized generators.
    apply top_le_iff.mp
    rw [← hx]
    rw [show M0.localized S =
      Submodule.span (Localization S)
        ((LocalizedModule.mkLinearMap S M) '' Set.range y) by
          simpa [M0] using
            (Submodule.localized'_span (Localization S) S (LocalizedModule.mkLinearMap S M)
              (Set.range y))]
    refine Submodule.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨i, rfl⟩
    rw [SetLike.mem_coe, ← IsLocalization.smul_mem_iff (s := t i)]
    rw [← (IsLocalizedModule.mk'_eq_iff (f := LocalizedModule.mkLinearMap S M)).mp (ht i)]
    exact Submodule.subset_span ⟨y i, ⟨i, rfl⟩, rfl⟩
  obtain ⟨m, π0, hπ0⟩ := Module.Finite.exists_fin' R M0
  let π : (Fin m → R) →ₗ[R] M := M0.subtype ∘ₗ π0
  have hM0_surj : Function.Surjective (LocalizedModule.map S M0.subtype) := by
    -- Localizing the inclusion of `M0` is surjective because `M0.localized S = ⊤`.
    exact LinearMap.range_eq_top.1
      (localized_subtype_range_eq_top_of_top_localized (S := S) M0 hM0_top)
  have hπ0_surj : Function.Surjective (LocalizedModule.map S π0) :=
    LocalizedModule.map_surjective S π0 hπ0
  have hπ_surj : Function.Surjective (LocalizedModule.map S π) := by
    -- Surjectivity survives composition after localizing the free cover of `M0`.
    intro z
    obtain ⟨z0, hz0⟩ := hM0_surj z
    obtain ⟨w, hw⟩ := hπ0_surj z0
    refine ⟨w, ?_⟩
    calc
      (LocalizedModule.map S π) w
          = (LocalizedModule.map S M0.subtype) ((LocalizedModule.map S π0) w) := by
              simpa [π] using
                LinearMap.congr_fun
                  (IsLocalizedModule.map_comp'
                    (S := S)
                    (f₀ := LocalizedModule.mkLinearMap S (Fin m → R))
                    (f₁ := LocalizedModule.mkLinearMap S M0)
                    (f₂ := LocalizedModule.mkLinearMap S M)
                    π0 M0.subtype)
                  w
      _ = (LocalizedModule.map S M0.subtype) z0 := by rw [hw]
      _ = z := hz0
  let _ : Module.Finite (Localization S) (LocalizedModule S (Fin m → R)) := inferInstance
  obtain ⟨Ksub, hKsub_finite, hKsub_top⟩ :=
    exists_finite_kernel_submodule_with_top_localized (S := S) (π := π) hπ_surj
  let K0 : Submodule R (Fin m → R) := Ksub.map (LinearMap.ker π).subtype
  let fbar : (Fin m → R) ⧸ K0 →ₗ[R] M :=
    K0.liftQ π (kernel_submodule_image_le_ker (π := π) Ksub)
  have hfbar : fbar.comp (Submodule.mkQ K0) = π := by
    -- The descended quotient map is defined to agree with `π` on generators.
    simpa [fbar] using K0.liftQ_mkQ π (kernel_submodule_image_le_ker (π := π) Ksub)
  have hK0_fg : K0.FG := by
    let _ : Module.Finite R Ksub := hKsub_finite
    have hKsub_fg : Ksub.FG :=
      Submodule.FG.of_finite (R := R) (M := LinearMap.ker π) (N := Ksub)
    -- Finite generation is preserved when we map the descended relation module into the free one.
    simpa [K0] using
      Submodule.FG.map (LinearMap.ker π).subtype hKsub_fg
  let _ : Module.FinitePresentation R ((Fin m → R) ⧸ K0) :=
    Module.finitePresentation_of_surjective (Submodule.mkQ K0) (Submodule.mkQ_surjective _) <| by
      -- The kernel of the quotient map is exactly the relation submodule `K0`.
      change (LinearMap.ker (Submodule.mkQ K0)).FG
      simpa using hK0_fg
  have hK0 :
      K0.localized S = (LinearMap.ker π).localized' (Localization S) S
        (LocalizedModule.mkLinearMap S (Fin m → R)) := by
    -- Localizing the descended relation submodule recovers the localized kernel of `π`.
    simpa [K0] using
      kernel_image_localized_eq_localized_kernel (S := S) (π := π) Ksub hKsub_top
  obtain ⟨e, he⟩ :=
    localized_quotient_equiv_of_surjective_and_kernel_match
      (S := S) (π := π) (K0 := K0) fbar hπ_surj hfbar hK0
  -- The quotient by the descended finite relation module is the desired finitely presented source.
  exact ⟨(Fin m → R) ⧸ K0, inferInstance, inferInstance, inferInstance, fbar, e, he⟩

end
