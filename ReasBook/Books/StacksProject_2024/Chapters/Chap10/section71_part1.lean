import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_71_1 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits
open ChainComplex

universe u v w

section

variable {R : Type u} [Ring R]
variable {M : Type (max u v)} [AddCommGroup M] [Module R M]

/-!
Domain-style sampling:
* primary domain: free resolutions of modules in an ambient `ModuleCat` universe large enough for
  both `M` and its free covers;
* sampled owner declarations:
  `ChainComplex.IsFreeResolution`,
  `ChainComplex.IsFiniteFreeResolution`,
  `LinearMap.exact_subtype_ker_map`;
* best owner abstraction:
  source-facing statements remain augmentations `π : F ⟶ (single₀.obj (ModuleCat.of R M))`
  equipped with `IsFreeResolution π` or `IsFiniteFreeResolution π`,
  while the proof-level governing object is the recursive sequence of syzygies
  from the textbook proof;
* primitive data: an augmented chain complex `π : F ⟶ (single₀.obj (ModuleCat.of R M))`;
* derived API: termwise freeness, termwise finiteness, and exactness of the
  associated short complexes.
-/

/-- Helper for Lemma 10.71.1: over a Noetherian ring, the kernel of a map from a finite free
module is finite. -/
lemma finite_syzygy_finite {N : Type w} [AddCommGroup N] [Module R N] [IsNoetherianRing R]
    {n : ℕ} (σ : (Fin n → R) →ₗ[R] N) :
    Module.Finite R (LinearMap.ker σ) := by
  -- A kernel is a submodule of the finite free source `R^n`, hence Noetherian and therefore finite.
  letI : IsNoetherian R (Fin n → R) := inferInstance
  letI : IsNoetherian R (LinearMap.ker σ) :=
    isNoetherian_of_submodule_of_noetherian R (Fin n → R) (LinearMap.ker σ) inferInstance
  exact Module.IsNoetherian.finite R (LinearMap.ker σ)

/-- Helper for Lemma 10.71.1: the canonical linear-combination map on a module is surjective. -/
lemma linearCombination_id_surjective {N : Type*} [AddCommGroup N] [Module R N] :
    Function.Surjective (Finsupp.linearCombination R (id : N → N)) := by
  -- The basis vector indexed by `x` maps to `x`.
  intro x
  refine ⟨Finsupp.single x 1, ?_⟩
  simpa using
    (Finsupp.linearCombination_single (R := R) (v := (id : N → N)) (c := (1 : R)) (a := x))

/-- Helper for Lemma 10.71.1: the canonical free cover of an `R`-module is the finitely supported
`R`-valued functions on its underlying set. -/
noncomputable abbrev free_cover_obj (N : Type (max u v)) [AddCommGroup N] [Module R N] :
    ModuleCat.{max u v} R :=
  ModuleCat.of R (N →₀ R)

/-- Helper for Lemma 10.71.1: the canonical free cover map sends a finitely supported function to
its linear combination in the target module. -/
noncomputable def free_cover_map (N : Type (max u v)) [AddCommGroup N] [Module R N] :
    free_cover_obj (R := R) N ⟶ ModuleCat.of R N :=
  ModuleCat.ofHom (Finsupp.linearCombination R (id : N → N))

/-- Helper for Lemma 10.71.1: the next differential in the source recursion is the free cover of
the current syzygy followed by the kernel inclusion. -/
noncomputable def free_cover_kernel_lift {X₀ X₁ : ModuleCat.{max u v} R} (f : X₁ ⟶ X₀) :
    free_cover_obj (R := R) (LinearMap.ker f.hom) ⟶ X₁ :=
  ModuleCat.ofHom <|
    (LinearMap.ker f.hom).subtype.comp
      (Finsupp.linearCombination R (id : LinearMap.ker f.hom → LinearMap.ker f.hom))

/-- Helper for Lemma 10.71.1: the kernel lift lands in the kernel by construction, so the next two
differentials compose to zero. -/
lemma free_cover_kernel_lift_comp_eq_zero {X₀ X₁ : ModuleCat.{max u v} R} (f : X₁ ⟶ X₀) :
    free_cover_kernel_lift (R := R) f ≫ f = 0 := by
  -- Each generator of the free cover maps into `ker f`, so the composite vanishes pointwise.
  apply ModuleCat.hom_ext
  ext x
  simp [free_cover_kernel_lift]

/-- Helper for Lemma 10.71.1: one step of the textbook free-cover recursion packages the next free
module, its differential, and the relation `d ≫ f = 0`. -/
noncomputable def free_cover_next {X₀ X₁ : ModuleCat.{max u v} R} (f : X₁ ⟶ X₀) :
    Σ' (X₂ : ModuleCat.{max u v} R) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
  ⟨free_cover_obj (R := R) (LinearMap.ker f.hom), free_cover_kernel_lift (R := R) f,
    free_cover_kernel_lift_comp_eq_zero (R := R) f⟩

/-- Helper for Lemma 10.71.1: the free-cover recursion packages the positive-degree part of the
source-faithful resolution into a chain complex. -/
noncomputable def free_cover_resolution_complex : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.mk'
    (free_cover_obj (R := R) M)
    (free_cover_obj (R := R) (LinearMap.ker (free_cover_map (R := R) M).hom))
    (free_cover_kernel_lift (R := R) (free_cover_map (R := R) M))
    (fun {_ _} f => free_cover_next (R := R) f)

/-- Helper for Lemma 10.71.1: the augmentation of the free-cover complex is the initial canonical
cover `R^{(M)} → M`. -/
noncomputable def free_cover_resolution_augmentation :
    free_cover_resolution_complex (R := R) (M := M) ⟶
      CategoryTheory.Functor.obj
        (ChainComplex.single₀ (ModuleCat.{max u v} R)) (ModuleCat.of R M) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨free_cover_map (R := R) M,
      free_cover_kernel_lift_comp_eq_zero (R := R) (free_cover_map (R := R) M)⟩

/-- Helper for Lemma 10.71.1: the first differential in the free-cover complex is exactly the map
obtained by covering the first syzygy and including it into the initial free cover. -/
lemma free_cover_resolution_complex_d_one_zero :
    (free_cover_resolution_complex (R := R) (M := M)).d 1 0 =
      free_cover_kernel_lift (R := R) (free_cover_map (R := R) M) := by
  -- This unfolds the `ChainComplex.mk'` constructor at the base step.
  simpa [free_cover_resolution_complex] using
    (ChainComplex.mk'_d_1_0
      (X₀ := free_cover_obj (R := R) M)
      (X₁ := free_cover_obj (R := R) (LinearMap.ker (free_cover_map (R := R) M).hom))
      (d₀ := free_cover_kernel_lift (R := R) (free_cover_map (R := R) M))
      (succ' := fun {_ _} f => free_cover_next (R := R) f))

/-- Helper for Lemma 10.71.1: a surjective cover of `ker f` yields the exact textbook
short complex `P → X₁ → X₀`. -/
lemma cover_of_kernel_exact {X₀ X₁ P : ModuleCat.{max u v} R} (f : X₁ ⟶ X₀)
    (σ : P ⟶ ModuleCat.of R (LinearMap.ker f.hom)) [Epi σ] :
    (ShortComplex.mk (σ ≫ ModuleCat.ofHom (LinearMap.ker f.hom).subtype) f
      (by
        apply ModuleCat.hom_ext
        ext x
        simp)).Exact := by
  -- The source proof uses that `σ` covers the syzygy; categorically this means the kernel lift is
  -- the composite of `σ` with the kernel object identified as `ker f`.
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  have hzero : σ ≫ ModuleCat.ofHom (LinearMap.ker f.hom).subtype ≫ f = 0 := by
    -- The image of `σ` lies in the syzygy, so composing with `f` vanishes pointwise.
    apply ModuleCat.hom_ext
    ext x
    simp
  have hkernel :
      kernel.lift f (σ ≫ ModuleCat.ofHom (LinearMap.ker f.hom).subtype) hzero =
        σ ≫ (ModuleCat.kernelIsoKer f).inv := by
    -- Both morphisms into `kernel f` become the same after composing with the kernel inclusion.
    rw [← cancel_mono (kernel.ι f), kernel.lift_ι]
    simp
  -- After rewriting the kernel lift to the explicit surjection onto the syzygy, epimorphicity is
  -- immediate from `σ` and the kernel isomorphism.
  rw [hkernel]
  infer_instance

/-- Helper for Lemma 10.71.1: the canonical free cover map is epi because every element is the
linear combination of its basis vector. -/
lemma free_cover_map_epi (N : Type (max u v)) [AddCommGroup N] [Module R N] :
    Epi (free_cover_map (R := R) N) := by
  -- We translate epimorphicity in `ModuleCat` to the surjectivity of the underlying linear map.
  rw [ModuleCat.epi_iff_surjective]
  exact linearCombination_id_surjective (R := R)

/-- Helper for Lemma 10.71.1: the canonical free cover of a syzygy gives the exact one-step
short complex used in the recursive construction. -/
lemma free_cover_kernel_lift_exact {X₀ X₁ : ModuleCat.{max u v} R} (f : X₁ ⟶ X₀) :
    (ShortComplex.mk (free_cover_kernel_lift (R := R) f) f
      (free_cover_kernel_lift_comp_eq_zero (R := R) f)).Exact := by
  -- This is the generic kernel-cover exactness lemma specialized to the canonical free cover.
  letI : Epi (free_cover_map (R := R) (LinearMap.ker f.hom)) :=
    free_cover_map_epi (R := R) (LinearMap.ker f.hom)
  simpa [free_cover_kernel_lift, free_cover_map] using
    cover_of_kernel_exact (R := R) f (free_cover_map (R := R) (LinearMap.ker f.hom))

/-- Helper for Lemma 10.71.1: the explicit inclusion of the module-theoretic kernel agrees with the
categorical kernel inclusion after identifying the two kernels. -/
lemma free_cover_map_comp_kernelIsoKer_inv_kernel_ι {X₀ X₁ : ModuleCat.{max u v} R}
    (f : X₁ ⟶ X₀) :
    free_cover_map (R := R) (LinearMap.ker f.hom) ≫
        ModuleCat.ofHom (LinearMap.ker f.hom).subtype =
      free_cover_map (R := R) (LinearMap.ker f.hom) ≫
        (ModuleCat.kernelIsoKer f).inv ≫ kernel.ι f := by
  -- This is just `kernelIsoKer_inv_kernel_ι` postcomposed with the chosen free cover.
  simpa [Category.assoc] using
    (congrArg
      (fun k =>
        free_cover_map (R := R) (LinearMap.ker f.hom) ≫ k)
      (ModuleCat.kernelIsoKer_inv_kernel_ι (f := f))).symm

/-- Helper for Lemma 10.71.1: the current differential in degree `n + 1` of the recursive
free-cover complex. -/
noncomputable abbrev free_cover_resolution_step_d (n : ℕ) :
    (free_cover_resolution_complex (R := R) (M := M)).X (n + 1) ⟶
      (free_cover_resolution_complex (R := R) (M := M)).X n :=
  (free_cover_resolution_complex (R := R) (M := M)).d (n + 1) n

/-- Helper for Lemma 10.71.1: the `mk'` bookkeeping isomorphism identifying the next term of the
recursive complex with the chosen free cover of the current syzygy. -/
noncomputable abbrev free_cover_resolution_step_iso (n : ℕ) :
    (free_cover_resolution_complex (R := R) (M := M)).X (n + 2) ≅
      free_cover_obj (R := R)
        (LinearMap.ker ((free_cover_resolution_step_d (R := R) (M := M) n).hom)) :=
  ChainComplex.mk'XIso
    (X₀ := free_cover_obj (R := R) M)
    (X₁ := free_cover_obj (R := R) (LinearMap.ker (free_cover_map (R := R) M).hom))
    (d₀ := free_cover_kernel_lift (R := R) (free_cover_map (R := R) M))
    (succ' := fun {_ _} f => free_cover_next (R := R) f)
    n

/-- Helper for Lemma 10.71.1: in positive degrees, the `kernel.lift` from `exactAt_iff'`
identifies with the chosen free cover of the current syzygy, transported through the `mk'`
constructor's bookkeeping isomorphism. -/
lemma free_cover_resolution_kernel_lift_eq (n : ℕ) :
    kernel.lift
        (free_cover_resolution_step_d (R := R) (M := M) n)
        ((free_cover_resolution_complex (R := R) (M := M)).d (n + 2) (n + 1))
        ((free_cover_resolution_complex (R := R) (M := M)).d_comp_d (n + 2) (n + 1) n) =
      (free_cover_resolution_step_iso (R := R) (M := M) n).hom ≫
        free_cover_map (R := R)
          (LinearMap.ker ((free_cover_resolution_step_d (R := R) (M := M) n).hom)) ≫
        (ModuleCat.kernelIsoKer (free_cover_resolution_step_d (R := R) (M := M) n)).inv := by
  -- The packaged differential is the chosen free cover of the current syzygy after the `mk'`
  -- bookkeeping isomorphism, so both maps into the categorical kernel agree after `kernel.ι`.
  rw [← cancel_mono
      (kernel.ι (free_cover_resolution_step_d (R := R) (M := M) n)),
    kernel.lift_ι]
  -- The remaining comparison is the explicit `mk'_d` formula followed by the kernel identification.
  calc
    (free_cover_resolution_complex (R := R) (M := M)).d (n + 2) (n + 1) =
        (free_cover_resolution_step_iso (R := R) (M := M) n).hom ≫
          free_cover_kernel_lift (R := R) (free_cover_resolution_step_d (R := R) (M := M) n) := by
      -- This is exactly the `mk'_d` description of the successor differential.
      simpa [free_cover_resolution_step_d, free_cover_resolution_step_iso, free_cover_resolution_complex]
        using
          (ChainComplex.mk'_d
            (X₀ := free_cover_obj (R := R) M)
            (X₁ := free_cover_obj (R := R) (LinearMap.ker (free_cover_map (R := R) M).hom))
            (d₀ := free_cover_kernel_lift (R := R) (free_cover_map (R := R) M))
            (succ' := fun {_ _} f => free_cover_next (R := R) f)
            n)
    _ =
        (free_cover_resolution_step_iso (R := R) (M := M) n).hom ≫
          free_cover_map (R := R)
            (LinearMap.ker ((free_cover_resolution_step_d (R := R) (M := M) n).hom)) ≫
          ModuleCat.ofHom
            ((LinearMap.ker ((free_cover_resolution_step_d (R := R) (M := M) n).hom)).subtype) := by
      -- Unfold the chosen cover of the current syzygy.
      simp [free_cover_kernel_lift, free_cover_map]
    _ =
        ((free_cover_resolution_step_iso (R := R) (M := M) n).hom ≫
            free_cover_map (R := R)
              (LinearMap.ker ((free_cover_resolution_step_d (R := R) (M := M) n).hom)) ≫
            (ModuleCat.kernelIsoKer (free_cover_resolution_step_d (R := R) (M := M) n)).inv) ≫
          kernel.ι (free_cover_resolution_step_d (R := R) (M := M) n) := by
      -- This is the module-kernel/categorical-kernel comparison with the `mk'` isomorphism prefixed.
      simpa [Category.assoc] using
        congrArg
          (fun k => (free_cover_resolution_step_iso (R := R) (M := M) n).hom ≫ k)
          (free_cover_map_comp_kernelIsoKer_inv_kernel_ι
            (R := R) (f := free_cover_resolution_step_d (R := R) (M := M) n))

/-- Helper for Lemma 10.71.1: in positive degrees, the packaged short complex `sc'` is exactly the
textbook syzygy-cover short complex, up to the `mk'` bookkeeping isomorphism on the left term. -/
noncomputable def free_cover_resolution_sc'_iso (n : ℕ) :
    ((free_cover_resolution_complex (R := R) (M := M)).sc' (n + 2) (n + 1) n) ≅
      ShortComplex.mk
        (free_cover_kernel_lift (R := R) (free_cover_resolution_step_d (R := R) (M := M) n))
        (free_cover_resolution_step_d (R := R) (M := M) n)
        (free_cover_kernel_lift_comp_eq_zero
          (R := R) (free_cover_resolution_step_d (R := R) (M := M) n)) :=
  ShortComplex.isoMk
    (free_cover_resolution_step_iso (R := R) (M := M) n)
    (Iso.refl _)
    (Iso.refl _)
    (by
      -- The first differential is exactly the chosen free cover of the current syzygy.
      have hmk :=
        (ChainComplex.mk'_d
          (X₀ := free_cover_obj (R := R) M)
          (X₁ := free_cover_obj (R := R) (LinearMap.ker (free_cover_map (R := R) M).hom))
          (d₀ := free_cover_kernel_lift (R := R) (free_cover_map (R := R) M))
          (succ' := fun {_ _} f => free_cover_next (R := R) f)
          n)
      simpa [free_cover_resolution_step_d, free_cover_resolution_complex] using hmk.symm)
    (by
      -- The second differential is unchanged: only the left term is transported.
      simp [free_cover_resolution_step_d])

/-- Helper for Lemma 10.71.1: every positive-degree short complex in the recursive free-cover
construction is exact. -/
lemma free_cover_resolution_exactAt_succ (n : ℕ) :
    (free_cover_resolution_complex (R := R) (M := M)).ExactAt (n + 1) := by
  -- Route correction: instead of unfolding `kernel.lift` on `sc'`, transport the whole short
  -- complex to the explicit textbook syzygy-cover complex and use its exactness directly.
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  -- After freezing the owner term by an isomorphism, exactness is the generic kernel-cover step.
  exact ShortComplex.exact_of_iso
    (free_cover_resolution_sc'_iso (R := R) (M := M) n).symm
    (free_cover_kernel_lift_exact
      (R := R) (free_cover_resolution_step_d (R := R) (M := M) n))

/-- Helper for Lemma 10.71.1: a finite module admits a surjection from a finite free module. -/
lemma exists_finite_free_cover {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N] :
    ∃ n : ℕ, ∃ σ : (Fin n → R) →ₗ[R] N, Function.Surjective σ := by
  -- This is the standard finite-generation presentation by `R^n`.
  simpa using Module.Finite.exists_fin' R N

/-- Helper for Lemma 10.71.1: the degree-`0` short-complex comparison for the free-cover
augmentation reduces quasi-isomorphism to the exact sequence `F₁ → F₀ → M`. -/
lemma free_cover_resolution_quasiIsoAt_zero :
    QuasiIsoAt (free_cover_resolution_augmentation (R := R) (M := M)) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
  · -- The explicit degree-`0` short complex is `F₁ → F₀ → M`, which is exact and surjective.
    let e :
        ShortComplex.mk
            ((free_cover_resolution_complex (R := R) (M := M)).d 1 0)
            ((free_cover_resolution_augmentation (R := R) (M := M)).f 0)
            (by
              simpa using
                ((free_cover_resolution_augmentation (R := R) (M := M)).comm 1 0).symm) ≅
          ShortComplex.mk
            (free_cover_kernel_lift (R := R) (free_cover_map (R := R) M))
            (free_cover_map (R := R) M)
            (free_cover_kernel_lift_comp_eq_zero (R := R) (free_cover_map (R := R) M)) :=
      ShortComplex.isoMk
        (Iso.refl _)
        (Iso.refl _)
        (Iso.refl _)
        (by
          -- The first map is the degree-`1` differential of the recursive complex.
          simpa using
            (free_cover_resolution_complex_d_one_zero (R := R) (M := M)).symm)
        (by
          -- The second map is the degree-`0` component of the augmentation.
          simpa [free_cover_resolution_augmentation] using
            (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
              (C := free_cover_resolution_complex (R := R) (M := M))
              (X := ModuleCat.of R M)
              (f := free_cover_map (R := R) M)
              (hf := free_cover_kernel_lift_comp_eq_zero (R := R) (free_cover_map (R := R) M))).symm)
    refine (ShortComplex.exact_and_epi_g_iff_of_iso e).2 ?_
    refine ⟨free_cover_kernel_lift_exact (R := R) (free_cover_map (R := R) M), ?_⟩
    exact free_cover_map_epi (R := R) M
  · rfl
  · rfl
  · rfl

/-- Helper for Lemma 10.71.1: every term of the recursive free-cover complex is a free
`R`-module. -/
lemma free_cover_resolution_termwise_free :
    ChainComplex.IsTermwiseFree (free_cover_resolution_complex (R := R) (M := M)) := by
  intro n
  match n with
  | 0 =>
      -- Degree `0` is the canonical free module on the underlying set of `M`.
      simpa [free_cover_resolution_complex, free_cover_obj] using
        (inferInstance : Module.Free R (M →₀ R))
  | 1 =>
      -- Degree `1` is the canonical free module on the first syzygy.
      simpa [free_cover_resolution_complex, free_cover_obj] using
        (inferInstance :
          Module.Free R (LinearMap.ker (free_cover_map (R := R) M).hom →₀ R))
  | n + 2 =>
      -- Higher degrees are only re-indexed versions of the same free-cover construction.
      let e :=
        free_cover_resolution_step_iso (R := R) (M := M) n
      let eₗ :
          (free_cover_resolution_complex (R := R) (M := M)).X (n + 2) ≃ₗ[R]
            (LinearMap.ker ((free_cover_resolution_step_d (R := R) (M := M) n).hom) →₀ R) :=
        LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)
      letI :
          Module.Free R
            (LinearMap.ker ((free_cover_resolution_step_d (R := R) (M := M) n).hom) →₀ R) :=
        inferInstance
      -- Transport freeness back across the bookkeeping linear equivalence.
      exact Module.Free.of_equiv' inferInstance eₗ.symm

/-- Helper for Lemma 10.71.1: the recursive free-cover complex together with its augmentation is a
free resolution. -/
lemma free_cover_resolution_isFreeResolution :
    IsFreeResolution (free_cover_resolution_augmentation (R := R) (M := M)) := by
  letI : QuasiIso (free_cover_resolution_augmentation (R := R) (M := M)) := ⟨fun n => by
    -- The quasi-isomorphism is checked in degree `0` by the explicit short exact sequence
    -- `F₁ → F₀ → M`, and in positive degrees by exactness against the zero complex.
    cases n with
    | zero =>
        simpa using free_cover_resolution_quasiIsoAt_zero (R := R) (M := M)
    | succ n =>
        rw [quasiIsoAt_iff_exactAt'
            (hL := ChainComplex.exactAt_succ_single_obj (ModuleCat.of R M) n)]
        exact free_cover_resolution_exactAt_succ (R := R) (M := M) n⟩
  -- The quasi-isomorphism is checked in degree `0` by the explicit short exact sequence
  -- `F₁ → F₀ → M`, and in positive degrees by exactness against the zero complex.
  exact ⟨free_cover_resolution_termwise_free (R := R) (M := M)⟩

/-- Lemma 10.71.1 (1): every `R`-module admits a resolution by free `R`-modules. -/
lemma module_exists_free_resolution :
    ∃ (F : ChainComplex (ModuleCat.{max u v} R) ℕ)
      (π : F ⟶ CategoryTheory.Functor.obj
        (ChainComplex.single₀ (ModuleCat.{max u v} R)) (ModuleCat.of R M)),
      IsFreeResolution π := by
  -- Route correction: the blocked `ModuleCat.projectiveResolution` owner is not the right source
  -- proof. The intended route is the textbook recursion by free covers of successive kernels.
  refine ⟨free_cover_resolution_complex (R := R) (M := M),
    free_cover_resolution_augmentation (R := R) (M := M), ?_⟩
  -- The packaged recursion is now known to be a free resolution.
  exact free_cover_resolution_isFreeResolution (R := R) (M := M)

/-- Helper for Lemma 10.71.1: a chosen finite free cover is packaged as its source object together
with the surjection onto the target module. -/
structure FreeCoverData (N : Type (max u v)) [AddCommGroup N] [Module R N] where
  /-- The chosen covering free module. -/
  obj : ModuleCat.{max u v} R
  /-- The chosen cover map. -/
  map : obj ⟶ ModuleCat.of R N
  /-- The chosen cover map is epi. -/
  epi_map : Epi map

attribute [instance] FreeCoverData.epi_map

/-- Helper for Lemma 10.71.1: the rank of a chosen finite free cover of a finite module. -/
noncomputable def finite_free_cover_rank (N : Type (max u v)) [AddCommGroup N] [Module R N]
    (hN : Module.Finite R N) : ℕ :=
  letI := hN
  Classical.choose (exists_finite_free_cover (R := R) (N := N))

/-- Helper for Lemma 10.71.1: the chosen surjection from a finite free module onto a finite
module. -/
noncomputable def finite_free_cover_linearMap (N : Type (max u v)) [AddCommGroup N] [Module R N]
    (hN : Module.Finite R N) :
    (Fin (finite_free_cover_rank (R := R) N hN) → R) →ₗ[R] N :=
  letI := hN
  Classical.choose (Classical.choose_spec (exists_finite_free_cover (R := R) (N := N)))

/-- Helper for Lemma 10.71.1: the chosen finite free cover map is surjective. -/
lemma finite_free_cover_linearMap_surjective (N : Type (max u v)) [AddCommGroup N] [Module R N]
    (hN : Module.Finite R N) :
    Function.Surjective (finite_free_cover_linearMap (R := R) N hN) := by
  -- This is the surjectivity witness bundled in the chosen finite free cover.
  letI := hN
  simpa [finite_free_cover_linearMap, finite_free_cover_rank] using
    (Classical.choose_spec
      (Classical.choose_spec (exists_finite_free_cover (R := R) (N := N))))

/-- Helper for Lemma 10.71.1: the chosen finite free cover map, viewed in `ModuleCat`, is epi. -/
lemma finite_free_cover_map_epi_of (N : Type (max u v)) [AddCommGroup N] [Module R N]
    (hN : Module.Finite R N) :
    Epi (ModuleCat.ofHom
      ((finite_free_cover_linearMap (R := R) N hN).comp ULift.moduleEquiv.toLinearMap)) := by
  -- Surjectivity survives precomposition with the `ULift` module equivalence.
  rw [ModuleCat.epi_iff_surjective]
  intro x
  obtain ⟨y, hy⟩ := finite_free_cover_linearMap_surjective (R := R) N hN x
  refine ⟨ULift.up y, ?_⟩
  simpa using hy

/-- Helper for Lemma 10.71.1: the chosen finite free cover data of a finite module. -/
noncomputable def finite_free_cover_data (N : Type (max u v)) [AddCommGroup N] [Module R N]
    (hN : Module.Finite R N) : FreeCoverData (R := R) N where
  obj := ModuleCat.of R (ULift.{v} (Fin (finite_free_cover_rank (R := R) N hN) → R))
  map := ModuleCat.ofHom <|
    (finite_free_cover_linearMap (R := R) N hN).comp ULift.moduleEquiv.toLinearMap
  epi_map := finite_free_cover_map_epi_of (R := R) N hN

/-- Helper for Lemma 10.71.1: the canonical free cover data used when no finiteness information is
available. -/
noncomputable def canonical_free_cover_data (N : Type (max u v)) [AddCommGroup N] [Module R N] :
    FreeCoverData (R := R) N where
  obj := free_cover_obj (R := R) N
  map := free_cover_map (R := R) N
  epi_map := free_cover_map_epi (R := R) N

/-- Helper for Lemma 10.71.1: choose a finite free cover when the module is finite, and otherwise
fall back to the canonical free cover. -/
noncomputable def selected_free_cover_data (N : Type (max u v)) [AddCommGroup N] [Module R N] :
    FreeCoverData (R := R) N :=
  let _ : Decidable (Module.Finite R N) := Classical.propDecidable _
  dite (Module.Finite R N)
    (fun hN => finite_free_cover_data (R := R) N hN)
    (fun _ => canonical_free_cover_data (R := R) N)

/-- Helper for Lemma 10.71.1: when the target module is finite, the selected cover data is the
chosen finite free cover data. -/
lemma selected_free_cover_data_eq_finite (N : Type (max u v)) [AddCommGroup N] [Module R N]
    (hN : Module.Finite R N) :
    selected_free_cover_data (R := R) N = finite_free_cover_data (R := R) N hN := by
  -- The selected cover chooses the finite branch whenever a finiteness witness is available.
  classical
  unfold selected_free_cover_data
  simp [hN]

/-- Helper for Lemma 10.71.1: when the target module is not finite, the selected cover data is the
canonical free cover data. -/
lemma selected_free_cover_data_eq_canonical (N : Type (max u v)) [AddCommGroup N] [Module R N]
    (hN : ¬ Module.Finite R N) :
    selected_free_cover_data (R := R) N = canonical_free_cover_data (R := R) N := by
  -- The selected cover falls back to the canonical free cover on the non-finite branch.
  classical
  unfold selected_free_cover_data
  simp [hN]

/-- Helper for Lemma 10.71.1: the source object of the selected free cover. -/
noncomputable abbrev selected_free_cover_obj (N : Type (max u v)) [AddCommGroup N] [Module R N] :
    ModuleCat.{max u v} R :=
  (selected_free_cover_data (R := R) N).obj

/-- Helper for Lemma 10.71.1: the cover map of the selected free cover. -/
noncomputable abbrev selected_free_cover_map (N : Type (max u v)) [AddCommGroup N] [Module R N] :
    selected_free_cover_obj (R := R) N ⟶ ModuleCat.of R N :=
  (selected_free_cover_data (R := R) N).map

/-- Helper for Lemma 10.71.1: every selected free cover source is free. -/
lemma selected_free_cover_obj_free (N : Type (max u v)) [AddCommGroup N] [Module R N] :
    Module.Free R (selected_free_cover_obj (R := R) N) := by
  -- Each branch of the selected cover is explicitly a free module of the form `I →₀ R`.
  classical
  by_cases hN : Module.Finite R N
  · unfold selected_free_cover_obj
    rw [selected_free_cover_data_eq_finite (R := R) N hN]
    simpa [finite_free_cover_data] using
      (inferInstance :
        Module.Free R (ULift.{v} (Fin (finite_free_cover_rank (R := R) N hN) → R)))
  · unfold selected_free_cover_obj
    rw [selected_free_cover_data_eq_canonical (R := R) N hN]
    simpa [canonical_free_cover_data, free_cover_obj] using
      (inferInstance : Module.Free R (N →₀ R))

/-- Helper for Lemma 10.71.1: if the target module is finite, then the selected free cover source
is finite. -/
lemma selected_free_cover_obj_finite (N : Type (max u v)) [AddCommGroup N] [Module R N]
    [Module.Finite R N] :
    Module.Finite R (selected_free_cover_obj (R := R) N) := by
  -- Along the finite branch, the selected cover is a standard finite free module `R^n`.
  classical
  by_cases hN : Module.Finite R N
  · unfold selected_free_cover_obj
    rw [selected_free_cover_data_eq_finite (R := R) N hN]
    simpa [finite_free_cover_data] using
      (inferInstance :
        Module.Finite R (ULift.{v} (Fin (finite_free_cover_rank (R := R) N hN) → R)))
  · exact False.elim (hN inferInstance)

/-- Helper for Lemma 10.71.1: the selected free cover map is always epi. -/
lemma selected_free_cover_map_epi (N : Type (max u v)) [AddCommGroup N] [Module R N] :
    Epi (selected_free_cover_map (R := R) N) := by
  -- Either we are on the chosen finite free branch, or on the canonical free-cover branch.
  unfold selected_free_cover_map
  infer_instance

/-- Helper for Lemma 10.71.1: the selected free cover of a kernel followed by the kernel inclusion
gives the next differential. -/
noncomputable def selected_free_cover_kernel_lift {X₀ X₁ : ModuleCat.{max u v} R} (f : X₁ ⟶ X₀) :
    selected_free_cover_obj (R := R) (LinearMap.ker f.hom) ⟶ X₁ :=
  selected_free_cover_map (R := R) (LinearMap.ker f.hom) ≫
    ModuleCat.ofHom (LinearMap.ker f.hom).subtype

/-- Helper for Lemma 10.71.1: the selected free cover of the kernel lands in the kernel by
construction, so consecutive differentials compose to zero. -/
lemma selected_free_cover_kernel_lift_comp_eq_zero {X₀ X₁ : ModuleCat.{max u v} R}
    (f : X₁ ⟶ X₀) :
    selected_free_cover_kernel_lift (R := R) f ≫ f = 0 := by
  -- The kernel inclusion is pointwise annihilated by `f`.
  apply ModuleCat.hom_ext
  ext x
  simp [selected_free_cover_kernel_lift]

/-- Helper for Lemma 10.71.1: a cover of the module-theoretic kernel agrees with the categorical
kernel inclusion after identifying the two kernels. -/
lemma cover_map_comp_kernelIsoKer_inv_kernel_ι {X₀ X₁ P : ModuleCat.{max u v} R}
    (f : X₁ ⟶ X₀) (σ : P ⟶ ModuleCat.of R (LinearMap.ker f.hom)) :
    σ ≫ ModuleCat.ofHom (LinearMap.ker f.hom).subtype =
      σ ≫ (ModuleCat.kernelIsoKer f).inv ≫ kernel.ι f := by
  -- This is just the standard `kernelIsoKer` comparison postcomposed with the chosen cover map.
  simpa [Category.assoc] using
    (congrArg (fun k => σ ≫ k) (ModuleCat.kernelIsoKer_inv_kernel_ι (f := f))).symm

/-- Helper for Lemma 10.71.1: the selected free cover of the current syzygy gives the exact
textbook short complex in one recursive step. -/
lemma selected_free_cover_kernel_lift_exact {X₀ X₁ : ModuleCat.{max u v} R} (f : X₁ ⟶ X₀) :
    (ShortComplex.mk (selected_free_cover_kernel_lift (R := R) f) f
      (selected_free_cover_kernel_lift_comp_eq_zero (R := R) f)).Exact := by
  -- Exactness is the generic `cover_of_kernel_exact` lemma applied to the selected cover of `ker f`.
  letI : Epi (selected_free_cover_map (R := R) (LinearMap.ker f.hom)) :=
    selected_free_cover_map_epi (R := R) (LinearMap.ker f.hom)
  simpa [selected_free_cover_kernel_lift] using
    cover_of_kernel_exact (R := R) f
      (selected_free_cover_map (R := R) (LinearMap.ker f.hom))

/-- Helper for Lemma 10.71.1: one recursive successor step for the selected-cover construction. -/
noncomputable def selected_free_cover_next {X₀ X₁ : ModuleCat.{max u v} R} (f : X₁ ⟶ X₀) :
    Σ' (X₂ : ModuleCat.{max u v} R) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
  ⟨selected_free_cover_obj (R := R) (LinearMap.ker f.hom),
    selected_free_cover_kernel_lift (R := R) f,
    selected_free_cover_kernel_lift_comp_eq_zero (R := R) f⟩

/-- Helper for Lemma 10.71.1: the selected-cover recursion packages the textbook kernel-cover
construction into a chain complex. -/
noncomputable def selected_free_cover_resolution_complex :
    ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.mk'
    (selected_free_cover_obj (R := R) M)
    (selected_free_cover_obj (R := R)
      (LinearMap.ker (selected_free_cover_map (R := R) M).hom))
    (selected_free_cover_kernel_lift (R := R) (selected_free_cover_map (R := R) M))
    (fun {_ _} f => selected_free_cover_next (R := R) f)

/-- Helper for Lemma 10.71.1: the augmentation of the selected-cover complex is the initial chosen
cover map onto `M`. -/
noncomputable def selected_free_cover_resolution_augmentation :
    selected_free_cover_resolution_complex (R := R) (M := M) ⟶
      CategoryTheory.Functor.obj
        (ChainComplex.single₀ (ModuleCat.{max u v} R)) (ModuleCat.of R M) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨selected_free_cover_map (R := R) M,
      selected_free_cover_kernel_lift_comp_eq_zero (R := R)
        (selected_free_cover_map (R := R) M)⟩

/-- Helper for Lemma 10.71.1: the first differential of the selected-cover complex is the chosen
cover of the first syzygy. -/
lemma selected_free_cover_resolution_complex_d_one_zero :
    (selected_free_cover_resolution_complex (R := R) (M := M)).d 1 0 =
      selected_free_cover_kernel_lift (R := R) (selected_free_cover_map (R := R) M) := by
  -- This is the base-step computation for `ChainComplex.mk'`.
  simpa [selected_free_cover_resolution_complex] using
    (ChainComplex.mk'_d_1_0
      (X₀ := selected_free_cover_obj (R := R) M)
      (X₁ := selected_free_cover_obj (R := R)
        (LinearMap.ker (selected_free_cover_map (R := R) M).hom))
      (d₀ := selected_free_cover_kernel_lift (R := R) (selected_free_cover_map (R := R) M))
      (succ' := fun {_ _} f => selected_free_cover_next (R := R) f))

/-- Helper for Lemma 10.71.1: the differential in degree `n + 1` of the selected-cover
resolution complex. -/
noncomputable abbrev selected_free_cover_resolution_step_d (n : ℕ) :
    (selected_free_cover_resolution_complex (R := R) (M := M)).X (n + 1) ⟶
      (selected_free_cover_resolution_complex (R := R) (M := M)).X n :=
  (selected_free_cover_resolution_complex (R := R) (M := M)).d (n + 1) n

/-- Helper for Lemma 10.71.1: the `mk'` bookkeeping isomorphism identifying the next selected-cover
term with the selected cover of the current syzygy. -/
noncomputable abbrev selected_free_cover_resolution_step_iso (n : ℕ) :
    (selected_free_cover_resolution_complex (R := R) (M := M)).X (n + 2) ≅
      selected_free_cover_obj (R := R)
        (LinearMap.ker ((selected_free_cover_resolution_step_d (R := R) (M := M) n).hom)) :=
  ChainComplex.mk'XIso
    (X₀ := selected_free_cover_obj (R := R) M)
    (X₁ := selected_free_cover_obj (R := R)
      (LinearMap.ker (selected_free_cover_map (R := R) M).hom))
    (d₀ := selected_free_cover_kernel_lift (R := R) (selected_free_cover_map (R := R) M))
    (succ' := fun {_ _} f => selected_free_cover_next (R := R) f)
    n

/-- Helper for Lemma 10.71.1: in positive degrees, the `kernel.lift` from `exactAt_iff'`
identifies with the chosen cover of the current syzygy after the `mk'` bookkeeping isomorphism. -/
lemma selected_free_cover_resolution_kernel_lift_eq (n : ℕ) :
    kernel.lift
        (selected_free_cover_resolution_step_d (R := R) (M := M) n)
        ((selected_free_cover_resolution_complex (R := R) (M := M)).d (n + 2) (n + 1))
        ((selected_free_cover_resolution_complex (R := R) (M := M)).d_comp_d (n + 2) (n + 1) n) =
      (selected_free_cover_resolution_step_iso (R := R) (M := M) n).hom ≫
        selected_free_cover_map (R := R)
          (LinearMap.ker ((selected_free_cover_resolution_step_d (R := R) (M := M) n).hom)) ≫
        (ModuleCat.kernelIsoKer
          (selected_free_cover_resolution_step_d (R := R) (M := M) n)).inv := by
  -- The packaged differential is the chosen cover of the current syzygy after the `mk'` isomorphism.
  rw [← cancel_mono
      (kernel.ι (selected_free_cover_resolution_step_d (R := R) (M := M) n)),
    kernel.lift_ι]
  calc
    (selected_free_cover_resolution_complex (R := R) (M := M)).d (n + 2) (n + 1) =
        (selected_free_cover_resolution_step_iso (R := R) (M := M) n).hom ≫
          selected_free_cover_kernel_lift (R := R)
            (selected_free_cover_resolution_step_d (R := R) (M := M) n) := by
      -- This is the explicit `mk'_d` formula for the recursive selected-cover construction.
      simpa [selected_free_cover_resolution_step_d, selected_free_cover_resolution_step_iso,
        selected_free_cover_resolution_complex] using
        (ChainComplex.mk'_d
          (X₀ := selected_free_cover_obj (R := R) M)
          (X₁ := selected_free_cover_obj (R := R)
            (LinearMap.ker (selected_free_cover_map (R := R) M).hom))
          (d₀ := selected_free_cover_kernel_lift (R := R) (selected_free_cover_map (R := R) M))
          (succ' := fun {_ _} f => selected_free_cover_next (R := R) f)
          n)
    _ =
        (selected_free_cover_resolution_step_iso (R := R) (M := M) n).hom ≫
          selected_free_cover_map (R := R)
            (LinearMap.ker ((selected_free_cover_resolution_step_d (R := R) (M := M) n).hom)) ≫
          ModuleCat.ofHom
            ((LinearMap.ker
              ((selected_free_cover_resolution_step_d (R := R) (M := M) n).hom)).subtype) := by
      -- Unfold the selected cover of the current syzygy.
      simp [selected_free_cover_kernel_lift]
    _ =
        ((selected_free_cover_resolution_step_iso (R := R) (M := M) n).hom ≫
            selected_free_cover_map (R := R)
              (LinearMap.ker ((selected_free_cover_resolution_step_d (R := R) (M := M) n).hom)) ≫
            (ModuleCat.kernelIsoKer
              (selected_free_cover_resolution_step_d (R := R) (M := M) n)).inv) ≫
          kernel.ι (selected_free_cover_resolution_step_d (R := R) (M := M) n) := by
      -- This is the module-kernel/categorical-kernel comparison prefixed by the `mk'` isomorphism.
      simpa [Category.assoc] using
        congrArg
          (fun k => (selected_free_cover_resolution_step_iso (R := R) (M := M) n).hom ≫ k)
          (cover_map_comp_kernelIsoKer_inv_kernel_ι
            (R := R)
            (selected_free_cover_resolution_step_d (R := R) (M := M) n)
            (selected_free_cover_map (R := R)
              (LinearMap.ker ((selected_free_cover_resolution_step_d
                (R := R) (M := M) n).hom))))

/-- Helper for Lemma 10.71.1: the packaged positive-degree short complex is the explicit
selected-cover syzygy short complex, up to the `mk'` bookkeeping isomorphism. -/
noncomputable def selected_free_cover_resolution_sc'_iso (n : ℕ) :
    ((selected_free_cover_resolution_complex (R := R) (M := M)).sc' (n + 2) (n + 1) n) ≅
      ShortComplex.mk
        (selected_free_cover_kernel_lift (R := R)
          (selected_free_cover_resolution_step_d (R := R) (M := M) n))
        (selected_free_cover_resolution_step_d (R := R) (M := M) n)
        (selected_free_cover_kernel_lift_comp_eq_zero
          (R := R) (selected_free_cover_resolution_step_d (R := R) (M := M) n)) :=
  ShortComplex.isoMk
    (selected_free_cover_resolution_step_iso (R := R) (M := M) n)
    (Iso.refl _)
    (Iso.refl _)
    (by
      -- The first differential is exactly the chosen cover of the current syzygy.
      have hmk :=
        (ChainComplex.mk'_d
          (X₀ := selected_free_cover_obj (R := R) M)
          (X₁ := selected_free_cover_obj (R := R)
            (LinearMap.ker (selected_free_cover_map (R := R) M).hom))
          (d₀ := selected_free_cover_kernel_lift (R := R) (selected_free_cover_map (R := R) M))
          (succ' := fun {_ _} f => selected_free_cover_next (R := R) f)
          n)
      simpa [selected_free_cover_resolution_step_d, selected_free_cover_resolution_complex] using
        hmk.symm)
    (by
      -- Only the left term is transported; the second differential stays unchanged.
      simp [selected_free_cover_resolution_step_d])

/-- Helper for Lemma 10.71.1: every positive-degree short complex in the selected-cover resolution
is exact. -/
lemma selected_free_cover_resolution_exactAt_succ (n : ℕ) :
    (selected_free_cover_resolution_complex (R := R) (M := M)).ExactAt (n + 1) := by
  -- Transport exactness to the explicit selected-cover short complex and apply the generic kernel step.
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  exact ShortComplex.exact_of_iso
    (selected_free_cover_resolution_sc'_iso (R := R) (M := M) n).symm
    (selected_free_cover_kernel_lift_exact
      (R := R) (selected_free_cover_resolution_step_d (R := R) (M := M) n))

/-- Helper for Lemma 10.71.1: the degree-`0` short-complex comparison for the selected-cover
augmentation reduces quasi-isomorphism to the explicit exact sequence `F₁ → F₀ → M`. -/
lemma selected_free_cover_resolution_quasiIsoAt_zero :
    QuasiIsoAt (selected_free_cover_resolution_augmentation (R := R) (M := M)) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
  · -- The degree-`0` short complex is exactly the initial syzygy cover sequence.
    let e :
        ShortComplex.mk
            ((selected_free_cover_resolution_complex (R := R) (M := M)).d 1 0)
            ((selected_free_cover_resolution_augmentation (R := R) (M := M)).f 0)
            (by
              simpa using
                ((selected_free_cover_resolution_augmentation
                  (R := R) (M := M)).comm 1 0).symm) ≅
          ShortComplex.mk
            (selected_free_cover_kernel_lift (R := R) (selected_free_cover_map (R := R) M))
            (selected_free_cover_map (R := R) M)
            (selected_free_cover_kernel_lift_comp_eq_zero
              (R := R) (selected_free_cover_map (R := R) M)) :=
      ShortComplex.isoMk
        (Iso.refl _)
        (Iso.refl _)
        (Iso.refl _)
        (by
          -- The first differential is the explicit chosen cover of the first syzygy.
          simpa using
            (selected_free_cover_resolution_complex_d_one_zero (R := R) (M := M)).symm)
        (by
          -- The augmentation in degree `0` is the initial chosen cover map.
          rfl)
    refine (ShortComplex.exact_and_epi_g_iff_of_iso e).2 ?_
    refine ⟨selected_free_cover_kernel_lift_exact
      (R := R) (selected_free_cover_map (R := R) M), ?_⟩
    exact selected_free_cover_map_epi (R := R) M
  · rfl
  · rfl
  · rfl

/-- Helper for Lemma 10.71.1: every term of the selected-cover resolution is a free `R`-module. -/
lemma selected_free_cover_resolution_termwise_free :
    ChainComplex.IsTermwiseFree (selected_free_cover_resolution_complex (R := R) (M := M)) := by
  intro n
  match n with
  | 0 =>
      -- Degree `0` is the selected free cover of `M`, hence free.
      simpa [selected_free_cover_resolution_complex] using
        selected_free_cover_obj_free (R := R) M
  | 1 =>
      -- Degree `1` is the selected free cover of the first syzygy, hence free.
      simpa [selected_free_cover_resolution_complex] using
        selected_free_cover_obj_free (R := R)
          (LinearMap.ker (selected_free_cover_map (R := R) M).hom)
  | n + 2 =>
      -- Higher degrees are reindexed copies of the same selected-cover construction.
      let e := selected_free_cover_resolution_step_iso (R := R) (M := M) n
      let eₗ :
          (selected_free_cover_resolution_complex (R := R) (M := M)).X (n + 2) ≃ₗ[R]
            selected_free_cover_obj (R := R)
              (LinearMap.ker ((selected_free_cover_resolution_step_d
                (R := R) (M := M) n).hom)) :=
        LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)
      letI :
          Module.Free R
            (selected_free_cover_obj (R := R)
              (LinearMap.ker ((selected_free_cover_resolution_step_d
                (R := R) (M := M) n).hom))) :=
        selected_free_cover_obj_free (R := R)
          (LinearMap.ker ((selected_free_cover_resolution_step_d
            (R := R) (M := M) n).hom))
      -- Transport freeness back across the bookkeeping linear equivalence.
      exact Module.Free.of_equiv' inferInstance eₗ.symm

/-- Helper for Lemma 10.71.1: the selected-cover complex together with its augmentation is a free
resolution of `M`. -/
lemma selected_free_cover_resolution_isFreeResolution :
    IsFreeResolution (selected_free_cover_resolution_augmentation (R := R) (M := M)) := by
  letI : QuasiIso (selected_free_cover_resolution_augmentation (R := R) (M := M)) := ⟨fun n => by
    -- The quasi-isomorphism is checked at degree `0` by the explicit short exact sequence,
    -- and in positive degrees by exactness against the zero complex.
    cases n with
    | zero =>
        simpa using selected_free_cover_resolution_quasiIsoAt_zero (R := R) (M := M)
    | succ n =>
        rw [quasiIsoAt_iff_exactAt'
            (hL := ChainComplex.exactAt_succ_single_obj (ModuleCat.of R M) n)]
        exact selected_free_cover_resolution_exactAt_succ (R := R) (M := M) n⟩
  -- Once quasi-isomorphism is known, only termwise freeness remains.
  exact ⟨selected_free_cover_resolution_termwise_free (R := R) (M := M)⟩

/-- Helper for Lemma 10.71.1: over a Noetherian ring, the kernel of a map from a finite module is
finite. -/
lemma kernel_finite_of_domain_finite {X₀ X₁ : ModuleCat.{max u v} R} [IsNoetherianRing R]
    (f : X₁ ⟶ X₀) [Module.Finite R X₁] :
    Module.Finite R (LinearMap.ker f.hom) := by
  -- A kernel is a submodule of the finite source, hence Noetherian and therefore finite.
  letI : IsNoetherian R X₁ := inferInstance
  letI : IsNoetherian R (LinearMap.ker f.hom) := inferInstance
  exact Module.IsNoetherian.finite R (LinearMap.ker f.hom)

/-- Helper for Lemma 10.71.1: if the ring is Noetherian and `M` is finite, then every term in the
selected-cover resolution is finite. -/
lemma selected_free_cover_resolution_termwise_finite [IsNoetherianRing R] [Module.Finite R M] :
    ChainComplex.IsTermwiseFinite (selected_free_cover_resolution_complex (R := R) (M := M)) := by
  intro n
  induction n with
  | zero =>
      -- Degree `0` is the selected finite free cover of `M`.
      simpa [selected_free_cover_resolution_complex] using
        selected_free_cover_obj_finite (R := R) M
  | succ n ih =>
      cases n with
      | zero =>
          -- Degree `1` is the selected finite free cover of the first syzygy.
          have hker : Module.Finite R
              (LinearMap.ker (selected_free_cover_map (R := R) M).hom) := by
            letI : Module.Finite R (selected_free_cover_obj (R := R) M) :=
              selected_free_cover_obj_finite (R := R) M
            exact kernel_finite_of_domain_finite (R := R)
              (selected_free_cover_map (R := R) M)
          letI := hker
          simpa [selected_free_cover_resolution_complex] using
            selected_free_cover_obj_finite (R := R)
              (LinearMap.ker (selected_free_cover_map (R := R) M).hom)
      | succ n =>
          -- Higher-degree terms are selected finite free covers of the previous syzygies.
          let e := selected_free_cover_resolution_step_iso (R := R) (M := M) n
          let eₗ :
              (selected_free_cover_resolution_complex (R := R) (M := M)).X (n + 2) ≃ₗ[R]
                selected_free_cover_obj (R := R)
                  (LinearMap.ker ((selected_free_cover_resolution_step_d
                    (R := R) (M := M) n).hom)) :=
            LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)
          have hker : Module.Finite R
              (LinearMap.ker ((selected_free_cover_resolution_step_d
                (R := R) (M := M) n).hom)) := by
            letI : Module.Finite R
                ((selected_free_cover_resolution_complex (R := R) (M := M)).X (n + 1)) := ih
            exact kernel_finite_of_domain_finite (R := R)
              (selected_free_cover_resolution_step_d (R := R) (M := M) n)
          letI := hker
          letI :
              Module.Finite R
                (selected_free_cover_obj (R := R)
                  (LinearMap.ker ((selected_free_cover_resolution_step_d
                    (R := R) (M := M) n).hom))) :=
            selected_free_cover_obj_finite (R := R)
              (LinearMap.ker ((selected_free_cover_resolution_step_d
                (R := R) (M := M) n).hom))
          -- Transport finiteness back across the bookkeeping linear equivalence.
          exact Module.Finite.equiv eₗ.symm

/-- Helper for Lemma 10.71.1: if the ring is Noetherian and `M` is finite, then the selected-cover
resolution is finite free. -/
lemma selected_free_cover_resolution_isFiniteFreeResolution [IsNoetherianRing R]
    [Module.Finite R M] :
    IsFiniteFreeResolution (selected_free_cover_resolution_augmentation (R := R) (M := M)) := by
  -- The free-resolution part is already closed; add the termwise finiteness proof.
  let hfree : IsFreeResolution
      (selected_free_cover_resolution_augmentation (R := R) (M := M)) :=
    selected_free_cover_resolution_isFreeResolution (R := R) (M := M)
  letI := hfree
  exact ⟨selected_free_cover_resolution_termwise_finite (R := R) (M := M)⟩

/-- Lemma 10.71.1 (2): if `R` is Noetherian and `M` is finite, then `M` admits a resolution by
finite free `R`-modules. -/
lemma module_exists_finite_free_resolution [IsNoetherianRing R] [Module.Finite R M] :
    ∃ (F : ChainComplex (ModuleCat.{max u v} R) ℕ)
      (π : F ⟶ CategoryTheory.Functor.obj
        (ChainComplex.single₀ (ModuleCat.{max u v} R)) (ModuleCat.of R M)),
      IsFiniteFreeResolution π := by
  -- The source-faithful Noetherian proof uses the same syzygy recursion, replacing each canonical
  -- free cover by a chosen finite free cover from `Module.Finite.exists_fin'`.
  refine ⟨selected_free_cover_resolution_complex (R := R) (M := M),
    selected_free_cover_resolution_augmentation (R := R) (M := M), ?_⟩
  -- The selected-cover recursion is exact in general and finite along the Noetherian branch.
  exact selected_free_cover_resolution_isFiniteFreeResolution (R := R) (M := M)

end

/-! ### Definition_10_71_2 (from Chap10) -/
open CategoryTheory ChainComplex

universe u v

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {F : ChainComplex (ModuleCat R) ℕ}

local notation "moduleSingle" =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/- Definition 10.71.2 (1): an augmented chain complex of `R`-modules
`π : F ⟶ moduleSingle` is a left resolution of `M`
when `π` is a quasi-isomorphism; this is the canonical mathlib notion `QuasiIso`. -/
recall QuasiIso

namespace ChainComplex

/-- A chain complex of `R`-modules is termwise free when every degree is a free `R`-module. -/
def IsTermwiseFree (F : ChainComplex (ModuleCat R) ℕ) : Prop :=
  ∀ n : ℕ, Module.Free R (F.X n)

/-- A chain complex of `R`-modules is termwise finite when every degree is a finite `R`-module. -/
def IsTermwiseFinite (F : ChainComplex (ModuleCat R) ℕ) : Prop :=
  ∀ n : ℕ, Module.Finite R (F.X n)

/-- Definition 10.71.2 (2): a free resolution of an `R`-module `M` is an augmented chain complex
`π : F ⟶ moduleSingle` which is a quasi-isomorphism and whose terms are all free `R`-modules. -/
class IsFreeResolution (π : F ⟶ moduleSingle) : Prop extends QuasiIso π where
  termwise_free : IsTermwiseFree F

namespace IsFreeResolution

theorem free (π : F ⟶ moduleSingle) [h : IsFreeResolution π] (n : ℕ) :
    Module.Free R (F.X n) :=
  h.termwise_free n

/-- A free resolution gives the canonical projective resolution of `ModuleCat.of R M`. -/
noncomputable def toProjectiveResolution (π : F ⟶ moduleSingle) [h : IsFreeResolution π] :
    ProjectiveResolution (ModuleCat.of R M) where
  complex := F
  projective n := by
    let _ : Module.Free R (F.X n) := h.termwise_free n
    infer_instance
  π := π

end IsFreeResolution

/-- Definition 10.71.2 (3): a finite free resolution of an `R`-module `M` is a free resolution
whose terms are finite `R`-modules. -/
class IsFiniteFreeResolution (π : F ⟶ moduleSingle) : Prop extends IsFreeResolution π where
  termwise_finite : IsTermwiseFinite F

namespace IsFiniteFreeResolution

theorem finite (π : F ⟶ moduleSingle) [h : IsFiniteFreeResolution π] (n : ℕ) :
    Module.Finite R (F.X n) :=
  h.termwise_finite n

end IsFiniteFreeResolution

end ChainComplex

end

/-! ### Lemma_10_71_3 (from Chap10) -/
/- Lemma 10.71.3: any two homotopic maps of complexes induce the same maps on
(co)homology groups. This is exactly the canonical mathlib statement
`Homotopy.homologyMap_eq`, which applies uniformly to chain and cochain complexes. -/
recall Homotopy.homologyMap_eq

/-! ### Lemma_10_71_4 (from Chap10) -/
open CategoryTheory
open Category
open CategoryTheory.Limits
open ChainComplex
open HomologicalComplex

universe u v

noncomputable section

section

variable {R : Type u} [Ring R]
variable {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {F G : ChainComplex (ModuleCat R) ℕ}

local notation "moduleSingle[" M "]" =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/-- Helper for Lemma 10.71.4: every free term of the source complex is projective in
`ModuleCat R`. -/
lemma termwise_projective (hFfree : ChainComplex.IsTermwiseFree F) (n : ℕ) :
    Projective (F.X n) := by
  -- Convert termwise freeness into the projectivity used by the lifting lemmas.
  let _ : Module.Free R (F.X n) := hFfree n
  infer_instance

/-- Helper for Lemma 10.71.4: the degree-`0` augmentation cofork is a cokernel cofork. -/
lemma quasiIso_single_zero_isColimitCokernelCofork_exists
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] :
    Nonempty (IsColimit (CokernelCofork.ofπ (πG.f 0) (by simpa using (πG.comm 1 0).symm))) := by
  -- Transport the canonical cokernel description of `opcycles` along the quasi-isomorphism in
  -- degree `0`.
  refine ⟨IsColimit.ofIsoColimit (G.opcyclesIsCokernel 1 0 (by simp)) ?_⟩
  refine Cofork.ext (G.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt πG 0 ≪≫
    singleObjHomologySelfIso _ _ _) ?_
  rw [← cancel_mono (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 _).inv,
    ← cancel_mono (ChainComplex.isoHomologyι₀ _).hom]
  dsimp
  simp only [ChainComplex.isoHomologyι₀_inv_naturality_assoc, p_opcyclesMap_assoc,
    single₀_obj_zero, assoc, Iso.hom_inv_id, comp_id, isoHomologyι_inv_hom_id,
    singleObjHomologySelfIso_inv_homologyι, singleObjOpcyclesSelfIso_hom, single₀ObjXSelf,
    Iso.refl_inv, id_comp]

/-- Helper for Lemma 10.71.4: a quasi-isomorphism to `single₀` identifies degree `0` with the
cokernel of the first differential. -/
noncomputable abbrev quasiIso_single_zero_isColimitCokernelCofork
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] :
    IsColimit (CokernelCofork.ofπ (πG.f 0) (by simpa using (πG.comm 1 0).symm)) :=
  Classical.choice (quasiIso_single_zero_isColimitCokernelCofork_exists (R := R) (N := N) (G := G) πG)

/-- Helper for Lemma 10.71.4: the augmentation at degree `0` is an epimorphism. -/
lemma quasiIso_single_epi_zero (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] :
    Epi (πG.f 0) := by
  -- The cokernel description at degree `0` gives the required epimorphism.
  simpa using Limits.epi_of_isColimit_cofork
    (quasiIso_single_zero_isColimitCokernelCofork (πG := πG))

/-- Helper for Lemma 10.71.4: the degree-`0` augmentation is available to typeclass search as an
epimorphism. -/
instance quasiIso_single_epi_zero_inst (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] :
    Epi (πG.f 0) :=
  quasiIso_single_epi_zero (R := R) (N := N) (G := G) πG

/-- Helper for Lemma 10.71.4: the short complex `G₁ ⟶ G₀ ⟶ N` is exact. -/
lemma quasiIso_single_exact_zero (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] :
    (ShortComplex.mk (G.d 1 0) (πG.f 0) (by simpa using (πG.comm 1 0).symm)).Exact := by
  -- Exactness at degree `0` follows from the cokernel description above.
  exact ShortComplex.exact_of_g_is_cokernel _ <|
    quasiIso_single_zero_isColimitCokernelCofork (πG := πG)

/-- Helper for Lemma 10.71.4: a quasi-isomorphism to `single₀` makes the target exact in every
positive degree. -/
lemma quasiIso_single_exact_succ (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (n : ℕ) :
    (ShortComplex.mk (G.d (n + 2) (n + 1)) (G.d (n + 1) n)
      (G.d_comp_d (n + 2) (n + 1) n)).Exact := by
  -- Away from degree `0`, the single complex is exact, so quasi-isomorphism transfers exactness
  -- back to `G`.
  have hExactAt : G.ExactAt (n + 1) :=
    (quasiIsoAt_iff_exactAt' πG (n + 1)
      (ChainComplex.exactAt_succ_single_obj (ModuleCat.of R N) n)).1 inferInstance
  exact
    ((HomologicalComplex.exactAt_iff' G (n + 2) (n + 1) n) (by simp only [prev]; rfl)
      (by simp)).1 hExactAt

/-- Helper for Lemma 10.71.4: choose the degree-`0` component of the lift by factoring through
the augmentation of the target resolution. -/
lemma lift_zero_component_exists
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M]) (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    ∃ g : F.X 0 ⟶ G.X 0, g ≫ πG.f 0 = πF.f 0 ≫ f := by
  -- Projectivity of `F₀` and surjectivity of `G₀ ⟶ N` give the first lift.
  let g : F.X 0 ⟶ G.X 0 :=
    @Projective.factorThru (ModuleCat R) _ (F.X 0) (ModuleCat.of R N) (G.X 0)
      (termwise_projective (F := F) (R := R) hFfree 0)
      (πF.f 0 ≫ f) (πG.f 0)
      (quasiIso_single_epi_zero (R := R) (N := N) (G := G) πG)
  refine ⟨g, ?_⟩
  simpa [g] using
    (@Projective.factorThru_comp (ModuleCat R) _ (F.X 0) (ModuleCat.of R N) (G.X 0)
      (termwise_projective (F := F) (R := R) hFfree 0)
      (πF.f 0 ≫ f) (πG.f 0)
      (quasiIso_single_epi_zero (R := R) (N := N) (G := G) πG))

/-- Helper for Lemma 10.71.4: choose the degree-`0` component of the lift by factoring through
the augmentation of the target resolution. -/
noncomputable abbrev lift_zero_component
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M]) (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    F.X 0 ⟶ G.X 0 :=
  Classical.choose (lift_zero_component_exists (R := R) (M := M) (N := N) (F := F) (G := G)
    f πF πG hFfree)

/-- Helper for Lemma 10.71.4: the degree-`0` lift is compatible with the augmentations. -/
lemma lift_zero_component_comp
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M]) (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    lift_zero_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree ≫ πG.f 0 =
      πF.f 0 ≫ f := by
  -- This is the chosen factorization equation from the previous existence lemma.
  exact Classical.choose_spec (lift_zero_component_exists (R := R) (M := M) (N := N)
    (F := F) (G := G) f πF πG hFfree)

/-- Helper for Lemma 10.71.4: the degree-`1` obstruction lands in the kernel of the augmentation
of `G₀`. -/
lemma lift_one_component_condition
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M]) (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    F.d 1 0 ≫ lift_zero_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree ≫
        πG.f 0 = 0 := by
  -- Compatibility of the degree-`0` lift with the augmentations kills the obstruction.
  have h :=
    congrArg (fun k ↦ F.d 1 0 ≫ k)
      (lift_zero_component_comp (R := R) (M := M) (N := N) (F := F) (G := G)
        f πF πG hFfree)
  have hπ : F.d 1 0 ≫ πF.f 0 = 0 := by
    simpa using (πF.comm 1 0).symm
  calc
    F.d 1 0 ≫ lift_zero_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG
        hFfree ≫ πG.f 0 =
      F.d 1 0 ≫ πF.f 0 ≫ f := by
        simpa [Category.assoc] using h
    _ = 0 := by
        exact (congrArg (fun k ↦ k ≫ f) hπ).trans <|
          (Limits.zero_comp : (0 : F.X 1 ⟶ ModuleCat.of R M) ≫ f = 0)

/-- Helper for Lemma 10.71.4: exactness at degree `0` lifts the first obstruction into degree
`1`. -/
noncomputable abbrev lift_one_component
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M]) (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    F.X 1 ⟶ G.X 1 :=
  letI : Projective (F.X 1) := termwise_projective (F := F) (R := R) hFfree 1
  (quasiIso_single_exact_zero (R := R) (N := N) (G := G) πG).liftFromProjective
    (F.d 1 0 ≫ lift_zero_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree)
    (lift_one_component_condition (R := R) (M := M) (N := N) (F := F) (G := G)
      f πF πG hFfree)

/-- Helper for Lemma 10.71.4: the lifted degree-`1` component commutes with the differentials. -/
lemma lift_one_component_comm
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M]) (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    lift_one_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree ≫ G.d 1 0 =
      F.d 1 0 ≫ lift_zero_component (R := R) (M := M) (N := N) (F := F) (G := G)
        f πF πG hFfree := by
  -- This is the defining equation of the exactness lift at degree `0`.
  letI : Projective (F.X 1) := termwise_projective (F := F) (R := R) hFfree 1
  exact (quasiIso_single_exact_zero (R := R) (N := N) (G := G) πG).liftFromProjective_comp _ _

/-- Helper for Lemma 10.71.4: exactness in positive degrees lifts each successive obstruction. -/
noncomputable abbrev lift_obstruction_through_exact_succ
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (n : ℕ) (g : F.X n ⟶ G.X n) (g' : F.X (n + 1) ⟶ G.X (n + 1))
    (w : g' ≫ G.d (n + 1) n = F.d (n + 1) n ≫ g) :
    Σ' g'' : F.X (n + 2) ⟶ G.X (n + 2),
      g'' ≫ G.d (n + 2) (n + 1) = F.d (n + 2) (n + 1) ≫ g' :=
  letI : Projective (F.X (n + 2)) := termwise_projective (F := F) (R := R) hFfree (n + 2)
  ⟨(quasiIso_single_exact_succ (R := R) (N := N) (G := G) πG n).liftFromProjective
      (F.d (n + 2) (n + 1) ≫ g') (by simp [w]),
    (quasiIso_single_exact_succ (R := R) (N := N) (G := G) πG n).liftFromProjective_comp _ _⟩

/-- Helper for Lemma 10.71.4: if `γ` dies after augmentation, its degree-`0` component lifts
through `G₁ ⟶ G₀`. -/
noncomputable abbrev nullhomotopy_zero_component
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (hγ : γ ≫ πG = 0) :
    F.X 0 ⟶ G.X 1 :=
  letI : Projective (F.X 0) := termwise_projective (F := F) (R := R) hFfree 0
  (quasiIso_single_exact_zero (R := R) (N := N) (G := G) πG).liftFromProjective
    (γ.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f hγ) 0)

/-- Helper for Lemma 10.71.4: the degree-`0` homotopy component kills `γ.f 0`. -/
lemma nullhomotopy_zero_component_comp
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (hγ : γ ≫ πG = 0) :
    nullhomotopy_zero_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ ≫ G.d 1 0 =
      γ.f 0 := by
  -- This is the defining property of the exactness lift at degree `0`.
  letI : Projective (F.X 0) := termwise_projective (F := F) (R := R) hFfree 0
  exact (quasiIso_single_exact_zero (R := R) (N := N) (G := G) πG).liftFromProjective_comp _ _

/-- Helper for Lemma 10.71.4: after correcting degree `0`, the degree-`1` obstruction is a
cycle in `G₁`. -/
lemma nullhomotopy_one_component_condition
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (hγ : γ ≫ πG = 0) :
    (γ.f 1 - F.d 1 0 ≫
        nullhomotopy_zero_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ) ≫
        G.d 1 0 = 0 := by
  -- The chain map identity and the degree-`0` correction cancel the boundary.
  rw [Preadditive.sub_comp, assoc, nullhomotopy_zero_component_comp, γ.comm]
  simp

/-- Helper for Lemma 10.71.4: after correcting by the degree-`0` homotopy component, the degree-`1`
obstruction lifts into `G₂`. -/
noncomputable abbrev nullhomotopy_one_component
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (hγ : γ ≫ πG = 0) :
    F.X 1 ⟶ G.X 2 :=
  letI : Projective (F.X 1) := termwise_projective (F := F) (R := R) hFfree 1
  (quasiIso_single_exact_succ (R := R) (N := N) (G := G) πG 0).liftFromProjective
    (γ.f 1 - F.d 1 0 ≫
      nullhomotopy_zero_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ)
    (nullhomotopy_one_component_condition (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ)

/-- Helper for Lemma 10.71.4: the degree-`1` homotopy component gives the required correction in
degree `1`. -/
lemma nullhomotopy_one_component_comp
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (hγ : γ ≫ πG = 0) :
    nullhomotopy_one_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ ≫ G.d 2 1 =
      γ.f 1 - F.d 1 0 ≫
        nullhomotopy_zero_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ := by
  -- This is the defining equation of the lift through `G₂ ⟶ G₁`.
  letI : Projective (F.X 1) := termwise_projective (F := F) (R := R) hFfree 1
  exact (quasiIso_single_exact_succ (R := R) (N := N) (G := G) πG 0).liftFromProjective_comp _ _

/-- Helper for Lemma 10.71.4: after two consecutive homotopy components are fixed, exactness in
positive degrees lifts the next corrected obstruction. -/
lemma nullhomotopy_succ_component_condition
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG]
    (γ : F ⟶ G) (n : ℕ) (g : F.X n ⟶ G.X (n + 1)) (g' : F.X (n + 1) ⟶ G.X (n + 2))
    (w : γ.f (n + 1) = F.d (n + 1) n ≫ g + g' ≫ G.d (n + 2) (n + 1)) :
    (γ.f (n + 2) - F.d (n + 2) (n + 1) ≫ g') ≫ G.d (n + 2) (n + 1) = 0 := by
  -- The inductive correction produces a cycle exactly as in the textbook recurrence.
  rw [Preadditive.sub_comp, γ.comm, w]
  simp [assoc]

/-- Helper for Lemma 10.71.4: after two consecutive homotopy components are fixed, exactness in
positive degrees lifts the next corrected obstruction. -/
noncomputable abbrev nullhomotopy_succ_component
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (n : ℕ) (g : F.X n ⟶ G.X (n + 1)) (g' : F.X (n + 1) ⟶ G.X (n + 2))
    (w : γ.f (n + 1) = F.d (n + 1) n ≫ g + g' ≫ G.d (n + 2) (n + 1)) :
    F.X (n + 2) ⟶ G.X (n + 3) :=
  letI : Projective (F.X (n + 2)) := termwise_projective (F := F) (R := R) hFfree (n + 2)
  (quasiIso_single_exact_succ (R := R) (N := N) (G := G) πG (n + 1)).liftFromProjective
    (γ.f (n + 2) - F.d (n + 2) (n + 1) ≫ g')
    (nullhomotopy_succ_component_condition (R := R) (N := N) (F := F) (G := G)
      πG γ n g g' w)

/-- Helper for Lemma 10.71.4: the successor homotopy component satisfies the inductive
correction identity. -/
lemma nullhomotopy_succ_component_comp
    (πG : G ⟶ moduleSingle[N]) [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    (γ : F ⟶ G) (n : ℕ) (g : F.X n ⟶ G.X (n + 1)) (g' : F.X (n + 1) ⟶ G.X (n + 2))
    (w : γ.f (n + 1) = F.d (n + 1) n ≫ g + g' ≫ G.d (n + 2) (n + 1)) :
    nullhomotopy_succ_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ n g g' w ≫
        G.d (n + 3) (n + 2) =
      γ.f (n + 2) - F.d (n + 2) (n + 1) ≫ g' := by
  -- This is the defining equation of the positive-degree lift.
  letI : Projective (F.X (n + 2)) := termwise_projective (F := F) (R := R) hFfree (n + 2)
  exact (quasiIso_single_exact_succ (R := R) (N := N) (G := G) πG (n + 1)).liftFromProjective_comp _ _

/-- Lemma 10.71.4 (1): for a map `M ⟶ N`, a resolution `πG : G ⟶ N`, and a chain complex
`πF : F ⟶ M` of free `R`-modules, there exists a chain map `F ⟶ G` compatible with the
augmentations. -/
-- Proof sketch: construct the lift degreewise using projectivity of the free source terms.
-- This is the same inductive lifting pattern as the owner construction
-- `ProjectiveResolution.lift`, specialized to a source complex that need not itself resolve `M`.
-- Since `F.X 0` is free, lift the composite `F.X 0 ⟶ M ⟶ N` through `πG.f 0`. Inductively,
-- exactness of `G` in positive degrees shows that the obstruction to extending the partial lift
-- lands in the image of the next differential, and the termwise-free hypothesis on `F` allows one
-- to lift through that differential in each degree.
lemma free_complex_lift_to_resolution_exists
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M])
    (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F) :
    ∃ α : F ⟶ G, α ≫ πG = πF ≫ (ChainComplex.single₀ (ModuleCat R)).map f := by
  -- Build the lift degreewise: degree `0`, degree `1`, and then the inductive successor step.
  refine ⟨ChainComplex.mkHom _ _
      (lift_zero_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree)
      (lift_one_component (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree)
      (lift_one_component_comm (R := R) (M := M) (N := N) (F := F) (G := G) f πF πG hFfree)
      (fun n p ↦
        lift_obstruction_through_exact_succ (R := R) (N := N) (F := F) (G := G) πG hFfree n
          p.1 p.2.1 p.2.2), ?_⟩
  -- The constructed chain map is compatible with the augmentations: degree `0` is by construction,
  -- and all positive degrees vanish against the single complex.
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      simpa using lift_zero_component_comp (R := R) (M := M) (N := N) (F := F) (G := G)
        f πF πG hFfree
  | succ n =>
      apply IsZero.eq_of_tgt
      apply HomologicalComplex.isZero_single_obj_X
      simp

/-- Lemma 10.71.4 (2): any two augmentation-compatible lifts from a free chain complex to a
resolution are homotopic. -/
-- Proof sketch: subtract the two lifts to reduce to a chain map `γ : F ⟶ G` with `γ ≫ πG = 0`.
-- The same inductive construction that underlies `ProjectiveResolution.liftHomotopy` then
-- yields a homotopy between `α` and `β`. Lift `γ.f 0` through `G.d 1 0` using exactness at
-- degree `0`, then inductively correct `γ.f (n + 1)` by the previously constructed homotopy
-- component and lift the remainder through `G.d (n + 2) (n + 1)` using exactness and the
-- termwise-free hypothesis on `F`.
theorem free_complex_lifts_to_resolution_are_homotopic
    (f : ModuleCat.of R M ⟶ ModuleCat.of R N)
    (πF : F ⟶ moduleSingle[M])
    (πG : G ⟶ moduleSingle[N])
    [QuasiIso πG] (hFfree : ChainComplex.IsTermwiseFree F)
    {α β : F ⟶ G}
    (hα : α ≫ πG = πF ≫ (ChainComplex.single₀ (ModuleCat R)).map f)
    (hβ : β ≫ πG = πF ≫ (ChainComplex.single₀ (ModuleCat R)).map f) :
    homotopic (ModuleCat R) (ComplexShape.down ℕ) α β := by
  -- Subtract the two compatible lifts and construct a null-homotopy of the difference.
  let γ : F ⟶ G := α - β
  have hγ : γ ≫ πG = 0 := by
    simp [γ, hα, hβ]
  refine ⟨Homotopy.equivSubZero.invFun <|
    Homotopy.mkInductive γ
      (nullhomotopy_zero_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ)
      (by
        have h :=
          nullhomotopy_zero_component_comp
            (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ
        simpa using h.symm)
      (nullhomotopy_one_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ)
      (by
        have h :=
          nullhomotopy_one_component_comp
            (R := R) (N := N) (F := F) (G := G) πG hFfree γ hγ
        rw [eq_sub_iff_add_eq] at h
        simpa [add_comm, add_left_comm, add_assoc] using h.symm)
      (fun n p ↦
        ⟨nullhomotopy_succ_component (R := R) (N := N) (F := F) (G := G) πG hFfree γ n
            p.1 p.2.1 p.2.2,
          by
            have h :=
              nullhomotopy_succ_component_comp
                (R := R) (N := N) (F := F) (G := G) πG hFfree γ n
                p.1 p.2.1 p.2.2
            rw [eq_sub_iff_add_eq] at h
            simpa [add_comm, add_left_comm, add_assoc] using h.symm⟩)⟩

end
