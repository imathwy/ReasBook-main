import StacksProject_2024.Chap10.Lemma_10_99_8
import StacksProject_2024.Chap10.Lemma_10_99_16.Index

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Pointwise
open scoped TensorProduct

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]

/-- Helper for Chap10 Lemma 10 99 16: once `M / fM` is flat over `A / (f)` and the principal quotient
owner vanishes, Lemma `10.99.8` gives the source sentence that every module annihilated by `f`
has vanishing quotient-first `Tor₁` with `M`. -/
lemma tor_one_of_f_annihilated_vanishes
    (f : A) (hfA : IsRegular f) (hfM : IsSMulRegular M f)
    (hquot : Module.Flat (A ⧸ Ideal.span ({f} : Set A)) (QuotSMulTop f M))
    {N : Type u} [AddCommGroup N] [Module A N]
    (hN : Ideal.span ({f} : Set A) ≤ Module.annihilator A N) :
    IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj (ModuleCat.of A M))) := by
  let I : Ideal A := Ideal.span ({f} : Set A)
  let _ : Module.Flat (A ⧸ I) (QuotSMulTop f M) := by
    simpa [I] using hquot
  let _ :
      IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A M))) := by
    simpa [I] using
      tor_one_quotient_first_by_regular_element_vanishes (A := A) (M := M) f hfA hfM
  let _ := hfM
  -- Proof comment: Lemma `10.99.8` applies directly with the principal ideal `(f)` and exponent
  -- `1`, since the annihilator hypothesis already says `N` is killed by `(f)`.
  have hNpow : I ^ 1 ≤ Module.annihilator A N := by
    simpa [I] using hN
  simpa [I] using
    tor_one_vanishes_of_annihilated_by_ideal_pow (R := A) (I := I) (M := M) 1 hNpow

/-- Helper for Chap10 Lemma 10 99 16: every module annihilated by `(f)` also has vanishing
quotient-first `Tor₂` with `M`. This is the source proof's descent from free `A / (f)`-covers. -/
lemma tor_two_of_f_annihilated_vanishes
    (f : A) (hfA : IsRegular f) (hfM : IsSMulRegular M f)
    (hquot : Module.Flat (A ⧸ Ideal.span ({f} : Set A)) (QuotSMulTop f M))
    {N : Type u} [AddCommGroup N] [Module A N]
    (hN : Ideal.span ({f} : Set A) ≤ Module.annihilator A N) :
    IsZero ((((Tor (ModuleCat A) 2).obj (ModuleCat.of A N)).obj (ModuleCat.of A M))) := by
  let I : Ideal A := Ideal.span ({f} : Set A)
  let Abar : Type u := A ⧸ I
  let _ : CommRing Abar := inferInstance
  let hfN : Module.IsTorsionBy A N f :=
    isTorsionBy_of_span_singleton_le_annihilator (A := A) f hN
  let hNset : Module.IsTorsionBySet A N (I : Set A) := by
    simpa [I] using (Module.isTorsionBySet_span_singleton_iff f).mpr hfN
  let _ : Module Abar N :=
    Module.IsTorsionBySet.module (R := A) (M := N) (I := I) hNset
  let _ : IsScalarTower A Abar N :=
    Module.IsTorsionBySet.isScalarTower (R := A) (M := N) (I := I) hNset
  let F : Type u := N →₀ Abar
  let π : F →ₗ[Abar] N := Finsupp.linearCombination Abar fun n : N => n
  have hπ_surjective : Function.Surjective π := by
    intro n
    refine ⟨Finsupp.single n 1, ?_⟩
    change (Finsupp.linearCombination Abar (fun n : N => n)) (Finsupp.single n 1) = n
    simp
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk
      ((LinearMap.ker π).subtype.restrictScalars A)
      (π.restrictScalars A)
      (Function.Exact.linearMap_comp_eq_zero
        ((π.restrictScalars A).exact_subtype_ker_map))
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [S] using ((π.restrictScalars A).exact_subtype_ker_map)
    · exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
    · exact (ModuleCat.epi_iff_surjective _).2 <| by
        simpa using hπ_surjective
  have hKerAnn :
      I ≤ Module.annihilator A (LinearMap.ker π) := by
    -- Proof comment: the kernel of the free `A / (f)`-cover is still an `A / (f)`-module.
    simpa [I] using
      span_singleton_le_annihilator_of_quotient_module
        (A := A) (f := f) (N := LinearMap.ker π)
  have hTor₂F :
      IsZero ((((Tor (ModuleCat A) 2).obj (ModuleCat.of A F)).obj
        (ModuleCat.of A M))) := by
    -- Proof comment: the middle free cover term is a free `A / (f)`-module, so the free base
    -- case applies.
    simpa [I, F] using
      tor_two_free_quotient_module_vanishes (A := A) (M := M) f hfA (ι := N)
  have hTor₁Ker :
      IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A (LinearMap.ker π))).obj
        (ModuleCat.of A M))) := by
    -- Proof comment: the kernel is annihilated by `(f)`, so the previously proved degree-`1`
    -- annihilated-module vanishing applies.
    simpa [I] using
      tor_one_of_f_annihilated_vanishes (A := A) (M := M) f hfA hfM hquot hKerAnn
  obtain ⟨δ, hFive⟩ :=
    tor_two_tor_one_five_term_exact_of_shortExact (A := A) (M := M) (S := S) hS
  let β :
      ((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).obj S.X₂) ⟶
        ((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).obj S.X₃) :=
    (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map S.g))
  have hβ_zero : β = 0 := by
    -- Proof comment: the free-cover term already has vanishing degree-`2` Tor.
    simpa [β, S] using hTor₂F.eq_of_src β 0
  have hδ_zero : δ = 0 := by
    -- Proof comment: the kernel term has vanishing degree-`1` Tor.
    simpa [S] using hTor₁Ker.eq_of_tgt δ 0
  have hExactMid :
      Function.Exact β.hom δ.hom := by
    -- Proof comment: exactness at `Tor₂(N, M)` comes from the quotient-first `(2,1)` exact row
    -- attached to the free-cover short exact sequence.
    simpa [β, S, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map S.f))
          (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map S.g))
          δ
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.f))
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.g))).sc
            hFive.toIsComplex 1)).1
        (hFive.exact 1)
  -- Proof comment: zero adjacent arrows force the middle `Tor₂(N, M)` object to vanish.
  simpa [β, S] using isZero_of_exact_zero_zero hExactMid hβ_zero hδ_zero

/-- Helper for Chap10 Lemma 10 99 16: the fixed-left source owner `Tor'` is the left derived functor of
tensoring in the second variable and evaluating at the fixed module `M`. -/
theorem sourceOwner_tor_eq_leftDerived_obj
    (X : ModuleCat A) (n : ℕ) :
    (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj X) =
      ((tensorRight X).leftDerived n).obj (ModuleCat.of A M) := by
  -- Proof comment: this is the definitional expansion needed for the projective-resolution
  -- computation of scalar maps on the source owner.
  rfl

/-- Helper for Chap10 Lemma 10 99 16: compute the fixed-left source owner on the chosen projective
resolution of `M`. -/
noncomputable def sourceOwner_tor_projectiveResolutionIso
    (X : ModuleCat A) (n : ℕ) :
    (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj X) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) n).obj
        (((tensorRight X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of A M)))) := by
  -- Proof comment: after unfolding the source owner, the standard projective resolution of `M`
  -- computes the derived functor.
  erw [sourceOwner_tor_eq_leftDerived_obj (A := A) (M := M) X n]
  exact
    (CategoryTheory.projectiveResolution (ModuleCat.of A M)).isoLeftDerivedObj
      (tensorRight X) n

/-- Helper for Chap10 Lemma 10 99 16: scalar multiplication on a `ModuleCat` identity morphism is the
bundled linear map `LinearMap.lsmul`. -/
lemma moduleCat_hom_smul_id_eq_lsmul (a : A) (X : ModuleCat A) :
    ModuleCat.Hom.hom (a • 𝟙 X) = LinearMap.lsmul A ↑X a := by
  -- Proof comment: this unwraps the category-level scalar action to the ordinary module action.
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 99 16: left tensoring a scalar-multiplication map is scalar
multiplication on the tensor product. -/
lemma lTensor_lsmul_eq_lsmul_tensor
    {P K : Type u} [AddCommGroup P] [Module A P] [AddCommGroup K] [Module A K] (a : A) :
    LinearMap.lTensor P (LinearMap.lsmul A K a) =
      LinearMap.lsmul A (P ⊗[A] K) a := by
  -- Proof comment: both maps send a pure tensor `p ⊗ k` to `a • (p ⊗ k)`.
  ext p k
  simpa [LinearMap.lsmul_apply] using (TensorProduct.tmul_smul p k a).symm

/-- Helper for Chap10 Lemma 10 99 16: on the tensorized resolution, the chain map induced by
`LinearMap.lsmul A K a` is scalar multiplication by `a`. -/
lemma tensorRight_mapHomologicalComplex_lsmul_eq_smul
    {K : Type u} [AddCommGroup K] [Module A K]
    (a : A) (C : ChainComplex (ModuleCat A) ℕ) :
    (NatTrans.mapHomologicalComplex
      ((tensoringRight (ModuleCat.{u} A)).map
        (ModuleCat.ofHom (LinearMap.lsmul A K a)))
      (ComplexShape.down ℕ)).app C =
      a • 𝟙 (((tensorRight (ModuleCat.of A K)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C) := by
  -- Proof comment: compare degreewise, where the tensor-level scalar identity applies.
  ext n x
  simpa [moduleCat_hom_smul_id_eq_lsmul] using
    congrArg (fun φ : ↑(C.X n) ⊗[A] K →ₗ[A] ↑(C.X n) ⊗[A] K => φ x)
      (lTensor_lsmul_eq_lsmul_tensor (A := A) (P := C.X n) (K := K) a)

/-- Helper for Chap10 Lemma 10 99 16: the short-complex cutout of a scalar map is the scalar map on the
short-complex cutout. -/
lemma shortComplexFunctor_map_smul_id
    (n : ℕ) {C : ChainComplex (ModuleCat A) ℕ} (a : A) :
    (HomologicalComplex.shortComplexFunctor (ModuleCat A) (ComplexShape.down ℕ) n).map
        (a • 𝟙 C) =
      a • 𝟙 (C.sc n) := by
  -- Proof comment: the short-complex functor only remembers the three adjacent components, and
  -- scalar multiplication is componentwise.
  ext <;>
    simp [HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']
  · rfl
  · rfl
  · rfl

/-- Helper for Chap10 Lemma 10 99 16: homology maps scalar multiplication on a chain complex to scalar
multiplication on homology. -/
lemma homologicalComplex_homologyMap_smul_id
    (n : ℕ) {C : ChainComplex (ModuleCat A) ℕ} (a : A) :
    HomologicalComplex.homologyMap (a • 𝟙 C) n =
      a • 𝟙 ((HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) n).obj C) := by
  -- Proof comment: reduce the homology map to the short-complex cutout, where scalar linearity is
  -- already available.
  dsimp [HomologicalComplex.homologyMap]
  rw [shortComplexFunctor_map_smul_id]
  rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

/-- Helper for Chap10 Lemma 10 99 16: in the fixed-left source owner, the morphism induced by
`LinearMap.lsmul A K a` is literal scalar multiplication by `a`. -/
lemma sourceOwner_map_lsmul_eq_smul
    (n : ℕ) {K : Type u} [AddCommGroup K] [Module A K] (a : A) :
    ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map
      (ModuleCat.ofHom (LinearMap.lsmul A K a)))) =
      ModuleCat.ofHom
        (LinearMap.lsmul A
          ↑((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K))) a) := by
  let X : ModuleCat A := ModuleCat.of A K
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of A M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A M)
  let C : ChainComplex (ModuleCat A) ℕ :=
    (((tensorRight X).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
  let e :
      ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj X)) ≅
        (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) n).obj C :=
    sourceOwner_tor_projectiveResolutionIso (A := A) (M := M) X n
  have hMapCat :
      ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom (LinearMap.lsmul A K a)))) =
        e.hom ≫
          HomologicalComplex.homologyMap
            ((NatTrans.mapHomologicalComplex
                ((tensoringRight (ModuleCat.{u} A)).map
                  (ModuleCat.ofHom (LinearMap.lsmul A K a)))
                (ComplexShape.down ℕ)).app P.complex)
            n ≫
          e.inv := by
    -- Proof comment: compute the source-owner map on the fixed projective resolution of `M`.
    simpa [X, C, sourceOwner_tor_eq_leftDerived_obj, Category.assoc, Tor'] using
      (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
        ((tensoringRight (ModuleCat.{u} A)).map
          (ModuleCat.ofHom (LinearMap.lsmul A K a))) P n)
  rw [hMapCat]
  rw [tensorRight_mapHomologicalComplex_lsmul_eq_smul (A := A) (K := K) (a := a) (C := P.complex)]
  rw [homologicalComplex_homologyMap_smul_id (A := A) (n := n) (C := C) a]
  -- Proof comment: linearity of the comparison isomorphism cancels the conjugation by `e`.
  apply ModuleCat.hom_ext
  ext x
  change e.inv.hom (a • e.hom.hom x) = a • x
  rw [LinearMap.map_smul]
  simpa using congrArg (fun y => a • y)
    (LinearEquiv.symm_apply_apply e.toLinearEquiv x)

/-- Helper for Chap10 Lemma 10 99 16: in the quotient-first public owner, the map induced by
`LinearMap.lsmul A K a` is literal scalar multiplication by `a`. -/
lemma torPublic_map_lsmul_eq_smul
    (n : ℕ) {K : Type u} [AddCommGroup K] [Module A K] (a : A) :
    (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map
      (ModuleCat.ofHom (LinearMap.lsmul A K a)))) =
      ModuleCat.ofHom
        (LinearMap.lsmul A
          ↑(((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K))) a) := by
  let X : ModuleCat A := ModuleCat.of A K
  let e :
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj X)) ≅
        ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj X)) :=
    (tor_left_owner_iso (A := A) (M := M) n).app X
  have hNat :
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom (LinearMap.lsmul A K a)))) ≫
        e.hom =
        e.hom ≫
          ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map
            (ModuleCat.ofHom (LinearMap.lsmul A K a)))) := by
    -- Proof comment: owner naturality transports the public map to the fixed-left source owner.
    simpa [e] using
      ((tor_left_owner_iso (A := A) (M := M) n).hom.naturality
        (ModuleCat.ofHom (LinearMap.lsmul A K a)))
  apply (cancel_mono e.hom).1
  rw [hNat, sourceOwner_map_lsmul_eq_smul (A := A) (M := M) (n := n) (K := K) a]
  -- Proof comment: scalar multiplication commutes with the linear comparison isomorphism.
  apply ModuleCat.hom_ext
  ext x
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.lsmul_apply] using
    (LinearMap.map_smul e.hom.hom a x).symm

/-- Helper for Chap10 Lemma 10 99 16: the kernel of multiplication by `f` is annihilated by `(f)`. -/
lemma span_singleton_le_annihilator_ker_lsmul
    (f : A) {K : Type u} [AddCommGroup K] [Module A K] :
    Ideal.span ({f} : Set A) ≤
      Module.annihilator A (LinearMap.ker (LinearMap.lsmul A K f)) := by
  -- Proof comment: the generator `f` kills each element of the kernel by definition.
  refine Ideal.span_le.mpr ?_
  intro a ha
  have ha' : a = f := by simpa using ha
  subst a
  change
    (Module.toAddMonoidEnd A
      (LinearMap.ker (LinearMap.lsmul A K f))) f = 0
  apply AddMonoidHom.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  simpa [LinearMap.mem_ker, LinearMap.lsmul_apply] using hx

/-- Helper for Chap10 Lemma 10 99 16: the quotient by the image of multiplication by `f` is
annihilated by `(f)`. -/
lemma span_singleton_le_annihilator_quotient_lsmul
    (f : A) {K : Type u} [AddCommGroup K] [Module A K] :
    Ideal.span ({f} : Set A) ≤
      Module.annihilator A (K ⧸ LinearMap.range (LinearMap.lsmul A K f)) := by
  let μ : K →ₗ[A] K := LinearMap.lsmul A K f
  -- Proof comment: the generator `f` acts by a representative lying in `range μ`, hence it is
  -- zero in the quotient.
  refine Ideal.span_le.mpr ?_
  intro a ha
  have ha' : a = f := by simpa using ha
  subst a
  change
    (Module.toAddMonoidEnd A
      (K ⧸ LinearMap.range (LinearMap.lsmul A K f))) f = 0
  apply AddMonoidHom.ext
  intro q
  rcases Submodule.mkQ_surjective (LinearMap.range μ) q with ⟨x, rfl⟩
  change Submodule.mkQ (LinearMap.range μ) (f • x) = 0
  apply (Submodule.Quotient.mk_eq_zero (LinearMap.range μ)).2
  exact ⟨x, by simp [μ, LinearMap.lsmul_apply]⟩

/-- Helper for Chap10 Lemma 10 99 16: if the Tor terms for the kernel and quotient rows of
multiplication by `a` vanish, then scalar multiplication by `a` is injective on the public
quotient-first Tor₁ owner. -/
lemma torPublic_one_smul_injective_of_kernel_and_quotient_vanishing
    {K : Type u} [AddCommGroup K] [Module A K] (a : A)
    (hker :
      IsZero
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (LinearMap.ker (LinearMap.lsmul A K a))))))
    (hquot :
      IsZero
        (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (K ⧸ LinearMap.range (LinearMap.lsmul A K a))))))
    (hmap :
      (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map
        (ModuleCat.ofHom (LinearMap.lsmul A K a)))) =
        ModuleCat.ofHom
          (LinearMap.lsmul A
            ↑(((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
              (ModuleCat.of A K))) a)) :
    Function.Injective
      fun t :
        ↑(((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A K))) ↦
        a • t := by
  let μ : K →ₗ[A] K := LinearMap.lsmul A K a
  let β₀ : K →ₗ[A] LinearMap.range μ := μ.rangeRestrict
  let γ₀ : LinearMap.range μ →ₗ[A] K := (LinearMap.range μ).subtype
  let q : K →ₗ[A] K ⧸ LinearMap.range μ := Submodule.mkQ (LinearMap.range μ)
  have hExactKerBase : Function.Exact (LinearMap.ker μ).subtype β₀ := by
    -- Proof comment: replacing multiplication by its range restriction keeps the same kernel and
    -- image.
    rw [LinearMap.exact_iff]
    simp [β₀]
  let Sker : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk (LinearMap.ker μ).subtype β₀
      (Function.Exact.linearMap_comp_eq_zero hExactKerBase)
  let Squot : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk γ₀ q
      (Function.Exact.linearMap_comp_eq_zero
        (by
          simpa [γ₀, q] using
            (LinearMap.exact_subtype_mkQ (LinearMap.range μ))))
  have hSker : Sker.ShortExact := by
    -- Proof comment: this is the short exact row `0 → ker μ → K → range μ → 0`.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [Sker] using hExactKerBase
    · exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
    · exact (ModuleCat.epi_iff_surjective _).2 <| by
        simpa [Sker, β₀] using μ.surjective_rangeRestrict
  have hSquot : Squot.ShortExact := by
    -- Proof comment: this is the short exact row `0 → range μ → K → K / range μ → 0`.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [Squot, γ₀, q] using
        (LinearMap.exact_subtype_mkQ (LinearMap.range μ))
    · exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
    · exact (ModuleCat.epi_iff_surjective _).2 <| by
        simpa [Squot, q] using Submodule.mkQ_surjective (LinearMap.range μ)
  obtain ⟨δKer, hFiveKer⟩ :=
    public_owner_tor_one_tensor_exact_of_shortExact (A := A) (M := M) (S := Sker) hSker
  obtain ⟨δ, hFiveQuot⟩ :=
    tor_two_tor_one_five_term_exact_of_shortExact (A := A) (M := M) (S := Squot) hSquot
  have hExactKer :
      Function.Exact
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Sker.f).hom)
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Sker.g).hom) := by
    -- Proof comment: exactness at the middle `Tor₁(K, M)` term comes from the kernel row.
    simpa [Sker, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Sker.f))
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Sker.g))
          δKer
          (((tensorRight (ModuleCat.of A M)).map Sker.f))
          (((tensorRight (ModuleCat.of A M)).map Sker.g))).sc hFiveKer.toIsComplex 0)).1
        (hFiveKer.exact 0)
  have hExactQuot :
      Function.Exact δ.hom
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Squot.f).hom) := by
    -- Proof comment: exactness at `Tor₁(range μ, M)` comes from the quotient row.
    simpa [Squot, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map Squot.f))
          (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map Squot.g))
          δ
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Squot.f))
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Squot.g))).sc
            hFiveQuot.toIsComplex 2)).1
        (hFiveQuot.exact 2)
  have hKerMapZero :
      ((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Sker.f) = 0 := by
    -- Proof comment: the first Tor object in the kernel row vanishes by hypothesis.
    simpa [Sker] using hker.eq_of_src
      (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Sker.f)) 0
  have hδZero : δ = 0 := by
    -- Proof comment: the degree-`2` Tor object for the quotient row vanishes by hypothesis.
    simpa [Squot] using hquot.eq_of_src δ 0
  have hβ_injective :
      Function.Injective
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Sker.g).hom) := by
    have hkerβ :
        LinearMap.ker (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Sker.g).hom) =
          ⊥ := by
      calc
        LinearMap.ker (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Sker.g).hom)
            =
          LinearMap.range (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Sker.f).hom) :=
              LinearMap.exact_iff.mp hExactKer
        _ = ⊥ := by
              have hzero :
                  (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Sker.f).hom) = 0 :=
                congrArg ModuleCat.Hom.hom hKerMapZero
              simpa [hzero] using (LinearMap.range_eq_bot.mpr hzero)
    exact (LinearMap.ker_eq_bot).1 hkerβ
  have hγ_injective :
      Function.Injective
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Squot.f).hom) := by
    have hkerγ :
        LinearMap.ker (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Squot.f).hom) =
          ⊥ := by
      calc
        LinearMap.ker (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Squot.f).hom)
            = LinearMap.range δ.hom := LinearMap.exact_iff.mp hExactQuot
        _ = ⊥ := by
              have hzero : δ.hom = 0 := congrArg ModuleCat.Hom.hom hδZero
              simpa [hzero] using (LinearMap.range_eq_bot.mpr hzero)
    exact (LinearMap.ker_eq_bot).1 hkerγ
  have hμ_cat : Sker.g ≫ Squot.f = ModuleCat.ofHom μ := by
    -- Proof comment: composing the range restriction with the range inclusion recovers `μ`.
    ext x
    rfl
  have hTorμ :
      (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom μ))).hom =
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Squot.f).hom).comp
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Sker.g).hom) := by
    have hmapComp :
        ((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom μ)) =
          ((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Sker.g) ≫
            ((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map Squot.f) := by
      simpa [hμ_cat] using
        ((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map_comp Sker.g Squot.f)
    simpa using congrArg ModuleCat.Hom.hom hmapComp
  have hTorμ_injective :
      Function.Injective
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom μ))).hom := by
    rw [hTorμ]
    exact hγ_injective.comp hβ_injective
  have hmap_hom :
      (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map
        (ModuleCat.ofHom μ))).hom =
        LinearMap.lsmul A
          ↑(((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K))) a := by
    simpa [μ] using congrArg ModuleCat.Hom.hom hmap
  -- Proof comment: rewrite the injective Tor map as literal scalar multiplication.
  intro x y hxy
  have hxy' :
      (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map
        (ModuleCat.ofHom μ))).hom x =
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom μ))).hom y := by
    rw [hmap_hom]
    simpa [LinearMap.lsmul_apply] using hxy
  exact hTorμ_injective hxy'

/-- Helper for Chap10 Lemma 10 99 16: once `Tor₁` and `Tor₂` vanish for modules annihilated by `(f)`,
multiplication by `f` is injective on the quotient-first owner `Tor₁^A(K, M)` for every module
`K`. -/
lemma tor_one_smul_injective_of_annihilated_vanishing
    (f : A) (hfA : IsRegular f) (hfM : IsSMulRegular M f)
    (hquot : Module.Flat (A ⧸ Ideal.span ({f} : Set A)) (QuotSMulTop f M))
    {K : Type u} [AddCommGroup K] [Module A K] :
    Function.Injective
      fun t :
        ↑(((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A K))) ↦
        f • t := by
  have hkerAnn :
      Ideal.span ({f} : Set A) ≤
        Module.annihilator A (LinearMap.ker (LinearMap.lsmul A K f)) :=
    span_singleton_le_annihilator_ker_lsmul (A := A) f
  have hquotAnn :
      Ideal.span ({f} : Set A) ≤
        Module.annihilator A (K ⧸ LinearMap.range (LinearMap.lsmul A K f)) :=
    span_singleton_le_annihilator_quotient_lsmul (A := A) f
  have hker :
      IsZero
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (LinearMap.ker (LinearMap.lsmul A K f))))) := by
    -- Proof comment: the kernel row term is killed by `(f)`, so degree-`1` annihilated Tor
    -- vanishing applies.
    simpa using
      tor_one_of_f_annihilated_vanishes
        (A := A) (M := M) f hfA hfM hquot hkerAnn
  have hquot₂ :
      IsZero
        (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (K ⧸ LinearMap.range (LinearMap.lsmul A K f))))) := by
    -- Proof comment: the quotient row term is also killed by `(f)`, so the degree-`2` bootstrap
    -- applies.
    simpa using
      tor_two_of_f_annihilated_vanishes
        (A := A) (M := M) f hfA hfM hquot hquotAnn
  -- Proof comment: the two exact rows now force scalar multiplication by `f` on Tor₁ to be
  -- injective.
  exact
    torPublic_one_smul_injective_of_kernel_and_quotient_vanishing
      (A := A) (M := M) (K := K) f hker hquot₂
      (torPublic_map_lsmul_eq_smul (A := A) (M := M) (n := 1) (K := K) f)

/-- Helper for Chap10 Lemma 10 99 16: if the right tensor factor is flat, then the positive-degree
fixed-left source owner `Tor'` vanishes. -/
lemma sourceOwner_tor_succ_isZero_of_flat_right
    (n : ℕ) {P : Type u} [AddCommGroup P] [Module A P]
    {K : Type u} [AddCommGroup K] [Module A K] [Module.Flat A K] :
    IsZero ((((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A P)).obj
      (ModuleCat.of A K))) := by
  let X : ModuleCat A := ModuleCat.of A K
  let Q : CategoryTheory.ProjectiveResolution (ModuleCat.of A P) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A P)
  let C : ChainComplex (ModuleCat A) ℕ :=
    (((tensorRight X).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)
  -- Proof comment: compute `Tor'` on a projective resolution of `P`; flatness of `K` keeps the
  -- tensorized resolution exact in positive degrees.
  refine IsZero.of_iso ?_ (sourceOwner_tor_projectiveResolutionIso (A := A) (M := P) X (n + 1))
  have hExactTensor : C.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' C (n + 2) (n + 1) n (by simp) (by simp)]
    simpa [C] using Module.Flat.rTensor_shortComplex_exact (M := X) _ (Q.exact_succ n)
  exact hExactTensor.isZero_homology

/-- Helper for Chap10 Lemma 10 99 16: if the left public `Tor` variable is flat, then all
positive public `Tor` objects against a fixed module vanish. -/
lemma tor_succ_isZero_of_flat_left
    (n : ℕ) {P : Type u} [AddCommGroup P] [Module A P] [Module.Flat A P] :
    IsZero ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A P)).obj
      (ModuleCat.of A M))) := by
  let X : ModuleCat A := ModuleCat.of A P
  let Q : CategoryTheory.ProjectiveResolution (ModuleCat.of A M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A M)
  let K : ChainComplex (ModuleCat A) ℕ :=
    ((tensorLeft X).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  -- Proof comment: compute public Tor from a projective resolution of the second variable and
  -- use flatness of the left tensor factor to preserve the positive exact window.
  refine IsZero.of_iso ?_ (Q.isoLeftDerivedObj (tensorLeft X) (n + 1))
  have hExactTensor : K.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' K (n + 2) (n + 1) n (by simp) (by simp)]
    simpa [K] using Module.Flat.lTensor_shortComplex_exact (M := X) _ (Q.exact_succ n)
  -- Proof comment: exactness at degree `n + 1` is precisely zero homology in that degree.
  exact hExactTensor.isZero_homology

/-- Helper for Chap10 Lemma 10 99 16: after localizing away from `a`, the module-first public
`Tor` object is zero in the tensor-product base-change spelling when `M[1/a]` is flat. -/
lemma torPublic_tensorLocalizedAway_moduleFirst_isZero_of_flatLocalization
    (a : A) (n : ℕ) {K : Type u} [AddCommGroup K] [Module A K]
    (hflat : Module.Flat (Localization.Away a) (LocalizedModule.Away a M)) :
    IsZero (ModuleCat.of (Localization.Away a)
      (Localization.Away a ⊗[A]
        ↑((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A K))))) := by
  let S : Type u := Localization.Away a
  let f : A →+* S := algebraMap A S
  have hf : f.Flat := by
    -- Proof comment: localization is a flat algebra map, supplying the base-change hypothesis.
    simpa [f, S] using
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away a) (Submonoid.powers a)))
  have hflatTensor : Module.Flat S (S ⊗[A] M) := by
    -- Proof comment: transfer the assumed flatness from localized modules to the tensor model.
    simpa [S] using
      (Module.Flat.of_linearEquiv
        ((LocalizedModule.equivTensorProduct (Submonoid.powers a) M).symm))
  let extTensorIso (T : Type u) [AddCommGroup T] [Module A T] :
      (ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
          (ModuleCat.of A T) ≅
        ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] T) := by
    let U : Type u :=
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away a))).obj
        (ModuleCat.of (Localization.Away a) (Localization.Away a))) : Type u)
    letI : IsScalarTower A (Localization.Away a) U :=
      { smul_assoc := by
          intro r s x
          rw [Algebra.smul_def, mul_smul]
          rfl }
    let e₁ : U ≃ₗ[Localization.Away a] Localization.Away a :=
      LinearEquiv.refl (Localization.Away a) (Localization.Away a)
    let e₂ : T ≃ₗ[A] T := LinearEquiv.refl A T
    -- Proof comment: the scalar-extension object uses the restricted scalar copy of the
    -- localization as its left tensor factor; this linear equivalence identifies it with the
    -- ordinary tensor-product spelling.
    exact (TensorProduct.AlgebraTensorModule.congr e₁ e₂).toModuleIso
  have hTargetTensor :
      IsZero
        ((((Tor (ModuleCat (Localization.Away a)) (n + 1)).obj
            (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] M))).obj
          (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] K)))) := by
    -- Proof comment: in the localized ring, the first public Tor variable is the flat module
    -- `S ⊗[A] M`, so the flat-left vanishing helper kills the base-changed target.
    exact
      (tor_succ_isZero_of_flat_left
        (A := Localization.Away a) (M := Localization.Away a ⊗[A] K) (n := n)
        (P := Localization.Away a ⊗[A] M))
  have hTargetCanonical :
      IsZero
        ((((Tor (ModuleCat (Localization.Away a)) (n + 1)).obj
            ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
              (ModuleCat.of A M))).obj
          ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
            (ModuleCat.of A K)))) := by
    let eM := extTensorIso M
    let eK := extTensorIso K
    let eFirst :
        ((((Tor (ModuleCat (Localization.Away a)) (n + 1)).obj
            ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
              (ModuleCat.of A M))).obj
          ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
            (ModuleCat.of A K)))) ≅
          ((((Tor (ModuleCat (Localization.Away a)) (n + 1)).obj
            (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] M))).obj
          ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
            (ModuleCat.of A K)))) :=
      ((Tor (ModuleCat (Localization.Away a)) (n + 1)).mapIso eM).app
        ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
          (ModuleCat.of A K))
    let eSecond :
        ((((Tor (ModuleCat (Localization.Away a)) (n + 1)).obj
            (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] M))).obj
          ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
            (ModuleCat.of A K)))) ≅
          ((((Tor (ModuleCat (Localization.Away a)) (n + 1)).obj
            (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] M))).obj
          (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] K)))) := by
      exact
        ((Tor (ModuleCat (Localization.Away a)) (n + 1)).obj
          (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] M))).mapIso eK
    let eTarget := eFirst ≪≫ eSecond
    -- Proof comment: transport the tensor-model vanishing across the two object comparisons.
    exact IsZero.of_iso hTargetTensor eTarget
  have hTarget :
      IsZero
        ((((Tor (ModuleCat S) (n + 1)).obj
            ((ModuleCat.extendScalars f).obj (ModuleCat.of A M))).obj
          ((ModuleCat.extendScalars f).obj (ModuleCat.of A K)))) := by
    -- Proof comment: unfold the local aliases for the scalar-extension objects only once.
    simpa [S, f] using hTargetCanonical
  have hIso : IsIso (torBaseChangeHom f hf (ModuleCat.of A M) (ModuleCat.of A K) (n + 1)) := by
    -- Proof comment: the flat base-change theorem identifies localized Tor with Tor over
    -- `A[1/a]`.
    simpa [f, S] using
      (flat_tor_base_change_map_isIso
        (f := f) (hf := hf) (M := M) (N := K) (i := n + 1))
  have hSource :
      IsZero
        ((ModuleCat.extendScalars f).obj
          ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K)))) := by
    -- Proof comment: transport zero backwards along the base-change isomorphism.
    exact IsZero.of_iso hTarget
      (asIso (torBaseChangeHom f hf (ModuleCat.of A M) (ModuleCat.of A K) (n + 1)))
  have hSourceTensorOwner :
      IsZero
        ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
          ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K)))) := by
    -- Proof comment: use the same canonical spelling of the localization algebra map as the
    -- tensor-product object comparison.
    simpa [S, f] using hSource
  let eSourceTensor :=
    extTensorIso
      ↑((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A K)))
  -- Proof comment: finally replace `extendScalars` by its tensor-product object spelling.
  exact IsZero.of_iso hSourceTensorOwner eSourceTensor.symm

/-- Helper for Chap10 Lemma 10 99 16: zero tensor-product base change implies zero literal
localization away from `a`. -/
lemma isZero_awayLocalizedModule_of_isZero_tensorProduct
    (a : A) {T : Type u} [AddCommGroup T] [Module A T]
    (hT : IsZero (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] T))) :
    IsZero
      (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a T)) := by
  let e :
      ModuleCat.of (Localization.Away a) (LocalizedModule.Away a T) ≅
        ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] T) := by
    simpa [LocalizedModule.Away, Localization.Away] using
      (LocalizedModule.equivTensorProduct (Submonoid.powers a) T).toModuleIso
  -- Proof comment: the canonical localized-module/tensor-product identification transports
  -- zero objects between the two spellings of localization.
  exact IsZero.of_iso hT e

/-- Helper for Chap10 Lemma 10 99 16: a commuting square of linear equivalences induces an equivalence
between the two kernels. -/
theorem kerEquivOfLadderLinearEquivNonempty
    {X₁ X₂ Y₁ Y₂ : Type u}
    [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂] [Module A X₂]
    [AddCommGroup Y₁] [Module A Y₁] [AddCommGroup Y₂] [Module A Y₂]
    {u : X₁ →ₗ[A] X₂} {v : Y₁ →ₗ[A] Y₂}
    (e₁ : X₁ ≃ₗ[A] Y₁) (e₂ : X₂ ≃ₗ[A] Y₂)
    (h : v.comp e₁.toLinearMap = e₂.toLinearMap.comp u) :
    Nonempty (LinearMap.ker u ≃ₗ[A] LinearMap.ker v) := by
  let f : LinearMap.ker u →ₗ[A] LinearMap.ker v :=
    { toFun := fun x ↦ ⟨e₁ x, by
        have hx := LinearMap.congr_fun h x.1
        simpa [LinearMap.comp_apply, x.2] using hx⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  -- Proof comment: the square sends kernel elements to kernel elements, and the inverse square
  -- gives surjectivity.
  refine ⟨LinearEquiv.ofBijective f ?_⟩
  constructor
  · intro x y hxy
    ext
    exact e₁.injective (congrArg Subtype.val hxy)
  · intro y
    refine ⟨⟨e₁.symm y, ?_⟩, ?_⟩
    · have hy := LinearMap.congr_fun h (e₁.symm y)
      apply e₂.injective
      simpa [LinearMap.comp_apply, y.2] using hy.symm
    · ext
      simp [f]

/-- Helper for Chap10 Lemma 10 99 16: choose the kernel equivalence induced by a commuting square of
linear equivalences. -/
noncomputable abbrev kerEquivOfLadderLinearEquiv
    {X₁ X₂ Y₁ Y₂ : Type u}
    [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂] [Module A X₂]
    [AddCommGroup Y₁] [Module A Y₁] [AddCommGroup Y₂] [Module A Y₂]
    {u : X₁ →ₗ[A] X₂} {v : Y₁ →ₗ[A] Y₂}
    (e₁ : X₁ ≃ₗ[A] Y₁) (e₂ : X₂ ≃ₗ[A] Y₂)
    (h : v.comp e₁.toLinearMap = e₂.toLinearMap.comp u) :
    LinearMap.ker u ≃ₗ[A] LinearMap.ker v :=
  Classical.choice (kerEquivOfLadderLinearEquivNonempty
    (A := A) (e₁ := e₁) (e₂ := e₂) h)

/-- Helper for Chap10 Lemma 10 99 16: at an arbitrary quotient `A / J`, the fixed-left source owner
`Tor'₁^A(M, A / J)` is identified with the kernel of `J ⊗[A] M → M`. -/
theorem sourceOwner_torOneQuotientByIdealEquivKerNonempty
    (J : Ideal A) :
    Nonempty
      ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A (A ⧸ J))) ≃ₗ[A]
        LinearMap.ker
          (TensorProduct.lift ((LinearMap.lsmul A M).comp J.subtype))) := by
  let μ : J ⊗[A] M →ₗ[A] M :=
    TensorProduct.lift ((LinearMap.lsmul A M).comp J.subtype)
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk J.subtype J.mkQ (by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem.2 x.2)
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa using (LinearMap.exact_subtype_mkQ J)
    · exact (ModuleCat.mono_iff_injective _).2 J.injective_subtype
    · exact (ModuleCat.epi_iff_surjective _).2 J.mkQ_surjective
  obtain ⟨δ, hFive⟩ :=
    source_owner_tor_one_tensor_exact_of_shortExact (A := A) (M := M) hS
  let β :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₂) ⟶
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₃) :=
    (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)
  let u :
      ((tensorLeft (ModuleCat.of A M)).obj S.X₁) ⟶
        ((tensorLeft (ModuleCat.of A M)).obj S.X₂) :=
    ((tensorLeft (ModuleCat.of A M)).map S.f)
  have hβ_zero : β = 0 := by
    -- Proof comment: the middle source-owner term is `Tor'₁(M, A)`, hence zero.
    simpa [β, S] using
      (source_owner_tor_one_unit_isZero (A := A) (M := M)).eq_of_src β 0
  have hExactTor :
      Function.Exact β.hom δ.hom := by
    simpa [β, S, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)
          δ
          ((tensorLeft (ModuleCat.of A M)).map S.f)
          ((tensorLeft (ModuleCat.of A M)).map S.g)).sc hFive.toIsComplex 1)).1
        (hFive.exact 1)
  have hExactTensor :
      Function.Exact δ.hom u.hom := by
    simpa [u, S, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)
          δ
          ((tensorLeft (ModuleCat.of A M)).map S.f)
          ((tensorLeft (ModuleCat.of A M)).map S.g)).sc hFive.toIsComplex 2)).1
        (hFive.exact 2)
  have hδ_injective : Function.Injective δ.hom := by
    have hkerδ : LinearMap.ker δ.hom = ⊥ := by
      calc
        LinearMap.ker δ.hom = LinearMap.range β.hom := LinearMap.exact_iff.mp hExactTor
        _ = ⊥ := by
          have hβhom : β.hom = 0 := congrArg ModuleCat.Hom.hom hβ_zero
          simpa [hβhom] using (LinearMap.range_eq_bot.mpr hβhom)
    exact (LinearMap.ker_eq_bot).1 hkerδ
  have hker :
      IsLimit
        (KernelFork.ofι δ
          (ModuleCat.hom_ext hExactTensor.linearMap_comp_eq_zero)) :=
    ModuleCat.isLimitKernelFork δ u hExactTensor hδ_injective
  have hu : u.hom = J.subtype.lTensor M := by
    -- Proof comment: the tensor map in the short exact row is tensoring the ideal inclusion.
    dsimp [u, S]
    rw [ModuleCat.hom_whiskerLeft]
    rfl
  have hμ :
      μ.comp (TensorProduct.comm A M J).toLinearMap =
        (TensorProduct.rid A M).toLinearMap.comp u.hom := by
    have hcommLid :
        (TensorProduct.lid A M).toLinearMap.comp (TensorProduct.comm A M A).toLinearMap =
          (TensorProduct.rid A M).toLinearMap := by
      exact congrArg LinearEquiv.toLinearMap TensorProduct.comm_trans_lid
    rw [hu]
    dsimp [μ]
    rw [← LinearMap.lid_comp_rTensor]
    change
      (TensorProduct.lid A M).toLinearMap.comp
          ((J.subtype.rTensor M).comp (TensorProduct.comm A M J).toLinearMap) =
        (TensorProduct.rid A M).toLinearMap.comp (J.subtype.lTensor M)
    rw [LinearMap.rTensor_comp_comm]
    change
      (TensorProduct.lid A M).toLinearMap.comp
          ((TensorProduct.comm A M A).toLinearMap.comp (J.subtype.lTensor M)) =
        (TensorProduct.rid A M).toLinearMap.comp (J.subtype.lTensor M)
    rw [← LinearMap.comp_assoc, hcommLid]
  let eSource :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A (A ⧸ J))) ≃ₗ[A]
        LinearMap.ker u.hom :=
    (((limit.isoLimitCone ⟨_, hker⟩).symm ≪≫ ModuleCat.kernelIsoKer u).toLinearEquiv)
  let eKer :
      LinearMap.ker u.hom ≃ₗ[A] LinearMap.ker μ :=
    kerEquivOfLadderLinearEquiv (A := A)
      (e₁ := TensorProduct.comm A M J) (e₂ := TensorProduct.rid A M) hμ
  -- Proof comment: both constructions compute the same kernel attached to
  -- `0 → J → A → A / J → 0`.
  refine ⟨?_⟩
  exact eSource.trans eKer

/-- Helper for Chap10 Lemma 10 99 16: choose the fixed-left source-owner quotient-kernel comparison. -/
noncomputable abbrev sourceOwner_torOneQuotientByIdealEquivKer
    (J : Ideal A) :
    (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A (A ⧸ J))) ≃ₗ[A]
      LinearMap.ker
        (TensorProduct.lift ((LinearMap.lsmul A M).comp J.subtype)) :=
  Classical.choice
    (sourceOwner_torOneQuotientByIdealEquivKerNonempty (A := A) (M := M) J)

/-- Helper for Chap10 Lemma 10 99 16: quotient-first degree-one Tor vanishing at `A / J` implies the
module-first degree-one Tor vanishing required by the flatness criterion. -/
lemma torOne_quotientPublic_to_modulePublic_isZero
    (J : Ideal A)
    (hJ :
      IsZero
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (A ⧸ J))))) :
    IsZero
      ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ J)))) := by
  have hSource :
      IsZero
        ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (A ⧸ J)))) := by
    let eSource :
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (A ⧸ J)))) ≅
          ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A (A ⧸ J)))) :=
      (tor_one_left_owner_iso (A := A) (M := M)).app (ModuleCat.of A (A ⧸ J))
    -- Proof comment: first move the quotient-first public owner to the fixed-left source owner.
    exact IsZero.of_iso hJ eSource.symm
  let eSource :
      ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ J)))) ≅
        ModuleCat.of A
          (LinearMap.ker
            (TensorProduct.lift ((LinearMap.lsmul A M).comp J.subtype))) :=
    (sourceOwner_torOneQuotientByIdealEquivKer (A := A) (M := M) J).toModuleIso
  let ePublic :
      ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ J)))) ≅
        ModuleCat.of A
          (LinearMap.ker
            (TensorProduct.lift ((LinearMap.lsmul A M).comp J.subtype))) :=
    (tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (R := A) (M := M) J).toModuleIso
  -- Proof comment: both source and public module-first owners compute the same tensor kernel.
  exact IsZero.of_iso hSource (ePublic ≪≫ eSource.symm)

/-- Helper for Chap10 Lemma 10 99 16: for quotient first variables, quotient-first and module-first
degree-one public `Tor` owners are linearly equivalent. -/
noncomputable abbrev torOne_quotientPublicLinearEquiv_modulePublic
    (J : Ideal A) :
    ↑(((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A (A ⧸ J)))) ≃ₗ[A]
      ↑((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ J)))) :=
  ((tor_one_left_owner_iso (A := A) (M := M)).app
      (ModuleCat.of A (A ⧸ J))).toLinearEquiv |>.trans
    ((sourceOwner_torOneQuotientByIdealEquivKer (A := A) (M := M) J).trans
      (tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module
        (R := A) (M := M) J).symm)

/-- Helper for Chap10 Lemma 10 99 16: localized zero objects transport across a linear equivalence
before localization away from `a`. -/
lemma isZero_awayLocalizedModule_of_linearEquiv
    (a : A) {T U : Type u} [AddCommGroup T] [Module A T]
    [AddCommGroup U] [Module A U] (e : T ≃ₗ[A] U)
    (hU : IsZero (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a U))) :
    IsZero (ModuleCat.of (Localization.Away a) (LocalizedModule.Away a T)) := by
  -- Proof comment: localizing the linear equivalence gives an isomorphism of localized modules,
  -- so zero of the target localized module pulls back to zero of the source localized module.
  refine IsZero.of_iso hU ?_
  simpa [LocalizedModule.Away, Localization.Away] using
    (IsLocalizedModule.mapEquiv (Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) T)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) U)
      (Localization (Submonoid.powers a)) e).toModuleIso

/-- Helper for Chap10 Lemma 10 99 16: after localizing away from `a`, the quotient-first degree-one
public `Tor` owner for `A / J` vanishes when the localized coefficient module is flat. -/
lemma torPublic_localizedAway_isZero_of_flatLocalization
    (a : A) (J : Ideal A)
    (hflat : Module.Flat (Localization.Away a) (LocalizedModule.Away a M)) :
    IsZero
      (ModuleCat.of (Localization.Away a)
        (LocalizedModule.Away a
          ↑(((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A (A ⧸ J)))))) := by
  let Tmodule : ModuleCat A :=
    ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A (A ⧸ J))))
  have hTensor :
      IsZero
        (ModuleCat.of (Localization.Away a)
          (Localization.Away a ⊗[A] ↑Tmodule)) := by
    -- Proof comment: the earlier base-change helper kills the localized module-first owner in
    -- the tensor-product model.
    simpa [Tmodule] using
      torPublic_tensorLocalizedAway_moduleFirst_isZero_of_flatLocalization
        (A := A) (M := M) a 0 (K := A ⧸ J) hflat
  have hModule :
      IsZero
        (ModuleCat.of (Localization.Away a)
          (LocalizedModule.Away a ↑Tmodule)) := by
    -- Proof comment: replace the tensor-product localization by the literal `LocalizedModule`
    -- spelling used in the final criterion.
    exact isZero_awayLocalizedModule_of_isZero_tensorProduct
      (A := A) a (T := ↑Tmodule) hTensor
  -- Proof comment: for quotient first variables, the quotient-first owner is linearly equivalent
  -- to the module-first owner, and this equivalence persists after localization.
  simpa [Tmodule] using
    isZero_awayLocalizedModule_of_linearEquiv
      (A := A) a
      (e := torOne_quotientPublicLinearEquiv_modulePublic (A := A) (M := M) J)
      hModule
-- Proof sketch: use the long exact sequence of `Tor` for multiplication by `f`, combine the
-- quotient-flatness hypothesis with the nilpotent-ideal criterion from Lemma `10.99.8` for
-- modules annihilated by `f`, and then detect vanishing of `Tor₁` after localizing away from `f`.
/-- Flat part of Chap10 Lemma 10 99 16: if `f` is a nonzerodivisor on `A` and on `M`,
the localization `M[1/f]` is flat over `A[1/f]`, and the quotient `M / fM`, written as
`QuotSMulTop f M`, is flat over `A / fA`, then `M` is flat over `A`. -/
@[stacks 0H7N]
theorem flat_of_regular_of_flat_localizedModule_away_and_flat_quotient (f : A)
    (hfA : IsRegular f) (hfM : IsSMulRegular M f)
    (hlocal : Module.Flat (Localization.Away f) (LocalizedModule.Away f M))
    (hquot : Module.Flat (A ⧸ Ideal.span {f}) (QuotSMulTop f M)) :
    Module.Flat A M := by
  let htfae := flat_tfae_tor_vanishing_criteria (R := A) (M := M)
  -- Proof comment: reduce the flatness theorem to the standard finite-ideal `Tor₁` vanishing
  -- criterion; for each quotient `A ⧸ J`, localized vanishing and scalar injectivity force the
  -- quotient-first owner to vanish.
  refine (htfae.out 0 4).2 ?_
  intro J hJ
  let T : ModuleCat A :=
    (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A (A ⧸ J))))
  have hsmul_injective :
      Function.Injective fun t : ↑T ↦ f • t := by
    -- Proof comment: the exact rows for multiplication by `f` give injectivity on the
    -- quotient-first `Tor₁` owner.
    simpa [T] using
      tor_one_smul_injective_of_annihilated_vanishing
        (A := A) (M := M) f hfA hfM hquot (K := A ⧸ J)
  have hAwayZero :
      IsZero
        (ModuleCat.of (Localization.Away f)
          (LocalizedModule.Away f ↑T)) := by
    -- Proof comment: the quotient-specialized localized helper combines module-first
    -- base-change vanishing with the quotient-owner linear equivalence.
    simpa [T] using
      torPublic_localizedAway_isZero_of_flatLocalization
        (A := A) (M := M) f J hlocal
  have hAwaySubsingleton :
      Subsingleton (LocalizedModule.Away f ↑T) :=
    (ModuleCat.isZero_of_iff_subsingleton
      (R := Localization.Away f)
      (M := LocalizedModule.Away f ↑T)).1 hAwayZero
  letI : Subsingleton (LocalizedModule.Away f ↑T) := hAwaySubsingleton
  have hQuotientFirst : IsZero T := by
    -- Proof comment: localization kills `T`, and multiplication by the inverted element is
    -- injective on `T`; hence `T` was already zero.
    change IsZero (ModuleCat.of A ↑T)
    exact isZero_of_localizedAway_isZero_of_smul_injective
      (A := A) (f := f) hsmul_injective
  -- Proof comment: the standard criterion wants the module-first owner, so transport through the
  -- quotient-only owner bridge.
  simpa [T] using
    torOne_quotientPublic_to_modulePublic_isZero (A := A) (M := M) J hQuotientFirst

-- Proof sketch: first obtain flatness from the previous criterion, then use the faithful-flatness
-- criterion via exactness reflection or nontriviality reflection, applying the same localization
-- and quotient argument with “flat” replaced by “faithfully flat”.
/-- Chap10 Lemma 10 99 16 (faithfully flat): under the same regularity hypotheses, if
`M[1/f]` is faithfully flat over `A[1/f]` and the quotient `M / fM`, written as
`QuotSMulTop f M`, is faithfully flat over `A / fA`, then `M` is faithfully flat over `A`. -/
@[stacks 0H7N]
theorem faithfullyFlat_of_regular_of_faithfullyFlat_localizedModule_away_and_faithfullyFlat_quotient
    (f : A) (hfA : IsRegular f) (hfM : IsSMulRegular M f)
    (hlocal : Module.FaithfullyFlat (Localization.Away f) (LocalizedModule.Away f M))
    (hquot : Module.FaithfullyFlat (A ⧸ Ideal.span {f}) (QuotSMulTop f M)) :
    Module.FaithfullyFlat A M := by
  -- Route correction: the faithful-flat argument should start from the flat criterion above, then
  -- use `Module.FaithfullyFlat.iff_flat_and_proper_ideal` together with localization of ideals
  -- away from `f` and the quotient criterion modulo `(f)`.
  let _ := hfA
  let _ := hfM
  let _ := hlocal
  let _ := hquot
  let _ := pow_mem_of_away_localized_ideal_eq_top (A := A) f
  have hflat :
      Module.Flat A M :=
    flat_of_regular_of_flat_localizedModule_away_and_flat_quotient
      (A := A) (M := M) f hfA hfM
      (by
        let _ : Module.FaithfullyFlat (Localization.Away f) (LocalizedModule.Away f M) := hlocal
        infer_instance)
      (by
        let _ : Module.FaithfullyFlat (A ⧸ Ideal.span {f}) (QuotSMulTop f M) := hquot
        infer_instance)
  refine (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top A M).2 ⟨hflat, ?_⟩
  intro J hJ
  have hAwaySmul :
      (Ideal.map (algebraMap A (Localization.Away f)) J) •
        (⊤ : Submodule (Localization.Away f) (LocalizedModule.Away f M)) = ⊤ :=
    away_localized_ideal_smul_top_eq_top (A := A) (M := M) f J hJ
  have hAwayTop :
      Ideal.map (algebraMap A (Localization.Away f)) J = ⊤ :=
    (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top
      (Localization.Away f) (LocalizedModule.Away f M)).1 hlocal |>.2 _ hAwaySmul
  obtain ⟨n, hn⟩ :=
    pow_mem_of_away_localized_ideal_eq_top (A := A) f J hAwayTop
  let I0 : Ideal A := Ideal.span ({f} : Set A)
  let Abar : Type u := A ⧸ I0
  have hQuotSmul :
      (Ideal.map (algebraMap A Abar) J) •
        (⊤ : Submodule Abar (QuotSMulTop f M)) = ⊤ :=
    by
      simpa [I0] using quotient_ideal_smul_top_eq_top (A := A) (M := M) f J hJ
  have hQuotTop :
      Ideal.map (algebraMap A Abar) J = ⊤ :=
    (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top Abar (QuotSMulTop f M)).1 hquot
      |>.2 _ hQuotSmul
  have hOneMem :
      (1 : Abar) ∈ Ideal.map (algebraMap A Abar) J := by
    simpa [Ideal.eq_top_iff_one] using hQuotTop
  have hOneMem' : (1 : Abar) ∈ Ideal.map (Ideal.Quotient.mk I0) J := by
    simpa [Ideal.Quotient.algebraMap_eq, I0] using hOneMem
  rcases (Ideal.mem_map_iff_of_surjective
      (f := Ideal.Quotient.mk I0) (hf := Ideal.Quotient.mk_surjective)).mp hOneMem'
      with ⟨a, haJ, ha1⟩
  have hdiff : 1 - a ∈ I0 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ha1]
    simp
  rcases (Ideal.mem_span_singleton').1 hdiff with ⟨b, hb⟩
  have habf : a + b * f = 1 := by
    calc
      a + b * f = a + (1 - a) := by rw [hb]
      _ = 1 := by abel
  let qJ : A →+* (A ⧸ J) := Ideal.Quotient.mk J
  have hqJa : qJ a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 haJ
  have hqJf_unit : IsUnit (qJ f) := by
    have hmul : qJ b * qJ f = 1 := by
      have hsum : qJ a + qJ b * qJ f = 1 := by
        calc
          qJ a + qJ b * qJ f = qJ (a + b * f) := by simp [qJ]
          _ = 1 := by simpa [habf]
      simpa [hqJa] using hsum
    exact IsUnit.of_mul_eq_one_right (qJ b) hmul
  have hpowzero : qJ f ^ n = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.2 <| by simpa [map_pow] using hn
  have hzero_unit : IsUnit (0 : A ⧸ J) := by
    simpa [hpowzero] using hqJf_unit.pow n
  have honezero : (1 : A ⧸ J) = 0 := by
    exact (isUnit_zero_iff.mp hzero_unit).symm
  exact (Ideal.eq_top_iff_one J).2 <| by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using honezero

end
