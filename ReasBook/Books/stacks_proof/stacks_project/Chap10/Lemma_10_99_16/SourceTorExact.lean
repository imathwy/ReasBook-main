import StacksProject_2024.Chap10.Lemma_10_99_16.TorOwnerBridge

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Pointwise
open scoped TensorProduct

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]

/-- Helper for Lemma 10.99.16: the fixed-left source owner `Tor'` is definitionally the left
derived functor of tensoring in the second variable and evaluating at the fixed module `M`. -/
private theorem source_tor_owner_eq_leftDerived_obj
    (X : ModuleCat A) (n : ℕ) :
    (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj X) =
      ((tensorRight X).leftDerived n).obj (ModuleCat.of A M) := by
  -- Proof comment: this is the definitional expansion of the source-owner orientation.
  rfl

/-- Helper for Lemma 10.99.16: categorical projectivity of `ModuleCat.of A X` implies the usual
module-theoretic projectivity of `X`. -/
private theorem module_projective_of_categorical_projective
    (X : Type u) [AddCommGroup X] [Module A X]
    (hX : Projective (ModuleCat.of A X)) :
    Module.Projective A X := by
  -- Proof comment: translate the categorical lifting property against epimorphisms into the
  -- ordinary module lifting property against surjective linear maps.
  let _ : Small.{u} A := small_self A
  refine Module.Projective.of_lifting_property ?_
  intro P Q _ _ _ _ f g hf
  let _ : Projective (ModuleCat.of A X) := hX
  have hf' : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  refine ⟨(Projective.factorThru (ModuleCat.ofHom g) (ModuleCat.ofHom f)).hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom
    (Projective.factorThru_comp (ModuleCat.ofHom g) (ModuleCat.ofHom f))

/-- Helper for Lemma 10.99.16: exactness is preserved when the middle term is replaced by a
linearly equivalent module and the adjacent maps are conjugated accordingly. -/
private theorem exact_conj_middle
    {X₁ X₂ X₂' X₃ : Type u}
    [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂] [Module A X₂]
    [AddCommGroup X₂'] [Module A X₂'] [AddCommGroup X₃] [Module A X₃]
    {u : X₁ →ₗ[A] X₂} {v : X₂ →ₗ[A] X₃} (e : X₂ ≃ₗ[A] X₂')
    (hExact : Function.Exact u v) :
    Function.Exact (e.toLinearMap.comp u) (v.comp e.symm.toLinearMap) := by
  -- Proof comment: rewrite exactness via kernels and ranges, then transport both sides across
  -- the chosen linear equivalence.
  rw [LinearMap.exact_iff] at hExact
  rw [LinearMap.exact_iff]
  rw [LinearMap.ker_comp, LinearMap.range_comp, Submodule.map_equiv_eq_comap_symm]
  simpa [hExact]

/-- Helper for Lemma 10.99.16: tensoring a short exact row on the left by a projective module
preserves short exactness. This supplies the degreewise exactness input for the fixed-resolution
source-owner long exact sequence. -/
private theorem tensorLeft_map_shortExact_of_projective
    (P : ModuleCat A) [Projective P] {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) :
    (S.map (tensorLeft P)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Proof comment: projective modules are flat, so exactness survives after tensoring on the
    -- left by `P`.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    let _ : Module.Projective A P :=
      module_projective_of_categorical_projective (A := A) P inferInstance
    let _ : Module.Flat A P := Module.Flat.of_projective
    have hExactBase : Function.Exact S.f.hom S.g.hom := by
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
    simpa [ModuleCat.hom_whiskerLeft] using
      (Module.Flat.lTensor_exact P hExactBase)
  · -- Proof comment: flatness also preserves injectivity of the first map.
    exact (ModuleCat.mono_iff_injective _).2 <| by
      let _ : Module.Projective A P :=
        module_projective_of_categorical_projective (A := A) P inferInstance
      let _ : Module.Flat A P := Module.Flat.of_projective
      have hu : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective _).1 hS.mono_f
      simpa [ModuleCat.hom_whiskerLeft] using
        (Module.Flat.lTensor_preserves_injective_linearMap (M := P) S.f.hom hu)
  · -- Proof comment: right exactness of tensoring gives surjectivity of the quotient map.
    exact (ModuleCat.epi_iff_surjective _).2 <| by
      have hv : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective _).1 hS.epi_g
      simpa [ModuleCat.hom_whiskerLeft] using
        (LinearMap.lTensor_surjective P hv)

/-- Helper for Lemma 10.99.16: computing `Tor'ₙ(M, X)` on the fixed projective resolution of `M`
identifies it with the `n`th homology of the tensorized resolution. -/
private noncomputable def source_owner_tor_projective_resolution_iso
    (X : ModuleCat A) (n : ℕ) :
    (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj X) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) n).obj
        (((tensorRight X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of A M)))) := by
  -- Proof comment: the fixed-left source owner is literally the left derived functor of
  -- `tensorRight X`, so the chosen projective resolution of `M` computes it directly.
  erw [source_tor_owner_eq_leftDerived_obj (A := A) (M := M) X n]
  exact
    (CategoryTheory.projectiveResolution (ModuleCat.of A M)).isoLeftDerivedObj
      (tensorRight X) n

/-- Helper for Lemma 10.99.16: the canonical degree-zero comparison
`leftDerived 0 ≅ tensor` is natural for natural transformations between right exact additive
endofunctors of `ModuleCat A`. -/
private theorem projectiveResolution_fromLeftDerivedZero'_nattrans
    {F G : ModuleCat A ⥤ ModuleCat A} [F.Additive] [G.Additive]
    (α : F ⟶ G) {X : ModuleCat A} (P : CategoryTheory.ProjectiveResolution X) :
    P.fromLeftDerivedZero' F ≫ α.app X =
      HomologicalComplex.opcyclesMap
          ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
        P.fromLeftDerivedZero' G := by
  -- Proof comment: cancel the universal opcycles projection and reduce to ordinary naturality on
  -- the augmentation map of the chosen projective resolution.
  rw [← cancel_epi (HomologicalComplex.pOpcycles _ _)]
  have hPrefixF :
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
        P.fromLeftDerivedZero' F =
      F.map (P.π.f 0) := by
    simpa using
      CategoryTheory.ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero' (P := P) (F := F)
  have h₁ :
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
          P.fromLeftDerivedZero' F ≫ α.app X =
        F.map (P.π.f 0) ≫ α.app X := by
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ α.app X) hPrefixF
  have h₂ :
      F.map (P.π.f 0) ≫ α.app X =
        α.app (P.complex.X 0) ≫ G.map (P.π.f 0) := by
    simpa using α.naturality (P.π.f 0)
  have h₃ :
      α.app (P.complex.X 0) ≫ G.map (P.π.f 0) =
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
          HomologicalComplex.opcyclesMap
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
          P.fromLeftDerivedZero' G := by
    have hPrefixG :
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
          P.fromLeftDerivedZero' G =
        G.map (P.π.f 0) := by
      simpa using
        CategoryTheory.ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero' (P := P) (F := G)
    have hOpcycles :
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
            HomologicalComplex.opcyclesMap
              ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 =
          α.app (P.complex.X 0) ≫
            ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 := by
      simpa using
        HomologicalComplex.p_opcyclesMap
          (φ := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex)
          (i := 0)
    have h₃a :
        α.app (P.complex.X 0) ≫ G.map (P.π.f 0) =
          α.app (P.complex.X 0) ≫
            (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
              P.fromLeftDerivedZero' G) := by
      simpa [Category.assoc] using congrArg (fun k ↦ α.app (P.complex.X 0) ≫ k) hPrefixG.symm
    have h₃b :
        α.app (P.complex.X 0) ≫
            (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
              P.fromLeftDerivedZero' G) =
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0 ≫
            HomologicalComplex.opcyclesMap
              ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
            P.fromLeftDerivedZero' G := by
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ P.fromLeftDerivedZero' G) hOpcycles.symm
    exact h₃a.trans h₃b
  exact h₁.trans (h₂.trans h₃)

/-- Helper for Lemma 10.99.16: the canonical degree-zero comparison
`leftDerived 0 ≅ tensor` is natural for natural transformations between right exact additive
endofunctors of `ModuleCat A`. -/
private theorem leftDerivedZeroIsoSelf_hom_nattrans
    {F G : ModuleCat A ⥤ ModuleCat A} [F.Additive] [G.Additive]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (α : F ⟶ G) :
    NatTrans.leftDerived α 0 ≫ G.leftDerivedZeroIsoSelf.hom =
      F.leftDerivedZeroIsoSelf.hom ≫ α := by
  apply NatTrans.ext
  funext X
  have hComp :
      (NatTrans.leftDerived α 0).app X ≫ G.fromLeftDerivedZero.app X =
        F.fromLeftDerivedZero.app X ≫ α.app X := by
    let P : CategoryTheory.ProjectiveResolution X :=
      CategoryTheory.projectiveResolution X
    rw [CategoryTheory.ProjectiveResolution.leftDerived_app_eq α P 0,
      CategoryTheory.ProjectiveResolution.fromLeftDerivedZero_eq P G,
      CategoryTheory.ProjectiveResolution.fromLeftDerivedZero_eq P F]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hIsoHomology :
        (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) 0).map
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) ≫
            (ChainComplex.isoHomologyι₀
              (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom =
          (ChainComplex.isoHomologyι₀
            (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
            HomologicalComplex.opcyclesMap
              ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 := by
      -- Proof comment: replace the degree-zero homology map by the matching opcycles map.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            (ChainComplex.isoHomologyι₀
              (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
                k ≫
                  (ChainComplex.isoHomologyι₀
                    (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom)
          (ChainComplex.isoHomologyι₀_inv_naturality
            (φ := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex))
    calc
      (P.isoLeftDerivedObj F 0).hom ≫
          (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) 0).map
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) ≫
          (ChainComplex.isoHomologyι₀
            (((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
          P.fromLeftDerivedZero' G =
        (P.isoLeftDerivedObj F 0).hom ≫
          (ChainComplex.isoHomologyι₀
            (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
          HomologicalComplex.opcyclesMap
            ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
          P.fromLeftDerivedZero' G := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ (P.isoLeftDerivedObj F 0).hom ≫ k ≫ P.fromLeftDerivedZero' G)
                hIsoHomology
      _ =
        (P.isoLeftDerivedObj F 0).hom ≫
          (ChainComplex.isoHomologyι₀
            (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
          P.fromLeftDerivedZero' F ≫ α.app X := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  (P.isoLeftDerivedObj F 0).hom ≫
                    (ChainComplex.isoHomologyι₀
                      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex))).hom ≫
                    k)
                (projectiveResolution_fromLeftDerivedZero'_nattrans (A := A) (α := α) P).symm
  simpa [Functor.leftDerivedZeroIsoSelf] using hComp

/-- Helper for Lemma 10.99.16: degree `0` of the fixed-left source owner is the literal tensor
product with `M`. -/
private noncomputable def source_owner_degree_zero_tensor_iso
    (X : ModuleCat A) :
    (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).obj X) ≅
      ((tensorLeft (ModuleCat.of A M)).obj X) := by
  -- Proof comment: `Tor'₀` is the degree-zero left derived functor, so it is just the original
  -- tensor functor on the nose.
  erw [source_tor_owner_eq_leftDerived_obj (A := A) (M := M) X 0]
  exact (tensorRight X).leftDerivedZeroIsoSelf.app (ModuleCat.of A M)

/-- Helper for Lemma 10.99.16: degree `1` of the fixed-left source owner is computed by tensoring
the chosen projective resolution of `M` with the second argument and taking first homology. -/
private noncomputable def source_owner_degree_one_projective_resolution_iso
    (X : ModuleCat A) :
    (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj X) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) 1).obj
        (((tensorRight X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of A M)))) := by
  -- Proof comment: the fixed projective resolution of `M` computes `Tor'₁(M, X)` directly.
  erw [source_tor_owner_eq_leftDerived_obj (A := A) (M := M) X 1]
  exact
    (CategoryTheory.projectiveResolution (ModuleCat.of A M)).isoLeftDerivedObj
      (tensorRight X) 1

/-- Helper for Lemma 10.99.16: degree `0` of the fixed-left source owner can be read on the
chosen projective resolution of `M`. -/
private noncomputable def source_owner_degree_zero_projective_resolution_iso
    (X : ModuleCat A) :
    (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).obj X) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) 0).obj
        (((tensorRight X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of A M)))) := by
  -- Proof comment: the same projective resolution computes the degree-zero source endpoint before
  -- the standard comparison identifies it with literal tensor product.
  erw [source_tor_owner_eq_leftDerived_obj (A := A) (M := M) X 0]
  exact
    (CategoryTheory.projectiveResolution (ModuleCat.of A M)).isoLeftDerivedObj
      (tensorRight X) 0

/-- Helper for Lemma 10.99.16: the degree-zero source-owner comparison transports a map in the
second variable to the literal left-tensor map. -/
private theorem source_owner_degree_zero_tensor_map_transport
    {X Y : ModuleCat A} (f : X ⟶ Y) :
    (tensorLeft (ModuleCat.of A M)).map f =
      (source_owner_degree_zero_tensor_iso (A := A) (M := M) X).inv ≫
        (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map f) ≫
        (source_owner_degree_zero_tensor_iso (A := A) (M := M) Y).hom := by
  let eLeft :
      (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).obj X) ≅
        ((tensorLeft (ModuleCat.of A M)).obj X) :=
    source_owner_degree_zero_tensor_iso (A := A) (M := M) X
  let eRight :
      (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).obj Y) ≅
        ((tensorLeft (ModuleCat.of A M)).obj Y) :=
    source_owner_degree_zero_tensor_iso (A := A) (M := M) Y
  have hNat :
      (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map f) ≫ eRight.hom =
        eLeft.hom ≫ (tensorLeft (ModuleCat.of A M)).map f := by
    -- Proof comment: this is just naturality of the degree-zero identification.
    simpa [eLeft, eRight, Tor', Category.assoc] using
      congrArg
        (fun k ↦ k.app (ModuleCat.of A M))
        (leftDerivedZeroIsoSelf_hom_nattrans (A := A)
          (((tensoringRight (ModuleCat A)).map f)))
  calc
    (tensorLeft (ModuleCat.of A M)).map f =
      eLeft.inv ≫ eLeft.hom ≫ (tensorLeft (ModuleCat.of A M)).map f := by
        simp
    _ = eLeft.inv ≫ ((((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map f) ≫ eRight.hom) := by
        rw [hNat]
    _ = eLeft.inv ≫ (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map f) ≫ eRight.hom := by
        simp

/-- Helper for Lemma 10.99.16: a short exact row
`0 → X₁ → X₂ → X₃ → 0` yields the fixed-left source-owner five-term exact row
`Tor'₁(M, X₁) → Tor'₁(M, X₂) → Tor'₁(M, X₃) → M ⊗ X₁ → M ⊗ X₂`. -/
lemma source_owner_tor_one_tensor_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) :
    ∃ δ :
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₃) ⟶
          ((tensorLeft (ModuleCat.of A M)).obj S.X₁),
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f)
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)
        δ
        (((tensorLeft (ModuleCat.of A M)).map S.f))
        (((tensorLeft (ModuleCat.of A M)).map S.g))).Exact := by
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of A M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A M)
  let φ :
      ((tensorRight (S.X₁ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₂ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} A)).map S.f)
      (ComplexShape.down ℕ)).app P.complex)
  let ψ :
      ((tensorRight (S.X₂ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₃ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} A)).map S.g)
      (ComplexShape.down ℕ)).app P.complex)
  have hzero : φ ≫ ψ = 0 := by
    -- Proof comment: tensoring the short exact row degreewise preserves the relation `S.f ≫ S.g = 0`.
    refine HomologicalComplex.Hom.ext ?_
    apply funext
    intro k
    apply ModuleCat.hom_ext
    ext x
    dsimp [φ, ψ]
    rw [← ModuleCat.hom_comp]
    rw [← MonoidalCategory.whiskerLeft_comp, S.zero]
    rw [ModuleCat.hom_whiskerLeft]
    change (LinearMap.lTensor (P.complex.X k) (0 : S.X₁ →ₗ[A] S.X₃)) x =
      (0 : P.complex.X k ⊗[A] S.X₁ →ₗ[A] P.complex.X k ⊗[A] S.X₃) x
    simp
  let T : ShortComplex (ChainComplex (ModuleCat.{u} A) ℕ) := ShortComplex.mk φ ψ hzero
  have hT : T.ShortExact := by
    -- Proof comment: every term of the chosen projective resolution is projective, hence flat, so
    -- left tensor preserves the short exact row degreewise.
    refine HomologicalComplex.shortExact_of_degreewise_shortExact T ?_
    intro k
    simpa [T, φ, ψ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
      ModuleCat.hom_whiskerLeft] using
      tensorLeft_map_shortExact_of_projective (A := A) (P := P.complex.X k) (S := S) hS
  let eSource₁X₁ :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₁) ≅ T.X₁.homology 1 :=
    source_owner_degree_one_projective_resolution_iso (A := A) (M := M) S.X₁
  let eSource₁X₂ :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₂) ≅ T.X₂.homology 1 :=
    source_owner_degree_one_projective_resolution_iso (A := A) (M := M) S.X₂
  let eSource₁X₃ :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₃) ≅ T.X₃.homology 1 :=
    source_owner_degree_one_projective_resolution_iso (A := A) (M := M) S.X₃
  let eTensorX₁ :
      ((tensorLeft (ModuleCat.of A M)).obj S.X₁) ≅ T.X₁.homology 0 :=
    (source_owner_degree_zero_tensor_iso (A := A) (M := M) S.X₁).symm ≪≫
      source_owner_degree_zero_projective_resolution_iso (A := A) (M := M) S.X₁
  let eTensorX₂ :
      ((tensorLeft (ModuleCat.of A M)).obj S.X₂) ≅ T.X₂.homology 0 :=
    (source_owner_degree_zero_tensor_iso (A := A) (M := M) S.X₂).symm ≪≫
      source_owner_degree_zero_projective_resolution_iso (A := A) (M := M) S.X₂
  let eTensorX₃ :
      ((tensorLeft (ModuleCat.of A M)).obj S.X₃) ≅ T.X₃.homology 0 :=
    (source_owner_degree_zero_tensor_iso (A := A) (M := M) S.X₃).symm ≪≫
      source_owner_degree_zero_projective_resolution_iso (A := A) (M := M) S.X₃
  have hSource₁MapF :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f) ≫ eSource₁X₂.hom =
        eSource₁X₁.hom ≫ HomologicalComplex.homologyMap T.f 1 := by
    -- Proof comment: degree-`1` source-owner maps are the homology maps of the tensorized
    -- projective-resolution chain maps.
    have hMap :
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f) =
          eSource₁X₁.hom ≫ HomologicalComplex.homologyMap T.f 1 ≫ eSource₁X₂.inv := by
      simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} A)).map S.f) P 1)
    rw [hMap]
    simp [Category.assoc]
  have hSource₁MapG :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g) ≫ eSource₁X₃.hom =
        eSource₁X₂.hom ≫ HomologicalComplex.homologyMap T.g 1 := by
    -- Proof comment: the same computation identifies the second degree-`1` source-owner map.
    have hMap :
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g) =
          eSource₁X₂.hom ≫ HomologicalComplex.homologyMap T.g 1 ≫ eSource₁X₃.inv := by
      simpa [T, ψ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} A)).map S.g) P 1)
    rw [hMap]
    simp [Category.assoc]
  have hSource₀MapF :
      (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map S.f) ≫
          (source_owner_degree_zero_projective_resolution_iso (A := A) (M := M) S.X₂).hom =
        (source_owner_degree_zero_projective_resolution_iso (A := A) (M := M) S.X₁).hom ≫
          HomologicalComplex.homologyMap T.f 0 := by
    -- Proof comment: degree `0` is computed on the same tensorized projective resolution.
    have hMap :
        (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map S.f) =
          (source_owner_degree_zero_projective_resolution_iso (A := A) (M := M) S.X₁).hom ≫
            HomologicalComplex.homologyMap T.f 0 ≫
            (source_owner_degree_zero_projective_resolution_iso (A := A) (M := M) S.X₂).inv := by
      simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} A)).map S.f) P 0)
    rw [hMap]
    simp [Category.assoc]
  have hSource₀MapG :
      (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map S.g) ≫
          (source_owner_degree_zero_projective_resolution_iso (A := A) (M := M) S.X₃).hom =
        (source_owner_degree_zero_projective_resolution_iso (A := A) (M := M) S.X₂).hom ≫
          HomologicalComplex.homologyMap T.g 0 := by
    -- Proof comment: and likewise for the last degree-zero source-owner arrow.
    have hMap :
        (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map S.g) =
          (source_owner_degree_zero_projective_resolution_iso (A := A) (M := M) S.X₂).hom ≫
            HomologicalComplex.homologyMap T.g 0 ≫
            (source_owner_degree_zero_projective_resolution_iso (A := A) (M := M) S.X₃).inv := by
      simpa [T, ψ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} A)).map S.g) P 0)
    rw [hMap]
    simp [Category.assoc]
  have hTensorMapF :
      ((tensorLeft (ModuleCat.of A M)).map S.f) ≫ eTensorX₂.hom =
        eTensorX₁.hom ≫ HomologicalComplex.homologyMap T.f 0 := by
    -- Proof comment: the degree-zero source-owner comparison converts the derived map into the
    -- literal tensor map.
    have hTransport :
        (tensorLeft (ModuleCat.of A M)).map S.f ≫ eTensorX₂.hom =
          (source_owner_degree_zero_tensor_iso (A := A) (M := M) S.X₁).inv ≫
            (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map S.f) ≫
            (source_owner_degree_zero_projective_resolution_iso (A := A) (M := M) S.X₂).hom := by
      rw [source_owner_degree_zero_tensor_map_transport (A := A) (M := M) S.f]
      simp [eTensorX₂, Category.assoc]
    rw [hTransport, hSource₀MapF]
    simp [eTensorX₁, Category.assoc]
  have hTensorMapG :
      ((tensorLeft (ModuleCat.of A M)).map S.g) ≫ eTensorX₃.hom =
        eTensorX₂.hom ≫ HomologicalComplex.homologyMap T.g 0 := by
    -- Proof comment: the same transport identifies the last tensor arrow with the raw homology
    -- map in degree `0`.
    have hTransport :
        (tensorLeft (ModuleCat.of A M)).map S.g ≫ eTensorX₃.hom =
          (source_owner_degree_zero_tensor_iso (A := A) (M := M) S.X₂).inv ≫
            (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map S.g) ≫
            (source_owner_degree_zero_projective_resolution_iso (A := A) (M := M) S.X₃).hom := by
      rw [source_owner_degree_zero_tensor_map_transport (A := A) (M := M) S.g]
      simp [eTensorX₃, Category.assoc]
    rw [hTransport, hSource₀MapG]
    simp [eTensorX₂, Category.assoc]
  let δSource :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₃) ⟶
        ((tensorLeft (ModuleCat.of A M)).obj S.X₁) :=
    eSource₁X₃.hom ≫ hT.δ 1 0 (by simp) ≫ eTensorX₁.inv
  have hSourceδ :
      δSource ≫ eTensorX₁.hom =
        eSource₁X₃.hom ≫ hT.δ 1 0 (by simp) := by
    -- Proof comment: the connecting map is the raw homology boundary conjugated by the endpoint
    -- identifications.
    simp [δSource, Category.assoc]
  let eSource :
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f)
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)
        δSource
        ((tensorLeft (ModuleCat.of A M)).map S.f)
        ((tensorLeft (ModuleCat.of A M)).map S.g)) ≅
        HomologicalComplex.HomologySequence.composableArrows₅ hT 1 0 (by simp) :=
    ComposableArrows.isoMk₅
      eSource₁X₁
      eSource₁X₂
      eSource₁X₃
      eTensorX₁
      eTensorX₂
      eTensorX₃
      hSource₁MapF
      hSource₁MapG
      hSourceδ
      hTensorMapF
      hTensorMapG
  have hSource :
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f)
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)
        δSource
        ((tensorLeft (ModuleCat.of A M)).map S.f)
        ((tensorLeft (ModuleCat.of A M)).map S.g)).Exact := by
    -- Proof comment: after identifying the chosen row with the raw homology row, exactness is
    -- inherited from the long exact sequence.
    have hRaw :
        (HomologicalComplex.HomologySequence.composableArrows₅ hT 1 0 (by simp)).Exact := by
      simpa using HomologicalComplex.HomologySequence.composableArrows₅_exact hT 1 0 (by simp)
    exact (ComposableArrows.exact_iff_of_iso eSource).2 hRaw
  refine ⟨δSource, ?_⟩
  -- Proof comment: this is the exact `(1,0)` source-owner row read directly from the homology
  -- long exact sequence of the tensorized projective-resolution short exact row.
  exact hSource

/-- Helper for Lemma 10.99.16: a short exact row
`0 → X₁ → X₂ → X₃ → 0` yields the quotient-first public five-term exact row
`Tor₁(X₁, M) → Tor₁(X₂, M) → Tor₁(X₃, M) → X₁ ⊗ M → X₂ ⊗ M`. -/
lemma public_owner_tor_one_tensor_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) :
    ∃ δ :
        ((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj S.X₃) ⟶
          ((tensorRight (ModuleCat.of A M)).obj S.X₁),
      (ComposableArrows.mk₅
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.g))
        δ
        (((tensorRight (ModuleCat.of A M)).map S.f))
        (((tensorRight (ModuleCat.of A M)).map S.g))).Exact := by
  obtain ⟨δSource, hSource⟩ :=
    source_owner_tor_one_tensor_exact_of_shortExact (A := A) (M := M) hS
  let ePublicX₁ := (tor_left_owner_iso (A := A) (M := M) 1).app S.X₁
  let ePublicX₂ := (tor_left_owner_iso (A := A) (M := M) 1).app S.X₂
  let ePublicX₃ := (tor_left_owner_iso (A := A) (M := M) 1).app S.X₃
  let eTensorX₁ :=
    ((BraidedCategory.tensorLeftIsoTensorRight (ModuleCat.of A M)).app S.X₁).symm
  let eTensorX₂ :=
    ((BraidedCategory.tensorLeftIsoTensorRight (ModuleCat.of A M)).app S.X₂).symm
  let eTensorX₃ :=
    ((BraidedCategory.tensorLeftIsoTensorRight (ModuleCat.of A M)).app S.X₃).symm
  have hPublicMapF :
      (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.f)) ≫ ePublicX₂.hom =
        ePublicX₁.hom ≫ (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f) := by
    -- Proof comment: naturality of `tor_left_owner_iso` rewrites the public quotient-first Tor
    -- map into the fixed-left source-owner map.
    simpa using (tor_left_owner_iso (A := A) (M := M) 1).hom.naturality S.f
  have hPublicMapG :
      (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.g)) ≫ ePublicX₃.hom =
        ePublicX₂.hom ≫ (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g) := by
    -- Proof comment: the same owner comparison applies to the second Tor arrow.
    simpa using (tor_left_owner_iso (A := A) (M := M) 1).hom.naturality S.g
  have hTensorMapF :
      ((tensorRight (ModuleCat.of A M)).map S.f) ≫ eTensorX₂.hom =
        eTensorX₁.hom ≫ ((tensorLeft (ModuleCat.of A M)).map S.f) := by
    -- Proof comment: the inverse braiding turns the public right-tensor map back into the
    -- source-owner left-tensor map.
    simpa [eTensorX₁, eTensorX₂] using
      (BraidedCategory.tensorLeftIsoTensorRight (ModuleCat.of A M)).inv.naturality S.f
  have hTensorMapG :
      ((tensorRight (ModuleCat.of A M)).map S.g) ≫ eTensorX₃.hom =
        eTensorX₂.hom ≫ ((tensorLeft (ModuleCat.of A M)).map S.g) := by
    -- Proof comment: and likewise for the last tensor arrow.
    simpa [eTensorX₂, eTensorX₃] using
      (BraidedCategory.tensorLeftIsoTensorRight (ModuleCat.of A M)).inv.naturality S.g
  let δ :
      ((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj S.X₃) ⟶
        ((tensorRight (ModuleCat.of A M)).obj S.X₁) :=
    ePublicX₃.hom ≫ δSource ≫ eTensorX₁.inv
  have hPublicδ :
      δ ≫ eTensorX₁.hom =
        ePublicX₃.hom ≫ δSource := by
    -- Proof comment: the public connecting map is obtained by conjugating the source-owner
    -- boundary map by the owner and braiding isomorphisms.
    simp [δ, Category.assoc]
  let ePublic :
      (ComposableArrows.mk₅
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.g))
        δ
        (((tensorRight (ModuleCat.of A M)).map S.f))
        (((tensorRight (ModuleCat.of A M)).map S.g))) ≅
        (ComposableArrows.mk₅
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)
          δSource
          ((tensorLeft (ModuleCat.of A M)).map S.f)
          ((tensorLeft (ModuleCat.of A M)).map S.g)) :=
    ComposableArrows.isoMk₅
      ePublicX₁
      ePublicX₂
      ePublicX₃
      eTensorX₁
      eTensorX₂
      eTensorX₃
      hPublicMapF
      hPublicMapG
      hPublicδ
      hTensorMapF
      hTensorMapG
  refine ⟨δ, ?_⟩
  -- Proof comment: after transporting both Tor endpoints and tensor endpoints, the public row is
  -- exactly the source-owner five-term row already proved above.
  exact (ComposableArrows.exact_iff_of_iso ePublic).2 hSource

/-- Helper for Lemma 10.99.16: in `ModuleCat`, an exact row with both adjacent arrows zero has
zero middle object. -/
lemma isZero_of_exact_zero_zero
    {X₁ X₂ X₃ : ModuleCat A} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}
    (hExact : Function.Exact f.hom g.hom) (hf : f = 0) (hg : g = 0) :
    IsZero X₂ := by
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk f.hom g.hom (Function.Exact.linearMap_comp_eq_zero hExact)
  have hS : S.Exact := by
    -- Proof comment: repackage the function-level exactness as exactness of a short complex so
    -- that the standard categorical zero-object lemma applies.
    simpa [S] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S := S)).2 hExact
  -- Proof comment: exactness with zero maps on both sides forces the middle object to be zero.
  simpa [S] using hS.isZero_X₂ hf hg

/-- Helper for Lemma 10.99.16: a short exact row
`0 → X₁ → X₂ → X₃ → 0` yields the quotient-first public five-term exact row
`Tor₂(X₁, M) → Tor₂(X₂, M) → Tor₂(X₃, M) → Tor₁(X₁, M) → Tor₁(X₂, M) → Tor₁(X₃, M)`. -/
lemma tor_two_tor_one_five_term_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) :
    ∃ δ :
        ((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).obj S.X₃) ⟶
          ((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj S.X₁),
      (ComposableArrows.mk₅
        (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map S.g))
        δ
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.g))).Exact := by
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of A M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A M)
  let φ :
      ((tensorRight (S.X₁ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₂ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} A)).map S.f)
      (ComplexShape.down ℕ)).app P.complex)
  let ψ :
      ((tensorRight (S.X₂ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₃ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} A)).map S.g)
      (ComplexShape.down ℕ)).app P.complex)
  have hzero : φ ≫ ψ = 0 := by
    -- Proof comment: the tensorized chain maps still compose to zero because `S.f ≫ S.g = 0`.
    refine HomologicalComplex.Hom.ext ?_
    apply funext
    intro k
    apply ModuleCat.hom_ext
    ext x
    dsimp [φ, ψ]
    rw [← ModuleCat.hom_comp]
    rw [← MonoidalCategory.whiskerLeft_comp, S.zero]
    rw [ModuleCat.hom_whiskerLeft]
    change (LinearMap.lTensor (P.complex.X k) (0 : S.X₁ →ₗ[A] S.X₃)) x =
      (0 : P.complex.X k ⊗[A] S.X₁ →ₗ[A] P.complex.X k ⊗[A] S.X₃) x
    simp
  let T : ShortComplex (ChainComplex (ModuleCat.{u} A) ℕ) := ShortComplex.mk φ ψ hzero
  have hT : T.ShortExact := by
    -- Proof comment: degreewise tensoring by the projective resolution terms preserves short
    -- exactness, since projective modules are flat.
    refine HomologicalComplex.shortExact_of_degreewise_shortExact T ?_
    intro k
    simpa [T, φ, ψ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
      ModuleCat.hom_whiskerLeft] using
      tensorLeft_map_shortExact_of_projective (A := A) (P := P.complex.X k) (S := S) hS
  let eSource₂X₁ :
      (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).obj S.X₁) ≅ T.X₁.homology 2 :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₁ 2
  let eSource₂X₂ :
      (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).obj S.X₂) ≅ T.X₂.homology 2 :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₂ 2
  let eSource₂X₃ :
      (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).obj S.X₃) ≅ T.X₃.homology 2 :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₃ 2
  let eSource₁X₁ :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₁) ≅ T.X₁.homology 1 :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₁ 1
  let eSource₁X₂ :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₂) ≅ T.X₂.homology 1 :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₂ 1
  let eSource₁X₃ :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₃) ≅ T.X₃.homology 1 :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₃ 1
  have hSource₂MapF :
      (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).map S.f) ≫ eSource₂X₂.hom =
        eSource₂X₁.hom ≫ HomologicalComplex.homologyMap T.f 2 := by
    -- Proof comment: transport the degree-`2` source-owner map to raw homology on the chosen
    -- tensorized resolution.
    have hMap :
        (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).map S.f) =
          eSource₂X₁.hom ≫ HomologicalComplex.homologyMap T.f 2 ≫ eSource₂X₂.inv := by
      simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} A)).map S.f) P 2)
    rw [hMap]
    simp [Category.assoc]
  have hSource₂MapG :
      (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).map S.g) ≫ eSource₂X₃.hom =
        eSource₂X₂.hom ≫ HomologicalComplex.homologyMap T.g 2 := by
    -- Proof comment: the same transport works for the second degree-`2` source-owner arrow.
    have hMap :
        (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).map S.g) =
          eSource₂X₂.hom ≫ HomologicalComplex.homologyMap T.g 2 ≫ eSource₂X₃.inv := by
      simpa [T, ψ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} A)).map S.g) P 2)
    rw [hMap]
    simp [Category.assoc]
  have hSource₁MapF :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f) ≫ eSource₁X₂.hom =
        eSource₁X₁.hom ≫ HomologicalComplex.homologyMap T.f 1 := by
    -- Proof comment: the degree-`1` source-owner map is the corresponding homology map.
    have hMap :
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f) =
          eSource₁X₁.hom ≫ HomologicalComplex.homologyMap T.f 1 ≫ eSource₁X₂.inv := by
      simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} A)).map S.f) P 1)
    rw [hMap]
    simp [Category.assoc]
  have hSource₁MapG :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g) ≫ eSource₁X₃.hom =
        eSource₁X₂.hom ≫ HomologicalComplex.homologyMap T.g 1 := by
    -- Proof comment: and similarly for the second degree-`1` source-owner arrow.
    have hMap :
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g) =
          eSource₁X₂.hom ≫ HomologicalComplex.homologyMap T.g 1 ≫ eSource₁X₃.inv := by
      simpa [T, ψ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} A)).map S.g) P 1)
    rw [hMap]
    simp [Category.assoc]
  let δSource :
      (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).obj S.X₃) ⟶
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₁) :=
    eSource₂X₃.hom ≫ hT.δ 2 1 (by simp) ≫ eSource₁X₁.inv
  have hSourceδ :
      δSource ≫ eSource₁X₁.hom =
        eSource₂X₃.hom ≫ hT.δ 2 1 (by simp) := by
    -- Proof comment: the connecting map is the raw boundary map conjugated by the endpoint
    -- comparisons.
    simp [δSource, Category.assoc]
  let eSource :
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).map S.f)
        (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).map S.g)
        δSource
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f)
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)) ≅
        HomologicalComplex.HomologySequence.composableArrows₅ hT 2 1 (by simp) :=
    ComposableArrows.isoMk₅
      eSource₂X₁
      eSource₂X₂
      eSource₂X₃
      eSource₁X₁
      eSource₁X₂
      eSource₁X₃
      hSource₂MapF
      hSource₂MapG
      hSourceδ
      hSource₁MapF
      hSource₁MapG
  have hRaw :
      (HomologicalComplex.HomologySequence.composableArrows₅ hT 2 1 (by simp)).Exact := by
    -- Proof comment: this is the `(2,1)` exact window in the homology long exact sequence of `T`.
    simpa using HomologicalComplex.HomologySequence.composableArrows₅_exact hT 2 1 (by simp)
  have hSource :
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).map S.f)
        (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).map S.g)
        δSource
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f)
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)).Exact := by
    -- Proof comment: once the source-owner row is identified with the raw homology row,
    -- exactness transfers immediately.
    exact (ComposableArrows.exact_iff_of_iso eSource).2 hRaw
  let ePublic₂X₁ := (tor_left_owner_iso (A := A) (M := M) 2).app S.X₁
  let ePublic₂X₂ := (tor_left_owner_iso (A := A) (M := M) 2).app S.X₂
  let ePublic₂X₃ := (tor_left_owner_iso (A := A) (M := M) 2).app S.X₃
  let ePublic₁X₁ := (tor_left_owner_iso (A := A) (M := M) 1).app S.X₁
  let ePublic₁X₂ := (tor_left_owner_iso (A := A) (M := M) 1).app S.X₂
  let ePublic₁X₃ := (tor_left_owner_iso (A := A) (M := M) 1).app S.X₃
  have hPublic₂MapF :
      (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map S.f)) ≫ ePublic₂X₂.hom =
        ePublic₂X₁.hom ≫ (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).map S.f) := by
    -- Proof comment: naturality of `tor_left_owner_iso` rewrites the public degree-`2` Tor map
    -- to the source-owner map.
    simpa using (tor_left_owner_iso (A := A) (M := M) 2).hom.naturality S.f
  have hPublic₂MapG :
      (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map S.g)) ≫ ePublic₂X₃.hom =
        ePublic₂X₂.hom ≫ (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).map S.g) := by
    -- Proof comment: the same naturality relation holds for the second degree-`2` arrow.
    simpa using (tor_left_owner_iso (A := A) (M := M) 2).hom.naturality S.g
  have hPublic₁MapF :
      (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.f)) ≫ ePublic₁X₂.hom =
        ePublic₁X₁.hom ≫ (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f) := by
    -- Proof comment: and likewise in degree `1`.
    simpa using (tor_left_owner_iso (A := A) (M := M) 1).hom.naturality S.f
  have hPublic₁MapG :
      (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.g)) ≫ ePublic₁X₃.hom =
        ePublic₁X₂.hom ≫ (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g) := by
    -- Proof comment: this identifies the last public arrow with the source-owner arrow.
    simpa using (tor_left_owner_iso (A := A) (M := M) 1).hom.naturality S.g
  let δ :
      ((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).obj S.X₃) ⟶
        ((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj S.X₁) :=
    ePublic₂X₃.hom ≫ δSource ≫ ePublic₁X₁.inv
  have hPublicδ :
      δ ≫ ePublic₁X₁.hom =
        ePublic₂X₃.hom ≫ δSource := by
    -- Proof comment: the public connecting map is the source-owner connecting map conjugated by
    -- the owner isomorphisms.
    simp [δ, Category.assoc]
  let ePublic :
      (ComposableArrows.mk₅
        (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) 2).flip).obj (ModuleCat.of A M)).map S.g))
        δ
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).map S.g))) ≅
        (ComposableArrows.mk₅
          (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) 2).obj (ModuleCat.of A M)).map S.g)
          δSource
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)) :=
    ComposableArrows.isoMk₅
      ePublic₂X₁
      ePublic₂X₂
      ePublic₂X₃
      ePublic₁X₁
      ePublic₁X₂
      ePublic₁X₃
      hPublic₂MapF
      hPublic₂MapG
      hPublicδ
      hPublic₁MapF
      hPublic₁MapG
  refine ⟨δ, ?_⟩
  -- Proof comment: the public quotient-first row is the conjugate of the source-owner exact row.
  exact (ComposableArrows.exact_iff_of_iso ePublic).2 hSource

/-- Helper for Lemma 10.99.16: the fixed-left source owner `Tor'₁^A(M, A)` vanishes because
tensoring with the unit object `A` is naturally isomorphic to the identity functor. -/
lemma source_owner_tor_one_unit_isZero :
    IsZero ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A A))) := by
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of A M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A M)
  let eTor :=
    source_owner_degree_one_projective_resolution_iso (A := A) (M := M) (ModuleCat.of A A)
  let eComplex :
      (((tensorRight (ModuleCat.of A A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        P.complex) ≅ P.complex := by
    -- Proof comment: the right unitor identifies the tensor-by-`A` complex with the original
    -- projective resolution complex degreewise.
    simpa [tensorRight] using
      (NatIso.mapHomologicalComplex
        (rightUnitorNatIso (ModuleCat A)) (ComplexShape.down ℕ)).app P.complex
  have hExact : P.complex.ExactAt 1 := by
    -- Proof comment: every projective resolution is exact in positive degrees.
    simpa using P.complex_exactAt_succ 0
  have hTensorExact :
      ((((tensorRight (ModuleCat.of A A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        P.complex)).ExactAt 1 := by
    -- Proof comment: exactness transports across the right-unitor complex isomorphism.
    exact hExact.of_iso eComplex.symm
  have hHomology :
      IsZero
        ((HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) 1).obj
          (((tensorRight (ModuleCat.of A A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            P.complex)) :=
    hTensorExact.isZero_homology
  -- Proof comment: the degree-one source owner is computed by this tensorized resolution, so its
  -- vanishing follows from the transported exactness.
  exact IsZero.of_iso hHomology eTor

/-- Helper for Lemma 10.99.16: if the first Tor variable is projective, then every higher
quotient-first Tor owner vanishes against the fixed module `M`. -/
lemma tor_succ_isZero_of_projective_left
    (n : ℕ) {P : Type u} [AddCommGroup P] [Module A P]
    [Projective (ModuleCat.of A P)] :
    IsZero ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A P)).obj
      (ModuleCat.of A M))) := by
  let X : ModuleCat A := ModuleCat.of A P
  letI : Module.Projective A X := by
    simpa [X] using
      module_projective_of_categorical_projective (A := A) P inferInstance
  letI : Module.Flat A X := Module.Flat.of_projective
  let Q : CategoryTheory.ProjectiveResolution (ModuleCat.of A M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A M)
  let K : ChainComplex (ModuleCat A) ℕ :=
    ((tensorLeft X).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  -- Proof comment: compute the public owner from a projective resolution of `M`, tensor the
  -- exact `n + 2 → n + 1 → n` window on the left by the flat module `P`, and read off the
  -- vanishing of the resulting homology object.
  refine IsZero.of_iso ?_ (Q.isoLeftDerivedObj (tensorLeft X) (n + 1))
  have hExactTensor : K.ExactAt (n + 1) := by
    -- Proof comment: projective modules are flat, so tensoring preserves the exact row in the
    -- chosen projective resolution of `M`.
    rw [HomologicalComplex.exactAt_iff' K (n + 2) (n + 1) n (by simp) (by simp)]
    simpa [K] using Module.Flat.lTensor_shortComplex_exact (M := X) _ (Q.exact_succ n)
  -- Proof comment: exactness at degree `n + 1` forces the corresponding homology object to be
  -- zero, which is exactly the higher `Tor` owner.
  exact hExactTensor.isZero_homology

end
