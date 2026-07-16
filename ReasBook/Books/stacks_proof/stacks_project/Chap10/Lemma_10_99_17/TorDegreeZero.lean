import stacks_proof.stacks_project.Chap10.Lemma_10_99_17.TorLongExact

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

section

variable {A : Type u} [CommRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]
variable {r : ℕ} (f : Fin r → A)

local notation "I" => Ideal.span (Set.range f)
local notation "Ā" => A ⧸ I
local notation "M̄" => M ⧸ (I • (⊤ : Submodule A M))
set_option quotPrecheck false in
local notation "TorQ[" n "]" =>
  (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj (ModuleCat.of A Ā))

/-- Helper for Lemma 10.99.17: the canonical degree-zero comparison
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

/-- Helper for Lemma 10.99.17: the canonical degree-zero comparison
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

/-- Helper for Lemma 10.99.17: degree `0` of the fixed-left source owner is the literal tensor
product with `M`. -/
private noncomputable def source_owner_degree_zero_tensor_iso
    (X : ModuleCat A) :
    (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).obj X) ≅
      ((tensorLeft (ModuleCat.of A M)).obj X) := by
  -- Proof comment: `Tor'₀` is the degree-zero left derived functor, so it identifies with the
  -- underlying tensor functor without further work.
  erw [source_tor_owner_eq_leftDerived_obj (A := A) (M := M) X 0]
  exact (tensorRight X).leftDerivedZeroIsoSelf.app (ModuleCat.of A M)

/-- Helper for Lemma 10.99.17: degree `0` of the fixed-left source owner can be computed on the
chosen projective resolution of `M`. -/
private noncomputable def source_owner_degree_zero_projective_resolution_iso
    (X : ModuleCat A) :
    (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).obj X) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) 0).obj
        (((tensorRight X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of A M)))) := by
  -- Proof comment: the same chosen projective resolution computes the degree-zero source owner.
  erw [source_tor_owner_eq_leftDerived_obj (A := A) (M := M) X 0]
  exact
    (CategoryTheory.projectiveResolution (ModuleCat.of A M)).isoLeftDerivedObj
      (tensorRight X) 0

/-- Helper for Lemma 10.99.17: the degree-zero source-owner comparison transports a map in the
second variable to the literal left-tensor map. -/
private theorem source_owner_degree_zero_tensor_map_transport
    {X Y : ModuleCat A} (g : X ⟶ Y) :
    (tensorLeft (ModuleCat.of A M)).map g =
      (source_owner_degree_zero_tensor_iso (A := A) (M := M) X).inv ≫
        (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map g) ≫
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
      (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map g) ≫ eRight.hom =
        eLeft.hom ≫ (tensorLeft (ModuleCat.of A M)).map g := by
    -- Proof comment: this is naturality of the degree-zero derived-to-underived comparison.
    simpa [eLeft, eRight, Tor', Category.assoc] using
      congrArg
        (fun k ↦ k.app (ModuleCat.of A M))
        (leftDerivedZeroIsoSelf_hom_nattrans (A := A)
          (((tensoringRight (ModuleCat A)).map g)))
  calc
    (tensorLeft (ModuleCat.of A M)).map g =
      eLeft.inv ≫ eLeft.hom ≫ (tensorLeft (ModuleCat.of A M)).map g := by
        simp
    _ = eLeft.inv ≫ ((((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map g) ≫ eRight.hom) := by
        rw [hNat]
    _ = eLeft.inv ≫ (((Tor' (ModuleCat A) 0).obj (ModuleCat.of A M)).map g) ≫ eRight.hom := by
        simp

/-- Helper for Lemma 10.99.17: a short exact row
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
    -- Proof comment: each projective term in the chosen resolution is flat, so left tensor
    -- preserves the degreewise short exact rows.
    refine HomologicalComplex.shortExact_of_degreewise_shortExact T ?_
    intro k
    simpa [T, φ, ψ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
      ModuleCat.hom_whiskerLeft] using
      tensorLeft_map_shortExact_of_projective (A := A) (P := P.complex.X k) (S := S) hS
  let eSource₁X₁ :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₁) ≅ T.X₁.homology 1 :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₁ 1
  let eSource₁X₂ :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₂) ≅ T.X₂.homology 1 :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₂ 1
  let eSource₁X₃ :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₃) ≅ T.X₃.homology 1 :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₃ 1
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
    -- literal left-tensor map.
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
    -- Proof comment: the connecting morphism is the raw boundary conjugated by the endpoint
    -- comparisons.
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
  -- Proof comment: this is the exact `(1,0)` source-owner row read off from the tensorized
  -- projective-resolution long exact sequence.
  exact hSource

/-- Helper for Lemma 10.99.17: the fixed-left source owner `Tor'₁^A(M, A)` vanishes because
tensoring with the unit object `A` is naturally isomorphic to the identity functor. -/
lemma source_owner_tor_one_unit_isZero :
    IsZero ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A A))) := by
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of A M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A M)
  let eTor :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) (ModuleCat.of A A) 1
  let eComplex :
      (((tensorRight (ModuleCat.of A A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        P.complex) ≅ P.complex := by
    -- Proof comment: tensoring by the unit object `A` is the identity on the chosen resolution.
    simpa [tensorRight] using
      (NatIso.mapHomologicalComplex
        (rightUnitorNatIso (ModuleCat A)) (ComplexShape.down ℕ)).app P.complex
  have hExact : P.complex.ExactAt 1 := by
    -- Proof comment: projective resolutions are exact in positive degrees.
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
  -- Proof comment: the degree-one source owner is computed by this tensorized resolution.
  exact IsZero.of_iso hHomology eTor

end
