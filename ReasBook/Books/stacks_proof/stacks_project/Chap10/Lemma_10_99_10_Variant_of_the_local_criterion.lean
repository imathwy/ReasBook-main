import StacksProject_2024.Chap10.Lemma_10_99_7_Local_criterion_for_flatness
import StacksProject_2024.Chap10.Lemma_10_99_8
import StacksProject_2024.Chap10.Lemma_10_72_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory IsLocalRing
open scoped TensorProduct Pointwise

universe u v

noncomputable section

section

variable {R : Type u} {S : Type v} {M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/- Domain-style sampling for the variant local criterion for flatness:
- primary domain: flatness of a finite module over a local homomorphism of Noetherian local rings,
  detected from quotient flatness and a degree-`1` `Tor` vanishing hypothesis;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `Tor₁[R](M, N)`,
  `flatness_and_tor_vanishing_along_ideal_powers`,
  `flat_of_residueField_tor_one_vanishing`;
- best owner abstraction: the public conclusion is the canonical owner `Module.Flat`, while the
  homological inputs and outputs should stay in the chapter owner notation `Tor₁`;
- bridge/view: the only nontrivial bridge is converting the given module-first quotient `Tor₁`
  hypothesis to the quotient-first owner used by Lemma `10.99.8`.
-/

-- Proof sketch: convert the given module-first quotient `Tor₁` vanishing into the fixed-left
-- source owner at `R / I`, compare that source owner with the canonical tensor kernel from
-- Remark `10.75.9`, and then feed the resulting quotient-first vanishing into Lemma `10.99.8`.
-- The output residue-field vanishing is exactly the hypothesis needed by Lemma `10.99.7`.
/-- Helper for Lemma 10.99.10: `tor_flip_iso` identifies the quotient-first public owner
`Tor₁^R(R / I, M)` with the fixed-left source owner `Tor'₁^R(M, R / I)`. -/
noncomputable abbrev tor_one_quotient_source_owner_iso
    (I : Ideal R) :
    (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M)) ≅
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
        (ModuleCat.of R (R ⧸ I))) :=
  (((tor_flip_iso (ModuleCat R) 1).app (ModuleCat.of R (R ⧸ I))).app (ModuleCat.of R M))

/-- Helper for Lemma 10.99.10: fixing the right Tor variable gives the canonical comparison
between the public owner and the fixed-left source owner. -/
private noncomputable def tor_one_left_owner_iso
    (M' : ModuleCat R) :
    (((Tor (ModuleCat R) 1).flip).obj M') ≅ ((Tor' (ModuleCat R) 1).obj M') where
  hom :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat R) 1).hom.app X).app M')
      naturality := by
        intro X Y f
        -- Proof comment: evaluating `tor_flip_iso` at the fixed right variable preserves
        -- naturality in the left variable.
        simpa using congrArg (fun α ↦ α.app M') ((tor_flip_iso (ModuleCat R) 1).hom.naturality f) }
  inv :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat R) 1).inv.app X).app M')
      naturality := by
        intro X Y f
        -- Proof comment: the inverse comparison is natural for the same reason.
        simpa using congrArg (fun α ↦ α.app M') ((tor_flip_iso (ModuleCat R) 1).inv.naturality f) }
  hom_inv_id := by
    ext X x
    -- Proof comment: the componentwise inverse law is inherited from `tor_flip_iso`.
    have h := congrArg (fun α ↦ α.app M') ((tor_flip_iso (ModuleCat R) 1).hom_inv_id_app X)
    simpa using congrArg (fun f ↦ f x) (congrArg ModuleCat.Hom.hom h)
  inv_hom_id := by
    ext X x
    -- Proof comment: and likewise for the other inverse law.
    have h := congrArg (fun α ↦ α.app M') ((tor_flip_iso (ModuleCat R) 1).inv_hom_id_app X)
    simpa using congrArg (fun f ↦ f x) (congrArg ModuleCat.Hom.hom h)

/-- Helper for Lemma 10.99.10: a commuting square of linear equivalences induces a linear
equivalence on kernels. -/
private theorem ker_equiv_of_ladder_linear_equiv_nonempty
    {X₁ X₂ Y₁ Y₂ : Type u}
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂]
    {u : X₁ →ₗ[R] X₂} {v : Y₁ →ₗ[R] Y₂}
    (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂)
    (h : v.comp e₁.toLinearMap = e₂.toLinearMap.comp u) :
    Nonempty (LinearMap.ker u ≃ₗ[R] LinearMap.ker v) := by
  let f : LinearMap.ker u →ₗ[R] LinearMap.ker v :=
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

/-- Helper for Lemma 10.99.10: extract the kernel equivalence from a commuting square of linear
equivalences. -/
private noncomputable abbrev ker_equiv_of_ladder_linear_equiv
    {X₁ X₂ Y₁ Y₂ : Type u}
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂]
    {u : X₁ →ₗ[R] X₂} {v : Y₁ →ₗ[R] Y₂}
    (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂)
    (h : v.comp e₁.toLinearMap = e₂.toLinearMap.comp u) :
    LinearMap.ker u ≃ₗ[R] LinearMap.ker v :=
  Classical.choice (ker_equiv_of_ladder_linear_equiv_nonempty
    (R := R) (e₁ := e₁) (e₂ := e₂) h)

/-- Helper for Lemma 10.99.10: the fixed-left source owner `X ↦ Tor'ₙ(M, X)` is the `n`th left
derived functor of `tensorRight X` evaluated at the fixed module `M`. -/
private theorem source_tor_owner_eq_leftDerived_obj
    (X : ModuleCat R) (n : ℕ) :
    (((Tor' (ModuleCat R) n).obj (ModuleCat.of R M)).obj X) =
      ((tensorRight X).leftDerived n).obj (ModuleCat.of R M) := by
  -- Proof comment: this is the definitional expansion of `Tor'` in the source-owner orientation.
  rfl

/-- Helper for Lemma 10.99.10: categorical projectivity of `ModuleCat.of R X` implies the usual
module-theoretic projectivity of `X`. -/
private theorem module_projective_of_categorical_projective
    (X : Type u) [AddCommGroup X] [Module R X]
    (hX : Projective (ModuleCat.of R X)) :
    Module.Projective R X := by
  -- Proof comment: translate the categorical lifting property against epimorphisms into the
  -- standard linear lifting property against surjective maps.
  let _ : Small.{u} R := small_self R
  refine Module.Projective.of_lifting_property ?_
  intro P Q _ _ _ _ f g hf
  let _ : Projective (ModuleCat.of R X) := hX
  have hf' : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  refine ⟨(Projective.factorThru (ModuleCat.ofHom g) (ModuleCat.ofHom f)).hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom
    (Projective.factorThru_comp (ModuleCat.ofHom g) (ModuleCat.ofHom f))

/-- Helper for Lemma 10.99.10: the projective-resolution model of `fromLeftDerivedZero'` is
natural in the functor variable. -/
private theorem projectiveResolution_fromLeftDerivedZero'_nattrans
    {F G : ModuleCat R ⥤ ModuleCat R} [F.Additive] [G.Additive]
    (α : F ⟶ G) {X : ModuleCat R} (P : CategoryTheory.ProjectiveResolution X) :
    P.fromLeftDerivedZero' F ≫ α.app X =
      HomologicalComplex.opcyclesMap
          ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
        P.fromLeftDerivedZero' G := by
  -- Proof comment: cancel the universal opcycles projection and reduce to naturality on the
  -- augmentation map.
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

/-- Helper for Lemma 10.99.10: the degree-zero comparison `leftDerived 0 ≅ tensor` is natural in
the functor variable. -/
private theorem leftDerivedZeroIsoSelf_hom_nattrans
    {F G : ModuleCat R ⥤ ModuleCat R} [F.Additive] [G.Additive]
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
        (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).map
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
          (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).map
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
                (projectiveResolution_fromLeftDerivedZero'_nattrans (R := R) (α := α) P).symm
  simpa [Functor.leftDerivedZeroIsoSelf] using hComp

/-- Helper for Lemma 10.99.10: tensoring a short exact row on the left by a projective module
preserves short exactness. -/
private theorem tensorLeft_map_shortExact_of_projective
    (P : ModuleCat R) [Projective P] {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    (S.map (tensorLeft P)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Proof comment: projective modules are flat, so exactness survives after tensoring on the
    -- left by `P`.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    let _ : Module.Projective R P :=
      module_projective_of_categorical_projective (R := R) P inferInstance
    let _ : Module.Flat R P := Module.Flat.of_projective
    have hExactBase : Function.Exact S.f.hom S.g.hom := by
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
    simpa [ModuleCat.hom_whiskerLeft] using
      (Module.Flat.lTensor_exact P hExactBase)
  · -- Proof comment: flatness also preserves injectivity of the first map.
    exact (ModuleCat.mono_iff_injective _).2 <| by
      let _ : Module.Projective R P :=
        module_projective_of_categorical_projective (R := R) P inferInstance
      let _ : Module.Flat R P := Module.Flat.of_projective
      have hu : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective _).1 hS.mono_f
      simpa [ModuleCat.hom_whiskerLeft] using
        (Module.Flat.lTensor_preserves_injective_linearMap (M := P) S.f.hom hu)
  · -- Proof comment: right exactness of tensoring gives surjectivity of the quotient map.
    exact (ModuleCat.epi_iff_surjective _).2 <| by
      have hv : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective _).1 hS.epi_g
      simpa [ModuleCat.hom_whiskerLeft] using
        (LinearMap.lTensor_surjective P hv)

/-- Helper for Lemma 10.99.10: degree `0` of the fixed-left source owner is the literal left
tensor product with `M`. -/
private noncomputable def source_owner_degree_zero_tensor_iso
    (X : ModuleCat R) :
    (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).obj X) ≅
      ((tensorLeft (ModuleCat.of R M)).obj X) := by
  -- Proof comment: `Tor'₀` is the original tensor functor.
  simpa [source_tor_owner_eq_leftDerived_obj (R := R) (M := M) X 0] using
    (tensorRight X).leftDerivedZeroIsoSelf.app (ModuleCat.of R M)

/-- Helper for Lemma 10.99.10: degree `1` of the fixed-left source owner is computed by tensoring
the chosen projective resolution of `M` with the second variable. -/
private noncomputable def source_owner_degree_one_projective_resolution_iso
    (X : ModuleCat R) :
    (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj X) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).obj
        (((tensorRight X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of R M)))) := by
  -- Proof comment: the fixed projective resolution of `M` computes `Tor'₁(M, X)` directly.
  simpa [source_tor_owner_eq_leftDerived_obj (R := R) (M := M) X 1] using
    (CategoryTheory.projectiveResolution (ModuleCat.of R M)).isoLeftDerivedObj
      (tensorRight X) 1

/-- Helper for Lemma 10.99.10: degree `0` of the fixed-left source owner can also be read on the
chosen projective resolution of `M`. -/
private noncomputable def source_owner_degree_zero_projective_resolution_iso
    (X : ModuleCat R) :
    (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).obj X) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).obj
        (((tensorRight X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of R M)))) := by
  -- Proof comment: the same fixed projective resolution computes the degree-zero source endpoint.
  simpa [source_tor_owner_eq_leftDerived_obj (R := R) (M := M) X 0] using
    (CategoryTheory.projectiveResolution (ModuleCat.of R M)).isoLeftDerivedObj
      (tensorRight X) 0

/-- Helper for Lemma 10.99.10: the degree-zero source-owner comparison transports a morphism in
the second variable to the literal left-tensor map. -/
private theorem source_owner_degree_zero_tensor_map_transport
    {X Y : ModuleCat R} (f : X ⟶ Y) :
    (tensorLeft (ModuleCat.of R M)).map f =
      (source_owner_degree_zero_tensor_iso (R := R) (M := M) X).inv ≫
        (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map f) ≫
        (source_owner_degree_zero_tensor_iso (R := R) (M := M) Y).hom := by
  let eLeft :
      (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).obj X) ≅
        ((tensorLeft (ModuleCat.of R M)).obj X) :=
    source_owner_degree_zero_tensor_iso (R := R) (M := M) X
  let eRight :
      (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).obj Y) ≅
        ((tensorLeft (ModuleCat.of R M)).obj Y) :=
    source_owner_degree_zero_tensor_iso (R := R) (M := M) Y
  have hNat :
      (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map f) ≫ eRight.hom =
        eLeft.hom ≫ (tensorLeft (ModuleCat.of R M)).map f := by
    -- Proof comment: this is naturality of the degree-zero source/tensor comparison.
    simpa [eLeft, eRight, Tor', Category.assoc] using
      congrArg
        (fun k ↦ k.app (ModuleCat.of R M))
        (leftDerivedZeroIsoSelf_hom_nattrans (R := R)
          (((tensoringRight (ModuleCat R)).map f)))
  calc
    (tensorLeft (ModuleCat.of R M)).map f =
      eLeft.inv ≫ eLeft.hom ≫ (tensorLeft (ModuleCat.of R M)).map f := by
        simp
    _ = eLeft.inv ≫ ((((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map f) ≫ eRight.hom) := by
        rw [hNat]
    _ = eLeft.inv ≫ (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map f) ≫ eRight.hom := by
        simp

/-- Helper for Lemma 10.99.10: a short exact row
`0 → X₁ → X₂ → X₃ → 0` yields the fixed-left source-owner five-term exact row
`Tor'₁(M, X₁) → Tor'₁(M, X₂) → Tor'₁(M, X₃) → M ⊗ X₁ → M ⊗ X₂`. -/
private lemma source_owner_tor_one_tensor_exact_of_shortExact
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    ∃ δ :
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₃) ⟶
          ((tensorLeft (ModuleCat.of R M)).obj S.X₁),
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g)
        δ
        (((tensorLeft (ModuleCat.of R M)).map S.f))
        (((tensorLeft (ModuleCat.of R M)).map S.g))).Exact := by
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of R M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of R M)
  let φ :
      ((tensorRight (S.X₁ : ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₂ : ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} R)).map S.f)
      (ComplexShape.down ℕ)).app P.complex)
  let ψ :
      ((tensorRight (S.X₂ : ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₃ : ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} R)).map S.g)
      (ComplexShape.down ℕ)).app P.complex)
  have hzero : φ ≫ ψ = 0 := by
    -- Proof comment: tensoring preserves the relation `S.f ≫ S.g = 0` degreewise.
    refine HomologicalComplex.Hom.ext ?_
    apply funext
    intro k
    apply ModuleCat.hom_ext
    ext x
    dsimp [φ, ψ]
    rw [← ModuleCat.hom_comp]
    rw [← MonoidalCategory.whiskerLeft_comp, S.zero]
    rw [ModuleCat.hom_whiskerLeft]
    change (LinearMap.lTensor (P.complex.X k) (0 : S.X₁ →ₗ[R] S.X₃)) x =
      (0 : P.complex.X k ⊗[R] S.X₁ →ₗ[R] P.complex.X k ⊗[R] S.X₃) x
    simp
  let T : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) := ShortComplex.mk φ ψ hzero
  have hT : T.ShortExact := by
    -- Proof comment: each projective term in the chosen resolution is flat, so left tensor
    -- preserves the short exact row degreewise.
    refine HomologicalComplex.shortExact_of_degreewise_shortExact T ?_
    intro k
    simpa [T, φ, ψ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
      ModuleCat.hom_whiskerLeft] using
      tensorLeft_map_shortExact_of_projective (R := R) (P := P.complex.X k) (S := S) hS
  let eSource₁X₁ :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₁) ≅ T.X₁.homology 1 :=
    source_owner_degree_one_projective_resolution_iso (R := R) (M := M) S.X₁
  let eSource₁X₂ :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₂) ≅ T.X₂.homology 1 :=
    source_owner_degree_one_projective_resolution_iso (R := R) (M := M) S.X₂
  let eSource₁X₃ :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₃) ≅ T.X₃.homology 1 :=
    source_owner_degree_one_projective_resolution_iso (R := R) (M := M) S.X₃
  let eTensorX₁ :
      ((tensorLeft (ModuleCat.of R M)).obj S.X₁) ≅ T.X₁.homology 0 :=
    (source_owner_degree_zero_tensor_iso (R := R) (M := M) S.X₁).symm ≪≫
      source_owner_degree_zero_projective_resolution_iso (R := R) (M := M) S.X₁
  let eTensorX₂ :
      ((tensorLeft (ModuleCat.of R M)).obj S.X₂) ≅ T.X₂.homology 0 :=
    (source_owner_degree_zero_tensor_iso (R := R) (M := M) S.X₂).symm ≪≫
      source_owner_degree_zero_projective_resolution_iso (R := R) (M := M) S.X₂
  let eTensorX₃ :
      ((tensorLeft (ModuleCat.of R M)).obj S.X₃) ≅ T.X₃.homology 0 :=
    (source_owner_degree_zero_tensor_iso (R := R) (M := M) S.X₃).symm ≪≫
      source_owner_degree_zero_projective_resolution_iso (R := R) (M := M) S.X₃
  have hSource₁MapF :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f) ≫ eSource₁X₂.hom =
        eSource₁X₁.hom ≫ HomologicalComplex.homologyMap T.f 1 := by
    -- Proof comment: the degree-`1` source-owner map is the homology map of the tensorized chain
    -- map in degree `1`.
    have hMap :
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f) =
          eSource₁X₁.hom ≫ HomologicalComplex.homologyMap T.f 1 ≫ eSource₁X₂.inv := by
      simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} R)).map S.f) P 1)
    rw [hMap]
    simp [Category.assoc]
  have hSource₁MapG :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g) ≫ eSource₁X₃.hom =
        eSource₁X₂.hom ≫ HomologicalComplex.homologyMap T.g 1 := by
    -- Proof comment: the same identification works for the second source-owner map.
    have hMap :
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g) =
          eSource₁X₂.hom ≫ HomologicalComplex.homologyMap T.g 1 ≫ eSource₁X₃.inv := by
      simpa [T, ψ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} R)).map S.g) P 1)
    rw [hMap]
    simp [Category.assoc]
  have hSource₀MapF :
      (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map S.f) ≫
          (source_owner_degree_zero_projective_resolution_iso
            (R := R) (M := M) S.X₂).hom =
        (source_owner_degree_zero_projective_resolution_iso
          (R := R) (M := M) S.X₁).hom ≫
          HomologicalComplex.homologyMap T.f 0 := by
    -- Proof comment: degree `0` is computed on the same tensorized projective resolution.
    have hMap :
        (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map S.f) =
          (source_owner_degree_zero_projective_resolution_iso
            (R := R) (M := M) S.X₁).hom ≫
            HomologicalComplex.homologyMap T.f 0 ≫
            (source_owner_degree_zero_projective_resolution_iso
              (R := R) (M := M) S.X₂).inv := by
      simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} R)).map S.f) P 0)
    rw [hMap]
    simp [Category.assoc]
  have hSource₀MapG :
      (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map S.g) ≫
          (source_owner_degree_zero_projective_resolution_iso
            (R := R) (M := M) S.X₃).hom =
        (source_owner_degree_zero_projective_resolution_iso
          (R := R) (M := M) S.X₂).hom ≫
          HomologicalComplex.homologyMap T.g 0 := by
    -- Proof comment: and likewise for the last degree-zero source-owner map.
    have hMap :
        (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map S.g) =
          (source_owner_degree_zero_projective_resolution_iso
            (R := R) (M := M) S.X₂).hom ≫
            HomologicalComplex.homologyMap T.g 0 ≫
            (source_owner_degree_zero_projective_resolution_iso
              (R := R) (M := M) S.X₃).inv := by
      simpa [T, ψ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} R)).map S.g) P 0)
    rw [hMap]
    simp [Category.assoc]
  have hTensorMapF :
      ((tensorLeft (ModuleCat.of R M)).map S.f) ≫ eTensorX₂.hom =
        eTensorX₁.hom ≫ HomologicalComplex.homologyMap T.f 0 := by
    -- Proof comment: transport the degree-zero source-owner map to the literal tensor map.
    have hTransport :
        (tensorLeft (ModuleCat.of R M)).map S.f ≫ eTensorX₂.hom =
          (source_owner_degree_zero_tensor_iso (R := R) (M := M) S.X₁).inv ≫
            (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map S.f) ≫
            (source_owner_degree_zero_projective_resolution_iso
              (R := R) (M := M) S.X₂).hom := by
      rw [source_owner_degree_zero_tensor_map_transport (R := R) (M := M) S.f]
      simp [eTensorX₂, Category.assoc]
    rw [hTransport, hSource₀MapF]
    simp [eTensorX₁, Category.assoc]
  have hTensorMapG :
      ((tensorLeft (ModuleCat.of R M)).map S.g) ≫ eTensorX₃.hom =
        eTensorX₂.hom ≫ HomologicalComplex.homologyMap T.g 0 := by
    -- Proof comment: the same transport identifies the final tensor arrow.
    have hTransport :
        (tensorLeft (ModuleCat.of R M)).map S.g ≫ eTensorX₃.hom =
          (source_owner_degree_zero_tensor_iso (R := R) (M := M) S.X₂).inv ≫
            (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).map S.g) ≫
            (source_owner_degree_zero_projective_resolution_iso
              (R := R) (M := M) S.X₃).hom := by
      rw [source_owner_degree_zero_tensor_map_transport (R := R) (M := M) S.g]
      simp [eTensorX₃, Category.assoc]
    rw [hTransport, hSource₀MapG]
    simp [eTensorX₂, Category.assoc]
  let δSource :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₃) ⟶
        ((tensorLeft (ModuleCat.of R M)).obj S.X₁) :=
    eSource₁X₃.hom ≫ hT.δ 1 0 (by simp) ≫ eTensorX₁.inv
  have hSourceδ :
      δSource ≫ eTensorX₁.hom =
        eSource₁X₃.hom ≫ hT.δ 1 0 (by simp) := by
    -- Proof comment: the connecting map is the raw homology boundary conjugated by the endpoint
    -- identifications.
    simp [δSource, Category.assoc]
  let eSource :
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g)
        δSource
        ((tensorLeft (ModuleCat.of R M)).map S.f)
        ((tensorLeft (ModuleCat.of R M)).map S.g)) ≅
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
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g)
        δSource
        ((tensorLeft (ModuleCat.of R M)).map S.f)
        ((tensorLeft (ModuleCat.of R M)).map S.g)).Exact := by
    -- Proof comment: after identifying the chosen row with the raw homology row, exactness is
    -- inherited from the long exact homology sequence.
    have hRaw :
        (HomologicalComplex.HomologySequence.composableArrows₅ hT 1 0 (by simp)).Exact := by
      simpa using HomologicalComplex.HomologySequence.composableArrows₅_exact hT 1 0 (by simp)
    exact (ComposableArrows.exact_iff_of_iso eSource).2 hRaw
  refine ⟨δSource, ?_⟩
  -- Proof comment: this is the exact `(1,0)` source-owner row read from the homology long exact
  -- sequence of the tensorized projective-resolution short exact row.
  exact hSource

/-- Helper for Lemma 10.99.10: the fixed-left source owner `Tor'₁^R(M, R)` vanishes because `R`
is projective over itself. -/
private lemma tor_one_isZero_of_projective_left
    {P : Type u} [AddCommGroup P] [Module R P] [Module.Projective R P] :
    IsZero ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R P)).obj (ModuleCat.of R M))) := by
  let X : ModuleCat R := ModuleCat.of R P
  let _ : Module.Flat R X := Module.Flat.of_projective
  let Q : CategoryTheory.ProjectiveResolution (ModuleCat.of R M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of R M)
  let K : ChainComplex (ModuleCat R) ℕ :=
    ((MonoidalCategory.tensorLeft X).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  -- Proof comment: compute `Tor₁(P, M)` from the chosen projective resolution of `M`, then use
  -- flatness of the projective module `P` to preserve exactness at degree `1`.
  refine IsZero.of_iso ?_ (Q.isoLeftDerivedObj (MonoidalCategory.tensorLeft X) 1)
  have hExactTensor : K.ExactAt 1 := by
    rw [HomologicalComplex.exactAt_iff' K 2 1 0 (by simp) (by simp)]
    simpa [K] using Module.Flat.lTensor_shortComplex_exact (M := X) _ (Q.exact_succ 0)
  exact hExactTensor.isZero_homology

/-- Helper for Lemma 10.99.10: the fixed-left source owner `Tor'₁^R(M, R)` vanishes because `R`
is projective over itself. -/
private lemma source_owner_tor_one_unit_isZero :
    IsZero ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R R))) := by
  have hTorR :
      IsZero ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R R)).obj (ModuleCat.of R M))) := by
    -- Proof comment: the public quotient-first owner vanishes because `R` is projective over
    -- itself in the first Tor variable.
    simpa using tor_one_isZero_of_projective_left (R := R) (M := M) (P := R)
  have hFlip :
      IsZero ((((Tor (ModuleCat R) 1).flip).obj (ModuleCat.of R M)).obj (ModuleCat.of R R)) := by
    -- Proof comment: evaluating the flipped public owner at `R` is definitionally the same term.
    simpa using hTorR
  -- Proof comment: transport the vanishing statement across the owner comparison.
  exact IsZero.of_iso hFlip
    ((tor_one_left_owner_iso (R := R) (M' := ModuleCat.of R M)).app (ModuleCat.of R R)).symm

/-- Helper for Lemma 10.99.10: the fixed-left source owner at `R / I` computes the kernel of the
canonical multiplication map `I ⊗[R] M → M`. -/
theorem source_owner_tor_one_quotient_equiv_ker_ideal_tensor_to_module_nonempty
    (I : Ideal R) :
    Nonempty
      ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R (R ⧸ I))) ≃ₗ[R]
        LinearMap.ker
          (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype))) := by
  -- Route correction: use the source-faithful five-term exact row for `Tor'₁^R(M, -)` on
  -- `0 → I → R → R / I → 0`, then identify the resulting tensor kernel with the canonical map
  -- from Remark `10.75.9`.
  let μ :
      I ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMk I.subtype I.mkQ (by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem.2 x.2)
  have hS : S.ShortExact := by
    -- Proof comment: package the quotient row as a short exact sequence in `ModuleCat`.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [S] using (LinearMap.exact_subtype_mkQ I)
    · exact (ModuleCat.mono_iff_injective _).2 I.injective_subtype
    · exact (ModuleCat.epi_iff_surjective _).2 I.mkQ_surjective
  let δ :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₃) ⟶
        ((tensorLeft (ModuleCat.of R M)).obj S.X₁) :=
    Classical.choose (source_owner_tor_one_tensor_exact_of_shortExact (R := R) (M := M) hS)
  have hFive :
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g)
        δ
        (((tensorLeft (ModuleCat.of R M)).map S.f))
        (((tensorLeft (ModuleCat.of R M)).map S.g))).Exact := by
    -- Proof comment: extract the exact row carried by the chosen connecting morphism.
    simpa [δ] using
      Classical.choose_spec
        (source_owner_tor_one_tensor_exact_of_shortExact (R := R) (M := M) hS)
  let β :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₂) ⟶
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj S.X₃) :=
    (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g)
  let u :
      ((tensorLeft (ModuleCat.of R M)).obj S.X₁) ⟶
        ((tensorLeft (ModuleCat.of R M)).obj S.X₂) :=
    ((tensorLeft (ModuleCat.of R M)).map S.f)
  have hβ_zero : β = 0 := by
    -- Proof comment: the middle source-owner term is `Tor'₁(M, R)`, which vanishes because `R`
    -- is projective over itself.
    simpa [β, S] using
      (source_owner_tor_one_unit_isZero (R := R) (M := M)).eq_of_src β 0
  have hExactTor :
      Function.Exact β.hom δ.hom := by
    -- Proof comment: this is the exactness window at `Tor'₁(M, R / I)`.
    simpa [β, S, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f)
          (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g)
          δ
          ((tensorLeft (ModuleCat.of R M)).map S.f)
          ((tensorLeft (ModuleCat.of R M)).map S.g)).sc hFive.toIsComplex 1)).1
        (hFive.exact 1)
  have hExactTensor :
      Function.Exact δ.hom u.hom := by
    -- Proof comment: this is the exactness window identifying the tensor kernel.
    simpa [u, S, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f)
          (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g)
          δ
          ((tensorLeft (ModuleCat.of R M)).map S.f)
          ((tensorLeft (ModuleCat.of R M)).map S.g)).sc hFive.toIsComplex 2)).1
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
  have hu : u.hom = I.subtype.lTensor M := by
    -- Proof comment: the endpoint tensor map is tensoring the ideal inclusion on the left.
    dsimp [u, S]
    rw [ModuleCat.hom_whiskerLeft]
    rfl
  have hμ :
      μ.comp (TensorProduct.comm R M I).toLinearMap =
        (TensorProduct.rid R M).toLinearMap.comp u.hom := by
    have hcommLid :
        (TensorProduct.lid R M).toLinearMap.comp (TensorProduct.comm R M R).toLinearMap =
          (TensorProduct.rid R M).toLinearMap := by
      exact congrArg LinearEquiv.toLinearMap TensorProduct.comm_trans_lid
    rw [hu]
    dsimp [μ]
    rw [← LinearMap.lid_comp_rTensor]
    change
      (TensorProduct.lid R M).toLinearMap.comp
          ((I.subtype.rTensor M).comp (TensorProduct.comm R M I).toLinearMap) =
        (TensorProduct.rid R M).toLinearMap.comp (I.subtype.lTensor M)
    rw [LinearMap.rTensor_comp_comm]
    change
      (TensorProduct.lid R M).toLinearMap.comp
          ((TensorProduct.comm R M R).toLinearMap.comp (I.subtype.lTensor M)) =
        (TensorProduct.rid R M).toLinearMap.comp (I.subtype.lTensor M)
    rw [← LinearMap.comp_assoc, hcommLid]
  let eSource :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R (R ⧸ I))) ≃ₗ[R]
        LinearMap.ker u.hom :=
    (((limit.isoLimitCone ⟨_, hker⟩).symm ≪≫ ModuleCat.kernelIsoKer u).toLinearEquiv)
  let eKer :
      LinearMap.ker u.hom ≃ₗ[R] LinearMap.ker μ :=
    ker_equiv_of_ladder_linear_equiv (R := R)
      (e₁ := TensorProduct.comm R M I) (e₂ := TensorProduct.rid R M) hμ
  -- Proof comment: the fixed-left source owner and the canonical ideal-tensor kernel compute the
  -- same kernel attached to `0 → I → R → R / I → 0`.
  exact ⟨by simpa using eSource.trans eKer⟩

/-- Helper for Lemma 10.99.10: choose the quotient-specialized source-owner/kernel comparison. -/
noncomputable abbrev source_owner_tor_one_quotient_equiv_ker_ideal_tensor_to_module
    (I : Ideal R) :
    (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R (R ⧸ I))) ≃ₗ[R]
      LinearMap.ker
        (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)) :=
  Classical.choice
    (source_owner_tor_one_quotient_equiv_ker_ideal_tensor_to_module_nonempty
      (R := R) (M := M) I)

/-- Helper for Lemma 10.99.10: vanishing of the module-first quotient `Tor₁^R(M, R / I)` forces
vanishing of the quotient-first owner required by Lemma `10.99.8`. -/
lemma tor_one_quotient_vanishes_of_module_quotient_vanishes
    (I : Ideal R) (hTor : IsZero (Tor₁[R](M, R ⧸ I))) :
    IsZero ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M))) := by
  let μ :
      I ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  let eKernel :=
    tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (R := R) (M := M) I
  have hKerSubsingleton : Subsingleton (LinearMap.ker μ) := by
    -- Proof comment: Remark `10.75.9` rewrites the given public owner as the kernel of the
    -- canonical multiplication map.
    exact
      (eKernel.toEquiv.subsingleton_congr).mp
        ((ModuleCat.isZero_iff_subsingleton).1 hTor)
  let eSource :=
    source_owner_tor_one_quotient_equiv_ker_ideal_tensor_to_module (R := R) (M := M) I
  have hSourceSubsingleton :
      Subsingleton ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
        (ModuleCat.of R (R ⧸ I)))) := by
    -- Proof comment: transport the zero kernel across the quotient-specialized source-owner
    -- comparison.
    exact (eSource.toEquiv.subsingleton_congr).mpr hKerSubsingleton
  have hSource :
      IsZero ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
        (ModuleCat.of R (R ⧸ I)))) := by
    exact (ModuleCat.isZero_iff_subsingleton).2 hSourceSubsingleton
  -- Proof comment: finally return to the quotient-first public owner used in Lemma `10.99.8`.
  exact IsZero.of_iso hSource (tor_one_quotient_source_owner_iso (R := R) (M := M) I)

include S

/-- Helper for Lemma 10.99.10: expose the target-ring parameter in Lemma `10.99.7` so the final
flatness step does not rely on metavariable inference for the ambient local homomorphism. -/
lemma flat_of_residueField_tor_one_vanishing_explicit_target
    (hTor : IsZero (Tor₁[R](ResidueField R, M))) :
    Module.Flat R M := by
  -- Proof comment: this is just Lemma `10.99.7` with the ambient target ring fixed explicitly.
  exact flat_of_residueField_tor_one_vanishing (R := R) (S := S) (M := M) hTor
omit S

include S
/-- Lemma 10.99.10 (Variant of the local criterion): let `R → S` be a local homomorphism of
Noetherian local rings, let `I ≠ R` be an ideal of `R`, and let `M` be a finite `S`-module. If
`Tor₁^R(M, R / I)` vanishes and `M / IM` is flat over `R / I`, then `M` is flat over `R`. -/
@[stacks 00ML]
theorem flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal
    (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : IsZero (Tor₁[R](M, R ⧸ I)))
    (hflat :
      Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Flat R M := by
  -- Route correction: keep the textbook `10.99.8 -> 10.99.7` route and only bridge the owner
  -- orientation of the quotient `Tor₁` hypothesis. The currently exposed API of Lemma `10.99.8`
  -- already packages the residue-field Tor vanishing consequence, so we read off that clause and
  -- then finish with Lemma `10.99.7`.
  have hQuotientFirst :
      IsZero ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R M))) := by
    -- Proof comment: the preceding bridge converts the given module-first quotient vanishing into
    -- the quotient-first owner required by Lemma `10.99.8`.
    exact tor_one_quotient_vanishes_of_module_quotient_vanishes (R := R) (M := M) I hTor
  obtain ⟨_, hAnnTor, _⟩ :=
    flatness_and_tor_vanishing_along_ideal_powers (R := R) (I := I) (M := M) hflat hQuotientFirst
  have hResidueTor :
      IsZero (Tor₁[R](ResidueField R, M)) := by
    -- Proof comment: a proper ideal in a local ring lies in the maximal ideal, so the residue
    -- field is annihilated by `I` itself.
    exact hAnnTor (N := ResidueField R)
      (by
        refine ⟨1, ?_⟩
        simpa [pow_one, module_annihilator_residueField_eq_maximalIdeal (R := R)] using
          (IsLocalRing.le_maximalIdeal (R := R) hI))
  -- Proof comment: conclude by the residue-field version of the local criterion for flatness.
  exact
    flat_of_residueField_tor_one_vanishing_explicit_target
      (R := R) (S := S) (M := M) hResidueTor
omit S

end
