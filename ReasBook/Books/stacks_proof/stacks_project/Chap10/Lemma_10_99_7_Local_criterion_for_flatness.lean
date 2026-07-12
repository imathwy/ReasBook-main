import Mathlib
import StacksProject_2024.Chap10.Lemma_10_39_5
import StacksProject_2024.Chap10.Lemma_10_51_2_Artin_Rees
import StacksProject_2024.Chap10.Lemma_10_59_9
import StacksProject_2024.Chap10.Lemma_10_97_3
import StacksProject_2024.Chap10.Lemma_10_99_6
import StacksProject_2024.Chap10.Remark_10_75_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory IsLocalRing
open scoped TensorProduct Pointwise

universe u v

section

variable {R : Type u} {S : Type v} {M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

/- Domain-style sampling:
- primary domain: the local flatness criterion for a finite module over a local homomorphism of
  local Noetherian rings, expressed through residue-field `Tor₁`-vanishing;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `Module.Flat.iff_lift_lsmul_comp_subtype_injective`,
  `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module`,
  `isZero_tor_one_of_isFiniteLength_of_residueField_vanishing`;
- best owner abstraction: the public owner is `Module.Flat`, while the source-facing homological
  hypothesis should use the chapter owner notation `Tor₁[R](ResidueField R, M)` rather than a raw
  derived-functor term;
- primitive data: the local map `R → S`, the finite `S`-module `M`, and the residue-field
  `Tor₁`-vanishing hypothesis;
- derived API: the flatness conclusion over the base ring `R`.

Source/core/bridge triage:
- `source-facing`: Lemma 10.99.7 itself;
- `core/canonical`: `Module.Flat` together with the canonical `Tor₁` owner from
  `Remark_10_75_9`;
- `bridge/view`: the quotient-by-ideal Tor/kernel comparison and the finite-length propagation of
  Lemma `10.99.6` belong to the proof route, not to the public statement.
-/

-- Proof sketch: by Lemma `10.39.5`, it is enough to prove injectivity of `I ⊗[R] M → M` for every
-- ideal `I` of `R`. Remark `10.75.9` identifies the kernel with `Tor₁^R(M, R / I)`, and Lemma
-- `10.99.6` gives vanishing for ideals of finite colength from the residue-field hypothesis. Use
-- the Artin-Rees argument from the textbook to reduce the general ideal case to finite-colength
-- ideals, then conclude by the faithfully flat maximal-ideal-adic completion from Lemma `10.97.3`.
/-- Helper for Lemma 10.99.7: `tor_flip_iso` moves the quotient-first public owner
`Tor₁^R(R / J, M)` to the flipped source owner that resolves `R / J` first. -/
private noncomputable def tor_one_quotient_flip_owner_iso
    (J : Ideal R) :
    (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ J))).obj (ModuleCat.of R M)) ≅
      (((Functor.flip (Tor' (ModuleCat R) 1)).obj (ModuleCat.of R (R ⧸ J))).obj
        (ModuleCat.of R M)) :=
  (((tor_flip_iso (ModuleCat R) 1).app (ModuleCat.of R (R ⧸ J))).app (ModuleCat.of R M))

/-- Helper for Lemma 10.99.7: `tor_flip_iso` moves the module-first public owner
`Tor₁^R(M, R / J)` to the flipped source owner that resolves `M` first. -/
private noncomputable def tor_one_module_quotient_flip_owner_iso
    (J : Ideal R) :
    (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R (R ⧸ J))) ≅
      (((Functor.flip (Tor' (ModuleCat R) 1)).obj (ModuleCat.of R M)).obj
        (ModuleCat.of R (R ⧸ J))) :=
  (((tor_flip_iso (ModuleCat R) 1).app (ModuleCat.of R M)).app (ModuleCat.of R (R ⧸ J)))

/-- Helper for Lemma 10.99.7: fixing the right Tor variable gives the canonical comparison
between the quotient-first public owner and the fixed-left source owner. -/
private noncomputable def tor_one_left_owner_iso
    (M' : ModuleCat R) :
    (((Tor (ModuleCat R) 1).flip).obj M') ≅ ((Tor' (ModuleCat R) 1).obj M') where
  hom :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat R) 1).hom.app X).app M')
      naturality := by
        intro X Y f
        -- Naturality of `tor_flip_iso` in the first Tor variable becomes naturality of the fixed
        -- right-variable owner after evaluation at `M'`.
        simpa using congrArg (fun α => α.app M') ((tor_flip_iso (ModuleCat R) 1).hom.naturality f) }
  inv :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat R) 1).inv.app X).app M')
      naturality := by
        intro X Y f
        -- The inverse comparison is natural for the same reason.
        simpa using congrArg (fun α => α.app M') ((tor_flip_iso (ModuleCat R) 1).inv.naturality f) }
  hom_inv_id := by
    ext X x
    -- The componentwise inverse law is inherited from `tor_flip_iso` after evaluation at `M'`.
    have h := congrArg (fun α => α.app M') ((tor_flip_iso (ModuleCat R) 1).hom_inv_id_app X)
    simpa using congrArg (fun f => f x) (congrArg ModuleCat.Hom.hom h)
  inv_hom_id := by
    ext X x
    -- The same componentwise argument proves the other inverse law.
    have h := congrArg (fun α => α.app M') ((tor_flip_iso (ModuleCat R) 1).inv_hom_id_app X)
    simpa using congrArg (fun f => f x) (congrArg ModuleCat.Hom.hom h)

/-- Helper for Lemma 10.99.7: the quotient-first public owner `Tor₁^R(R / J, M)` must be
identified with the fixed-left source owner `Tor'₁^R(M, R / J)` before Remark `10.75.9` can be
applied in the source proof. -/
private noncomputable def tor_one_quotient_source_owner_iso
    (J : Ideal R) :
    (((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ J))).obj (ModuleCat.of R M)) ≅
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
        (ModuleCat.of R (R ⧸ J))) := by
  -- Route correction: fix the right Tor variable and evaluate the canonical owner comparison at
  -- the quotient `R / J`.
  simpa using
    (tor_one_left_owner_iso (R := R) (M' := ModuleCat.of R M)).app (ModuleCat.of R (R ⧸ J))

/-- Helper for Lemma 10.99.7: Lemma `10.99.6` already kills the flipped source owner whose fixed
module is the finite-colength quotient `R / J`. -/
private lemma isZero_tor_one_quotient_flip_owner_of_isFiniteLength
    (hTor : IsZero (Tor₁[R](ResidueField R, M))) (J : Ideal R)
    (hJ : IsFiniteLength R (R ⧸ J)) :
    IsZero
      ((((Functor.flip (Tor' (ModuleCat R) 1)).obj (ModuleCat.of R (R ⧸ J))).obj
        (ModuleCat.of R M))) := by
  have hQuotient :
      IsZero (Tor₁[R](R ⧸ J, M)) :=
    isZero_tor_one_of_isFiniteLength_of_residueField_vanishing (R := R) (M := M) hTor hJ
  -- Transport the finite-length vanishing across the pointwise `tor_flip_iso` component.
  exact IsZero.of_iso hQuotient (tor_one_quotient_flip_owner_iso (R := R) (M := M) J).symm

/-- Helper for Lemma 10.99.7: a commuting square of linear equivalences induces a linear
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

/-- Helper for Lemma 10.99.7: a proof-free extractor for the kernel equivalence from a
commutative square of linear equivalences. -/
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

/-- Helper for Lemma 10.99.7: the fixed-left source owner `X ↦ Tor'ₙ(M, X)` is the `n`th left
derived functor of `tensorRight X` evaluated at the fixed module `M`. -/
private theorem source_tor_owner_eq_leftDerived_obj
    (X : ModuleCat R) (n : ℕ) :
    (((Tor' (ModuleCat R) n).obj (ModuleCat.of R M)).obj X) =
      ((tensorRight X).leftDerived n).obj (ModuleCat.of R M) := by
  -- Proof comment: this is the definitional expansion of `Tor'` in the source-owner orientation.
  rfl

/-- Helper for Lemma 10.99.7: categorical projectivity of `ModuleCat.of R X` implies the usual
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

/-- Helper for Lemma 10.99.7: the projective-resolution model of `fromLeftDerivedZero'` is
natural in the functor variable. -/
private theorem projectiveResolution_fromLeftDerivedZero'_nattrans
    {F G : ModuleCat R ⥤ ModuleCat R} [F.Additive] [G.Additive]
    (α : F ⟶ G) {X : ModuleCat R} (P : CategoryTheory.ProjectiveResolution X) :
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

/-- Helper for Lemma 10.99.7: the degree-zero comparison `leftDerived 0 ≅ tensor` is natural in
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

/-- Helper for Lemma 10.99.7: tensoring a short exact row on the left by a projective module
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

/-- Helper for Lemma 10.99.7: degree `0` of the fixed-left source owner is the literal left
tensor product with `M`. -/
private noncomputable def source_owner_degree_zero_tensor_iso
    (X : ModuleCat R) :
    (((Tor' (ModuleCat R) 0).obj (ModuleCat.of R M)).obj X) ≅
      ((tensorLeft (ModuleCat.of R M)).obj X) := by
  -- Proof comment: `Tor'₀` is the original tensor functor.
  simpa [source_tor_owner_eq_leftDerived_obj (R := R) (M := M) X 0] using
    (tensorRight X).leftDerivedZeroIsoSelf.app (ModuleCat.of R M)

/-- Helper for Lemma 10.99.7: degree `1` of the fixed-left source owner is computed by tensoring
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

/-- Helper for Lemma 10.99.7: degree `0` of the fixed-left source owner can also be read on the
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

/-- Helper for Lemma 10.99.7: the degree-zero source-owner comparison transports a morphism in
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

/-- Helper for Lemma 10.99.7: a short exact row
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

/-- Helper for Lemma 10.99.7: specializing `0 → J → R → R / J → 0` to the public fixed-left
exactness theorem gives the exact source-owner window needed for the quotient bridge. -/
private lemma source_owner_ideal_quotient_exact
    (J : Ideal R) :
    Function.Exact
      ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map (ModuleCat.ofHom J.subtype)).hom)
      ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map (ModuleCat.ofHom J.mkQ)).hom) := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMk J.subtype J.mkQ (by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem.2 x.2)
  have hS : S.ShortExact := by
    -- Proof comment: package the quotient row as a short exact sequence in `ModuleCat`.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [S] using (LinearMap.exact_subtype_mkQ J)
    · exact (ModuleCat.mono_iff_injective _).2 J.injective_subtype
    · exact (ModuleCat.epi_iff_surjective _).2 J.mkQ_surjective
  -- Proof comment: the imported source-owner exactness theorem now applies directly.
  simpa [S] using
    (ModuleCat.source_owner_tor_one_exact_of_shortExact (R := R) (ModuleCat.of R M) hS)

/-- Helper for Lemma 10.99.7: if the first Tor variable is projective, then `Tor₁` against the
fixed module `M` vanishes. -/
private lemma tor_one_isZero_of_projective_left
    {P : Type u} [AddCommGroup P] [Module R P] [Module.Projective R P] :
    IsZero ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R P)).obj (ModuleCat.of R M))) := by
  let X : ModuleCat R := ModuleCat.of R P
  letI : Module.Flat R X := Module.Flat.of_projective
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

/-- Helper for Lemma 10.99.7: the fixed-left source owner `Tor'₁^R(M, R)` vanishes because `R`
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

/-- Helper for Lemma 10.99.7: the fixed-left source owner `Tor'₁^R(M, R / J)` should compute the
same kernel as Remark `10.75.9`. This is the quotient-specialized owner bridge needed to avoid
the unavailable global source-owner swap. -/
private noncomputable abbrev source_owner_tor_one_quotient_equiv_ker_ideal_tensor_to_module
    (J : Ideal R) :
    (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R (R ⧸ J))) ≃ₗ[R]
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul R M).comp J.subtype)) := by
  let μ :
      J ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp J.subtype)
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMk J.subtype J.mkQ (by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem.2 x.2)
  have hS : S.ShortExact := by
    -- Proof comment: this is the same short exact quotient row used in the source proof.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [S] using (LinearMap.exact_subtype_mkQ J)
    · exact (ModuleCat.mono_iff_injective _).2 J.injective_subtype
    · exact (ModuleCat.epi_iff_surjective _).2 J.mkQ_surjective
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
    -- Proof comment: this is the exactness window at `Tor'₁(M, R / J)`.
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
    -- Proof comment: and this is the exactness window identifying the tensor kernel.
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
  have hu : u.hom = J.subtype.lTensor M := by
    -- Proof comment: the endpoint tensor map is tensoring the ideal inclusion on the left.
    dsimp [u, S]
    rw [ModuleCat.hom_whiskerLeft]
    rfl
  have hμ :
      μ.comp (TensorProduct.comm R M J).toLinearMap =
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
          ((J.subtype.rTensor M).comp (TensorProduct.comm R M J).toLinearMap) =
        (TensorProduct.rid R M).toLinearMap.comp (J.subtype.lTensor M)
    rw [LinearMap.rTensor_comp_comm]
    change
      (TensorProduct.lid R M).toLinearMap.comp
          ((TensorProduct.comm R M R).toLinearMap.comp (J.subtype.lTensor M)) =
        (TensorProduct.rid R M).toLinearMap.comp (J.subtype.lTensor M)
    rw [← LinearMap.comp_assoc, hcommLid]
  let eSource :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R (R ⧸ J))) ≃ₗ[R]
        LinearMap.ker u.hom :=
    (((limit.isoLimitCone ⟨_, hker⟩).symm ≪≫ ModuleCat.kernelIsoKer u).toLinearEquiv)
  let eKer :
      LinearMap.ker u.hom ≃ₗ[R] LinearMap.ker μ :=
    ker_equiv_of_ladder_linear_equiv (R := R)
      (e₁ := TensorProduct.comm R M J) (e₂ := TensorProduct.rid R M) hμ
  -- Proof comment: the fixed-left source owner and the canonical ideal-tensor kernel compute the
  -- same kernel attached to `0 → J → R → R / J → 0`.
  simpa using eSource.trans eKer

/-- Helper for Lemma 10.99.7: if `R / J` has finite length, then the canonical map
`J ⊗[R] M → M` is injective. -/
private lemma injective_ideal_tensor_of_isFiniteLength_quotient
    (hTor : IsZero (Tor₁[R](ResidueField R, M))) (J : Ideal R)
    (hJ : IsFiniteLength R (R ⧸ J)) :
    Function.Injective (TensorProduct.lift ((LinearMap.lsmul R M).comp J.subtype)) := by
  let μ :
      J ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp J.subtype)
  have hSource :
      IsZero ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
        (ModuleCat.of R (R ⧸ J)))) := by
    have hQuotient :
        IsZero (Tor₁[R](R ⧸ J, M)) :=
      isZero_tor_one_of_isFiniteLength_of_residueField_vanishing (R := R) (M := M) hTor hJ
    -- Route correction: stay in the quotient-specialized source owner already supplied by
    -- Lemma `10.99.6`, instead of attempting a nonexistent public-owner commutativity shortcut.
    exact IsZero.of_iso hQuotient
      (tor_one_quotient_source_owner_iso (R := R) (M := M) J).symm
  let eKernel :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
        (ModuleCat.of R (R ⧸ J))) ≃ₗ[R] LinearMap.ker μ :=
    source_owner_tor_one_quotient_equiv_ker_ideal_tensor_to_module (R := R) (M := M) J
  have hker_subsingleton : Subsingleton (LinearMap.ker μ) := by
    -- The quotient-specialized source-owner bridge identifies the kernel with a zero source-owner
    -- object.
    exact eKernel.toEquiv.subsingleton_congr.mp
      ((ModuleCat.isZero_iff_subsingleton).1 hSource)
  -- An `R`-linear map is injective exactly when its kernel is trivial.
  exact LinearMap.ker_eq_bot.mp <| Submodule.subsingleton_iff_eq_bot.mp hker_subsingleton

/-- Helper for Lemma 10.99.7: adjoining a positive power of the maximal ideal produces a
finite-length quotient. -/
private lemma isFiniteLength_quotient_sup_maximalIdeal_pow
    (I : Ideal R) (n : ℕ) :
    IsFiniteLength R (R ⧸ (I ⊔ maximalIdeal R ^ (n + 1))) := by
  have hpow' :
      IsFiniteLength R (R ⧸ ((maximalIdeal R ^ (n + 1)) • (⊤ : Submodule R R))) := by
    -- The maximal ideal is an ideal of definition in a Noetherian local ring.
    exact
      Ideal.isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := R) (maximalIdeal R) Ideal.maximalIdeal_isIdealOfDefinition n
  have hpowEq :
      ((maximalIdeal R ^ (n + 1)) • (⊤ : Submodule R R)) = maximalIdeal R ^ (n + 1) := by
    simpa [Ideal.smul_eq_mul] using (Ideal.mul_top (I := maximalIdeal R ^ (n + 1)))
  have hpow : IsFiniteLength R (R ⧸ maximalIdeal R ^ (n + 1)) := by
    exact (Submodule.quotEquivOfEq _ _ hpowEq).isFiniteLength hpow'
  let f :
      (R ⧸ maximalIdeal R ^ (n + 1)) →ₗ[R] (R ⧸ (I ⊔ maximalIdeal R ^ (n + 1))) :=
    { toFun := Ideal.Quotient.factor
        (le_sup_right : maximalIdeal R ^ (n + 1) ≤ I ⊔ maximalIdeal R ^ (n + 1))
      map_add' := by
        intro a b
        simpa using
          (Ideal.Quotient.factor
            (le_sup_right : maximalIdeal R ^ (n + 1) ≤ I ⊔ maximalIdeal R ^ (n + 1))).map_add a b
      map_smul' := by
        intro r x
        change
          (Ideal.Quotient.factor
            (le_sup_right : maximalIdeal R ^ (n + 1) ≤ I ⊔ maximalIdeal R ^ (n + 1)))
              ((Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) r) * x) =
            (Ideal.Quotient.mk (I ⊔ maximalIdeal R ^ (n + 1)) r) *
              (Ideal.Quotient.factor
                (le_sup_right : maximalIdeal R ^ (n + 1) ≤ I ⊔ maximalIdeal R ^ (n + 1))) x
        simpa using
          (Ideal.Quotient.factor
            (le_sup_right : maximalIdeal R ^ (n + 1) ≤ I ⊔ maximalIdeal R ^ (n + 1))).map_mul
              (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) r) x }
  -- Quotients of finite-length modules still have finite length.
  exact IsFiniteLength.of_surjective (f := f) hpow <|
    Ideal.Quotient.factor_surjective
      (le_sup_right : maximalIdeal R ^ (n + 1) ≤ I ⊔ maximalIdeal R ^ (n + 1))

/-- Helper for Lemma 10.99.7: the intersection `I ∩ J`, viewed as a submodule of `I`. -/
private abbrev intersection_in_ideal
    (I J : Ideal R) : Submodule R I :=
  Submodule.comap I.subtype (J : Submodule R R)

/-- Helper for Lemma 10.99.7: the textbook diagonal map `I ∩ J → I × J`. -/
private abbrev intersection_diagonal
    (I J : Ideal R) :
    ↥(intersection_in_ideal I J) →ₗ[R] ↥I × ↥J :=
  { toFun := fun x ↦ (x.1, ⟨x.1.1, x.2⟩)
    map_add' := fun x y ↦ by
      ext <;> rfl
    map_smul' := fun r x ↦ by
      ext <;> rfl }

/-- Helper for Lemma 10.99.7: the difference of an element of `I` and an element of `J` lies in
`I ⊔ J`. -/
private lemma sup_difference_mem_sup
    (I J : Ideal R) (a : I) (b : J) :
    ((a : R) - (b : R)) ∈ I ⊔ J := by
  -- Proof comment: each summand already lies in the corresponding side of the supremum, so their
  -- difference lies there as well.
  exact (I ⊔ J).sub_mem (Ideal.mem_sup_left a.2) (Ideal.mem_sup_right b.2)

/-- Helper for Lemma 10.99.7: the difference map `I × J → I + J` used in the source proof. -/
private def sup_difference
    (I J : Ideal R) :
    ↥I × ↥J →ₗ[R] ↥(I ⊔ J) :=
  LinearMap.coprod
    (Submodule.inclusion (show I ≤ I ⊔ J from le_sup_left))
    (- Submodule.inclusion (show J ≤ I ⊔ J from le_sup_right))

/-- Helper for Lemma 10.99.7: the source row `I ∩ J → I × J → I + J` is exact and surjective. -/
private lemma intersection_sup_row_exact
    (I J : Ideal R) :
    Function.Exact
        (intersection_diagonal I J)
        (sup_difference I J) ∧
      Function.Surjective
        (sup_difference I J) := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: the kernel of `(a, b) ↦ a - b` consists exactly of pairs coming from a
    -- common element of `I ∩ J`.
    refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
    · ext x
      simp [sup_difference, intersection_diagonal]
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      have hEq : ((x.1 : I) : R) = ((x.2 : J) : R) := by
        have hx' : (((sup_difference I J) x : ↥(I ⊔ J)) : R) = 0 := by
          exact congrArg (fun y : ↥(I ⊔ J) => (y : R)) hx
        exact sub_eq_zero.mp <| by simpa [sup_difference, sub_eq_add_neg] using hx'
      let y : ↥(intersection_in_ideal I J) :=
        ⟨x.1, by
          change (((x.1 : I) : R) ∈ J)
          simpa [hEq] using x.2.2⟩
      refine ⟨y, ?_⟩
      ext <;> simp [intersection_diagonal, y, hEq]
  · -- Proof comment: write an element of `I ⊔ J` as a sum from `I` and `J`, then absorb the plus
    -- sign by negating the `J`-component.
    intro x
    rcases Submodule.mem_sup.1 x.2 with ⟨a, ha, b, hb, hab⟩
    refine ⟨(⟨a, ha⟩, ⟨-b, show -b ∈ J from neg_mem hb⟩), ?_⟩
    apply Subtype.ext
    simpa [sup_difference, sub_eq_add_neg, hab, add_assoc]

/-- Helper for Lemma 10.99.7: after right tensoring with `M`, the source row stays exact in the
product coordinates coming from `TensorProduct.prodLeft`. -/
private lemma intersection_sup_row_tensor_exact_prodLeft
    (I J : Ideal R) :
    Function.Exact
      ((TensorProduct.prodLeft R R I J M).toLinearMap.comp
        ((intersection_diagonal I J).rTensor M))
      (((sup_difference I J).rTensor M).comp
        (TensorProduct.prodLeft R R I J M).symm.toLinearMap) := by
  let e := TensorProduct.prodLeft R R I J M
  rcases intersection_sup_row_exact (R := R) I J with ⟨hExact, hSurj⟩
  have hTensor :
      Function.Exact ((intersection_diagonal I J).rTensor M) ((sup_difference I J).rTensor M) :=
    rTensor_exact M hExact hSurj
  -- Proof comment: transport the kernel/range description across the middle linear equivalence
  -- `prodLeft`; this avoids re-proving tensor exactness from scratch in product coordinates.
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
  · ext x
    simp [e, LinearMap.comp_assoc, hTensor.linearMap_comp_eq_zero]
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    have hx' :
        e.symm x ∈ LinearMap.ker ((sup_difference I J).rTensor M) := by
      simpa [e, LinearMap.comp_apply] using hx
    rw [hTensor.linearMap_ker_eq] at hx'
    rcases hx' with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    calc
      (e.toLinearMap.comp ((intersection_diagonal I J).rTensor M)) y
          = e (((intersection_diagonal I J).rTensor M) y) := rfl
      _ = e (e.symm x) := by rw [hy]
      _ = x := by simp [e]

/-- Helper for Lemma 10.99.7: after transporting the tensorized difference map through
`TensorProduct.prodLeft`, the left product summand is the tensor of the canonical inclusion
`I → I ⊔ J`. -/
private lemma prodLeft_transport_difference_inl_formula
    (I J : Ideal R) :
    ((((sup_difference I J).rTensor M).comp
        (TensorProduct.prodLeft R R I J M).symm.toLinearMap).comp
        (LinearMap.inl R (I ⊗[R] M) (J ⊗[R] M))) =
      ((Submodule.inclusion (show I ≤ I ⊔ J from le_sup_left)).rTensor M) := by
  apply TensorProduct.ext'
  intro i m
  -- Proof comment: on a pure tensor, the transported left summand is `(i, 0) ⊗ m`, so the
  -- difference map keeps only the inclusion of `i` into `I ⊔ J`.
  have hzero : (0 : J ⊗[R] M) = ((0 : J) ⊗ₜ[R] m) := by simp
  simp [LinearMap.comp_apply]
  rw [hzero, TensorProduct.prodLeft_symm_tmul]
  simp [sup_difference]

/-- Helper for Lemma 10.99.7: after transporting the tensorized difference map through
`TensorProduct.prodLeft`, the right product summand is the negative tensor of the canonical
inclusion `J → I ⊔ J`. -/
private lemma prodLeft_transport_difference_inr_formula
    (I J : Ideal R) :
    ((((sup_difference I J).rTensor M).comp
        (TensorProduct.prodLeft R R I J M).symm.toLinearMap).comp
        (LinearMap.inr R (I ⊗[R] M) (J ⊗[R] M))) =
      -(((Submodule.inclusion (show J ≤ I ⊔ J from le_sup_right)).rTensor M)) := by
  apply TensorProduct.ext'
  intro j m
  -- Proof comment: on a pure tensor, the transported right summand is `(0, j) ⊗ m`, and the
  -- difference map contributes the negative inclusion of `j` into `I ⊔ J`.
  have hzero : (0 : I ⊗[R] M) = ((0 : I) ⊗ₜ[R] m) := by simp
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_inr, Function.comp_apply,
    LinearMap.rTensor_tmul]
  rw [hzero, TensorProduct.prodLeft_symm_tmul]
  simpa [sup_difference] using
    (TensorProduct.neg_tmul
      ((Submodule.inclusion (show J ≤ I ⊔ J from le_sup_right)) j) m)

/-- Helper for Lemma 10.99.7: after transporting the tensorized difference map through
`TensorProduct.prodLeft`, the whole map is the expected copair of the two tensor inclusions. -/
private lemma prodLeft_transport_difference_eq_coprod
    (I J : Ideal R) :
    (((sup_difference I J).rTensor M).comp
        (TensorProduct.prodLeft R R I J M).symm.toLinearMap) =
      LinearMap.coprod
        (((Submodule.inclusion (show I ≤ I ⊔ J from le_sup_left)).rTensor M))
        (-(((Submodule.inclusion (show J ≤ I ⊔ J from le_sup_right)).rTensor M))) := by
  -- Proof comment: equality of linear maps out of a product is determined by the two endpoint
  -- formulas proved just above.
  apply LinearMap.prod_ext
  · rw [LinearMap.coprod_inl]
    exact prodLeft_transport_difference_inl_formula (R := R) (M := M) I J
  · rw [LinearMap.coprod_inr]
    exact prodLeft_transport_difference_inr_formula (R := R) (M := M) I J

/-- Helper for Lemma 10.99.7: projecting the transported tensorized diagonal map to the first
product coordinate recovers the tensor of the inclusion `I ∩ J → I`. -/
private lemma prodLeft_transport_intersection_diagonal_fst
    (I J : Ideal R) :
    (LinearMap.fst R (I ⊗[R] M) (J ⊗[R] M)).comp
        ((TensorProduct.prodLeft R R I J M).toLinearMap.comp
          ((intersection_diagonal I J).rTensor M)) =
      (((intersection_in_ideal I J).subtype).rTensor M) := by
  apply TensorProduct.ext'
  intro y m
  -- Proof comment: on pure tensors, `prodLeft` records both diagonal coordinates and `fst`
  -- keeps only the `I`-component, which is exactly the subtype inclusion.
  simp [LinearMap.comp_apply, intersection_diagonal, TensorProduct.prodLeft_tmul]

/-- Helper for Lemma 10.99.7: injectivity on `(I + J) ⊗[R] M → M` forces
`ker (I ⊗[R] M → M)` into the range of `(I ∩ J) ⊗[R] M → I ⊗[R] M`. -/
private lemma ker_le_range_inf_tensor_from_intersection_row
    (I J : Ideal R)
    (hμSup :
      Function.Injective
        (TensorProduct.lift ((LinearMap.lsmul R M).comp (I ⊔ J).subtype))) :
    LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)) ≤
      LinearMap.range
        (((intersection_in_ideal I J).subtype).rTensor M) := by
  let μI :
      I ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  let μSup :
      ↥(I ⊔ J) ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp (I ⊔ J).subtype)
  have hExact := intersection_sup_row_tensor_exact_prodLeft (R := R) (M := M) I J
  have hμCompat :
      μSup.comp
          ((Submodule.inclusion (show I ≤ I ⊔ J from le_sup_left)).rTensor M) =
        μI := by
    apply TensorProduct.ext'
    intro i m
    -- Proof comment: tensoring the inclusion `I ↪ I ⊔ J` and then multiplying agrees with
    -- multiplying directly through `I ↪ R`.
    simp [μI, μSup, LinearMap.comp_apply]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hMiddleZero :
      ((((sup_difference I J).rTensor M).comp
          (TensorProduct.prodLeft R R I J M).symm.toLinearMap)
          ((LinearMap.inl R (I ⊗[R] M) (J ⊗[R] M)) x)) = 0 := by
    -- Proof comment: `(x, 0)` maps into `(I ⊔ J) ⊗[R] M`, and injectivity of the right vertical
    -- map forces the transported difference to vanish.
    apply hμSup
    simp only [LinearMap.map_zero]
    have hInl :
        ((((sup_difference I J).rTensor M).comp
              (TensorProduct.prodLeft R R I J M).symm.toLinearMap).comp
            (LinearMap.inl R (I ⊗[R] M) (J ⊗[R] M))) x =
          (((Submodule.inclusion (show I ≤ I ⊔ J from le_sup_left)).rTensor M) x) := by
      simpa [LinearMap.comp_apply] using
        LinearMap.congr_fun
          (prodLeft_transport_difference_inl_formula (R := R) (M := M) I J) x
    calc
      μSup
          ((((sup_difference I J).rTensor M).comp
              (TensorProduct.prodLeft R R I J M).symm.toLinearMap)
              ((LinearMap.inl R (I ⊗[R] M) (J ⊗[R] M)) x))
          =
        μSup (((Submodule.inclusion (show I ≤ I ⊔ J from le_sup_left)).rTensor M) x) := by
          exact congrArg μSup hInl
      _ = μI x := by
          simpa [LinearMap.comp_apply] using LinearMap.congr_fun hμCompat x
      _ = 0 := hx
  have hExactEq :
      LinearMap.range
          ((TensorProduct.prodLeft R R I J M).toLinearMap.comp
            ((intersection_diagonal I J).rTensor M)) =
        LinearMap.ker
          (((sup_difference I J).rTensor M).comp
            (TensorProduct.prodLeft R R I J M).symm.toLinearMap) :=
    (LinearMap.exact_iff.mp hExact).symm
  have hInKer :
      (LinearMap.inl R (I ⊗[R] M) (J ⊗[R] M)) x ∈
        LinearMap.ker
          (((sup_difference I J).rTensor M).comp
            (TensorProduct.prodLeft R R I J M).symm.toLinearMap) := by
    rw [LinearMap.mem_ker]
    exact hMiddleZero
  have hInRange :
      (LinearMap.inl R (I ⊗[R] M) (J ⊗[R] M)) x ∈
        LinearMap.range
          ((TensorProduct.prodLeft R R I J M).toLinearMap.comp
            ((intersection_diagonal I J).rTensor M)) := by
    rw [hExactEq]
    exact hInKer
  rcases hInRange with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  have hfst :
      (LinearMap.fst R (I ⊗[R] M) (J ⊗[R] M))
          (((TensorProduct.prodLeft R R I J M).toLinearMap.comp
              ((intersection_diagonal I J).rTensor M)) y) = x := by
    -- Proof comment: the exactness witness maps to `(x, 0)`, so projecting to the first factor
    -- recovers exactly `x`.
    simpa [LinearMap.comp_apply] using congrArg
      (fun z ↦ (LinearMap.fst R (I ⊗[R] M) (J ⊗[R] M)) z) hy
  calc
    (((intersection_in_ideal I J).subtype).rTensor M) y
        =
      (LinearMap.fst R (I ⊗[R] M) (J ⊗[R] M))
        (((TensorProduct.prodLeft R R I J M).toLinearMap.comp
            ((intersection_diagonal I J).rTensor M)) y) := by
          simpa [LinearMap.comp_apply] using
            (LinearMap.congr_fun
              (prodLeft_transport_intersection_diagonal_fst (R := R) (M := M) I J) y).symm
    _ = x := hfst

/-- Helper for Lemma 10.99.7: if a submodule of an ideal is contained in `J I`, then tensoring
that inclusion with `M` lands inside `J (I ⊗[R] M)`. -/
private lemma range_subtype_rTensor_le_smul_top
    (I : Ideal R) (N : Submodule R I) (J : Ideal R)
    (hN : N ≤ J • (⊤ : Submodule R I)) :
    LinearMap.range (N.subtype.rTensor M) ≤ J • (⊤ : Submodule R (I ⊗[R] M)) := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  -- Tensor induction reduces the statement to pure tensors with left factor in `N`.
  refine TensorProduct.induction_on y ?_ ?_ ?_
  · simp
  · intro n m
    change ((n : I) ⊗ₜ[R] m : I ⊗[R] M) ∈ J • (⊤ : Submodule R (I ⊗[R] M))
    have hn :
        (n : I) ∈ J • (⊤ : Submodule R I) :=
      hN n.2
    -- Expand the left factor inside `J • ⊤` and push each generator across the tensor product.
    refine Submodule.smul_induction_on hn ?_ ?_
    · intro r hr z hz
      simpa [TensorProduct.smul_tmul'] using
        (Submodule.smul_mem_smul hr
          (show z ⊗ₜ[R] m ∈ (⊤ : Submodule R (I ⊗[R] M)) by simp))
    · intro z w hz hw
      simpa [TensorProduct.add_tmul] using add_mem hz hw
  · intro y z hy hz
    simpa [LinearMap.map_add] using add_mem hy hz

/-- Helper for Lemma 10.99.7: the mapped maximal-ideal power filtration on `I ⊗[R] M`, viewed
as an `R`-submodule after transporting the right `S`-action across `TensorProduct.comm`. -/
private abbrev mapped_maximalIdeal_pow_tensor_stage
    (I : Ideal R) (n : ℕ) : Submodule R (I ⊗[R] M) :=
  let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  ((((Ideal.map (algebraMap R S) (maximalIdeal R)) ^ n) •
      (⊤ : Submodule S (I ⊗[R] M))).restrictScalars R)

/-- Helper for Lemma 10.99.7: Artin-Rees forces the tensor range of
`I ∩ maximalIdeal R ^ (n + 1)` into a deep mapped maximal-ideal power on `I ⊗[R] M`. -/
private lemma intersection_tensor_range_le_mapped_maximalIdeal_pow_smul
    (I : Ideal R) :
    ∃ c > 0, ∀ n ≥ c,
      let N : Submodule R I :=
        Submodule.comap I.subtype ((maximalIdeal R ^ (n + 1) : Ideal R) : Submodule R R)
      LinearMap.range (N.subtype.rTensor M) ≤
        mapped_maximalIdeal_pow_tensor_stage (R := R) (S := S) (M := M) I (n - c) := by
  obtain ⟨c, hc, hAR⟩ := Ideal.exists_pos_pow_inf_eq_pow_smul
    (R := R) (M := R) (maximalIdeal R) (I : Submodule R R)
  refine ⟨c, hc, ?_⟩
  intro n hn
  let N : Submodule R I :=
    Submodule.comap I.subtype ((maximalIdeal R ^ (n + 1) : Ideal R) : Submodule R R)
  have hN :
      N ≤ (maximalIdeal R ^ ((n + 1) - c)) • (⊤ : Submodule R I) := by
    intro x hx
    -- Proof comment: Artin-Rees puts the ambient element `(x : R)` inside a deep power of the
    -- maximal ideal times `I`; then `Submodule.mem_smul_top_iff` moves that statement back to the
    -- subtype module `I`.
    apply (Submodule.mem_smul_top_iff
      (I := maximalIdeal R ^ ((n + 1) - c)) (N := I) (x := x)).2
    have hxPow :
        ((x : I) : R) ∈ ((maximalIdeal R ^ (n + 1) : Ideal R) : Submodule R R) := by
      simpa [N] using hx
    have hxInter :
        ((x : I) : R) ∈
          ((maximalIdeal R ^ (n + 1) • (⊤ : Submodule R R)) ⊓ (I : Submodule R R)) := by
      simpa [Ideal.smul_eq_mul] using show
        ((x : I) : R) ∈
          (((maximalIdeal R ^ (n + 1) : Ideal R) : Submodule R R) ⊓ (I : Submodule R R)) from
            ⟨hxPow, x.2⟩
    have hAR' :
        (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R R)) ⊓ (I : Submodule R R) =
          maximalIdeal R ^ ((n + 1) - c) •
            ((maximalIdeal R ^ c • (⊤ : Submodule R R)) ⊓ (I : Submodule R R)) := by
      simpa using hAR (n + 1) (Nat.le_trans hn (Nat.le_succ n))
    rw [hAR'] at hxInter
    have hxAmbient :
        ((x : I) : R) ∈
          maximalIdeal R ^ ((n + 1) - c) • (I : Submodule R R) := by
      have hmono :
          maximalIdeal R ^ ((n + 1) - c) •
              ((maximalIdeal R ^ c • (⊤ : Submodule R R)) ⊓ (I : Submodule R R)) ≤
            maximalIdeal R ^ ((n + 1) - c) • (I : Submodule R R) :=
        smul_mono_right (maximalIdeal R ^ ((n + 1) - c)) inf_le_right
      exact hmono hxInter
    exact hxAmbient
  have hRange :
      LinearMap.range (N.subtype.rTensor M) ≤
        (maximalIdeal R ^ ((n + 1) - c)) • (⊤ : Submodule R (I ⊗[R] M)) := by
    -- Proof comment: tensor the Artin-Rees containment directly over `R` before rewriting it to
    -- the mapped `S`-adic filtration used by the completion step.
    simpa [N] using
      (range_subtype_rTensor_le_smul_top (R := R)
        I N (maximalIdeal R ^ ((n + 1) - c)) hN)
  have hpow :
      maximalIdeal R ^ ((n + 1) - c) ≤ maximalIdeal R ^ (n - c) := by
    have hexp : (n + 1) - c = (n - c) + 1 := by omega
    rw [hexp]
    exact Ideal.pow_le_pow_right (Nat.le_succ (n - c))
  -- Proof comment: the `(n + 1 - c)`-stage is deeper than the `n - c`-stage, so monotonicity of
  -- the ideal action gives the stated filtration bound.
  have hFinalR :
      LinearMap.range (N.subtype.rTensor M) ≤
        (maximalIdeal R ^ (n - c)) • (⊤ : Submodule R (I ⊗[R] M)) :=
    hRange.trans (Submodule.smul_mono_left hpow)
  have hRewrite :
      (maximalIdeal R ^ (n - c)) • (⊤ : Submodule R (I ⊗[R] M)) =
        mapped_maximalIdeal_pow_tensor_stage (R := R) (S := S) (M := M) I (n - c) := by
    -- Proof comment: rewrite the `R`-adic stage as the mapped maximal-ideal stage over `S` so
    -- the main proof can pass directly to the `mS`-adic completion.
    letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    unfold mapped_maximalIdeal_pow_tensor_stage
    simpa [Ideal.map_pow] using
      (Ideal.smul_restrictScalars
        (R := R) (S := S) (M := I ⊗[R] M) (maximalIdeal R ^ (n - c))
        (⊤ : Submodule S (I ⊗[R] M))).symm
  exact hFinalR.trans (le_of_eq hRewrite)

/-- Helper for Lemma 10.99.7: the tensor product `I ⊗[R] M`, equipped with its natural
`S`-module structure from the right factor, is finite over `S`. -/
private lemma ideal_tensor_finite_over_target
    (I : Ideal R) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    Module.Finite S (I ⊗[R] M) := by
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  let _ : Module.Finite R I := Module.Finite.of_fg I.fg_of_isNoetherianRing
  let _ : Module.Finite S (S ⊗[R] I) := by infer_instance
  let _ : Module.Finite S ((S ⊗[R] I) ⊗[S] M) := by infer_instance
  let eComm :
      (I ⊗[R] M) ≃ₗ[S] (M ⊗[R] I) :=
    (TensorProduct.comm R I M).toAddEquiv.linearEquiv S
  let e :
      ((S ⊗[R] I) ⊗[S] M) ≃ₗ[S] (I ⊗[R] M) :=
    (TensorProduct.comm S M (S ⊗[R] I)).symm.trans <|
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M I).trans
        eComm.symm
  -- Route correction: transport finiteness through the canonical base-change tensor equivalence
  -- rather than rebuilding generators for `I ⊗[R] M` by hand.
  simpa using (Module.Finite.equiv e : Module.Finite S (I ⊗[R] M))

/-- Helper for Lemma 10.99.7: the image of the maximal ideal of `R` in `S` is a proper ideal. -/
private lemma mapped_maximalIdeal_ne_top :
    Ideal.map (algebraMap R S) (maximalIdeal R) ≠ (⊤ : Ideal S) := by
  exact (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne

/-- Helper for Lemma 10.99.7: an element of `I ⊗[R] M` lying in every mapped maximal-ideal
power stage maps to zero in the mapped-maximal-ideal adic completion. -/
private lemma completion_of_mem_all_mapped_maximalIdeal_stages_eq_zero
    (I : Ideal R) (x : I ⊗[R] M)
    (hx : ∀ n : ℕ,
      x ∈ mapped_maximalIdeal_pow_tensor_stage (R := R) (S := S) (M := M) I n) :
    let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
    let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
    AdicCompletion.of (Ideal.map (algebraMap R S) (maximalIdeal R)) (I ⊗[R] M) x = 0 := by
  let mS : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  apply AdicCompletion.ext
  intro n
  -- Proof comment: evaluate in the `n`th quotient and use the stage-membership hypothesis.
  change
    AdicCompletion.eval mS (I ⊗[R] M) n (AdicCompletion.of mS (I ⊗[R] M) x) =
      AdicCompletion.eval mS (I ⊗[R] M) n 0
  rw [AdicCompletion.eval_of]
  simp only [LinearMap.map_zero]
  have hstage :
      x ∈ ((mS ^ n) • (⊤ : Submodule S (I ⊗[R] M))).restrictScalars R := by
    simpa [mS, mapped_maximalIdeal_pow_tensor_stage] using hx n
  exact (Submodule.Quotient.mk_eq_zero _).2 hstage

/-- Helper for Lemma 10.99.7: vanishing in the mapped-maximal-ideal adic completion reflects to
vanishing in `I ⊗[R] M` by faithful flatness of the completion map. -/
private lemma eq_zero_of_mapped_completion_eq_zero
    (I : Ideal R) (x : I ⊗[R] M)
    (hx :
      let _ : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
      let _ : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
      AdicCompletion.of (Ideal.map (algebraMap R S) (maximalIdeal R)) (I ⊗[R] M) x = 0) :
    x = 0 := by
  let mS : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  let _ : Module.Finite S (I ⊗[R] M) := by
    simpa using ideal_tensor_finite_over_target (R := R) (S := S) (M := M) I
  let _ : IsHausdorff mS (I ⊗[R] M) :=
    IsHausdorff.of_isLocalRing (I := mS) (M := I ⊗[R] M) mapped_maximalIdeal_ne_top
  -- Proof comment: over the local Noetherian target ring, mapped maximal-ideal adic completion
  -- is Hausdorff, so the canonical map into the completion reflects zero.
  exact (AdicCompletion.of_injective mS (I ⊗[R] M)) (by simpa [mS] using hx)

/-- Helper for Lemma 10.99.7: if every kernel element lies in every mapped maximal-ideal power
stage, then the kernel of `I ⊗[R] M → M` is zero. -/
private lemma ker_eq_bot_of_completion_zero_over_mapped_maximalIdeal
    (I : Ideal R)
    (μ : I ⊗[R] M →ₗ[R] M)
    (hμ :
      ∀ n : ℕ,
        LinearMap.ker μ ≤
          mapped_maximalIdeal_pow_tensor_stage (R := R) (S := S) (M := M) I n) :
    LinearMap.ker μ = ⊥ := by
  letI : Module S (I ⊗[R] M) := (TensorProduct.comm R I M).toAddEquiv.module S
  letI : IsScalarTower R S (I ⊗[R] M) := (TensorProduct.comm R I M).isScalarTower (A := S)
  apply le_antisymm
  · intro x hx
    -- Proof comment: each kernel element dies in the completion, and faithful flatness reflects
    -- that vanishing back to the source tensor product.
    rw [Submodule.mem_bot]
    have hcompletion :
        AdicCompletion.of (Ideal.map (algebraMap R S) (maximalIdeal R)) (I ⊗[R] M) x = 0 :=
      completion_of_mem_all_mapped_maximalIdeal_stages_eq_zero
        I x (fun n ↦ hμ n hx)
    exact eq_zero_of_mapped_completion_eq_zero
      I x hcompletion
  · exact bot_le

/-- Helper for Lemma 10.99.7: under the full local-homomorphism and finiteness hypotheses from
the textbook statement, the Artin-Rees plus completion argument proves flatness over `R`. -/
private theorem flat_of_residueField_tor_one_vanishing_over_local_hom
    (S' : Type v) [CommRing S'] [Algebra R S']
    [IsLocalRing S'] [IsLocalHom (algebraMap R S')] [IsNoetherianRing S']
    [Module S' M] [IsScalarTower R S' M] [Module.Finite S' M]
    (hTor : IsZero (Tor₁[R](ResidueField R, M))) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I hI
  let μ :
      I ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
  obtain ⟨c, hc, hRangePow⟩ :=
    intersection_tensor_range_le_mapped_maximalIdeal_pow_smul
      (R := R) (S := S') (M := M) I
  have hKernelPow :
      ∀ n : ℕ,
        LinearMap.ker μ ≤
          mapped_maximalIdeal_pow_tensor_stage (R := R) (S := S') (M := M) I n := by
    intro n
    have hFiniteLength :
        IsFiniteLength R (R ⧸ (I ⊔ maximalIdeal R ^ (n + c + 1))) :=
      isFiniteLength_quotient_sup_maximalIdeal_pow (R := R) I (n + c)
    have hμSup :
        Function.Injective
          (TensorProduct.lift
            ((LinearMap.lsmul R M).comp (I ⊔ maximalIdeal R ^ (n + c + 1)).subtype)) :=
      injective_ideal_tensor_of_isFiniteLength_quotient
        (R := R) (M := M) hTor (I ⊔ maximalIdeal R ^ (n + c + 1)) hFiniteLength
    have hKernelRange :
        LinearMap.ker μ ≤
          LinearMap.range
            ((((intersection_in_ideal I (maximalIdeal R ^ (n + c + 1))).subtype).rTensor M)) := by
      -- Proof comment: injectivity for the finite-colength ideal `I ⊔ 𝔪^(n+c+1)` gives the
      -- textbook diagram-chase containment of `ker μ` inside the tensorized intersection row.
      simpa [μ, intersection_in_ideal] using
        ker_le_range_inf_tensor_from_intersection_row
          (R := R) (M := M) I (maximalIdeal R ^ (n + c + 1)) hμSup
    have hRangeStage :
        LinearMap.range
            ((((intersection_in_ideal I (maximalIdeal R ^ (n + c + 1))).subtype).rTensor M)) ≤
          mapped_maximalIdeal_pow_tensor_stage (R := R) (S := S') (M := M) I n := by
      -- Proof comment: Artin-Rees identifies the tensorized intersection with a deep stage of
      -- the mapped maximal-ideal filtration after reindexing by `n + c`.
      simpa [intersection_in_ideal, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_sub_cancel] using hRangePow (n + c) (by omega)
    exact hKernelRange.trans hRangeStage
  -- Proof comment: every kernel element maps to zero in the mapped maximal-ideal completion, and
  -- faithful flatness of that completion reflects the vanishing back to the tensor product.
  exact (LinearMap.ker_eq_bot).mp <|
    ker_eq_bot_of_completion_zero_over_mapped_maximalIdeal
      (R := R) (S := S') (M := M) I μ hKernelPow

include S in
/-- Lemma 10.99.7 (Local criterion for flatness): if `R → S` is a local homomorphism of local
Noetherian rings, `M` is a finite `S`-module, and `Tor₁^R(ResidueField R, M)` vanishes, then `M`
is flat over `R`. -/
@[stacks 00MK]
theorem flat_of_residueField_tor_one_vanishing
    (hTor : IsZero (Tor₁[R](ResidueField R, M))) :
    Module.Flat R M := by
  -- Proof comment: the private theorem already formalizes the full source proof for any local
  -- Noetherian target ring over `R`, so the public statement is its specialization to the ambient
  -- section data `S`.
  exact
    flat_of_residueField_tor_one_vanishing_over_local_hom
      (R := R) (S' := S) (M := M) hTor

end
