import Mathlib
import StacksProject_2024.Chap10.Lemma_10_75_5
import StacksProject_2024.Chap13.Lemma_13_14_3
import StacksProject_2024.Chap13.Lemma_13_16_1
import StacksProject_2024.Chap13.Definition_13_16_2
import StacksProject_2024.Chap15.Definition_15_59_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ComposableArrows
open CategoryTheory.MonoidalCategory
open ComplexShape
open scoped DerivedTensorProduct

noncomputable section

universe u

namespace ModuleCat

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

attribute [local instance] Classical.propDecidable

local notation "DMod" => DerivedCategory (ModuleCat R)
private abbrev single0 : ModuleCat R ⥤ DMod :=
  DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

private abbrev torOne (M : ModuleCat R) : ModuleCat R ⥤ ModuleCat R :=
  ((Tor (ModuleCat R) 1).obj M)

/-- Helper for Lemma 10.75.2: the source-faithful fixed-coefficient owner is the functor
`X ↦ Tor'_n(M, X)`, i.e. the `n`th left derived functor of `tensorRight X` evaluated at the fixed
module `M`. -/
private theorem source_tor_owner_eq_leftDerived_obj
    (M X : ModuleCat R) (n : ℕ) :
    (((Tor' (ModuleCat R) n).obj M).obj X) =
      ((tensorRight X).leftDerived n).obj M := by
  -- This is the definitional expansion of `Tor'` in the fixed-left-factor orientation.
  rfl

private noncomputable instance tensorRight_preservesFiniteColimits (M : ModuleCat R) :
    PreservesFiniteColimits (tensorRight M) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

/-- Helper for Lemma 10.75.2: in degree `0`, the fixed-coefficient source owner `Tor'_0(M, X)` is
the ordinary tensor product `M ⊗[R] X`. This isolates the degree-zero source endpoint used in the
textbook exact row. -/
private noncomputable def source_tor_owner_degree_zero_tensor_iso
    (M X : ModuleCat R) :
    (((Tor' (ModuleCat R) 0).obj M).obj X) ≅ (M ⊗ X) := by
  -- Route correction: compute degree `0` directly from the fixed-coefficient `Tor'` owner.
  erw [source_tor_owner_eq_leftDerived_obj (R := R) M X 0]
  exact (tensorRight X).leftDerivedZeroIsoSelf.app M

/-- Helper for Lemma 10.75.2: in degree `1`, the fixed-coefficient source owner `Tor'_1(M, X)` is
computed by tensoring the chosen projective resolution of `M` with `X` termwise and taking first
homology. This is the concrete source model behind the textbook boundary map. -/
private noncomputable def source_tor_owner_degree_one_projective_resolution_iso
    (M X : ModuleCat R) :
    (((Tor' (ModuleCat R) 1).obj M).obj X) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat R) (down ℕ) 1).obj
        (((tensorRight X).mapHomologicalComplex (down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution M))) := by
  -- The source proof computes `Tor'_1(M, X)` on a fixed projective resolution of `M`.
  erw [source_tor_owner_eq_leftDerived_obj (R := R) M X 1]
  exact
    (CategoryTheory.projectiveResolution M).isoLeftDerivedObj
      (tensorRight X) 1

/-- Helper for Lemma 10.75.2: the degree-zero source owner can also be read on the chosen
projective resolution of `M`; this is the raw homology endpoint of the source proof. -/
private noncomputable def source_tor_owner_degree_zero_projective_resolution_iso
    (M X : ModuleCat R) :
    (((Tor' (ModuleCat R) 0).obj M).obj X) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat R) (down ℕ) 0).obj
        (((tensorRight X).mapHomologicalComplex (down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution M))) := by
  -- The fixed projective resolution of `M` computes degree `0` before the standard tensor
  -- comparison identifies that homology with the literal tensor product.
  erw [source_tor_owner_eq_leftDerived_obj (R := R) M X 0]
  exact
    (CategoryTheory.projectiveResolution M).isoLeftDerivedObj
      (tensorRight X) 0

/-- Helper for Lemma 10.75.2: categorical projectivity of `ModuleCat.of R X` implies the usual
module-theoretic projectivity of `X`. This is the flatness bridge used after tensoring the chosen
projective resolution of `M`. -/
private theorem module_projective_of_categorical_projective
    (X : Type u) [AddCommGroup X] [Module R X]
    (hX : Projective (ModuleCat.of R X)) :
    Module.Projective R X := by
  -- Translate the categorical lifting property against epimorphisms into the standard linear
  -- lifting property against surjective maps.
  let _ : Small.{u} R := small_self R
  refine Module.Projective.of_lifting_property ?_
  intro M N _ _ _ _ f g hf
  let _ : Projective (ModuleCat.of R X) := hX
  have hf' : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  refine ⟨(Projective.factorThru (ModuleCat.ofHom g) (ModuleCat.ofHom f)).hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom
    (Projective.factorThru_comp (ModuleCat.ofHom g) (ModuleCat.ofHom f))

/-- Helper for Lemma 10.75.2: the projective-resolution model of `fromLeftDerivedZero'` is
natural in the functor variable. This is the fixed-resolution degree-zero transport needed to
compare `Tor'_0(M, -)` with literal tensor maps. -/
private theorem projectiveResolution_fromLeftDerivedZero'_nattrans
    {F G : ModuleCat R ⥤ ModuleCat R} [F.Additive] [G.Additive]
    (α : F ⟶ G) {X : ModuleCat R} (P : CategoryTheory.ProjectiveResolution X) :
    P.fromLeftDerivedZero' F ≫ α.app X =
      HomologicalComplex.opcyclesMap
          ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) 0 ≫
        P.fromLeftDerivedZero' G := by
  -- Cancel the universal opcycles projection and reduce to naturality of `α` on the augmentation.
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

/-- Helper for Lemma 10.75.2: the canonical degree-zero comparison
`leftDerived 0 ≅ tensor` is natural for natural transformations between right exact additive
endofunctors of `ModuleCat R`. -/
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
      -- Replace the degree-zero homology map by the corresponding opcycles map.
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

/-- Helper for Lemma 10.75.2: the degree-zero source-owner comparison transports the map induced
by a module morphism to the literal tensor map. -/
private theorem source_owner_degree_zero_tensor_map_transport
    (M : ModuleCat R) {X Y : ModuleCat R} (f : X ⟶ Y) :
    ModuleCat.ofHom (f.hom.lTensor M) =
      (source_tor_owner_degree_zero_tensor_iso (R := R) M X).inv ≫
        (((Tor' (ModuleCat R) 0).obj M).map f) ≫
        (source_tor_owner_degree_zero_tensor_iso (R := R) M Y).hom := by
  let eLeft :
      (((Tor' (ModuleCat R) 0).obj M).obj X) ≅ (M ⊗ X) :=
    source_tor_owner_degree_zero_tensor_iso (R := R) M X
  let eRight :
      (((Tor' (ModuleCat R) 0).obj M).obj Y) ≅ (M ⊗ Y) :=
    source_tor_owner_degree_zero_tensor_iso (R := R) M Y
  have hNat :
      (((Tor' (ModuleCat R) 0).obj M).map f) ≫ eRight.hom =
        eLeft.hom ≫ ModuleCat.ofHom (f.hom.lTensor M) := by
    -- Read naturality of the degree-zero comparison at the fixed module `M`.
    simpa [eLeft, eRight, Tor', Category.assoc, ModuleCat.hom_whiskerLeft] using
      congrArg
        (fun k ↦ k.app M)
        (leftDerivedZeroIsoSelf_hom_nattrans (R := R)
          (((tensoringRight (ModuleCat R)).map f)))
  -- Insert the identity `eLeft.inv ≫ eLeft.hom = 𝟙` and replace the middle factor by `hNat`.
  calc
    ModuleCat.ofHom (f.hom.lTensor M) =
      eLeft.inv ≫ eLeft.hom ≫ ModuleCat.ofHom (f.hom.lTensor M) := by
        simp
    _ = eLeft.inv ≫ ((((Tor' (ModuleCat R) 0).obj M).map f) ≫ eRight.hom) := by
        rw [hNat]
    _ = eLeft.inv ≫ (((Tor' (ModuleCat R) 0).obj M).map f) ≫ eRight.hom := by
        simp

/-- Helper for Lemma 10.75.2: the terminal two-arrow complex
`M ⊗ S.X₂ ⟶ M ⊗ S.X₃ ⟶ 0` is exact because tensoring preserves the epimorphism `S.g`. -/
private theorem tensorLeft_map_g_zero_exact
    (M : ModuleCat R) {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    (ComposableArrows.mk₂ ((tensorLeft M).map S.g) (0 : (M ⊗ S.X₃) ⟶ ⊤_ (ModuleCat R))).Exact := by
  -- The final arrow is zero, so exactness is equivalent to epimorphy of the tensorized quotient
  -- map. This is inherited from `hS.epi_g` because `tensorLeft M` preserves finite colimits.
  letI : PreservesFiniteColimits (tensorLeft M) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm
  have hEpi : Epi ((tensorLeft M).map S.g) :=
    ((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi (F := tensorLeft M)).1
      inferInstance S hS).2
  let T : ShortComplex (ModuleCat R) :=
    ShortComplex.mk ((tensorLeft M).map S.g) (0 : (M ⊗ S.X₃) ⟶ ⊤_ (ModuleCat R))
      (by
        change ((tensorLeft M).map S.g) ≫ (0 : (M ⊗ S.X₃) ⟶ ⊤_ (ModuleCat R)) = 0
        rfl)
  letI : Epi T.f := hEpi
  have hT : T.Exact :=
    (ShortComplex.exact_iff_epi (S := T) rfl).2 inferInstance
  exact hT.exact_toComposableArrows

/-- Helper for Lemma 10.75.2: tensoring a short exact row on the left by a projective module
preserves short exactness. This isolates the flatness input used degreewise on projective
resolutions. -/
private theorem tensorLeft_map_shortExact_of_projective
    (P : ModuleCat R) [Projective P] {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    (S.map (tensorLeft P)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Projective modules are flat, so exactness survives after tensoring on the left by `P`.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    let _ : Module.Projective R P :=
      module_projective_of_categorical_projective (R := R) P inferInstance
    let _ : Module.Flat R P := Module.Flat.of_projective
    have hExactBase : Function.Exact S.f.hom S.g.hom := by
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
    simpa [ModuleCat.hom_whiskerLeft] using
      (Module.Flat.lTensor_exact P hExactBase)
  · -- The left tensor functor also preserves the injectivity of the first map.
    exact (ModuleCat.mono_iff_injective _).2 <| by
      let _ : Module.Projective R P :=
        module_projective_of_categorical_projective (R := R) P inferInstance
      let _ : Module.Flat R P := Module.Flat.of_projective
      have hf : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective _).1 hS.mono_f
      simpa [ModuleCat.hom_whiskerLeft] using
        (Module.Flat.lTensor_preserves_injective_linearMap (M := P) S.f.hom hf)
  · -- Surjectivity of the quotient map is preserved by left tensoring.
    exact (ModuleCat.epi_iff_surjective _).2 <| by
      have hg : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective _).1 hS.epi_g
      simpa [ModuleCat.hom_whiskerLeft] using
        (LinearMap.lTensor_surjective P hg)

/-- Helper for Lemma 10.75.2: tensoring the chosen projective resolution of the fixed left factor
`M` with a short exact row in the second variable yields the exact five-term source-owner row
`Tor'₁(M, X₁) → Tor'₁(M, X₂) → Tor'₁(M, X₃) → M ⊗ X₁ → M ⊗ X₂ → M ⊗ X₃`. -/
private theorem source_owner_tor_one_tensor_five_term_exact_of_shortExact
    (M : ModuleCat R) {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    ∃ δ : ((((Tor' (ModuleCat R) 1).obj M).obj S.X₃) ⟶ (M ⊗ S.X₁)),
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj M).map S.f)
        (((Tor' (ModuleCat R) 1).obj M).map S.g)
        δ
        ((tensorLeft M).map S.f)
        ((tensorLeft M).map S.g)).Exact := by
  -- Route correction: the current file had already reduced degree `0` to literal tensor maps.
  -- Here we finish the source-faithful fixed-projective-resolution skeleton first, before the
  -- separate public `Tor₁(M, -)` transport.
  let P : CategoryTheory.ProjectiveResolution M :=
    CategoryTheory.projectiveResolution M
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
    -- The tensorized chain maps still compose to zero because they come from `S.f ≫ S.g = 0`.
    refine HomologicalComplex.Hom.ext ?_
    funext n
    apply ModuleCat.hom_ext
    ext x
    dsimp [φ, ψ]
    rw [← ModuleCat.hom_comp]
    rw [← MonoidalCategory.whiskerLeft_comp, S.zero]
    rw [ModuleCat.hom_whiskerLeft]
    change (LinearMap.lTensor (P.complex.X n) (0 : S.X₁ →ₗ[R] S.X₃)) x =
      ((0 :
          TensorProduct R (P.complex.X n) S.X₁ →ₗ[R]
            TensorProduct R (P.complex.X n) S.X₃) x)
    simpa using
      congrArg (fun t ↦ t x)
        (LinearMap.lTensor_zero (R := R) (M := P.complex.X n) (N := S.X₁) (P := S.X₃))
  let T : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) := ShortComplex.mk φ ψ hzero
  have hT : T.ShortExact := by
    -- Apply the projective-flatness helper degreewise along the chosen resolution of `M`.
    refine HomologicalComplex.shortExact_of_degreewise_shortExact T ?_
    intro n
    simpa [T, φ, ψ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
      ModuleCat.hom_whiskerLeft] using
      tensorLeft_map_shortExact_of_projective (R := R) (P := P.complex.X n) (S := S) hS
  let eTorX₁ :
      (((Tor' (ModuleCat R) 1).obj M).obj S.X₁) ≅ T.X₁.homology 1 :=
    source_tor_owner_degree_one_projective_resolution_iso (R := R) M S.X₁
  let eTorX₂ :
      (((Tor' (ModuleCat R) 1).obj M).obj S.X₂) ≅ T.X₂.homology 1 :=
    source_tor_owner_degree_one_projective_resolution_iso (R := R) M S.X₂
  let eTorX₃ :
      (((Tor' (ModuleCat R) 1).obj M).obj S.X₃) ≅ T.X₃.homology 1 :=
    source_tor_owner_degree_one_projective_resolution_iso (R := R) M S.X₃
  let eTensorX₁ :
      (M ⊗ S.X₁) ≅ T.X₁.homology 0 :=
    (source_tor_owner_degree_zero_tensor_iso (R := R) M S.X₁).symm ≪≫
      source_tor_owner_degree_zero_projective_resolution_iso (R := R) M S.X₁
  let eTensorX₂ :
      (M ⊗ S.X₂) ≅ T.X₂.homology 0 :=
    (source_tor_owner_degree_zero_tensor_iso (R := R) M S.X₂).symm ≪≫
      source_tor_owner_degree_zero_projective_resolution_iso (R := R) M S.X₂
  let eTensorX₃ :
      (M ⊗ S.X₃) ≅ T.X₃.homology 0 :=
    (source_tor_owner_degree_zero_tensor_iso (R := R) M S.X₃).symm ≪≫
      source_tor_owner_degree_zero_projective_resolution_iso (R := R) M S.X₃
  have hTorMapF :
      (((Tor' (ModuleCat R) 1).obj M).map S.f) ≫ eTorX₂.hom =
        eTorX₁.hom ≫ HomologicalComplex.homologyMap T.f 1 := by
    -- Degree `1` source-owner maps are the homology maps of the tensorized chain maps.
    have hMap :
        (((Tor' (ModuleCat R) 1).obj M).map S.f) =
          eTorX₁.hom ≫ HomologicalComplex.homologyMap T.f 1 ≫ eTorX₂.inv := by
      simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} R)).map S.f) P 1)
    rw [hMap]
    simp [Category.assoc]
  have hTorMapG :
      (((Tor' (ModuleCat R) 1).obj M).map S.g) ≫ eTorX₃.hom =
        eTorX₂.hom ≫ HomologicalComplex.homologyMap T.g 1 := by
    -- The same identification holds for the second source-owner `Tor'₁` arrow.
    have hMap :
        (((Tor' (ModuleCat R) 1).obj M).map S.g) =
          eTorX₂.hom ≫ HomologicalComplex.homologyMap T.g 1 ≫ eTorX₃.inv := by
      simpa [T, ψ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} R)).map S.g) P 1)
    rw [hMap]
    simp [Category.assoc]
  have hOwnerMapF :
      (((Tor' (ModuleCat R) 0).obj M).map S.f) ≫
          (source_tor_owner_degree_zero_projective_resolution_iso (R := R) M S.X₂).hom =
        (source_tor_owner_degree_zero_projective_resolution_iso (R := R) M S.X₁).hom ≫
          HomologicalComplex.homologyMap T.f 0 := by
    -- Degree `0` source-owner maps are likewise computed on the same tensorized resolution.
    have hMap :
        (((Tor' (ModuleCat R) 0).obj M).map S.f) =
          (source_tor_owner_degree_zero_projective_resolution_iso (R := R) M S.X₁).hom ≫
            HomologicalComplex.homologyMap T.f 0 ≫
            (source_tor_owner_degree_zero_projective_resolution_iso
              (R := R) M S.X₂).inv := by
      simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} R)).map S.f) P 0)
    rw [hMap]
    simp [Category.assoc]
  have hOwnerMapG :
      (((Tor' (ModuleCat R) 0).obj M).map S.g) ≫
          (source_tor_owner_degree_zero_projective_resolution_iso (R := R) M S.X₃).hom =
        (source_tor_owner_degree_zero_projective_resolution_iso (R := R) M S.X₂).hom ≫
          HomologicalComplex.homologyMap T.g 0 := by
    -- And similarly for the last degree-zero source-owner arrow.
    have hMap :
        (((Tor' (ModuleCat R) 0).obj M).map S.g) =
          (source_tor_owner_degree_zero_projective_resolution_iso (R := R) M S.X₂).hom ≫
            HomologicalComplex.homologyMap T.g 0 ≫
            (source_tor_owner_degree_zero_projective_resolution_iso
              (R := R) M S.X₃).inv := by
      simpa [T, ψ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} R)).map S.g) P 0)
    rw [hMap]
    simp [Category.assoc]
  have hTensorMapF :
      ((tensorLeft M).map S.f) ≫ eTensorX₂.hom =
        eTensorX₁.hom ≫ HomologicalComplex.homologyMap T.f 0 := by
    -- The degree-zero comparison rewrites the source-owner map as the literal tensor map.
    change ModuleCat.ofHom (S.f.hom.lTensor M) ≫ eTensorX₂.hom =
      eTensorX₁.hom ≫ HomologicalComplex.homologyMap T.f 0
    have hTransport :
        ModuleCat.ofHom (S.f.hom.lTensor M) ≫ eTensorX₂.hom =
          (source_tor_owner_degree_zero_tensor_iso (R := R) M S.X₁).inv ≫
            (((Tor' (ModuleCat R) 0).obj M).map S.f) ≫
            (source_tor_owner_degree_zero_projective_resolution_iso
              (R := R) M S.X₂).hom := by
      rw [source_owner_degree_zero_tensor_map_transport (R := R) M S.f]
      simp [eTensorX₂, Category.assoc]
    rw [hTransport, hOwnerMapF]
    simp [eTensorX₁, Category.assoc]
  have hTensorMapG :
      ((tensorLeft M).map S.g) ≫ eTensorX₃.hom =
        eTensorX₂.hom ≫ HomologicalComplex.homologyMap T.g 0 := by
    -- The same transport identifies the last literal tensor map with the raw homology map.
    change ModuleCat.ofHom (S.g.hom.lTensor M) ≫ eTensorX₃.hom =
      eTensorX₂.hom ≫ HomologicalComplex.homologyMap T.g 0
    have hTransport :
        ModuleCat.ofHom (S.g.hom.lTensor M) ≫ eTensorX₃.hom =
          (source_tor_owner_degree_zero_tensor_iso (R := R) M S.X₂).inv ≫
            (((Tor' (ModuleCat R) 0).obj M).map S.g) ≫
            (source_tor_owner_degree_zero_projective_resolution_iso
              (R := R) M S.X₃).hom := by
      rw [source_owner_degree_zero_tensor_map_transport (R := R) M S.g]
      simp [eTensorX₃, Category.assoc]
    rw [hTransport, hOwnerMapG]
    simp [eTensorX₂, Category.assoc]
  let δ : (((Tor' (ModuleCat R) 1).obj M).obj S.X₃) ⟶ (M ⊗ S.X₁) :=
    eTorX₃.hom ≫ hT.δ 1 0 (by simp) ≫ eTensorX₁.inv
  have hδ :
      δ ≫ eTensorX₁.hom = eTorX₃.hom ≫ hT.δ 1 0 (by simp) := by
    -- The transported connecting morphism is the raw boundary map conjugated by endpoint
    -- identifications.
    simp [δ, Category.assoc]
  let e :
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj M).map S.f)
        (((Tor' (ModuleCat R) 1).obj M).map S.g)
        δ
        ((tensorLeft M).map S.f)
        ((tensorLeft M).map S.g)) ≅
        HomologicalComplex.HomologySequence.composableArrows₅ hT 1 0 (by simp) :=
    ComposableArrows.isoMk₅ eTorX₁ eTorX₂ eTorX₃ eTensorX₁ eTensorX₂ eTensorX₃
      hTorMapF hTorMapG hδ hTensorMapF hTensorMapG
  refine ⟨δ, ?_⟩
  have hRaw : (HomologicalComplex.HomologySequence.composableArrows₅ hT 1 0 (by simp)).Exact := by
    -- This is the raw homology exact sequence of the tensorized short exact row.
    simpa [T] using HomologicalComplex.HomologySequence.composableArrows₅_exact hT 1 0 (by simp)
  exact (ComposableArrows.exact_iff_of_iso e).2 hRaw

/-- Helper for Lemma 10.75.2: `tor_flip_iso` identifies the public functor `Tor₁^R(M, -)` with
the flipped source owner `X ↦ Tor'₁^R(X, M)`. -/
private noncomputable def tor_one_to_flipped_source_owner_iso
    (M : ModuleCat R) :
    torOne M ≅ ((Functor.flip (Tor' (ModuleCat R) 1)).obj M) := by
  -- This is exactly the degree-`1` component of the canonical tensor-symmetry comparison.
  simpa [torOne] using ((tor_flip_iso (ModuleCat R) 1).app M)

/-- Helper for Lemma 10.75.2: the flipped source owner
`X ↦ Tor'ₙ^R(X, M)` is definitionally the `n`th left derived functor of `tensorRight M`. -/
private theorem flipped_source_owner_eq_leftDerived_obj
    (M X : ModuleCat R) (n : ℕ) :
    ((((Functor.flip (Tor' (ModuleCat R) n)).obj M).obj X)) =
      ((tensorRight M).leftDerived n).obj X := by
  -- This is the owner that `tor_flip_iso` actually lands in.
  rfl

/-- Helper for Lemma 10.75.2: in degree `0`, the flipped source owner
`X ↦ Tor'₀^R(X, M)` is the ordinary tensor product `X ⊗[R] M`. -/
private noncomputable abbrev flipped_source_owner_degree_zero_tensor_iso
    (M X : ModuleCat R) :
    ((((Functor.flip (Tor' (ModuleCat R) 0)).obj M).obj X)) ≅ (X ⊗ M) :=
  -- This is the standard degree-zero comparison for the functor `tensorRight M`.
  (tensorRight M).leftDerivedZeroIsoSelf.app X

/-- Helper for Lemma 10.75.2: the braiding identifies the tensor map in the public row with the
tensor map in the flipped-owner row. -/
private theorem tensorLeft_map_comp_tensorRightIso_hom
    {X Y : ModuleCat R} (M : ModuleCat R) (f : X ⟶ Y) :
    (tensorLeft M).map f ≫ ((BraidedCategory.tensorLeftIsoTensorRight M).app Y).hom =
      ((BraidedCategory.tensorLeftIsoTensorRight M).app X).hom ≫ (tensorRight M).map f := by
  -- This is the objectwise naturality of the braiding in the right tensor variable.
  simpa using (BraidedCategory.braiding_naturality_right M f)

/-- Helper for Lemma 10.75.2: a degreewise split horseshoe row of projective resolutions for a
short exact sequence in the first variable. The downstream exactness proof only needs the middle
resolution, the two comparison maps, and degreewise splittings. -/
private structure FirstVariableHorseshoeRow
    (S : ShortComplex (ModuleCat R)) where
  /-- The chosen middle projective resolution resolving `S.X₂`. -/
  P2 : CategoryTheory.ProjectiveResolution S.X₂
  /-- The comparison map from the left resolution into the middle resolution. -/
  iota :
      (CategoryTheory.projectiveResolution S.X₁).complex ⟶
        P2.complex
  /-- The comparison map from the middle resolution to the right resolution. -/
  pi :
      P2.complex ⟶
        (CategoryTheory.projectiveResolution S.X₃).complex
  /-- The horseshoe row is a short complex of chain complexes. -/
  zero : iota ≫ pi = 0
  /-- The left comparison map lifts the augmentation `S.f`. -/
  iota_augment :
      iota ≫ P2.π =
        (CategoryTheory.projectiveResolution S.X₁).π ≫
          (ChainComplex.single₀ (ModuleCat R)).map S.f
  /-- The right comparison map lifts the augmentation `S.g`. -/
  pi_augment :
      pi ≫ (CategoryTheory.projectiveResolution S.X₃).π =
        P2.π ≫ (ChainComplex.single₀ (ModuleCat R)).map S.g
  /-- Each degree is split exact; this is the precise source-side data needed after tensoring by
  `M`. -/
  split :
      ∀ n,
        (ShortComplex.mk
          (iota.f n)
          (pi.f n)
          (by
            simpa using congr_fun (congrArg HomologicalComplex.Hom.f zero) n)).Splitting

/-- Helper for Lemma 10.75.2: the missing source object is a degreewise split horseshoe row of
projective resolutions in the first variable. -/
private structure FirstVariableHorseshoeComplexData
    (S : ShortComplex (ModuleCat R)) where
  /-- The concrete middle chain complex in the first-variable horseshoe construction. -/
  K : ChainComplex (ModuleCat R) ℕ
  /-- The augmentation from the concrete middle complex to `S.X₂`. -/
  πK : K ⟶ (ChainComplex.single₀ (ModuleCat R)).obj S.X₂
  /-- The left comparison map into the concrete middle complex. -/
  iota :
      (CategoryTheory.projectiveResolution S.X₁).complex ⟶
        K
  /-- The right comparison map out of the concrete middle complex. -/
  pi :
      K ⟶
        (CategoryTheory.projectiveResolution S.X₃).complex
  /-- The horseshoe row is still a short complex before tensoring. -/
  zero : iota ≫ pi = 0
  /-- The left comparison map lifts the augmentation `S.f`. -/
  iota_augment :
      iota ≫ πK =
        (CategoryTheory.projectiveResolution S.X₁).π ≫
          (ChainComplex.single₀ (ModuleCat R)).map S.f
  /-- The right comparison map lifts the augmentation `S.g`. -/
  pi_augment :
      pi ≫ (CategoryTheory.projectiveResolution S.X₃).π =
        πK ≫ (ChainComplex.single₀ (ModuleCat R)).map S.g
  /-- Each degree of the concrete row is split exact. -/
  split :
      ∀ n,
        (ShortComplex.mk
          (iota.f n)
          (pi.f n)
          (by
            simpa using congr_fun (congrArg HomologicalComplex.Hom.f zero) n)).Splitting
  /-- The augmentation from the concrete middle complex is a quasi-isomorphism, so the complex
  really resolves `S.X₂`. -/
  quasiIso_πK : QuasiIso πK

/-- Helper for Lemma 10.75.2: the concrete middle horseshoe complex is degreewise projective
because each split short exact row identifies the middle term with a biproduct of projective
resolution terms. -/
private theorem first_variable_horseshoe_complex_termwise_projective
    {S : ShortComplex (ModuleCat R)}
    (H : FirstVariableHorseshoeComplexData (R := R) S) :
    ∀ n, Projective (H.K.X n) := by
  intro n
  -- Read the `n`th split row as an isomorphism with a biproduct of the outer projective terms.
  let Tn : ShortComplex (ModuleCat R) :=
    ShortComplex.mk
      (H.iota.f n)
      (H.pi.f n)
      (by
        simpa using congr_fun (congrArg HomologicalComplex.Hom.f H.zero) n)
  let e :
      H.K.X n ≅
        (CategoryTheory.projectiveResolution S.X₁).complex.X n ⊞
          (CategoryTheory.projectiveResolution S.X₃).complex.X n :=
    ShortComplex.Splitting.isoBinaryBiproduct (S := Tn) (H.split n)
  letI : Projective ((CategoryTheory.projectiveResolution S.X₁).complex.X n) :=
    (CategoryTheory.projectiveResolution S.X₁).projective n
  letI : Projective ((CategoryTheory.projectiveResolution S.X₃).complex.X n) :=
    (CategoryTheory.projectiveResolution S.X₃).projective n
  -- Transport projectivity across the splitting isomorphism.
  exact Projective.of_iso e.symm inferInstance

/-- Helper for Lemma 10.75.2: isolate the source-faithful blocker as the concrete middle
horseshoe complex together with its augmentation and the degreewise splittings. -/
private noncomputable def first_variable_horseshoe_complex_data_of_shortExact
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    FirstVariableHorseshoeComplexData (R := R) S :=
  -- Route correction: the failed `singleTriangle` route never produced a literal short exact row
  -- of chain complexes. This helper now stops at the concrete middle complex promised by the
  -- source horseshoe proof, before any quasi-isomorphism packaging.
  -- TODO: define the biproduct-middle complex, its augmentation, and the comparison maps by the
  -- first-variable horseshoe recursion, and separately prove below that the augmentation is a
  -- quasi-isomorphism via the resulting degreewise split short exact row.
  sorry

/-- Helper for Lemma 10.75.2: once the concrete horseshoe data are fixed, the only remaining
source-faithful structural claim is that its augmentation is a quasi-isomorphism. -/
private theorem first_variable_horseshoe_complex_quasiIso
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    QuasiIso (first_variable_horseshoe_complex_data_of_shortExact (R := R) hS).πK := by
  -- The remaining source-faithful work is now packaged in the concrete horseshoe datum itself.
  exact (first_variable_horseshoe_complex_data_of_shortExact (R := R) hS).quasiIso_πK

/-- Helper for Lemma 10.75.2: once the concrete middle horseshoe complex is available, packaging
it as the middle projective resolution is formal. -/
private noncomputable def first_variable_horseshoe_row_of_shortExact
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    FirstVariableHorseshoeRow (R := R) S :=
  let H := first_variable_horseshoe_complex_data_of_shortExact (R := R) hS
  -- The remaining work is already isolated in the concrete horseshoe complex datum.
  { P2 :=
      { complex := H.K
        projective := first_variable_horseshoe_complex_termwise_projective (R := R) H
        π := H.πK
        quasiIso := first_variable_horseshoe_complex_quasiIso (R := R) hS }
    iota := H.iota
    pi := H.pi
    zero := H.zero
    iota_augment := H.iota_augment
    pi_augment := H.pi_augment
    split := H.split }

/-- Helper for Lemma 10.75.2: tensoring the horseshoe row by `M` produces the short complex of
chain complexes whose `(1,0)` homology window gives the flipped-owner exact row. -/
private noncomputable def FirstVariableHorseshoeRow.tensorizedShortComplex
    {S : ShortComplex (ModuleCat R)}
    (H : FirstVariableHorseshoeRow (R := R) S) (M : ModuleCat R) :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk
    (((tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).map H.iota)
    (((tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ)).map H.pi)
    (by
      rw [← Functor.map_comp, H.zero, Functor.map_zero])

/-- Helper for Lemma 10.75.2: the degreewise split horseshoe row stays short exact after
tensoring on the right by `M`. -/
private theorem tensorRight_horseshoe_shortExact
    (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (H : FirstVariableHorseshoeRow (R := R) S) :
    (H.tensorizedShortComplex M).ShortExact := by
  -- Exactness is checked degreewise from the stored splittings, then repackaged as exactness of a
  -- short complex of chain complexes.
  refine HomologicalComplex.shortExact_of_degreewise_shortExact
    (H.tensorizedShortComplex M) ?_
  intro n
  simpa [FirstVariableHorseshoeRow.tensorizedShortComplex,
    CategoryTheory.Functor.mapHomologicalComplex_map_f] using
    ((H.split n).map (tensorRight M)).shortExact

/-- Helper for Lemma 10.75.2: the degree-zero flipped-owner comparison transports a morphism in
the source variable to the literal tensor map for the fixed functor `tensorRight M`. -/
private theorem flipped_source_owner_degree_zero_tensor_map_transport
    (M : ModuleCat R) {X Y : ModuleCat R} (f : X ⟶ Y) :
    (tensorRight M).map f =
      (flipped_source_owner_degree_zero_tensor_iso (R := R) M X).inv ≫
        (((Functor.flip (Tor' (ModuleCat R) 0)).obj M).map f) ≫
        (flipped_source_owner_degree_zero_tensor_iso (R := R) M Y).hom := by
  let eLeft :
      ((((Functor.flip (Tor' (ModuleCat R) 0)).obj M).obj X)) ≅ (X ⊗ M) :=
    flipped_source_owner_degree_zero_tensor_iso (R := R) M X
  let eRight :
      ((((Functor.flip (Tor' (ModuleCat R) 0)).obj M).obj Y)) ≅ (Y ⊗ M) :=
    flipped_source_owner_degree_zero_tensor_iso (R := R) M Y
  have hNat :
      (((Functor.flip (Tor' (ModuleCat R) 0)).obj M).map f) ≫ eRight.hom =
        eLeft.hom ≫ (tensorRight M).map f := by
    -- This is just naturality of the degree-zero comparison for the fixed functor `tensorRight M`.
    simpa [eLeft, eRight, Tor'] using
      ((tensorRight M).leftDerivedZeroIsoSelf).hom.naturality f
  have hInsert :
      (tensorRight M).map f =
        eLeft.inv ≫ eLeft.hom ≫ (tensorRight M).map f := by
    -- Insert the identity `eLeft.inv ≫ eLeft.hom = 𝟙` on the source side.
    simp
  have hRewrite :
      eLeft.inv ≫ eLeft.hom ≫ (tensorRight M).map f =
        eLeft.inv ≫ ((((Functor.flip (Tor' (ModuleCat R) 0)).obj M).map f) ≫ eRight.hom) := by
    -- Replace the middle factor by the degree-zero naturality square.
    simpa [Category.assoc] using congrArg (fun k ↦ eLeft.inv ≫ k) hNat.symm
  -- Combine the inserted identity with naturality and reassociate to the target form.
  exact hInsert.trans <| hRewrite.trans <| by
    simpa [eLeft, eRight]

/-- Helper for Lemma 10.75.2: a concrete `(1,0)` homology window for the flipped-owner route.
The missing source-faithful step is to build such a window from a degreewise split horseshoe row
of projective resolutions in the first variable. -/
private structure FlippedSourceOwnerFiveTermData
    (M : ModuleCat R) (S : ShortComplex (ModuleCat R)) where
  /-- The short complex of chain complexes produced by tensoring the horseshoe row by `M`. -/
  T : ShortComplex (ChainComplex (ModuleCat R) ℕ)
  /-- The tensorized horseshoe row is short exact degreewise, hence short exact as a row of
  chain complexes. -/
  hT : T.ShortExact
  /-- The left endpoint `Tor'₁(S.X₁, M)` identified with first homology of the left chain
  complex. -/
  eTorX₁ : ((((Functor.flip (Tor' (ModuleCat R) 1)).obj M).obj S.X₁)) ≅ T.X₁.homology 1
  /-- The middle endpoint `Tor'₁(S.X₂, M)` identified with first homology of the middle chain
  complex. -/
  eTorX₂ : ((((Functor.flip (Tor' (ModuleCat R) 1)).obj M).obj S.X₂)) ≅ T.X₂.homology 1
  /-- The right endpoint `Tor'₁(S.X₃, M)` identified with first homology of the right chain
  complex. -/
  eTorX₃ : ((((Functor.flip (Tor' (ModuleCat R) 1)).obj M).obj S.X₃)) ≅ T.X₃.homology 1
  /-- The left degree-zero endpoint identified with the literal tensor product `S.X₁ ⊗ M`. -/
  eTensorX₁ : (S.X₁ ⊗ M) ≅ T.X₁.homology 0
  /-- The middle degree-zero endpoint identified with the literal tensor product `S.X₂ ⊗ M`. -/
  eTensorX₂ : (S.X₂ ⊗ M) ≅ T.X₂.homology 0
  /-- The right degree-zero endpoint identified with the literal tensor product `S.X₃ ⊗ M`. -/
  eTensorX₃ : (S.X₃ ⊗ M) ≅ T.X₃.homology 0
  /-- The first flipped-owner `Tor'₁` arrow agrees with the raw homology map on `T.f`. -/
  hTorMapF :
      (((Functor.flip (Tor' (ModuleCat R) 1)).obj M).map S.f) ≫ eTorX₂.hom =
        eTorX₁.hom ≫ HomologicalComplex.homologyMap T.f 1
  /-- The second flipped-owner `Tor'₁` arrow agrees with the raw homology map on `T.g`. -/
  hTorMapG :
      (((Functor.flip (Tor' (ModuleCat R) 1)).obj M).map S.g) ≫ eTorX₃.hom =
        eTorX₂.hom ≫ HomologicalComplex.homologyMap T.g 1
  /-- The first tensor arrow agrees with the raw degree-zero homology map on `T.f`. -/
  hTensorMapF :
      ((tensorRight M).map S.f) ≫ eTensorX₂.hom =
        eTensorX₁.hom ≫ HomologicalComplex.homologyMap T.f 0
  /-- The second tensor arrow agrees with the raw degree-zero homology map on `T.g`. -/
  hTensorMapG :
      ((tensorRight M).map S.g) ≫ eTensorX₃.hom =
        eTensorX₂.hom ≫ HomologicalComplex.homologyMap T.g 0

/-- Helper for Lemma 10.75.2: once the degreewise split horseshoe row is available, the flipped
owner exact row is obtained by tensoring that row by `M` and reading off the `(1,0)` homology
window. -/
private theorem flipped_source_owner_five_term_data_nonempty_of_horseshoe_row
    (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (H : FirstVariableHorseshoeRow (R := R) S) :
    Nonempty (FlippedSourceOwnerFiveTermData (R := R) M S) := by
  let T := H.tensorizedShortComplex M
  let hT := tensorRight_horseshoe_shortExact (R := R) M H
  let eTorX₁ :
      ((((Functor.flip (Tor' (ModuleCat R) 1)).obj M).obj S.X₁)) ≅ T.X₁.homology 1 := by
    -- Read the left endpoint on the chosen projective resolution of `S.X₁`.
    erw [flipped_source_owner_eq_leftDerived_obj (R := R) M S.X₁ 1]
    exact (CategoryTheory.projectiveResolution S.X₁).isoLeftDerivedObj (tensorRight M) 1
  let eTorX₂ :
      ((((Functor.flip (Tor' (ModuleCat R) 1)).obj M).obj S.X₂)) ≅ T.X₂.homology 1 := by
    -- The middle endpoint is computed on the middle projective resolution supplied by `H`.
    erw [flipped_source_owner_eq_leftDerived_obj (R := R) M S.X₂ 1]
    exact H.P2.isoLeftDerivedObj (tensorRight M) 1
  let eTorX₃ :
      ((((Functor.flip (Tor' (ModuleCat R) 1)).obj M).obj S.X₃)) ≅ T.X₃.homology 1 := by
    -- Read the right endpoint on the chosen projective resolution of `S.X₃`.
    erw [flipped_source_owner_eq_leftDerived_obj (R := R) M S.X₃ 1]
    exact (CategoryTheory.projectiveResolution S.X₃).isoLeftDerivedObj (tensorRight M) 1
  let eOwnerX₁ :
      ((((Functor.flip (Tor' (ModuleCat R) 0)).obj M).obj S.X₁)) ≅ T.X₁.homology 0 := by
    -- Degree `0` is still computed by the same chosen projective resolution.
    erw [flipped_source_owner_eq_leftDerived_obj (R := R) M S.X₁ 0]
    exact (CategoryTheory.projectiveResolution S.X₁).isoLeftDerivedObj (tensorRight M) 0
  let eOwnerX₂ :
      ((((Functor.flip (Tor' (ModuleCat R) 0)).obj M).obj S.X₂)) ≅ T.X₂.homology 0 := by
    -- The middle degree-zero endpoint uses the middle projective resolution from `H`.
    erw [flipped_source_owner_eq_leftDerived_obj (R := R) M S.X₂ 0]
    exact H.P2.isoLeftDerivedObj (tensorRight M) 0
  let eOwnerX₃ :
      ((((Functor.flip (Tor' (ModuleCat R) 0)).obj M).obj S.X₃)) ≅ T.X₃.homology 0 := by
    -- Read the right degree-zero endpoint on the chosen projective resolution of `S.X₃`.
    erw [flipped_source_owner_eq_leftDerived_obj (R := R) M S.X₃ 0]
    exact (CategoryTheory.projectiveResolution S.X₃).isoLeftDerivedObj (tensorRight M) 0
  let eTensorX₁ : (S.X₁ ⊗ M) ≅ T.X₁.homology 0 :=
    (flipped_source_owner_degree_zero_tensor_iso (R := R) M S.X₁).symm ≪≫ eOwnerX₁
  let eTensorX₂ : (S.X₂ ⊗ M) ≅ T.X₂.homology 0 :=
    (flipped_source_owner_degree_zero_tensor_iso (R := R) M S.X₂).symm ≪≫ eOwnerX₂
  let eTensorX₃ : (S.X₃ ⊗ M) ≅ T.X₃.homology 0 :=
    (flipped_source_owner_degree_zero_tensor_iso (R := R) M S.X₃).symm ≪≫ eOwnerX₃
  have hIotaAug0 :
      H.iota.f 0 ≫ H.P2.π.f 0 =
        (CategoryTheory.projectiveResolution S.X₁).π.f 0 ≫ S.f := by
    -- The degree-zero component of `H.iota_augment` is the compatibility needed for naturality.
    simpa using congr_fun (congrArg HomologicalComplex.Hom.f H.iota_augment) 0
  have hPiAug0 :
      H.pi.f 0 ≫ (CategoryTheory.projectiveResolution S.X₃).π.f 0 =
        H.P2.π.f 0 ≫ S.g := by
    -- Likewise for the right comparison map.
    simpa using congr_fun (congrArg HomologicalComplex.Hom.f H.pi_augment) 0
  have hTorMapF :
      (((Functor.flip (Tor' (ModuleCat R) 1)).obj M).map S.f) ≫ eTorX₂.hom =
        eTorX₁.hom ≫ HomologicalComplex.homologyMap T.f 1 := by
    -- Transport the first flipped-owner map along the chain map induced by `H.iota`.
    simpa [T, FirstVariableHorseshoeRow.tensorizedShortComplex] using
      (CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_hom_naturality
        (f := S.f)
        (P := CategoryTheory.projectiveResolution S.X₁)
        (Q := H.P2)
        (φ := H.iota)
        (comm := hIotaAug0)
        (F := tensorRight M)
        (n := 1))
  have hTorMapG :
      (((Functor.flip (Tor' (ModuleCat R) 1)).obj M).map S.g) ≫ eTorX₃.hom =
        eTorX₂.hom ≫ HomologicalComplex.homologyMap T.g 1 := by
    -- The second flipped-owner map is the homology map induced by `H.pi`.
    simpa [T, FirstVariableHorseshoeRow.tensorizedShortComplex] using
      (CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_hom_naturality
        (f := S.g)
        (P := H.P2)
        (Q := CategoryTheory.projectiveResolution S.X₃)
        (φ := H.pi)
        (comm := hPiAug0)
        (F := tensorRight M)
        (n := 1))
  have hOwnerMapF :
      (((Functor.flip (Tor' (ModuleCat R) 0)).obj M).map S.f) ≫ eOwnerX₂.hom =
        eOwnerX₁.hom ≫ HomologicalComplex.homologyMap T.f 0 := by
    -- The degree-zero owner map is computed on the same tensorized chain map.
    simpa [T, FirstVariableHorseshoeRow.tensorizedShortComplex] using
      (CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_hom_naturality
        (f := S.f)
        (P := CategoryTheory.projectiveResolution S.X₁)
        (Q := H.P2)
        (φ := H.iota)
        (comm := hIotaAug0)
        (F := tensorRight M)
        (n := 0))
  have hOwnerMapG :
      (((Functor.flip (Tor' (ModuleCat R) 0)).obj M).map S.g) ≫ eOwnerX₃.hom =
        eOwnerX₂.hom ≫ HomologicalComplex.homologyMap T.g 0 := by
    -- And similarly for the second degree-zero map.
    simpa [T, FirstVariableHorseshoeRow.tensorizedShortComplex] using
      (CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_hom_naturality
        (f := S.g)
        (P := H.P2)
        (Q := CategoryTheory.projectiveResolution S.X₃)
        (φ := H.pi)
        (comm := hPiAug0)
        (F := tensorRight M)
        (n := 0))
  have hTensorMapF :
      ((tensorRight M).map S.f) ≫ eTensorX₂.hom =
        eTensorX₁.hom ≫ HomologicalComplex.homologyMap T.f 0 := by
    -- Rewrite the literal tensor map through the degree-zero owner comparison, then use
    -- naturality on the chosen resolutions.
    have hTransport :
        (tensorRight M).map S.f ≫ eTensorX₂.hom =
          (flipped_source_owner_degree_zero_tensor_iso (R := R) M S.X₁).inv ≫
            (((Functor.flip (Tor' (ModuleCat R) 0)).obj M).map S.f) ≫
            eOwnerX₂.hom := by
      rw [flipped_source_owner_degree_zero_tensor_map_transport (R := R) (M := M) S.f]
      dsimp [eTensorX₂, flipped_source_owner_degree_zero_tensor_iso]
      have hCancel :
          (tensorRight M).fromLeftDerivedZero.app S.X₂ ≫
              (tensorRight M).leftDerivedZeroIsoSelf.inv.app S.X₂ ≫
                eOwnerX₂.hom =
            eOwnerX₂.hom := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ k ≫ eOwnerX₂.hom)
            (Functor.leftDerivedZeroIsoSelf_hom_inv_id_app (F := tensorRight M) (X := S.X₂))
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            (tensorRight M).leftDerivedZeroIsoSelf.inv.app S.X₁ ≫
              (((tensoringRight (ModuleCat R)).obj M).leftDerived 0).map S.f ≫ k)
          hCancel
    rw [hTransport, hOwnerMapF]
    simp [eTensorX₁, Category.assoc]
  have hTensorMapG :
      ((tensorRight M).map S.g) ≫ eTensorX₃.hom =
        eTensorX₂.hom ≫ HomologicalComplex.homologyMap T.g 0 := by
    -- The same degree-zero transport works for the second tensor arrow.
    have hTransport :
        (tensorRight M).map S.g ≫ eTensorX₃.hom =
          (flipped_source_owner_degree_zero_tensor_iso (R := R) M S.X₂).inv ≫
            (((Functor.flip (Tor' (ModuleCat R) 0)).obj M).map S.g) ≫
            eOwnerX₃.hom := by
      rw [flipped_source_owner_degree_zero_tensor_map_transport (R := R) (M := M) S.g]
      dsimp [eTensorX₃, flipped_source_owner_degree_zero_tensor_iso]
      have hCancel :
          (tensorRight M).fromLeftDerivedZero.app S.X₃ ≫
              (tensorRight M).leftDerivedZeroIsoSelf.inv.app S.X₃ ≫
                eOwnerX₃.hom =
            eOwnerX₃.hom := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ k ≫ eOwnerX₃.hom)
            (Functor.leftDerivedZeroIsoSelf_hom_inv_id_app (F := tensorRight M) (X := S.X₃))
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            (tensorRight M).leftDerivedZeroIsoSelf.inv.app S.X₂ ≫
              (((tensoringRight (ModuleCat R)).obj M).leftDerived 0).map S.g ≫ k)
          hCancel
    rw [hTransport, hOwnerMapG]
    simp [eTensorX₂, Category.assoc]
  -- Package the tensorized horseshoe row together with the endpoint identifications.
  exact ⟨{
    T := T
    hT := hT
    eTorX₁ := eTorX₁
    eTorX₂ := eTorX₂
    eTorX₃ := eTorX₃
    eTensorX₁ := eTensorX₁
    eTensorX₂ := eTensorX₂
    eTensorX₃ := eTensorX₃
    hTorMapF := hTorMapF
    hTorMapG := hTorMapG
    hTensorMapF := hTensorMapF
    hTensorMapG := hTensorMapG }⟩

/-- Helper for Lemma 10.75.2: once the degreewise split horseshoe row is available, the flipped
owner exact row is obtained by tensoring that row by `M` and reading off the `(1,0)` homology
window. -/
private noncomputable def flipped_source_owner_five_term_data_of_horseshoe_row
    (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (H : FirstVariableHorseshoeRow (R := R) S) :
    FlippedSourceOwnerFiveTermData (R := R) M S :=
  Classical.choice
    (flipped_source_owner_five_term_data_nonempty_of_horseshoe_row
      (R := R) (M := M) (S := S) H)

/-- Helper for Lemma 10.75.2: package the degreewise split horseshoe construction needed for the
flipped-owner proof as explicit homology-window data. -/
private noncomputable def flipped_source_owner_five_term_data_of_shortExact
    (M : ModuleCat R) {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    FlippedSourceOwnerFiveTermData (R := R) M S :=
  -- Specializing the formal packaging only depends on the horseshoe row already isolated above.
  flipped_source_owner_five_term_data_of_horseshoe_row
    (R := R) (M := M) (S := S)
    (first_variable_horseshoe_row_of_shortExact (R := R) hS)

/-- Helper for Lemma 10.75.2: the honest owner supplied by `tor_flip_iso`,
`X ↦ Tor'₁^R(X, M)`, admits the five-term exact row
`Tor'₁(X₁, M) → Tor'₁(X₂, M) → Tor'₁(X₃, M) → X₁ ⊗ M → X₂ ⊗ M`. -/
private theorem flipped_source_owner_tor_one_tensor_five_term_exact_of_shortExact
    (M : ModuleCat R) {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    ∃ δ : ((((Functor.flip (Tor' (ModuleCat R) 1)).obj M).obj S.X₃) ⟶ (S.X₁ ⊗ M)),
      (ComposableArrows.mk₅
        (((Functor.flip (Tor' (ModuleCat R) 1)).obj M).map S.f)
        (((Functor.flip (Tor' (ModuleCat R) 1)).obj M).map S.g)
        δ
        ((tensorRight M).map S.f)
        ((tensorRight M).map S.g)).Exact := by
  -- Route correction: after isolating the missing horseshoe package, the closing argument is the
  -- same conjugation step already used for the fixed-left-factor owner.
  let data := flipped_source_owner_five_term_data_of_shortExact (R := R) (M := M) (S := S) hS
  let δ : ((((Functor.flip (Tor' (ModuleCat R) 1)).obj M).obj S.X₃) ⟶ (S.X₁ ⊗ M)) :=
    data.eTorX₃.hom ≫ data.hT.δ 1 0 (by simp) ≫ data.eTensorX₁.inv
  have hδ :
      δ ≫ data.eTensorX₁.hom =
        data.eTorX₃.hom ≫ data.hT.δ 1 0 (by simp) := by
    -- The connecting morphism is the raw boundary map conjugated by the endpoint isomorphisms.
    simp [δ, Category.assoc]
  let e :
      (ComposableArrows.mk₅
        (((Functor.flip (Tor' (ModuleCat R) 1)).obj M).map S.f)
        (((Functor.flip (Tor' (ModuleCat R) 1)).obj M).map S.g)
        δ
        ((tensorRight M).map S.f)
        ((tensorRight M).map S.g)) ≅
        HomologicalComplex.HomologySequence.composableArrows₅ data.hT 1 0 (by simp) :=
    ComposableArrows.isoMk₅
      data.eTorX₁
      data.eTorX₂
      data.eTorX₃
      data.eTensorX₁
      data.eTensorX₂
      data.eTensorX₃
      data.hTorMapF
      data.hTorMapG
      hδ
      data.hTensorMapF
      data.hTensorMapG
  refine ⟨δ, ?_⟩
  have hRaw :
      (HomologicalComplex.HomologySequence.composableArrows₅ data.hT 1 0 (by simp)).Exact := by
    -- This is the raw homology exact sequence of the tensorized horseshoe row.
    simpa using HomologicalComplex.HomologySequence.composableArrows₅_exact data.hT 1 0 (by simp)
  exact (ComposableArrows.exact_iff_of_iso e).2 hRaw

/-- Helper for Lemma 10.75.2: the fixed projective resolution of `M`, tensored degreewise with a
short exact row, yields the public five-term exact row
`Tor₁(M, X₁) → Tor₁(M, X₂) → Tor₁(M, X₃) → M ⊗ X₁ → M ⊗ X₂`. -/
private theorem tor_one_tensor_five_term_exact_of_shortExact
    (M : ModuleCat R) {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    ∃ δ : ((torOne M).obj S.X₃) ⟶ (M ⊗ S.X₁),
      (ComposableArrows.mk₅
        ((torOne M).map S.f)
        ((torOne M).map S.g)
        δ
        ((tensorLeft M).map S.f)
        ((tensorLeft M).map S.g)).Exact := by
  -- Route correction: transport the canonical exact row from the flipped owner that
  -- `tor_flip_iso` actually provides, rather than from the unavailable fixed-left-factor owner.
  let eTor := tor_one_to_flipped_source_owner_iso (R := R) M
  let eTensorX₁ := (BraidedCategory.tensorLeftIsoTensorRight M).app S.X₁
  let eTensorX₂ := (BraidedCategory.tensorLeftIsoTensorRight M).app S.X₂
  let eTensorX₃ := (BraidedCategory.tensorLeftIsoTensorRight M).app S.X₃
  obtain ⟨δOwner, hOwner⟩ :=
    flipped_source_owner_tor_one_tensor_five_term_exact_of_shortExact
      (R := R) (M := M) (S := S) hS
  let δ : ((torOne M).obj S.X₃) ⟶ (M ⊗ S.X₁) :=
    (eTor.hom.app S.X₃) ≫ δOwner ≫ eTensorX₁.inv
  have hTorMapF :
      ((torOne M).map S.f) ≫ (eTor.hom.app S.X₂) =
        (eTor.hom.app S.X₁) ≫
          (((Functor.flip (Tor' (ModuleCat R) 1)).obj M).map S.f) := by
    -- Naturality identifies the public `Tor₁` map with the flipped source-owner map.
    simpa using eTor.hom.naturality S.f
  have hTorMapG :
      ((torOne M).map S.g) ≫ (eTor.hom.app S.X₃) =
        (eTor.hom.app S.X₂) ≫
          (((Functor.flip (Tor' (ModuleCat R) 1)).obj M).map S.g) := by
    -- The same naturality relation holds for the second `Tor₁` arrow.
    simpa using eTor.hom.naturality S.g
  have hδ :
      δ ≫ eTensorX₁.hom =
        (eTor.hom.app S.X₃) ≫ δOwner := by
    -- The connecting morphism is conjugated by the tensor-symmetry isomorphism on the target.
    simp [δ, eTensorX₁, Category.assoc]
  have hTensorMapF :
      ((tensorLeft M).map S.f) ≫ eTensorX₂.hom =
        eTensorX₁.hom ≫ (tensorRight M).map S.f := by
    -- The braiding transports the public tensor arrow to the flipped tensor arrow.
    simpa [eTensorX₁, eTensorX₂] using
      tensorLeft_map_comp_tensorRightIso_hom (R := R) (M := M) S.f
  have hTensorMapG :
      ((tensorLeft M).map S.g) ≫ eTensorX₃.hom =
        eTensorX₂.hom ≫ (tensorRight M).map S.g := by
    -- The same braiding naturality relation holds for the last tensor arrow.
    simpa [eTensorX₂, eTensorX₃] using
      tensorLeft_map_comp_tensorRightIso_hom (R := R) (M := M) S.g
  let e :
      (ComposableArrows.mk₅
        ((torOne M).map S.f)
        ((torOne M).map S.g)
        δ
        ((tensorLeft M).map S.f)
        ((tensorLeft M).map S.g)) ≅
        (ComposableArrows.mk₅
          (((Functor.flip (Tor' (ModuleCat R) 1)).obj M).map S.f)
          (((Functor.flip (Tor' (ModuleCat R) 1)).obj M).map S.g)
          δOwner
          ((tensorRight M).map S.f)
          ((tensorRight M).map S.g)) :=
    ComposableArrows.isoMk₅
      (eTor.app S.X₁)
      (eTor.app S.X₂)
      (eTor.app S.X₃)
      eTensorX₁
      eTensorX₂
      eTensorX₃
      hTorMapF
      hTorMapG
      hδ
      hTensorMapF
      hTensorMapG
  refine ⟨δ, ?_⟩
  -- Once the owner row is known, the public row is just its conjugate by the endpoint
  -- comparison isomorphisms.
  exact (ComposableArrows.exact_iff_of_iso e).2 hOwner

/-- The canonical six-term `Tor₁`/tensor row attached to a short exact sequence `hS`.
The middle map is chosen from the source-faithful five-term exact row built from the tensorized
fixed projective resolution of `M`. -/
def torTensorSixTermSequence (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) : ComposableArrows (ModuleCat R) 6 :=
  (ComposableArrows.mk₅
      ((torOne M).map S.g)
      (Classical.choose (tor_one_tensor_five_term_exact_of_shortExact (R := R) (M := M) (S := S) hS))
      ((tensorLeft M).map S.f)
      ((tensorLeft M).map S.g)
      (0 : (M ⊗ S.X₃) ⟶ ⊤_ (ModuleCat R))).precomp ((torOne M).map S.f)

/-- Lemma 10.75.2: for a short exact sequence `hS`, the canonical six-term sequence
`Tor₁^R(M, S.X₁) ⟶ Tor₁^R(M, S.X₂) ⟶ Tor₁^R(M, S.X₃) ⟶
M ⊗[R] S.X₁ ⟶ M ⊗[R] S.X₂ ⟶ M ⊗[R] S.X₃ ⟶ 0`
is exact. In Lean the tensor terms are the monoidal products `M ⊗ S.Xᵢ` in `ModuleCat R`. -/
theorem torTensorSixTermSequence_exact (M : ModuleCat R) {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) :
    (torTensorSixTermSequence M hS).Exact := by
  let δ :=
    Classical.choose (tor_one_tensor_five_term_exact_of_shortExact (R := R) (M := M) (S := S) hS)
  have hPublicδlast :
      (ComposableArrows.mk₅
        ((torOne M).map S.f)
        ((torOne M).map S.g)
        δ
        ((tensorLeft M).map S.f)
        ((tensorLeft M).map S.g)).Exact := by
    -- The chosen five-arrow prefix is exactly the transported source-faithful exact row.
    exact Classical.choose_spec
      (tor_one_tensor_five_term_exact_of_shortExact (R := R) (M := M) (S := S) hS)
  let eδlast :
      (torTensorSixTermSequence M hS).δlast ≅
        ComposableArrows.mk₅
          ((torOne M).map S.f)
          ((torOne M).map S.g)
          δ
          ((tensorLeft M).map S.f)
          ((tensorLeft M).map S.g) := by
    refine ComposableArrows.isoMk₅ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ ?_
    · dsimp [torTensorSixTermSequence, δ]
      rfl
    · dsimp [torTensorSixTermSequence, δ]
      rfl
    · dsimp [torTensorSixTermSequence, δ]
      rfl
    · dsimp [torTensorSixTermSequence, δ]
      rfl
    · dsimp [torTensorSixTermSequence, δ]
      rfl
  have hδlast : (torTensorSixTermSequence M hS).δlast.Exact := by
    -- Replace the `δlast` normal form by the chosen public five-arrow row before using exactness.
    exact (ComposableArrows.exact_iff_of_iso eδlast).2 hPublicδlast
  -- Append the right-exact tensor tail `M ⊗ S.X₂ ⟶ M ⊗ S.X₃ ⟶ 0`.
  exact ComposableArrows.exact_of_δlast (torTensorSixTermSequence M hS) hδlast
    (tensorLeft_map_g_zero_exact M hS)

end ModuleCat

/- Lemma 10.75.2: for a short exact sequence `0 → N' → N → N'' → 0` of `R`-modules, the canonical
six-term row
`Tor₁^R(M, N') → Tor₁^R(M, N) → Tor₁^R(M, N'') → M ⊗[R] N' → M ⊗[R] N → M ⊗[R] N'' → 0`
is exact. In Lean, this source-facing sequence is formalized by
`ModuleCat.torTensorSixTermSequence_exact`. -/
recall ModuleCat.torTensorSixTermSequence_exact
