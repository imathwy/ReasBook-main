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
structure FirstVariableHorseshoeRow
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

/-- Helper for Lemma 10.75.2: the first-variable horseshoe boundary recursion consists of the
degree-zero lift into `S.X₂` together with the off-diagonal maps that make the biproduct
differential square to zero. -/
private structure FirstVariableHorseshoeBoundaryData
    (S : ShortComplex (ModuleCat R)) where
  /-- The degree-zero lift through the quotient map `S.g`. -/
  tau0 :
      (CategoryTheory.projectiveResolution S.X₃).complex.X 0 ⟶
        S.X₂
  /-- The off-diagonal matrix entries in the horseshoe differential. -/
  sigma :
      ∀ n,
        (CategoryTheory.projectiveResolution S.X₃).complex.X (n + 1) ⟶
          (CategoryTheory.projectiveResolution S.X₁).complex.X n
  /-- The chosen degree-zero lift maps to the augmentation of the right resolution. -/
  tau0_comp :
      tau0 ≫ S.g =
        (CategoryTheory.projectiveResolution S.X₃).π.f 0
  /-- The first off-diagonal map matches the degree-zero augmentation compatibility. -/
  sigma_zero_comp :
      sigma 0 ≫ (CategoryTheory.projectiveResolution S.X₁).π.f 0 ≫ S.f =
        -((CategoryTheory.projectiveResolution S.X₃).complex.d 1 0 ≫ tau0)
  /-- The higher off-diagonal maps make the matrix differential square to zero. -/
  sigma_succ_comp :
      ∀ n,
        sigma (n + 1) ≫
            (CategoryTheory.projectiveResolution S.X₁).complex.d (n + 1) n =
          -((CategoryTheory.projectiveResolution S.X₃).complex.d (n + 2) (n + 1) ≫
            sigma n)

/-- Helper for Lemma 10.75.2: the degree-zero augmentation of the right projective resolution
factors through the quotient map `S.g`. -/
private theorem first_variable_horseshoe_tau0_exists
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    ∃ tau0 : (CategoryTheory.projectiveResolution S.X₃).complex.X 0 ⟶ S.X₂,
      tau0 ≫ S.g = (CategoryTheory.projectiveResolution S.X₃).π.f 0 := by
  let P₃ : CategoryTheory.ProjectiveResolution S.X₃ :=
    CategoryTheory.projectiveResolution S.X₃
  let tau0 : P₃.complex.X 0 ⟶ S.X₂ :=
    @Projective.factorThru (ModuleCat R) _ (P₃.complex.X 0) S.X₃ S.X₂
      inferInstance (P₃.π.f 0) S.g hS.epi_g
  refine ⟨tau0, ?_⟩
  -- The factorization equation is the defining property of `Projective.factorThru`.
  change tau0 ≫ S.g = P₃.π.f 0
  simpa [tau0] using
    @Projective.factorThru_comp (ModuleCat R) _ (P₃.complex.X 0) S.X₃ S.X₂
      inferInstance (P₃.π.f 0) S.g hS.epi_g

/-- Helper for Lemma 10.75.2: once the degree-zero lift `tau0` is fixed, the first off-diagonal
map `sigma 0` is obtained by lifting the initial obstruction through `S.f` and then factoring
through the augmentation of the left projective resolution. -/
private theorem first_variable_horseshoe_sigma_zero_exists
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (tau0 : (CategoryTheory.projectiveResolution S.X₃).complex.X 0 ⟶ S.X₂)
    (htau0 : tau0 ≫ S.g = (CategoryTheory.projectiveResolution S.X₃).π.f 0) :
    ∃ sigma0 :
        (CategoryTheory.projectiveResolution S.X₃).complex.X 1 ⟶
          (CategoryTheory.projectiveResolution S.X₁).complex.X 0,
      sigma0 ≫ (CategoryTheory.projectiveResolution S.X₁).π.f 0 ≫ S.f =
        -((CategoryTheory.projectiveResolution S.X₃).complex.d 1 0 ≫ tau0) := by
  let P₁ : CategoryTheory.ProjectiveResolution S.X₁ :=
    CategoryTheory.projectiveResolution S.X₁
  let P₃ : CategoryTheory.ProjectiveResolution S.X₃ :=
    CategoryTheory.projectiveResolution S.X₃
  let u0 : P₃.complex.X 1 ⟶ S.X₁ :=
    hS.exact.liftFromProjective
      (-((P₃.complex.d 1 0) ≫ tau0))
      (by
        -- The first obstruction dies after `S.g` because `tau0` lifts the augmentation.
        rw [Preadditive.neg_comp, Category.assoc, htau0]
        simpa [Category.assoc] using P₃.complex_d_comp_π_f_zero)
  have hP₁Epi : Epi (P₁.π.f 0) := by
    infer_instance
  let sigma0 : P₃.complex.X 1 ⟶ P₁.complex.X 0 :=
    @Projective.factorThru (ModuleCat R) _ (P₃.complex.X 1) S.X₁ (P₁.complex.X 0)
      inferInstance u0 (P₁.π.f 0) hP₁Epi
  refine ⟨sigma0, ?_⟩
  -- The factorization through `P₁.π.f 0` reduces the claim to the defining lift equation for `u0`.
  calc
    sigma0 ≫ P₁.π.f 0 ≫ S.f = u0 ≫ S.f := by
      have hfactor : sigma0 ≫ P₁.π.f 0 = u0 := by
        simpa [sigma0] using
          @Projective.factorThru_comp (ModuleCat R) _ (P₃.complex.X 1) S.X₁ (P₁.complex.X 0)
            inferInstance u0 (P₁.π.f 0) hP₁Epi
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ S.f) hfactor
    _ = -((P₃.complex.d 1 0) ≫ tau0) := by
      simpa [u0] using hS.exact.liftFromProjective_comp
        (-((P₃.complex.d 1 0) ≫ tau0))
        (by
          simpa [Preadditive.neg_comp, Category.assoc, htau0] using
            P₃.complex_d_comp_π_f_zero)

/-- Helper for Lemma 10.75.2: after `sigma 0` is fixed, exactness of the left resolution in
degree `0` lifts the first successor `sigma 1`. -/
private theorem first_variable_horseshoe_sigma_one_exists
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (tau0 : (CategoryTheory.projectiveResolution S.X₃).complex.X 0 ⟶ S.X₂)
    (_htau0 : tau0 ≫ S.g = (CategoryTheory.projectiveResolution S.X₃).π.f 0)
    (sigma0 : (CategoryTheory.projectiveResolution S.X₃).complex.X 1 ⟶
      (CategoryTheory.projectiveResolution S.X₁).complex.X 0)
    (hsigma0 : sigma0 ≫ (CategoryTheory.projectiveResolution S.X₁).π.f 0 ≫ S.f =
      -((CategoryTheory.projectiveResolution S.X₃).complex.d 1 0 ≫ tau0)) :
    ∃ sigma1 :
        (CategoryTheory.projectiveResolution S.X₃).complex.X 2 ⟶
          (CategoryTheory.projectiveResolution S.X₁).complex.X 1,
      sigma1 ≫ (CategoryTheory.projectiveResolution S.X₁).complex.d 1 0 =
        -((CategoryTheory.projectiveResolution S.X₃).complex.d 2 1 ≫ sigma0) := by
  let P₁ : CategoryTheory.ProjectiveResolution S.X₁ :=
    CategoryTheory.projectiveResolution S.X₁
  let P₃ : CategoryTheory.ProjectiveResolution S.X₃ :=
    CategoryTheory.projectiveResolution S.X₃
  letI : Projective (P₃.complex.X 2) := P₃.projective 2
  letI : Mono S.f := hS.mono_f
  have hcycle :
      (-(P₃.complex.d 2 1 ≫ sigma0)) ≫ P₁.π.f 0 = 0 := by
    apply (cancel_mono S.f).1
    -- The first obstruction becomes a cycle after postcomposing with `S.f`; exactness at
    -- `P₁.complex.X 0` then allows the degree-`1` lift.
    have hstep₁ :
        (-(P₃.complex.d 2 1 ≫ sigma0)) ≫ P₁.π.f 0 ≫ S.f =
          ((-(P₃.complex.d 2 1)) ≫ sigma0) ≫ P₁.π.f 0 ≫ S.f := by
      simp [Preadditive.neg_comp]
    have hstep₂ :
        ((-(P₃.complex.d 2 1)) ≫ sigma0) ≫ P₁.π.f 0 ≫ S.f =
          P₃.complex.d 2 1 ≫ P₃.complex.d 1 0 ≫ tau0 := by
      simpa only [Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp, neg_neg] using
        congrArg (fun k ↦ (-(P₃.complex.d 2 1)) ≫ k) hsigma0
    exact hstep₁.trans <| hstep₂.trans <| by
      rw [← Category.assoc, P₃.complex.d_comp_d 2 1 0, zero_comp]
      exact Eq.symm (show (0 : P₃.complex.X 2 ⟶ S.X₁) ≫ S.f = 0 by simp)
  refine ⟨P₁.exact₀.liftFromProjective (-(P₃.complex.d 2 1 ≫ sigma0)) hcycle, ?_⟩
  -- The lifted morphism satisfies the required differential identity by construction.
  simpa using P₁.exact₀.liftFromProjective_comp (-(P₃.complex.d 2 1 ≫ sigma0)) hcycle

/-- Helper for Lemma 10.75.2: once two consecutive off-diagonal terms are fixed, exactness of the
left resolution in positive degrees lifts the next successor term. -/
private theorem first_variable_horseshoe_sigma_succ_exists
    {S : ShortComplex (ModuleCat R)} (n : ℕ)
    (sigma_n :
      (CategoryTheory.projectiveResolution S.X₃).complex.X (n + 1) ⟶
        (CategoryTheory.projectiveResolution S.X₁).complex.X n)
    (sigma_succ :
      (CategoryTheory.projectiveResolution S.X₃).complex.X (n + 2) ⟶
        (CategoryTheory.projectiveResolution S.X₁).complex.X (n + 1))
    (hsigma_succ :
      sigma_succ ≫ (CategoryTheory.projectiveResolution S.X₁).complex.d (n + 1) n =
        -((CategoryTheory.projectiveResolution S.X₃).complex.d (n + 2) (n + 1) ≫ sigma_n)) :
    ∃ sigma_next :
        (CategoryTheory.projectiveResolution S.X₃).complex.X (n + 3) ⟶
          (CategoryTheory.projectiveResolution S.X₁).complex.X (n + 2),
      sigma_next ≫ (CategoryTheory.projectiveResolution S.X₁).complex.d (n + 2) (n + 1) =
        -((CategoryTheory.projectiveResolution S.X₃).complex.d (n + 3) (n + 2) ≫ sigma_succ) := by
  let P₁ : CategoryTheory.ProjectiveResolution S.X₁ :=
    CategoryTheory.projectiveResolution S.X₁
  let P₃ : CategoryTheory.ProjectiveResolution S.X₃ :=
    CategoryTheory.projectiveResolution S.X₃
  letI : Projective (P₃.complex.X (n + 3)) := P₃.projective (n + 3)
  have hcycle :
      (-(P₃.complex.d (n + 3) (n + 2) ≫ sigma_succ)) ≫ P₁.complex.d (n + 1) n = 0 := by
    -- The successor obstruction is a cycle because both complexes square to zero.
    have hstep₁ :
        (-(P₃.complex.d (n + 3) (n + 2) ≫ sigma_succ)) ≫ P₁.complex.d (n + 1) n =
          ((-(P₃.complex.d (n + 3) (n + 2))) ≫ sigma_succ) ≫ P₁.complex.d (n + 1) n := by
      simp [Preadditive.neg_comp]
    have hstep₂ :
        ((-(P₃.complex.d (n + 3) (n + 2))) ≫ sigma_succ) ≫ P₁.complex.d (n + 1) n =
          P₃.complex.d (n + 3) (n + 2) ≫ P₃.complex.d (n + 2) (n + 1) ≫ sigma_n := by
      simpa only [Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp, neg_neg] using
        congrArg (fun k ↦ (-(P₃.complex.d (n + 3) (n + 2))) ≫ k) hsigma_succ
    exact hstep₁.trans <| hstep₂.trans <| by
      rw [← Category.assoc, P₃.complex.d_comp_d (n + 3) (n + 2) (n + 1), zero_comp]
  refine ⟨(P₁.exact_succ n).liftFromProjective
    (-(P₃.complex.d (n + 3) (n + 2) ≫ sigma_succ)) hcycle, ?_⟩
  -- Exactness in positive degrees gives the lifted equality directly.
  simpa using
    (P₁.exact_succ n).liftFromProjective_comp
      (-(P₃.complex.d (n + 3) (n + 2) ≫ sigma_succ)) hcycle

private theorem first_variable_horseshoe_boundary_data_nonempty_of_shortExact
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    Nonempty (FirstVariableHorseshoeBoundaryData (R := R) S) := by
  let P₁ : CategoryTheory.ProjectiveResolution S.X₁ :=
    CategoryTheory.projectiveResolution S.X₁
  let P₃ : CategoryTheory.ProjectiveResolution S.X₃ :=
    CategoryTheory.projectiveResolution S.X₃
  obtain ⟨tau0, htau0⟩ := first_variable_horseshoe_tau0_exists (R := R) hS
  obtain ⟨sigma0, hsigma0⟩ :=
    first_variable_horseshoe_sigma_zero_exists (R := R) hS tau0 htau0
  obtain ⟨sigma1, hsigma1⟩ :=
    first_variable_horseshoe_sigma_one_exists (R := R) hS tau0 htau0 sigma0 hsigma0
  let StepData : ℕ → Type _ := fun n =>
    Σ' sigma_n : P₃.complex.X (n + 1) ⟶ P₁.complex.X n,
      Σ' sigma_succ : P₃.complex.X (n + 2) ⟶ P₁.complex.X (n + 1),
        sigma_succ ≫ P₁.complex.d (n + 1) n =
          -((P₃.complex.d (n + 2) (n + 1)) ≫ sigma_n)
  let step : ∀ n, StepData n → StepData (n + 1)
    | n, ⟨sigma_n, sigma_succ, hsigma_succ⟩ =>
        let hsigma_next_exists :=
          first_variable_horseshoe_sigma_succ_exists
            (R := R) (S := S) n sigma_n sigma_succ hsigma_succ
        let sigma_next := Classical.choose hsigma_next_exists
        let hsigma_next := Classical.choose_spec hsigma_next_exists
        ⟨sigma_succ, sigma_next, hsigma_next⟩
  let data : ∀ n, StepData n :=
    Nat.rec ⟨sigma0, sigma1, hsigma1⟩ step
  let sigma :
      ∀ n, P₃.complex.X (n + 1) ⟶ P₁.complex.X n
    | 0 => sigma0
    | n + 1 => (data n).2.1
  have hsigma_zero_comp :
      sigma 0 ≫ P₁.π.f 0 ≫ S.f = -((P₃.complex.d 1 0) ≫ tau0) := by
    -- The degree-zero compatibility is exactly the defining property of `sigma 0`.
    simpa [sigma] using hsigma0
  have hsigma_succ_comp :
      ∀ n,
        sigma (n + 1) ≫ P₁.complex.d (n + 1) n =
          -((P₃.complex.d (n + 2) (n + 1)) ≫ sigma n) := by
    intro n
    cases n with
    | zero =>
        -- The first successor is the separately constructed `sigma 1`.
        simpa [sigma, data] using hsigma1
    | succ n =>
        -- After that, the pair recursion shifts the previously constructed successor forward.
        simpa [sigma, data, step] using (data (n + 1)).2.2
  -- Route correction: the blocker was the infinite `sigma` recursion; the source-faithful pair
  -- recursion now packages exactly the degree-zero lift and all successor lifts.
  exact ⟨⟨tau0, sigma, htau0, hsigma_zero_comp, hsigma_succ_comp⟩⟩

/-- Helper for Lemma 10.75.2: extract the horseshoe boundary recursion from the existence proof. -/
private noncomputable def first_variable_horseshoe_boundary_data_of_shortExact
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    FirstVariableHorseshoeBoundaryData (R := R) S :=
  Classical.choice
    (first_variable_horseshoe_boundary_data_nonempty_of_shortExact (R := R) hS)

/-- Helper for Lemma 10.75.2: the source-faithful horseshoe differential on the middle
degreewise biproduct terms is the usual upper-triangular matrix with diagonal entries coming from
the two outer resolutions and off-diagonal entry `sigma`. -/
private noncomputable abbrev first_variable_horseshoe_middle_d
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) (n : ℕ) :
    ((CategoryTheory.projectiveResolution S.X₁).complex.X (n + 1) ⊞
        (CategoryTheory.projectiveResolution S.X₃).complex.X (n + 1)) ⟶
      ((CategoryTheory.projectiveResolution S.X₁).complex.X n ⊞
        (CategoryTheory.projectiveResolution S.X₃).complex.X n) :=
  let P₁ : CategoryTheory.ProjectiveResolution S.X₁ :=
    CategoryTheory.projectiveResolution S.X₁
  let P₃ : CategoryTheory.ProjectiveResolution S.X₃ :=
    CategoryTheory.projectiveResolution S.X₃
  biprod.desc
    (P₁.complex.d (n + 1) n ≫ biprod.inl)
    (B.sigma n ≫ biprod.inl + P₃.complex.d (n + 1) n ≫ biprod.inr)

/-- Helper for Lemma 10.75.2: the source horseshoe differential squares to zero on the concrete
degreewise biproduct middle object. -/
private theorem first_variable_horseshoe_middle_d_comp_d
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) (n : ℕ) :
    first_variable_horseshoe_middle_d (R := R) B (n + 1) ≫
        first_variable_horseshoe_middle_d (R := R) B n =
      0 := by
  let P₁ : CategoryTheory.ProjectiveResolution S.X₁ :=
    CategoryTheory.projectiveResolution S.X₁
  let P₃ : CategoryTheory.ProjectiveResolution S.X₃ :=
    CategoryTheory.projectiveResolution S.X₃
  -- Read the matrix equation on the left and right source summands separately.
  apply biprod.hom_ext'
  · -- On the left summand only the left differential survives, so `d ∘ d = 0` comes from `P₁`.
    apply biprod.hom_ext
    · simpa [first_variable_horseshoe_middle_d, Category.assoc, Preadditive.comp_add,
        Preadditive.add_comp] using
        P₁.complex.d_comp_d (n + 2) (n + 1) n
    · simp [first_variable_horseshoe_middle_d, Category.assoc, Preadditive.comp_add,
        Preadditive.add_comp]
  · -- On the right summand the upper-right entry is exactly the `sigma` recursion.
    apply biprod.hom_ext
    · simp [first_variable_horseshoe_middle_d, Category.assoc, Preadditive.comp_add,
        Preadditive.add_comp, B.sigma_succ_comp n]
    · simpa [first_variable_horseshoe_middle_d, Category.assoc, Preadditive.comp_add,
        Preadditive.add_comp] using
        P₃.complex.d_comp_d (n + 2) (n + 1) n

/-- Helper for Lemma 10.75.2: the concrete middle horseshoe complex is the literal degreewise
biproduct of the two outer resolutions equipped with the triangular differential above. -/
private noncomputable def first_variable_horseshoe_middle_complex
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    ChainComplex (ModuleCat R) ℕ :=
  let P₁ : CategoryTheory.ProjectiveResolution S.X₁ :=
    CategoryTheory.projectiveResolution S.X₁
  let P₃ : CategoryTheory.ProjectiveResolution S.X₃ :=
    CategoryTheory.projectiveResolution S.X₃
  ChainComplex.of
    (fun n ↦ P₁.complex.X n ⊞ P₃.complex.X n)
    (first_variable_horseshoe_middle_d (R := R) B)
    (first_variable_horseshoe_middle_d_comp_d (R := R) B)

/-- Helper for Lemma 10.75.2: the left outer resolution includes into the middle horseshoe
complex as the first direct summand in every degree. -/
private noncomputable def first_variable_horseshoe_middle_iota
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    (CategoryTheory.projectiveResolution S.X₁).complex ⟶
      first_variable_horseshoe_middle_complex (R := R) B where
  f n := biprod.inl
  comm' i j hij := by
    obtain rfl : i = j + 1 := by
      simpa using hij.symm
    -- The triangular differential restricts to the left differential on the left summand.
    simp [first_variable_horseshoe_middle_complex, first_variable_horseshoe_middle_d,
      Category.assoc, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Lemma 10.75.2: the middle horseshoe complex projects to the right outer resolution
by forgetting the left direct summand in every degree. -/
private noncomputable def first_variable_horseshoe_middle_pi
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    first_variable_horseshoe_middle_complex (R := R) B ⟶
      (CategoryTheory.projectiveResolution S.X₃).complex where
  f n := biprod.snd
  comm' i j hij := by
    obtain rfl : i = j + 1 := by
      simpa using hij.symm
    -- Projecting away the left summand leaves exactly the right differential.
    apply biprod.hom_ext'
    · simp [first_variable_horseshoe_middle_complex, first_variable_horseshoe_middle_d,
        Category.assoc, Preadditive.comp_add, Preadditive.add_comp]
    · simp [first_variable_horseshoe_middle_complex, first_variable_horseshoe_middle_d,
        Category.assoc, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Lemma 10.75.2: the degree-zero augmentation on the middle horseshoe complex is the
obvious map induced by the left augmentation and the chosen lift `tau0`. -/
private theorem first_variable_horseshoe_middle_piK_d_zero
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    first_variable_horseshoe_middle_d (R := R) B 0 ≫
        biprod.desc
          ((CategoryTheory.projectiveResolution S.X₁).π.f 0 ≫ S.f)
          B.tau0 =
      0 := by
  let P₁ : CategoryTheory.ProjectiveResolution S.X₁ :=
    CategoryTheory.projectiveResolution S.X₁
  let P₃ : CategoryTheory.ProjectiveResolution S.X₃ :=
    CategoryTheory.projectiveResolution S.X₃
  -- Evaluate the matrix differential on the two source summands separately.
  apply biprod.hom_ext'
  · -- On the left summand we recover the usual augmentation identity of `P₁`.
    have hLeft : P₁.complex.d 1 0 ≫ P₁.π.f 0 ≫ S.f = 0 := by
      have hLeft' : P₁.complex.d 1 0 ≫ P₁.π.f 0 ≫ S.f = 0 ≫ S.f :=
        P₁.complex_d_comp_π_f_zero_assoc S.f
      simpa using hLeft'
    simpa [first_variable_horseshoe_middle_d, Category.assoc] using hLeft
  · -- On the right summand the defining relation for `sigma 0` makes the two terms cancel.
    have hRight : B.sigma 0 ≫ P₁.π.f 0 ≫ S.f + P₃.complex.d 1 0 ≫ B.tau0 = 0 := by
      rw [B.sigma_zero_comp]
      exact neg_add_cancel _
    simpa [first_variable_horseshoe_middle_d, Category.assoc, Preadditive.add_comp] using hRight

/-- Helper for Lemma 10.75.2: the augmentation of the middle horseshoe complex is the chain map
to `single₀ S.X₂` determined by the degree-zero boundary data. -/
private noncomputable def first_variable_horseshoe_middle_piK
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    first_variable_horseshoe_middle_complex (R := R) B ⟶
      (ChainComplex.single₀ (ModuleCat R)).obj S.X₂ :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨biprod.desc
        ((CategoryTheory.projectiveResolution S.X₁).π.f 0 ≫ S.f)
        B.tau0,
      first_variable_horseshoe_middle_piK_d_zero (R := R) B⟩

/-- Helper for Lemma 10.75.2: the two comparison maps in the concrete horseshoe row still compose
to zero because `biprod.inl ≫ biprod.snd = 0` degreewise. -/
private theorem first_variable_horseshoe_middle_zero
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    first_variable_horseshoe_middle_iota (R := R) B ≫
        first_variable_horseshoe_middle_pi (R := R) B =
      0 := by
  -- Compare components degreewise; each one is exactly `biprod.inl ≫ biprod.snd = 0`.
  ext n x
  change
    ((biprod.snd :
      (CategoryTheory.projectiveResolution S.X₁).complex.X n ⊞
        (CategoryTheory.projectiveResolution S.X₃).complex.X n ⟶
          (CategoryTheory.projectiveResolution S.X₃).complex.X n).hom)
      (((biprod.inl :
        (CategoryTheory.projectiveResolution S.X₁).complex.X n ⟶
          (CategoryTheory.projectiveResolution S.X₁).complex.X n ⊞
            (CategoryTheory.projectiveResolution S.X₃).complex.X n).hom) x) = 0
  have hzero :
      (biprod.inl :
        (CategoryTheory.projectiveResolution S.X₁).complex.X n ⟶
          (CategoryTheory.projectiveResolution S.X₁).complex.X n ⊞
            (CategoryTheory.projectiveResolution S.X₃).complex.X n) ≫
          (biprod.snd :
            (CategoryTheory.projectiveResolution S.X₁).complex.X n ⊞
              (CategoryTheory.projectiveResolution S.X₃).complex.X n ⟶
                (CategoryTheory.projectiveResolution S.X₃).complex.X n) =
        0 := by
    simp
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hzero) x

/-- Helper for Lemma 10.75.2: the left comparison map intertwines the middle augmentation with
the original inclusion `S.f`. -/
private theorem first_variable_horseshoe_middle_iota_augment
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    first_variable_horseshoe_middle_iota (R := R) B ≫
        first_variable_horseshoe_middle_piK (R := R) B =
      (CategoryTheory.projectiveResolution S.X₁).π ≫
        (ChainComplex.single₀ (ModuleCat R)).map S.f := by
  -- Pass to degree `0`, where the left summand of the biproduct augmentation is the obvious map.
  apply HomologicalComplex.to_single_hom_ext
  change
    biprod.inl ≫
        biprod.desc ((CategoryTheory.projectiveResolution S.X₁).π.f 0 ≫ S.f) B.tau0 =
      (CategoryTheory.projectiveResolution S.X₁).π.f 0 ≫ S.f
  simp

/-- Helper for Lemma 10.75.2: the right comparison map intertwines the middle augmentation with
the original quotient map `S.g`. -/
private theorem first_variable_horseshoe_middle_pi_augment
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    first_variable_horseshoe_middle_pi (R := R) B ≫
        (CategoryTheory.projectiveResolution S.X₃).π =
      first_variable_horseshoe_middle_piK (R := R) B ≫
        (ChainComplex.single₀ (ModuleCat R)).map S.g := by
  -- Reduce to degree `0`; the left summand dies by `S.zero`, and the right one is `tau0_comp`.
  apply HomologicalComplex.to_single_hom_ext
  change
    biprod.snd ≫ (CategoryTheory.projectiveResolution S.X₃).π.f 0 =
      biprod.desc ((CategoryTheory.projectiveResolution S.X₁).π.f 0 ≫ S.f) B.tau0 ≫ S.g
  refine biprod.hom_ext' _ _ ?_ ?_
  · simp [Category.assoc, S.zero]
  · simpa [Category.assoc] using B.tau0_comp.symm

/-- Helper for Lemma 10.75.2: each degree of the concrete middle row is the canonical split short
complex `X₁ ⟶ X₁ ⊞ X₃ ⟶ X₃`. -/
private noncomputable abbrev first_variable_horseshoe_middle_split
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) (n : ℕ) :
    (ShortComplex.mk
      ((first_variable_horseshoe_middle_iota (R := R) B).f n)
      ((first_variable_horseshoe_middle_pi (R := R) B).f n)
      (by
        simpa [first_variable_horseshoe_middle_iota, first_variable_horseshoe_middle_pi] using
          congr_fun (congrArg HomologicalComplex.Hom.f
            (first_variable_horseshoe_middle_zero (R := R) B)) n)).Splitting :=
  ShortComplex.Splitting.ofHasBinaryBiproduct
    ((CategoryTheory.projectiveResolution S.X₁).complex.X n)
    ((CategoryTheory.projectiveResolution S.X₃).complex.X n)

/-- Helper for Lemma 10.75.2: the explicit biproduct middle row is short exact as a short complex
of chain complexes because it is degreewise split exact. -/
private theorem first_variable_horseshoe_middle_row_shortExact
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    (ShortComplex.mk
      (first_variable_horseshoe_middle_iota (R := R) B)
      (first_variable_horseshoe_middle_pi (R := R) B)
      (first_variable_horseshoe_middle_zero (R := R) B)).ShortExact := by
  -- Repackage the degreewise splittings as exactness of a row of chain complexes.
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ ?_
  intro n
  exact (first_variable_horseshoe_middle_split (R := R) B n).shortExact

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

/-- Helper for Lemma 10.75.2: in positive degrees the middle horseshoe complex is exact because
the degreewise split horseshoe row induces an exact row on homology, and the outer homology groups
vanish there. -/
private theorem first_variable_horseshoe_middle_exactAt_succ
    {S : ShortComplex (ModuleCat R)} (_hS : S.ShortExact)
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) (n : ℕ) :
    (first_variable_horseshoe_middle_complex (R := R) B).ExactAt (n + 1) := by
  let K := first_variable_horseshoe_middle_complex (R := R) B
  have h₁ :
      (CategoryTheory.projectiveResolution S.X₁).complex.ExactAt (n + 1) := by
    simpa using (CategoryTheory.projectiveResolution S.X₁).complex_exactAt_succ n
  have h₃ :
      (CategoryTheory.projectiveResolution S.X₃).complex.ExactAt (n + 1) := by
    simpa using (CategoryTheory.projectiveResolution S.X₃).complex_exactAt_succ n
  have h₁_zero :
      IsZero ((CategoryTheory.projectiveResolution S.X₁).complex.homology (n + 1)) :=
    h₁.isZero_homology
  have h₃_zero :
      IsZero ((CategoryTheory.projectiveResolution S.X₃).complex.homology (n + 1)) :=
    h₃.isZero_homology
  have hExact :
      (ShortComplex.mk
        (HomologicalComplex.homologyMap (first_variable_horseshoe_middle_iota (R := R) B) (n + 1))
        (HomologicalComplex.homologyMap (first_variable_horseshoe_middle_pi (R := R) B) (n + 1))
        (by
          rw [← HomologicalComplex.homologyMap_comp,
            first_variable_horseshoe_middle_zero (R := R) B,
            HomologicalComplex.homologyMap_zero])).Exact := by
    simpa using (first_variable_horseshoe_middle_row_shortExact (R := R) B).homology_exact₂
      (n + 1)
  have hLeft :
      HomologicalComplex.homologyMap (first_variable_horseshoe_middle_iota (R := R) B) (n + 1) =
        0 :=
    h₁_zero.eq_of_src _ _
  have hRight :
      HomologicalComplex.homologyMap (first_variable_horseshoe_middle_pi (R := R) B) (n + 1) =
        0 :=
    h₃_zero.eq_of_tgt _ _
  -- Exactness is equivalent to vanishing homology, and the exact homology row has zero outer
  -- terms because the two outer projective resolutions are acyclic in positive degree.
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact hExact.isZero_X₂ hLeft hRight

/-- Helper for Lemma 10.75.2: the first differential of any projective resolution is exact
against its augmentation as a pair of linear maps. -/
private theorem projectiveResolution_exact_zero_function
    {X : ModuleCat R} (P : CategoryTheory.ProjectiveResolution X) :
    Function.Exact (P.complex.d 1 0).hom (P.π.f 0).hom := by
  -- Translate the categorical exactness owner theorem into the linear-map formulation used in the
  -- degree-zero horseshoe chase.
  simpa using (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀

/-- Helper for Lemma 10.75.2: the degree-`0` component of the middle augmentation is literally
the biproduct descent map `[π₀ ≫ S.f, tau0]`. -/
private theorem first_variable_horseshoe_middle_piK_f_zero
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    (first_variable_horseshoe_middle_piK (R := R) B).f 0 =
      biprod.desc
        ((CategoryTheory.projectiveResolution S.X₁).π.f 0 ≫ S.f)
        B.tau0 := by
  -- Unpack the chain map produced by `ChainComplex.toSingle₀Equiv` at degree `0`.
  simpa [first_variable_horseshoe_middle_piK] using
    (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
      (C := first_variable_horseshoe_middle_complex (R := R) B)
      (X := S.X₂)
      (f := biprod.desc
        ((CategoryTheory.projectiveResolution S.X₁).π.f 0 ≫ S.f)
        B.tau0)
      (hf := first_variable_horseshoe_middle_piK_d_zero (R := R) B))

/-- Helper for Lemma 10.75.2: a morphism out of a `ModuleCat` biproduct acts on an element by
applying the two summand maps and adding the results. -/
private theorem biprod_desc_hom_apply
    {A B C : ModuleCat R} (f : A ⟶ C) (g : B ⟶ C) (z : (A ⊞ B : ModuleCat R)) :
    (biprod.desc f g).hom z =
      f.hom ((biprod.fst : A ⊞ B ⟶ A).hom z) +
        g.hom ((biprod.snd : A ⊞ B ⟶ B).hom z) := by
  -- Expand the biproduct descent map into the sum of its two component maps.
  simpa [biprod.desc_eq, LinearMap.comp_apply, LinearMap.add_apply] using
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (biprod.desc_eq (f := f) (g := g))) z

/-- Helper for Lemma 10.75.2: evaluating the degree-`0` middle augmentation on a biproduct
element is the literal sum of its left and right component formulas. -/
private theorem first_variable_horseshoe_middle_piK_apply_zero
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S)
    (z : (first_variable_horseshoe_middle_complex (R := R) B).X 0) :
    ((first_variable_horseshoe_middle_piK (R := R) B).f 0).hom z =
      (((CategoryTheory.projectiveResolution S.X₁).π.f 0 ≫ S.f).hom
          ((biprod.fst :
              (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
                (CategoryTheory.projectiveResolution S.X₃).complex.X 0 ⟶
                  (CategoryTheory.projectiveResolution S.X₁).complex.X 0).hom z) +
        B.tau0.hom
          ((biprod.snd :
              (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
                (CategoryTheory.projectiveResolution S.X₃).complex.X 0 ⟶
                  (CategoryTheory.projectiveResolution S.X₃).complex.X 0).hom z)) := by
  -- Rewrite the augmentation once as the explicit biproduct descent map.
  rw [first_variable_horseshoe_middle_piK_f_zero (R := R) B]
  simpa using
    biprod_desc_hom_apply
      (((CategoryTheory.projectiveResolution S.X₁).π.f 0) ≫ S.f) B.tau0 z

/-- Helper for Lemma 10.75.2: a `ModuleCat` biproduct element is the sum of its left and right
components reinserted by `biprod.inl` and `biprod.inr`. -/
private theorem biprod_eta_apply
    {A B : ModuleCat R} (z : (A ⊞ B : ModuleCat R)) :
    (biprod.inl : A ⟶ A ⊞ B).hom ((biprod.fst : A ⊞ B ⟶ A).hom z) +
      (biprod.inr : B ⟶ A ⊞ B).hom ((biprod.snd : A ⊞ B ⟶ B).hom z) = z := by
  -- Reassemble the element from the binary biproduct total relation.
  change
    (((biprod.fst : A ⊞ B ⟶ A) ≫ (biprod.inl : A ⟶ A ⊞ B) +
        (biprod.snd : A ⊞ B ⟶ B) ≫ (biprod.inr : B ⟶ A ⊞ B)).hom z) = z
  simpa [LinearMap.comp_apply, LinearMap.add_apply] using
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (biprod.total (X := A) (Y := B))) z

/-- Helper for Lemma 10.75.2: the two biproduct projections recover the components of an element
written as `biprod.inl x + biprod.inr y`. -/
private theorem biprod_fst_snd_apply_inl_inr
    {A B : ModuleCat R} (x : A) (y : B) :
    (biprod.fst : A ⊞ B ⟶ A).hom
        ((biprod.inl : A ⟶ A ⊞ B).hom x + (biprod.inr : B ⟶ A ⊞ B).hom y) = x ∧
      (biprod.snd : A ⊞ B ⟶ B).hom
          ((biprod.inl : A ⟶ A ⊞ B).hom x + (biprod.inr : B ⟶ A ⊞ B).hom y) = y := by
  have hinl_fst :
      (biprod.fst : A ⊞ B ⟶ A).hom ((biprod.inl : A ⟶ A ⊞ B).hom x) = x := by
    change (((biprod.inl : A ⟶ A ⊞ B) ≫ (biprod.fst : A ⊞ B ⟶ A)).hom x) = x
    simpa using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (biprod.inl_fst (X := A) (Y := B))) x
  have hinr_fst :
      (biprod.fst : A ⊞ B ⟶ A).hom ((biprod.inr : B ⟶ A ⊞ B).hom y) = 0 := by
    change (((biprod.inr : B ⟶ A ⊞ B) ≫ (biprod.fst : A ⊞ B ⟶ A)).hom y) = 0
    simpa using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (biprod.inr_fst (X := A) (Y := B))) y
  have hinl_snd :
      (biprod.snd : A ⊞ B ⟶ B).hom ((biprod.inl : A ⟶ A ⊞ B).hom x) = 0 := by
    change (((biprod.inl : A ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B)).hom x) = 0
    simpa using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (biprod.inl_snd (X := A) (Y := B))) x
  have hinr_snd :
      (biprod.snd : A ⊞ B ⟶ B).hom ((biprod.inr : B ⟶ A ⊞ B).hom y) = y := by
    change (((biprod.inr : B ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B)).hom y) = y
    simpa using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (biprod.inr_snd (X := A) (Y := B))) y
  constructor
  · -- The first projection kills the right summand and keeps the left one.
    calc
      (biprod.fst : A ⊞ B ⟶ A).hom
          ((biprod.inl : A ⟶ A ⊞ B).hom x + (biprod.inr : B ⟶ A ⊞ B).hom y) =
          (biprod.fst : A ⊞ B ⟶ A).hom ((biprod.inl : A ⟶ A ⊞ B).hom x) +
            (biprod.fst : A ⊞ B ⟶ A).hom ((biprod.inr : B ⟶ A ⊞ B).hom y) := by
              simp [LinearMap.map_add]
      _ = x + 0 := by rw [hinl_fst, hinr_fst]
      _ = x := by simp
  · -- The second projection kills the left summand and keeps the right one.
    calc
      (biprod.snd : A ⊞ B ⟶ B).hom
          ((biprod.inl : A ⟶ A ⊞ B).hom x + (biprod.inr : B ⟶ A ⊞ B).hom y) =
          (biprod.snd : A ⊞ B ⟶ B).hom ((biprod.inl : A ⟶ A ⊞ B).hom x) +
            (biprod.snd : A ⊞ B ⟶ B).hom ((biprod.inr : B ⟶ A ⊞ B).hom y) := by
              simp [LinearMap.map_add]
      _ = 0 + y := by rw [hinl_snd, hinr_snd]
      _ = y := by simp

/-- Helper for Lemma 10.75.2: the degree-`0` horseshoe differential on an explicit biproduct
pair is the expected triangular matrix formula on the two components. -/
private theorem first_variable_horseshoe_middle_d_apply_pair
    {S : ShortComplex (ModuleCat R)}
    (B : FirstVariableHorseshoeBoundaryData (R := R) S)
    (y1 : (CategoryTheory.projectiveResolution S.X₁).complex.X 1)
    (y3 : (CategoryTheory.projectiveResolution S.X₃).complex.X 1) :
    (first_variable_horseshoe_middle_d (R := R) B 0).hom
        ((biprod.inl :
            (CategoryTheory.projectiveResolution S.X₁).complex.X 1 ⟶
              (CategoryTheory.projectiveResolution S.X₁).complex.X 1 ⊞
                (CategoryTheory.projectiveResolution S.X₃).complex.X 1).hom y1 +
          (biprod.inr :
            (CategoryTheory.projectiveResolution S.X₃).complex.X 1 ⟶
              (CategoryTheory.projectiveResolution S.X₁).complex.X 1 ⊞
                (CategoryTheory.projectiveResolution S.X₃).complex.X 1).hom y3) =
      (biprod.inl :
          (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⟶
            (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
              (CategoryTheory.projectiveResolution S.X₃).complex.X 0).hom
          (((CategoryTheory.projectiveResolution S.X₁).complex.d 1 0).hom y1 +
            (B.sigma 0).hom y3) +
        (biprod.inr :
          (CategoryTheory.projectiveResolution S.X₃).complex.X 0 ⟶
            (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
              (CategoryTheory.projectiveResolution S.X₃).complex.X 0).hom
          (((CategoryTheory.projectiveResolution S.X₃).complex.d 1 0).hom y3) := by
  let w :
      ((CategoryTheory.projectiveResolution S.X₁).complex.X 1 ⊞
        (CategoryTheory.projectiveResolution S.X₃).complex.X 1 : ModuleCat R) :=
    (biprod.inl :
        (CategoryTheory.projectiveResolution S.X₁).complex.X 1 ⟶
          (CategoryTheory.projectiveResolution S.X₁).complex.X 1 ⊞
            (CategoryTheory.projectiveResolution S.X₃).complex.X 1).hom y1 +
      (biprod.inr :
        (CategoryTheory.projectiveResolution S.X₃).complex.X 1 ⟶
          (CategoryTheory.projectiveResolution S.X₁).complex.X 1 ⊞
            (CategoryTheory.projectiveResolution S.X₃).complex.X 1).hom y3
  have hw :
      (biprod.fst :
          (CategoryTheory.projectiveResolution S.X₁).complex.X 1 ⊞
            (CategoryTheory.projectiveResolution S.X₃).complex.X 1 ⟶
              (CategoryTheory.projectiveResolution S.X₁).complex.X 1).hom w = y1 ∧
        (biprod.snd :
            (CategoryTheory.projectiveResolution S.X₁).complex.X 1 ⊞
              (CategoryTheory.projectiveResolution S.X₃).complex.X 1 ⟶
                (CategoryTheory.projectiveResolution S.X₃).complex.X 1).hom w = y3 :=
    by
      simpa [w] using
        biprod_fst_snd_apply_inl_inr (R := R) y1 y3
  -- Evaluate the triangular differential on the chosen biproduct element, then simplify the two
  -- projection terms using the cached component formulas above.
  calc
    (first_variable_horseshoe_middle_d (R := R) B 0).hom w =
        (((CategoryTheory.projectiveResolution S.X₁).complex.d 1 0) ≫
            (biprod.inl :
              (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⟶
                (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
                  (CategoryTheory.projectiveResolution S.X₃).complex.X 0)).hom
            ((biprod.fst :
                (CategoryTheory.projectiveResolution S.X₁).complex.X 1 ⊞
                  (CategoryTheory.projectiveResolution S.X₃).complex.X 1 ⟶
                    (CategoryTheory.projectiveResolution S.X₁).complex.X 1).hom w) +
          (((B.sigma 0) ≫
              (biprod.inl :
                (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⟶
                  (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
                    (CategoryTheory.projectiveResolution S.X₃).complex.X 0)) +
            ((CategoryTheory.projectiveResolution S.X₃).complex.d 1 0) ≫
              (biprod.inr :
                (CategoryTheory.projectiveResolution S.X₃).complex.X 0 ⟶
                  (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
                    (CategoryTheory.projectiveResolution S.X₃).complex.X 0)).hom
              ((biprod.snd :
                  (CategoryTheory.projectiveResolution S.X₁).complex.X 1 ⊞
                    (CategoryTheory.projectiveResolution S.X₃).complex.X 1 ⟶
                      (CategoryTheory.projectiveResolution S.X₃).complex.X 1).hom w) := by
          simpa [first_variable_horseshoe_middle_d, w] using
            biprod_desc_hom_apply
              (((CategoryTheory.projectiveResolution S.X₁).complex.d 1 0) ≫
                (biprod.inl :
                  (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⟶
                    (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
                      (CategoryTheory.projectiveResolution S.X₃).complex.X 0))
              (((B.sigma 0) ≫
                  (biprod.inl :
                    (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⟶
                      (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
                        (CategoryTheory.projectiveResolution S.X₃).complex.X 0)) +
                ((CategoryTheory.projectiveResolution S.X₃).complex.d 1 0) ≫
                  (biprod.inr :
                    (CategoryTheory.projectiveResolution S.X₃).complex.X 0 ⟶
                      (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
                        (CategoryTheory.projectiveResolution S.X₃).complex.X 0))
              w
    _ =
        (((CategoryTheory.projectiveResolution S.X₁).complex.d 1 0) ≫
            (biprod.inl :
              (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⟶
                (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
                  (CategoryTheory.projectiveResolution S.X₃).complex.X 0)).hom y1 +
          (((B.sigma 0) ≫
              (biprod.inl :
                (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⟶
                  (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
                    (CategoryTheory.projectiveResolution S.X₃).complex.X 0)) +
            ((CategoryTheory.projectiveResolution S.X₃).complex.d 1 0) ≫
              (biprod.inr :
                (CategoryTheory.projectiveResolution S.X₃).complex.X 0 ⟶
                  (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
                    (CategoryTheory.projectiveResolution S.X₃).complex.X 0)).hom y3 := by
          rw [hw.1, hw.2]
    _ =
        (biprod.inl :
            (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⟶
              (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
                (CategoryTheory.projectiveResolution S.X₃).complex.X 0).hom
            (((CategoryTheory.projectiveResolution S.X₁).complex.d 1 0).hom y1 +
              (B.sigma 0).hom y3) +
          (biprod.inr :
              (CategoryTheory.projectiveResolution S.X₃).complex.X 0 ⟶
                (CategoryTheory.projectiveResolution S.X₁).complex.X 0 ⊞
                  (CategoryTheory.projectiveResolution S.X₃).complex.X 0).hom
            (((CategoryTheory.projectiveResolution S.X₃).complex.d 1 0).hom y3) := by
          simp [LinearMap.comp_apply, LinearMap.map_add, LinearMap.add_apply, add_assoc]

/-- Helper for Lemma 10.75.2: a degree-`0` cycle in the middle horseshoe augmentation has right
component in the kernel of the right augmentation, hence lifts through `P₃.d 1 0`. -/
private theorem first_variable_horseshoe_middle_right_component_lift_zero
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    let K := first_variable_horseshoe_middle_complex (R := R) B
    let P₃ : CategoryTheory.ProjectiveResolution S.X₃ := CategoryTheory.projectiveResolution S.X₃
    ∀ {z : K.X 0}, ((first_variable_horseshoe_middle_piK (R := R) B).f 0).hom z = 0 →
      ∃ y3, (P₃.complex.d 1 0).hom y3 =
        ((first_variable_horseshoe_middle_pi (R := R) B).f 0).hom z := by
  dsimp
  let P₃ : CategoryTheory.ProjectiveResolution S.X₃ :=
    CategoryTheory.projectiveResolution S.X₃
  have hP₃Exact : Function.Exact (P₃.complex.d 1 0).hom (P₃.π.f 0).hom := by
    -- The right outer projective resolution is exact at degree `0`.
    exact projectiveResolution_exact_zero_function (R := R) P₃
  intro z hz
  have hker :
      (P₃.π.f 0).hom ((biprod.snd : _ ⟶ P₃.complex.X 0).hom z) = 0 := by
    -- Postcompose the kernel equation with `S.g` and rewrite via the augmentation comparison.
    have hz_g :
        S.g.hom (((first_variable_horseshoe_middle_piK (R := R) B).f 0).hom z) = S.g.hom 0 :=
      congrArg S.g.hom hz
    have haugment :
        (biprod.snd : _ ⟶ P₃.complex.X 0) ≫ P₃.π.f 0 =
          ((first_variable_horseshoe_middle_piK (R := R) B).f 0) ≫ S.g := by
      simpa [first_variable_horseshoe_middle_pi] using
        congr_fun
          (congrArg HomologicalComplex.Hom.f
            (first_variable_horseshoe_middle_pi_augment (R := R) B))
          0
    calc
      (P₃.π.f 0).hom ((biprod.snd : _ ⟶ P₃.complex.X 0).hom z) =
          S.g.hom (((first_variable_horseshoe_middle_piK (R := R) B).f 0).hom z) := by
            simpa [LinearMap.comp_apply] using
              LinearMap.congr_fun (congrArg ModuleCat.Hom.hom haugment) z
      _ = S.g.hom 0 := hz_g
      _ = 0 := by
            simpa using LinearMap.map_zero S.g.hom
  rcases (hP₃Exact _).mp hker with ⟨y3, hy3⟩
  refine ⟨y3, ?_⟩
  simpa [first_variable_horseshoe_middle_pi] using hy3

/-- Helper for Lemma 10.75.2: after correcting by `sigma 0`, the left component of a degree-`0`
cycle in the middle horseshoe augmentation lifts through `P₁.d 1 0`. -/
private theorem first_variable_horseshoe_middle_left_component_lift_zero
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    let K := first_variable_horseshoe_middle_complex (R := R) B
    let P₁ : CategoryTheory.ProjectiveResolution S.X₁ := CategoryTheory.projectiveResolution S.X₁
    let P₃ : CategoryTheory.ProjectiveResolution S.X₃ := CategoryTheory.projectiveResolution S.X₃
    ∀ {z : K.X 0} {y3 : P₃.complex.X 1},
      ((first_variable_horseshoe_middle_piK (R := R) B).f 0).hom z = 0 →
      (P₃.complex.d 1 0).hom y3 = ((first_variable_horseshoe_middle_pi (R := R) B).f 0).hom z →
      ∃ y1, (P₁.complex.d 1 0).hom y1 =
        ((biprod.fst : K.X 0 ⟶ P₁.complex.X 0).hom z) - (B.sigma 0).hom y3 := by
  dsimp
  let P₁ : CategoryTheory.ProjectiveResolution S.X₁ :=
    CategoryTheory.projectiveResolution S.X₁
  let P₃ : CategoryTheory.ProjectiveResolution S.X₃ :=
    CategoryTheory.projectiveResolution S.X₃
  have hP₁Exact : Function.Exact (P₁.complex.d 1 0).hom (P₁.π.f 0).hom := by
    -- The left outer projective resolution is exact at degree `0`.
    exact projectiveResolution_exact_zero_function (R := R) P₁
  have hf_inj : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective _).1 hS.mono_f
  intro z y3 hz hy3
  have hy3' :
      (P₃.complex.d 1 0).hom y3 =
        ((biprod.snd : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₃.complex.X 0).hom z) := by
    -- The right comparison map is literally the second projection in degree `0`.
    simpa [first_variable_horseshoe_middle_pi] using hy3
  have hsigma_eval :
      ((P₁.π.f 0 ≫ S.f).hom ((B.sigma 0).hom y3)) =
        -(B.tau0.hom ((biprod.snd : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₃.complex.X 0).hom z)) := by
    -- Evaluate the defining degree-zero `sigma` relation on `y3`.
    have hsigma0 :
        ((P₁.π.f 0 ≫ S.f).hom ((B.sigma 0).hom y3)) =
          (-((P₃.complex.d 1 0 ≫ B.tau0))).hom y3 := by
      simpa [LinearMap.comp_apply, Category.assoc] using
        LinearMap.congr_fun (congrArg ModuleCat.Hom.hom B.sigma_zero_comp) y3
    simpa [LinearMap.comp_apply, hy3'] using hsigma0
  have hkernel_sf :
      ((P₁.π.f 0 ≫ S.f).hom
        (((biprod.fst : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₁.complex.X 0).hom z) -
          (B.sigma 0).hom y3)) = 0 := by
    -- Rewrite the kernel equation for the middle augmentation into the corrected left component.
    have hz_explicit :
        ((P₁.π.f 0 ≫ S.f).hom
            ((biprod.fst : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₁.complex.X 0).hom z) +
          B.tau0.hom
            ((biprod.snd : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₃.complex.X 0).hom z)) = 0 := by
      calc
        ((P₁.π.f 0 ≫ S.f).hom
            ((biprod.fst : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₁.complex.X 0).hom z) +
          B.tau0.hom
            ((biprod.snd : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₃.complex.X 0).hom z)) =
            ((first_variable_horseshoe_middle_piK (R := R) B).f 0).hom z := by
              symm
              exact first_variable_horseshoe_middle_piK_apply_zero (R := R) B z
        _ = 0 := hz
    calc
      ((P₁.π.f 0 ≫ S.f).hom
          (((biprod.fst : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₁.complex.X 0).hom z) -
            (B.sigma 0).hom y3)) =
          (P₁.π.f 0 ≫ S.f).hom
              ((biprod.fst : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₁.complex.X 0).hom z) -
            (P₁.π.f 0 ≫ S.f).hom ((B.sigma 0).hom y3) := by
              simp
      _ =
          (P₁.π.f 0 ≫ S.f).hom
              ((biprod.fst : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₁.complex.X 0).hom z) +
            B.tau0.hom
              ((biprod.snd : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₃.complex.X 0).hom z) := by
              rw [hsigma_eval]
              abel
      _ = 0 := hz_explicit
  have hkernel :
      (P₁.π.f 0).hom
        (((biprod.fst : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₁.complex.X 0).hom z) -
          (B.sigma 0).hom y3) = 0 := by
    -- Cancel `S.f` using the monomorphism in the original short exact sequence.
    apply hf_inj
    calc
      S.f.hom
          ((P₁.π.f 0).hom
            (((biprod.fst : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₁.complex.X 0).hom z) -
              (B.sigma 0).hom y3)) =
          ((P₁.π.f 0 ≫ S.f).hom
            (((biprod.fst : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₁.complex.X 0).hom z) -
              (B.sigma 0).hom y3)) := by
            rfl
      _ = 0 := hkernel_sf
      _ = S.f.hom 0 := by simp
  rcases (hP₁Exact _).mp hkernel with ⟨y1, hy1⟩
  exact ⟨y1, hy1⟩

/-- Helper for Lemma 10.75.2: the degree-`0` augmentation exactness of the middle horseshoe
complex is the source-faithful two-step kernel chase on the biproduct term. -/
private theorem first_variable_horseshoe_middle_exact_zero_function
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    let K := first_variable_horseshoe_middle_complex (R := R) B
    let πK := first_variable_horseshoe_middle_piK (R := R) B
    Function.Exact (K.d 1 0).hom (πK.f 0).hom := by
  dsimp
  let P₁ : CategoryTheory.ProjectiveResolution S.X₁ :=
    CategoryTheory.projectiveResolution S.X₁
  let P₃ : CategoryTheory.ProjectiveResolution S.X₃ :=
    CategoryTheory.projectiveResolution S.X₃
  intro z
  constructor
  · intro hz
    obtain ⟨y3, hy3⟩ :=
      first_variable_horseshoe_middle_right_component_lift_zero (R := R) hS B hz
    obtain ⟨y1, hy1⟩ :=
      first_variable_horseshoe_middle_left_component_lift_zero (R := R) hS B hz hy3
    let w : (P₁.complex.X 1 ⊞ P₃.complex.X 1 : ModuleCat R) :=
      (biprod.inl : P₁.complex.X 1 ⟶ P₁.complex.X 1 ⊞ P₃.complex.X 1).hom y1 +
        (biprod.inr : P₃.complex.X 1 ⟶ P₁.complex.X 1 ⊞ P₃.complex.X 1).hom y3
    have hy3' :
        (P₃.complex.d 1 0).hom y3 =
          (biprod.snd : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₃.complex.X 0).hom z := by
      simpa [P₁, P₃, first_variable_horseshoe_middle_pi] using hy3
    have hleft :
        (P₁.complex.d 1 0).hom y1 + (B.sigma 0).hom y3 =
          (biprod.fst : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₁.complex.X 0).hom z := by
      rw [hy1]
      abel
    refine ⟨w, ?_⟩
    -- Route correction: rebuild the boundary from the lifted right component and the corrected
    -- left component, then reassemble the biproduct element with `biprod_eta_apply`.
    calc
      (first_variable_horseshoe_middle_d (R := R) B 0).hom w =
          (biprod.inl : P₁.complex.X 0 ⟶ P₁.complex.X 0 ⊞ P₃.complex.X 0).hom
              ((P₁.complex.d 1 0).hom y1 + (B.sigma 0).hom y3) +
            (biprod.inr : P₃.complex.X 0 ⟶ P₁.complex.X 0 ⊞ P₃.complex.X 0).hom
              ((P₃.complex.d 1 0).hom y3) := by
            simpa [P₁, P₃, w] using
              first_variable_horseshoe_middle_d_apply_pair (R := R) B y1 y3
      _ =
          (biprod.inl : P₁.complex.X 0 ⟶ P₁.complex.X 0 ⊞ P₃.complex.X 0).hom
              ((biprod.fst : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₁.complex.X 0).hom z) +
            (biprod.inr : P₃.complex.X 0 ⟶ P₁.complex.X 0 ⊞ P₃.complex.X 0).hom
              ((biprod.snd : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₃.complex.X 0).hom z) := by
            rw [hleft, hy3']
      _ = z := biprod_eta_apply z
  · rintro ⟨w, rfl⟩
    -- The augmentation is already a chain map to the degree-zero single complex, so every
    -- boundary maps to zero.
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom (first_variable_horseshoe_middle_piK_d_zero (R := R) B))
        w

/-- Helper for Lemma 10.75.2: the remaining degree-`0` work is to show that the explicit
augmentation `[π₀ ≫ S.f, tau0]` is exact and epi on the middle horseshoe complex. -/
private theorem first_variable_horseshoe_middle_exact_and_epi_zero
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (B : FirstVariableHorseshoeBoundaryData (R := R) S) :
    let K := first_variable_horseshoe_middle_complex (R := R) B
    let πK := first_variable_horseshoe_middle_piK (R := R) B
    (ShortComplex.mk (K.d 1 0) (πK.f 0) (by simpa using (πK.comm 1 0).symm)).Exact ∧
      Epi (πK.f 0) := by
  dsimp
  let P₁ : CategoryTheory.ProjectiveResolution S.X₁ :=
    CategoryTheory.projectiveResolution S.X₁
  let P₃ : CategoryTheory.ProjectiveResolution S.X₃ :=
    CategoryTheory.projectiveResolution S.X₃
  constructor
  · -- The degree-zero exactness package is exactly the function-level horseshoe chase above.
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 <|
      first_variable_horseshoe_middle_exact_zero_function (R := R) hS B
  · -- Surjectivity follows by the textbook element chase through the two outer augmentations.
    rw [ModuleCat.epi_iff_surjective]
    intro x2
    have hP₁Surj : Function.Surjective (P₁.π.f 0).hom := by
      exact (ModuleCat.epi_iff_surjective _).1 inferInstance
    have hP₃Surj : Function.Surjective (P₃.π.f 0).hom := by
      exact (ModuleCat.epi_iff_surjective _).1 inferInstance
    have hSExact : Function.Exact S.f.hom S.g.hom := by
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
    obtain ⟨y3, hy3⟩ := hP₃Surj (S.g.hom x2)
    have htau_eval : S.g.hom (B.tau0.hom y3) = S.g.hom x2 := by
      rw [show S.g.hom (B.tau0.hom y3) = (P₃.π.f 0).hom y3 by
            simpa [LinearMap.comp_apply] using
              LinearMap.congr_fun (congrArg ModuleCat.Hom.hom B.tau0_comp) y3]
      exact hy3
    have hker :
        S.g.hom (x2 - B.tau0.hom y3) = 0 := by
      calc
        S.g.hom (x2 - B.tau0.hom y3) =
            S.g.hom x2 - S.g.hom (B.tau0.hom y3) := by
              simp
        _ = 0 := by
              rw [htau_eval]
              abel
    obtain ⟨x1, hx1⟩ := (hSExact (x2 - B.tau0.hom y3)).mp hker
    obtain ⟨y1, hy1⟩ := hP₁Surj x1
    let w : (P₁.complex.X 0 ⊞ P₃.complex.X 0 : ModuleCat R) :=
      (biprod.inl : P₁.complex.X 0 ⟶ P₁.complex.X 0 ⊞ P₃.complex.X 0).hom y1 +
        (biprod.inr : P₃.complex.X 0 ⟶ P₁.complex.X 0 ⊞ P₃.complex.X 0).hom y3
    have hw :
        (biprod.fst : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₁.complex.X 0).hom w = y1 ∧
          (biprod.snd : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₃.complex.X 0).hom w = y3 := by
      simpa [w] using biprod_fst_snd_apply_inl_inr (R := R) y1 y3
    refine ⟨w, ?_⟩
    calc
      ((first_variable_horseshoe_middle_piK (R := R) B).f 0).hom w =
          ((P₁.π.f 0 ≫ S.f).hom
              ((biprod.fst : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₁.complex.X 0).hom w) +
            B.tau0.hom
              ((biprod.snd : P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ P₃.complex.X 0).hom w)) := by
            exact first_variable_horseshoe_middle_piK_apply_zero (R := R) B w
      _ = (P₁.π.f 0 ≫ S.f).hom y1 + B.tau0.hom y3 := by
            rw [hw.1, hw.2]
      _ = S.f.hom ((P₁.π.f 0).hom y1) + B.tau0.hom y3 := by
            rfl
      _ = S.f.hom x1 + B.tau0.hom y3 := by
            rw [hy1]
      _ = (x2 - B.tau0.hom y3) + B.tau0.hom y3 := by
            rw [hx1]
      _ = x2 := by
            abel

/-- Helper for Lemma 10.75.2: the only remaining source-faithful blocker is now the
quasi-isomorphism of the explicit middle augmentation. The concrete middle row, augmentation, and
degreewise splittings are already fixed above. -/
private theorem first_variable_horseshoe_middle_quasiIso
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    QuasiIso
      (first_variable_horseshoe_middle_piK (R := R)
        (first_variable_horseshoe_boundary_data_of_shortExact (R := R) hS)) := by
  let B := first_variable_horseshoe_boundary_data_of_shortExact (R := R) hS
  let K := first_variable_horseshoe_middle_complex (R := R) B
  let πK := first_variable_horseshoe_middle_piK (R := R) B
  have hzero : K.d 1 0 ≫ πK.f 0 = 0 := by
    -- The augmentation is already a chain map, so the degree-zero short complex is well-defined.
    simpa using (πK.comm 1 0).symm
  let T : ShortComplex (ModuleCat R) := ShortComplex.mk (K.d 1 0) (πK.f 0) hzero
  have hT : T.Exact ∧ Epi T.g :=
    first_variable_horseshoe_middle_exact_and_epi_zero (R := R) hS B
  have hcomm₁₂ : (Iso.refl T.X₁).hom ≫ (K.d 1 0) = T.f ≫ (Iso.refl T.X₂).hom := by
    simp [T]
  have hcomm₂₃ :
      (Iso.refl T.X₂).hom ≫ (πK.f 0) =
        T.g ≫ (Iso.refl T.X₃).hom := by
    simp [T]
  let e : T ≅ ShortComplex.mk (K.d 1 0) (πK.f 0) hzero :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) hcomm₁₂ hcomm₂₃
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
      -- Degree `0` is exactly the explicit short-complex exactness-and-epi package above.
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · exact (ShortComplex.exact_and_epi_g_iff_of_iso e).2 hT
      all_goals rfl
  | succ n =>
      -- In positive degrees the middle complex is exact and the single complex has zero homology.
      rw [quasiIsoAt_iff_exactAt']
      · simpa [K] using first_variable_horseshoe_middle_exactAt_succ (R := R) hS B n
      · apply ChainComplex.exactAt_succ_single_obj

/-- Helper for Lemma 10.75.2: isolate the source-faithful blocker as the concrete middle
horseshoe complex together with its augmentation and the degreewise splittings. -/
private noncomputable def first_variable_horseshoe_complex_data_of_shortExact
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    FirstVariableHorseshoeComplexData (R := R) S :=
  let B := first_variable_horseshoe_boundary_data_of_shortExact (R := R) hS
  { K := first_variable_horseshoe_middle_complex (R := R) B
    πK := first_variable_horseshoe_middle_piK (R := R) B
    iota := first_variable_horseshoe_middle_iota (R := R) B
    pi := first_variable_horseshoe_middle_pi (R := R) B
    zero := first_variable_horseshoe_middle_zero (R := R) B
    iota_augment := first_variable_horseshoe_middle_iota_augment (R := R) B
    pi_augment := first_variable_horseshoe_middle_pi_augment (R := R) B
    split := first_variable_horseshoe_middle_split (R := R) B
    quasiIso_πK := first_variable_horseshoe_middle_quasiIso (R := R) hS }

/-- Helper for Lemma 10.75.2: once the concrete horseshoe data are fixed, the only remaining
source-faithful structural claim is that its augmentation is a quasi-isomorphism. -/
private theorem first_variable_horseshoe_complex_quasiIso
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    QuasiIso (first_variable_horseshoe_complex_data_of_shortExact (R := R) hS).πK := by
  -- The remaining source-faithful work is now packaged in the concrete horseshoe datum itself.
  exact (first_variable_horseshoe_complex_data_of_shortExact (R := R) hS).quasiIso_πK

/-- Helper for Lemma 10.75.2: once the concrete middle horseshoe complex is available, packaging
it as the middle projective resolution is formal. -/
noncomputable def first_variable_horseshoe_row_of_shortExact
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

/-- Helper for Lemma 10.75.2: the fixed-left source owner `X ↦ Tor'₁^R(M, X)` is exact on the
first two arrows of any short exact row. This exposes the source-faithful exactness input needed
by later finite-length inductions without redoing the projective-resolution construction. -/
theorem source_owner_tor_one_exact_of_shortExact
    (M : ModuleCat R) {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    Function.Exact ((((Tor' (ModuleCat R) 1).obj M).map S.f).hom)
      ((((Tor' (ModuleCat R) 1).obj M).map S.g).hom) := by
  -- Read the first short-complex window off the already constructed exact five-term source row.
  obtain ⟨δ, hFive⟩ :=
    source_owner_tor_one_tensor_five_term_exact_of_shortExact (R := R) (M := M) (S := S) hS
  -- Convert the categorical exactness of the first two arrows back to `Function.Exact`.
  simpa [ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := (ComposableArrows.mk₅
        (((Tor' (ModuleCat R) 1).obj M).map S.f)
        (((Tor' (ModuleCat R) 1).obj M).map S.g)
        δ
        ((tensorLeft M).map S.f)
        ((tensorLeft M).map S.g)).sc hFive.toIsComplex 0)).1
      (hFive.exact 0)

/-- Helper for Lemma 10.75.2: the fixed-left source owner also exposes the connecting map
`Tor'₁(M, S.X₃) ⟶ M ⊗ S.X₁` and the two exact pairs adjacent to it in the five-term tensor row.
-/
theorem source_owner_tor_one_tensor_kernel_exact_of_shortExact
    (M : ModuleCat R) {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    ∃ δ : ((((Tor' (ModuleCat R) 1).obj M).obj S.X₃) ⟶ (M ⊗ S.X₁)),
      Function.Exact ((((Tor' (ModuleCat R) 1).obj M).map S.g).hom) δ.hom ∧
        Function.Exact δ.hom (((tensorLeft M).map S.f).hom) := by
  -- Read the connecting morphism and exactness from the already constructed five-term source row.
  obtain ⟨δ, hFive⟩ :=
    source_owner_tor_one_tensor_five_term_exact_of_shortExact (R := R) (M := M) (S := S) hS
  refine ⟨δ, ?_, ?_⟩
  · -- The short complex at positions `1,2,3` is `(Tor' map S.g, δ)`.
    simpa [ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((Tor' (ModuleCat R) 1).obj M).map S.f)
          (((Tor' (ModuleCat R) 1).obj M).map S.g)
          δ
          ((tensorLeft M).map S.f)
          ((tensorLeft M).map S.g)).sc hFive.toIsComplex 1)).1
        (hFive.exact 1)
  · -- The next short complex is `(δ, (tensorLeft M).map S.f)`.
    simpa [ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((Tor' (ModuleCat R) 1).obj M).map S.f)
          (((Tor' (ModuleCat R) 1).obj M).map S.g)
          δ
          ((tensorLeft M).map S.f)
          ((tensorLeft M).map S.g)).sc hFive.toIsComplex 2)).1
        (hFive.exact 2)

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
@[stacks 00M0]
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
