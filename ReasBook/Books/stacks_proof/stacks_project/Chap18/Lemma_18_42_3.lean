import Mathlib
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import StacksProject_2024.Chap10.Definition_10_90_1
import StacksProject_2024.Chap18.Lemma_18_3_1
import StacksProject_2024.Chap18.Lemma_18_42_1
import StacksProject_2024.Chap18.Lemma_18_42_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {Λ : Type u} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{u} Λ)]

/-- Helper for Lemma 18.42.3: injectivity of a module map should remain injective after applying
the constant module sheaf functor and evaluating at a section object. -/
theorem constantSheafMapAppInjective
    {A B : ModuleCat.{u} Λ} (u : A ⟶ B) (U : C)
    (hu : Function.Injective u.hom) :
    Function.Injective (((constantSheaf J (ModuleCat.{u} Λ)).map u).hom.app (op U)) := by
  let F := forget (ModuleCat.{u} Λ)
  let φ : (Functor.const Cᵒᵖ).obj (F.obj A) ⟶ (Functor.const Cᵒᵖ).obj (F.obj B) :=
    (Functor.const Cᵒᵖ).map (F.map u)
  have hTypeMono : Mono ((constantSheaf J (Type u)).map (F.map u)) := by
    have hPresheafInj : ∀ V : C, Function.Injective (φ.app (op V)) := by
      intro V
      simpa [φ, F] using hu
    -- First prove the constant presheaf map in `Type` is locally injective, then sheafify it.
    letI : Sheaf.IsLocallyInjective ((presheafToSheaf J (Type u)).map φ) := by
      simpa [Presheaf.isLocallyInjective_presheafToSheaf_map_iff] using
        Presheaf.isLocallyInjective_of_injective J φ fun V ↦ hPresheafInj V.unop
    have hSheafMono : Mono ((presheafToSheaf J (Type u)).map φ) :=
      Sheaf.mono_of_isLocallyInjective ((presheafToSheaf J (Type u)).map φ)
    simpa [constantSheaf] using
      hSheafMono
  have hTypeHomMono : Mono (((constantSheaf J (Type u)).map (F.map u)).hom) :=
    (sheafToPresheaf J (Type u)).map_mono ((constantSheaf J (Type u)).map (F.map u))
  have hTypeAppInj :
      Function.Injective
        ((((constantSheaf J (Type u)).map (F.map u)).hom.app (op U))) :=
    (CategoryTheory.mono_iff_injective _).1
      ((NatTrans.mono_iff_mono_app (((constantSheaf J (Type u)).map (F.map u)).hom)).1
        hTypeHomMono (op U))
  let E := constantCommuteCompose J F
  let eA := ((sheafToPresheaf J (Type u)).mapIso (E.app A)).app (op U)
  let eB := ((sheafToPresheaf J (Type u)).mapIso (E.app B)).app (op U)
  have heA :
      Function.LeftInverse eA.inv eA.hom := by
    intro z
    simpa using CategoryTheory.hom_inv_id_apply eA z
  have hforgetNat
      (z : (((constantSheaf J (ModuleCat.{u} Λ)).obj A).obj.obj (op U))) :
      eB.hom ((((constantSheaf J (ModuleCat.{u} Λ)).map u).hom.app (op U)) z) =
        (((constantSheaf J (Type u)).map (F.map u)).hom.app (op U)) (eA.hom z) := by
    -- Evaluate the naturality square of `constantCommuteCompose` at the chosen section.
    have hnat :
        ((((constantSheaf J (ModuleCat.{u} Λ) ⋙ sheafCompose J F).map u) ≫
            (E.hom.app B)).hom.app (op U)) =
          (((E.hom.app A) ≫ ((F ⋙ constantSheaf J (Type u)).map u)).hom.app (op U)) := by
      exact
        congrArg
          (fun α :
            ((constantSheaf J (ModuleCat.{u} Λ) ⋙ sheafCompose J F).obj A) ⟶
              ((F ⋙ constantSheaf J (Type u)).obj B) =>
            α.hom.app (op U))
          (E.hom.naturality u)
    simpa [E, eA, eB, F, Functor.comp_map] using ConcreteCategory.congr_hom hnat z
  intro x y hxy
  apply heA.injective
  -- Transport the equality of module-valued sections to the forgotten abelian-group side.
  have hxyAdd :
      (((constantSheaf J (Type u)).map (F.map u)).hom.app (op U)) (eA.hom x) =
        (((constantSheaf J (Type u)).map (F.map u)).hom.app (op U)) (eA.hom y) := by
    have hx := hforgetNat x
    have hy := hforgetNat y
    rw [← hx, hxy, hy]
  exact hTypeAppInj hxyAdd

/-- Helper for Lemma 18.42.3: evaluating a constant-sheaf isomorphism at `U` gives the matching
linear equivalence on section modules. -/
private noncomputable def constantSheafAppLinearEquivOfIso
    {A B : ModuleCat.{u} Λ} (e : A ≅ B) (U : C) :
    (((constantSheaf J (ModuleCat.{u} Λ)).obj A).obj.obj (op U)) ≃ₗ[Λ]
      (((constantSheaf J (ModuleCat.{u} Λ)).obj B).obj.obj (op U)) :=
  (((sheafToPresheaf J (ModuleCat.{u} Λ)).mapIso
      ((constantSheaf J (ModuleCat.{u} Λ)).mapIso e)).app (op U)).toLinearEquiv

/-- Helper for Lemma 18.42.3: before comparing tensor presentations, one can commute the ideal
factor past `M` on sections of the constant sheaf. -/
private noncomputable def constantSheafTensorCommAppLinearEquiv
    (M : ModuleCat.{u} Λ) (I : Ideal Λ) (U : C) :
    (((constantSheaf J (ModuleCat.{u} Λ)).obj
        (ModuleCat.of Λ (TensorProduct Λ I M))).obj.obj (op U)) ≃ₗ[Λ]
      (((constantSheaf J (ModuleCat.{u} Λ)).obj
        (ModuleCat.of Λ (TensorProduct Λ M I))).obj.obj (op U)) :=
  -- The tensor commutativity isomorphism can be applied before taking sections.
  constantSheafAppLinearEquivOfIso (J := J) ((TensorProduct.comm Λ I M).toModuleIso) U

/-- Helper for Lemma 18.42.3: evaluating the constant sheaf of a finite product of copies of `M`
identifies with the corresponding finite product of the evaluated constant sheaf of `M`. -/
private noncomputable def constantSheafFinitePiAppLinearEquiv
    (M : ModuleCat.{u} Λ) (n : ℕ) (U : C) :
    (((constantSheaf J (ModuleCat.{u} Λ)).obj
        (ModuleCat.of Λ (Fin n → M))).obj.obj (op U)) ≃ₗ[Λ]
      (Fin n → (((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj.obj (op U))) := by
  let F₁ : ModuleCat.{u} Λ ⥤ Sheaf J (ModuleCat.{u} Λ) :=
    constantSheaf J (ModuleCat.{u} Λ)
  let F₂ : Sheaf J (ModuleCat.{u} Λ) ⥤ (Cᵒᵖ ⥤ ModuleCat.{u} Λ) :=
    sheafToPresheaf J (ModuleCat.{u} Λ)
  let F₃ : (Cᵒᵖ ⥤ ModuleCat.{u} Λ) ⥤ ModuleCat.{u} Λ :=
    (evaluation Cᵒᵖ (ModuleCat.{u} Λ)).obj (op U)
  let G : ModuleCat.{u} Λ ⥤ ModuleCat.{u} Λ := F₁ ⋙ F₂ ⋙ F₃
  let Z : Fin n → ModuleCat.{u} Λ := fun _ ↦ M
  letI : PreservesLimit (Discrete.functor Z) F₁ := by
    dsimp [F₁, constantSheaf]
    infer_instance
  letI : PreservesLimit ((Discrete.functor Z) ⋙ F₁) F₂ := by
    dsimp [F₂]
    infer_instance
  letI : PreservesLimit (((Discrete.functor Z) ⋙ F₁) ⋙ F₂) F₃ := by
    dsimp [F₃]
    infer_instance
  letI : PreservesLimit (Discrete.functor Z) G := by
    dsimp [G]
    infer_instance
  let e :
      G.obj (ModuleCat.of Λ (Fin n → M)) ≅
        ModuleCat.of Λ (Fin n → (((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj.obj (op U))) :=
    (G.mapIso (ModuleCat.piIsoPi Z).symm) ≪≫
      (preservesLimitIso G (Discrete.functor Z)) ≪≫
      (CategoryTheory.Limits.Pi.isoLimit (Discrete.functor Z ⋙ G)).symm ≪≫
      ModuleCat.piIsoPi (fun _ : Fin n ↦ G.obj M)
  -- Route correction: package the finite-product preservation once at the evaluation functor,
  -- so later tensor-presentation comparisons can rewrite finite free modules without reopening
  -- sheafification transport.
  exact e.toLinearEquiv

/-- Helper for Lemma 18.42.3: after commuting tensor with a finite free module on the right,
evaluating the constant sheaf identifies sections with a finite tuple of sections of `M`. -/
private noncomputable def constantSheafTensorFreeAppLinearEquiv
    (M : ModuleCat.{u} Λ) (n : ℕ) (U : C) :
    (((constantSheaf J (ModuleCat.{u} Λ)).obj
        (ModuleCat.of Λ (TensorProduct Λ M (Fin n → Λ)))).obj.obj (op U)) ≃ₗ[Λ]
      (Fin n → (((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj.obj (op U))) :=
  -- First rewrite the tensor with the free rank-`n` module as a product of `n` copies of `M`,
  -- then evaluate the resulting constant sheaf product sectionwise.
  (constantSheafAppLinearEquivOfIso (J := J)
      ((TensorProduct.piScalarRight Λ Λ M (Fin n)).toModuleIso) U) ≪≫ₗ
    constantSheafFinitePiAppLinearEquiv (J := J) M n U

/-- Helper for Lemma 18.42.3: a finitely presented `\Lambda`-module admits an exact presentation
by finite free modules. -/
private theorem finitelyPresentedModuleExistsFreePresentation
    (Q : ModuleCat.{u} Λ) [Module.FinitePresentation Λ Q] :
    ∃ (m n : ℕ) (f : ModuleCat.of Λ (Fin m → Λ) ⟶ ModuleCat.of Λ (Fin n → Λ))
      (g : ModuleCat.of Λ (Fin n → Λ) ⟶ Q),
      Function.Exact f.hom g.hom ∧ Function.Surjective g.hom := by
  classical
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin Λ Q
  obtain ⟨t, ht⟩ := hK
  let generators : t → (Fin n → Λ) := fun i ↦ i.1
  let ψ :
      (Fin t.card → Λ) ≃ₗ[Λ] t →₀ Λ :=
    (Finsupp.linearEquivFunOnFinite Λ Λ (Fin t.card)).symm ≪≫ₗ
      Finsupp.domLCongr t.equivFin.symm
  let φ :
      (Fin t.card → Λ) →ₗ[Λ] (Fin n → Λ) :=
    Finsupp.linearCombination Λ generators ∘ₗ ψ.toLinearMap
  have hφ_range : LinearMap.range φ = K := by
    have hgenerators :
        LinearMap.range (Finsupp.linearCombination Λ generators) = K := by
      rw [Finsupp.range_linearCombination]
      simpa [generators, Subtype.range_coe_subtype] using ht
    rw [LinearMap.range_comp_of_range_eq_top _ ψ.range]
    exact hgenerators
  let gLinear : (Fin n → Λ) →ₗ[Λ] Q :=
    e.symm.toLinearMap.comp K.mkQ
  have hg_ker : LinearMap.ker gLinear = K := by
    have heker : LinearMap.ker e.symm.toLinearMap = ⊥ :=
      LinearMap.ker_eq_bot.mpr e.symm.injective
    -- Proof comment: the quotient map contributes the kernel `K`, and the final equivalence does
    -- not change the kernel.
    change LinearMap.ker (e.symm.toLinearMap.comp K.mkQ) = K
    rw [LinearMap.ker_comp, heker, Submodule.comap_bot, Submodule.ker_mkQ]
  have hExact : Function.Exact φ gLinear := by
    -- Proof comment: exactness is the range-kernel identification coming from the chosen
    -- presentation.
    rw [LinearMap.exact_iff, hφ_range, hg_ker]
  have hgSurj : Function.Surjective gLinear := by
    exact e.symm.surjective.comp (Submodule.mkQ_surjective K)
  exact ⟨t.card, n, ModuleCat.ofHom φ, ModuleCat.ofHom gLinear, hExact, hgSurj⟩

/-- Helper for Lemma 18.42.3: tensoring a finite free presentation with `M` preserves the exact
and surjective right-exact pair needed for the ideal comparison. -/
private theorem tensorFreePresentationExact
    {Q : ModuleCat.{u} Λ} (M : ModuleCat.{u} Λ)
    {m n : ℕ}
    {f : ModuleCat.of Λ (Fin m → Λ) ⟶ ModuleCat.of Λ (Fin n → Λ)}
    {g : ModuleCat.of Λ (Fin n → Λ) ⟶ Q}
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) :
    Function.Exact (f.hom.lTensor M) (g.hom.lTensor M) ∧
      Function.Surjective (g.hom.lTensor M) := by
  constructor
  · -- Proof comment: this is the standard right exactness of tensoring on the left.
    exact lTensor_exact M hfg hg
  · -- Proof comment: surjectivity is preserved after tensoring with a fixed module.
    exact LinearMap.lTensor_surjective M hg

/-- Helper for Lemma 18.42.3: a linear equivalence yields a quotient linear equivalence once it
identifies the source submodule with the target submodule. -/
private theorem quotientLinearEquivOfSubmoduleMapEq
    {A : Type*} [Ring A]
    {V W : Type*} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (e : V ≃ₗ[A] W) (S : Submodule A V) (T : Submodule A W)
    (hST : S.map e.toLinearMap = T) :
    Nonempty ((V ⧸ S) ≃ₗ[A] (W ⧸ T)) := by
  let hForward : S ≤ Submodule.comap e.toLinearMap T := by
    intro x hx
    change e x ∈ T
    rw [← hST]
    exact ⟨x, hx, rfl⟩
  let hBackward : T ≤ Submodule.comap e.symm.toLinearMap S := by
    intro y hy
    change e.symm y ∈ S
    have hy' : y ∈ S.map e.toLinearMap := by
      simpa [hST] using hy
    rcases hy' with ⟨x, hx, rfl⟩
    simpa using hx
  let fQ : (V ⧸ S) →ₗ[A] (W ⧸ T) := Submodule.mapQ S T e.toLinearMap hForward
  let gQ : (W ⧸ T) →ₗ[A] (V ⧸ S) := Submodule.mapQ T S e.symm.toLinearMap hBackward
  -- Proof comment: both quotient maps reduce on representatives to `e` and `e.symm`, so the
  -- inverse identities follow by quotient induction.
  exact
    ⟨LinearEquiv.ofLinear fQ gQ
      (by
        apply LinearMap.ext
        intro q
        refine Quotient.inductionOn' q ?_
        intro x
        change fQ (gQ (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
        have hgQ :
            gQ (Submodule.Quotient.mk x) =
              (Submodule.Quotient.mk (e.symm x) : V ⧸ S) := by
          simpa [gQ] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ T S e.symm.toLinearMap) x
        rw [hgQ]
        have hfQ :
            fQ (Submodule.Quotient.mk (e.symm x)) =
              (Submodule.Quotient.mk (e (e.symm x)) : W ⧸ T) := by
          simpa [fQ] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ S T e.toLinearMap) (e.symm x)
        rw [hfQ]
        simp)
      (by
        apply LinearMap.ext
        intro q
        refine Quotient.inductionOn' q ?_
        intro x
        change gQ (fQ (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
        have hfQ :
            fQ (Submodule.Quotient.mk x) =
              (Submodule.Quotient.mk (e x) : W ⧸ T) := by
          simpa [fQ] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ S T e.toLinearMap) x
        rw [hfQ]
        have hgQ :
            gQ (Submodule.Quotient.mk (e x)) =
              (Submodule.Quotient.mk (e.symm (e x)) : V ⧸ S) := by
          simpa [gQ] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ T S e.symm.toLinearMap) (e x)
        rw [hgQ]
        simp)⟩

/-- Helper for Lemma 18.42.3: for a finitely generated ideal `I`, sections of the constant sheaf
of `I ⊗ M` over `U` identify with tensoring the section module of `M` by `I` on the left. -/
noncomputable def constantSheafTensorIdealAppLinearEquiv
    [IsCoherentRing Λ] (M : ModuleCat.{u} Λ) (I : Ideal Λ) (hI : I.FG) (U : C) :
    (((constantSheaf J (ModuleCat.{u} Λ)).obj
        (ModuleCat.of Λ (TensorProduct Λ I M))).obj.obj (op U)) ≃ₗ[Λ]
      TensorProduct Λ I (((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj.obj (op U)) :=
  letI : Module.Finite Λ I := by
    simpa [Module.Finite.iff_fg] using hI
  letI : Module.FinitePresentation Λ I :=
    Module.Coherent.finitePresentation_submodule (R := Λ) (M := Λ) I inferInstance
  letI := constantModuleTensorComparison_app_isIso J M (ModuleCat.of Λ I) U
  -- Proof comment: commute the ideal factor to the right, use the imported sectionwise tensor
  -- comparison from Lemma 18.42.2, and then commute the resulting tensor factors back.
  (constantSheafTensorCommAppLinearEquiv (J := J) M I U) ≪≫ₗ
    (asIso (((constantModuleTensorComparison J M (ModuleCat.of Λ I)).hom.app
      (op U)))).toLinearEquiv ≪≫ₗ
    (TensorProduct.comm Λ (((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj.obj (op U))
      I).toLinearEquiv

/-- Helper for Lemma 18.42.3: the sectionwise comparison
`constantSheafTensorIdealAppLinearEquiv` intertwines the flatness-test tensor map with the map on
sections induced by `I ⊗ M → M`. -/
theorem constantSheafTensorIdealAppLinearEquiv_naturality
    [IsCoherentRing Λ] (M : ModuleCat.{u} Λ) (I : Ideal Λ) (hI : I.FG) (U : C) :
    TensorProduct.lift
        (((LinearMap.lsmul Λ (((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj.obj (op U))).comp
          I.subtype)) =
      (((((constantSheaf J (ModuleCat.{u} Λ)).map
            (ModuleCat.ofHom
              (TensorProduct.lift ((LinearMap.lsmul Λ M).comp I.subtype)))).hom.app
            (op U)).hom).comp
        (constantSheafTensorIdealAppLinearEquiv (J := J) M I hI U).symm.toLinearMap) := by
  let N := (((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj.obj (op U))
  let μ : ModuleCat.of Λ (TensorProduct Λ I M) ⟶ M :=
    ModuleCat.ofHom (TensorProduct.lift ((LinearMap.lsmul Λ M).comp I.subtype))
  let ν : ModuleCat.of Λ (TensorProduct Λ M I) ⟶ M :=
    ModuleCat.ofHom <|
      (TensorProduct.lift ((LinearMap.lsmul Λ M).comp I.subtype)).comp
        (TensorProduct.comm Λ M I).toLinearEquiv.toLinearMap
  let rightAction : TensorProduct Λ N I →ₗ[Λ] N :=
    TensorProduct.lift
      { toFun := fun x =>
          { toFun := fun i => (i : Λ) • x
            map_add' := by
              intro i j
              simp [add_smul]
            map_smul' := by
              intro a i
              simp [smul_smul, mul_comm] }
        map_add' := by
          intro x y
          ext i
          simp [add_smul]
        map_smul' := by
          intro a x
          ext i
          simp [smul_smul, mul_left_comm, mul_assoc] }
  let rightActionNat :
      ((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj ⋙ tensorRight (ModuleCat.of Λ I) ⟶
        ((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj :=
    { app := fun V => ModuleCat.ofHom <| rightAction (U := V.unop)
      naturality := by
        intro V W f
        ext x i
        rfl }
  let θ :
      ⟨((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj ⋙ tensorRight (ModuleCat.of Λ I),
        constantModuleTensorSectionsPresheaf_isSheaf J M (ModuleCat.of Λ I)⟩ ⟶
        (constantSheaf J (ModuleCat.{u} Λ)).obj M :=
    ObjectProperty.homMk rightActionNat
  have hTarget :
      TensorProduct.lift (((LinearMap.lsmul Λ N).comp I.subtype)) =
        (rightAction (U := U)).comp
          (TensorProduct.comm Λ N I).toLinearEquiv.toLinearMap := by
    -- Proof comment: the target tensor commutor only swaps the tensor factors before applying the
    -- same scalar multiplication map.
    apply TensorProduct.ext'
    intro i x
    simp [rightAction, LinearMap.comp_apply, TensorProduct.comm_tmul]
  have hMiddleFactor :
      CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of Λ (TensorProduct Λ M I))) ≫
          (constantModuleTensorComparison J M (ModuleCat.of Λ I) ≫ θ).hom =
        ((Functor.const Cᵒᵖ).map ν) ≫
          CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M) := by
    -- Proof comment: after pulling back to the constant presheaf, the public comparison map is
    -- the evident sectionwise tensor map, and collapsing `- ⊗ I` by scalar multiplication matches
    -- the constant-sheaf map induced by `ν`.
    rw [Category.assoc, constantModuleTensorComparison, CategoryTheory.toSheafify_sheafifyLift]
    ext V x i
    simp [ν, rightActionNat, rightAction, constantModuleTensorComparisonNatTrans,
      CategoryTheory.Functor.constComp_hom_app, ModuleCat.hom_whiskerRight,
      ModuleCat.comp_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      TensorProduct.comm_tmul]
  have hMiddleHom :
      (constantModuleTensorComparison J M (ModuleCat.of Λ I) ≫ θ).hom =
        ((constantSheaf J (ModuleCat.{u} Λ)).map ν).hom := by
    -- Proof comment: both sheaf morphisms are the unique lifts of the same presheaf-level map.
    have hLeft :
        (constantModuleTensorComparison J M (ModuleCat.of Λ I) ≫ θ).hom =
          CategoryTheory.sheafifyLift J
            (((Functor.const Cᵒᵖ).map ν) ≫
              CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M))
            (((constantSheaf J (ModuleCat.{u} Λ)).obj M).property) := by
      symm
      exact
        CategoryTheory.sheafifyLift_unique J
          (((Functor.const Cᵒᵖ).map ν) ≫
            CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (((constantSheaf J (ModuleCat.{u} Λ)).obj M).property)
          ((constantModuleTensorComparison J M (ModuleCat.of Λ I) ≫ θ).hom)
          hMiddleFactor
    have hRight :
        ((constantSheaf J (ModuleCat.{u} Λ)).map ν).hom =
          CategoryTheory.sheafifyLift J
            (((Functor.const Cᵒᵖ).map ν) ≫
              CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M))
            (((constantSheaf J (ModuleCat.{u} Λ)).obj M).property) := by
      symm
      exact
        CategoryTheory.sheafifyLift_unique J
          (((Functor.const Cᵒᵖ).map ν) ≫
            CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (((constantSheaf J (ModuleCat.{u} Λ)).obj M).property)
          (((constantSheaf J (ModuleCat.{u} Λ)).map ν).hom)
          (by
            simpa [constantSheaf, Category.assoc] using
              (CategoryTheory.toSheafify_naturality J ((Functor.const Cᵒᵖ).map ν)))
    exact hLeft.trans hRight.symm
  have hMiddle :
      (rightAction (U := U)).comp
          (((constantModuleTensorComparison J M (ModuleCat.of Λ I)).hom.app (op U)).hom) =
        ((((constantSheaf J (ModuleCat.{u} Λ)).map ν).hom.app (op U)).hom) := by
    -- Proof comment: evaluate the sheaf-level comparison square at the chosen object `U`.
    simpa [θ, rightActionNat, ModuleCat.comp_apply] using
      congrArg
        (fun α :
          (constantSheaf J (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ (TensorProduct Λ M I)) ⟶
            (constantSheaf J (ModuleCat.{u} Λ)).obj M =>
          (α.hom.app (op U)).hom)
        hMiddleHom
  have hSource :
      ((((constantSheaf J (ModuleCat.{u} Λ)).map ν).hom.app (op U)).hom).comp
          (constantSheafTensorCommAppLinearEquiv (J := J) M I U).toLinearMap =
        ((((constantSheaf J (ModuleCat.{u} Λ)).map μ).hom.app (op U)).hom) := by
    -- Proof comment: the source tensor commutor is exactly the map induced on sections by the
    -- tensor commutativity isomorphism `I ⊗ M ≅ M ⊗ I`.
    have hμν :
        (TensorProduct.comm Λ I M).toModuleIso.hom ≫ ν = μ := by
      ext i x
      simp [μ, ν, ModuleCat.comp_apply, LinearMap.comp_apply, TensorProduct.comm_tmul]
    simpa [constantSheafTensorCommAppLinearEquiv, constantSheafAppLinearEquivOfIso,
      hμν, Category.assoc, Functor.map_comp, μ, ν, ModuleCat.comp_apply]
      using
        congrArg
          (fun α :
            (constantSheaf J (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ (TensorProduct Λ I M)) ⟶
              (constantSheaf J (ModuleCat.{u} Λ)).obj M =>
            (α.hom.app (op U)).hom)
          (by
            simpa [hμν] using
              (Functor.map_comp (constantSheaf J (ModuleCat.{u} Λ))
                (TensorProduct.comm Λ I M).toModuleIso.hom ν))
  have hComp :
      (TensorProduct.lift (((LinearMap.lsmul Λ N).comp I.subtype))).comp
          (constantSheafTensorIdealAppLinearEquiv (J := J) M I hI U).toLinearMap =
        ((((constantSheaf J (ModuleCat.{u} Λ)).map μ).hom.app (op U)).hom) := by
    -- Proof comment: compose the target commutor identity, the middle comparison identity, and
    -- the source commutor identity in the forward direction.
    calc
      (TensorProduct.lift (((LinearMap.lsmul Λ N).comp I.subtype))).comp
          (constantSheafTensorIdealAppLinearEquiv (J := J) M I hI U).toLinearMap =
        (TensorProduct.lift (((LinearMap.lsmul Λ N).comp I.subtype))).comp
            (TensorProduct.comm Λ N I).toLinearEquiv.toLinearMap.comp
            ((asIso (((constantModuleTensorComparison J M (ModuleCat.of Λ I)).hom.app
              (op U)))).toLinearEquiv.toLinearMap).comp
            (constantSheafTensorCommAppLinearEquiv (J := J) M I U).toLinearMap := by
              rfl
      _ = (rightAction (U := U)).comp
            ((asIso (((constantModuleTensorComparison J M (ModuleCat.of Λ I)).hom.app
              (op U)))).toLinearEquiv.toLinearMap).comp
            (constantSheafTensorCommAppLinearEquiv (J := J) M I U).toLinearMap := by
              rw [← LinearMap.comp_assoc, hTarget]
      _ = ((((constantSheaf J (ModuleCat.{u} Λ)).map ν).hom.app (op U)).hom).comp
            (constantSheafTensorCommAppLinearEquiv (J := J) M I U).toLinearMap := by
              rw [← LinearMap.comp_assoc, hMiddle]
      _ = ((((constantSheaf J (ModuleCat.{u} Λ)).map μ).hom.app (op U)).hom) := hSource
  -- Proof comment: convert the stated inverse-comparison formula into the forward version above,
  -- then evaluate it on preimages under the comparison equivalence.
  ext z
  rcases (constantSheafTensorIdealAppLinearEquiv (J := J) M I hI U).surjective z with ⟨w, rfl⟩
  simpa [LinearMap.comp_apply, μ] using congrArg (fun f => f w) hComp

/- Domain-style sampling:
- primary domain: constant sheaves of `Λ`-modules on a site, evaluated sectionwise, together with
  flatness detected by tensoring with finitely generated ideals over a coherent ring;
- sampled owner declarations:
  `IsCoherentRing`,
  `Module.Coherent`,
  `constantSheaf`,
  `Module.Flat`,
  `Module.Flat.iff_lift_lsmul_comp_subtype_injective`,
  `constantModuleTensorComparison_app_isIso`;
- best owner abstraction: ring coherence is carried by the chapter owner class
  `IsCoherentRing Λ`, whose derived module-level API is `[Module.Coherent Λ Λ]`; the public owner
  on the sheaf side is still the canonical sheaf
  `(constantSheaf J (ModuleCat Λ)).obj M`; the source-facing statement is its sectionwise
  flatness at `U`, while `constantModuleTensorComparison_app_isIso` from Lemma `18.42.2` is the
  bridge that identifies tensoring sections with sections of the tensor constant sheaf;
- primitive data: the coherent-ring owner instance `[IsCoherentRing Λ]`, the flat `Λ`-module `M`,
  and the object `U : C`;
- derived API: the flatness statement for the section module
  `(((constantSheaf J (ModuleCat Λ)).obj M).obj).obj (op U)`.

Source/core/bridge triage:
- `source-facing`: `constantSheaf_app_flat`;
- `core/canonical`: `constantSheaf` and `Module.Flat`;
- `bridge/view`: `constantModuleTensorComparison_app_isIso`, used to transport the tensor-flatness
  criterion from `M` to the section module of its constant sheaf. -/

-- Proof sketch: by Lemma 10.39.5 it is enough to test injectivity after tensoring with a finite
-- ideal `I ⊆ Λ`. The owner abstraction `[IsCoherentRing Λ]` makes `I` coherent, hence finitely
-- presented, so Lemma 18.42.2 identifies
-- `\underline M(U) ⊗ I` with `\underline{M ⊗ I}(U)`. Since `M` is flat, `M ⊗ I → M` is
-- injective, and evaluation of the induced morphism of constant sheaves at `U` remains injective.
/-- Lemma 18.42.3: if `Λ` is a coherent ring, `M` is a flat `Λ`-module, and `U` is an object of
the site `C`, then the `Λ`-module of sections `\underline M(U)` of the constant sheaf is flat. -/
@[stacks 093L]
theorem constantSheaf_app_flat
    [IsCoherentRing Λ] (M : ModuleCat.{u} Λ) [Module.Flat Λ M] (U : C) :
    Module.Flat Λ ((((constantSheaf J (ModuleCat.{u} Λ)).obj M).obj).obj (op U)) := by
  -- Apply the coherent-ideal criterion for flatness to the section module at `U`.
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I hI
  haveI : Module.Finite Λ I := by
    simpa [Module.Finite.iff_fg] using hI
  haveI : Module.FinitePresentation Λ I :=
    Module.Coherent.finitePresentation_submodule (R := Λ) (M := Λ) I inferInstance
  let e := constantSheafTensorIdealAppLinearEquiv (J := J) M I hI U
  let μ : ModuleCat.of Λ (TensorProduct Λ I M) ⟶ M :=
    ModuleCat.ofHom (TensorProduct.lift ((LinearMap.lsmul Λ M).comp I.subtype))
  have hμinj : Function.Injective μ.hom := by
    -- Flatness of `M` gives injectivity of `M ⊗ I → M`.
    simpa [μ] using
      (Module.Flat.iff_lift_lsmul_comp_subtype_injective (R := Λ) (M := M)).1
        inferInstance hI
  have hsecinj :
      Function.Injective (((constantSheaf J (ModuleCat.{u} Λ)).map μ).hom.app (op U)) :=
    constantSheafMapAppInjective (J := J) μ U hμinj
  -- Route correction: once the tensor-sections comparison is available, injectivity transports
  -- directly across that linear equivalence.
  rw [constantSheafTensorIdealAppLinearEquiv_naturality (J := J) M I hI U]
  exact hsecinj.comp e.symm.injective

end CategoryTheory
