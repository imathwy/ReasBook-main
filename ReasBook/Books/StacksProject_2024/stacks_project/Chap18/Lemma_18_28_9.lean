import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_12
import StacksProject_2024.stacks_project.Chap18.Definition_18_28_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_28_5
import StacksProject_2024.stacks_project.Chap18.Lemma_18_28_8
import StacksProject_2024.stacks_project.Chap18.Lemma_18_28_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory Opposite

noncomputable section

universe u

namespace CategoryTheory

/-- Helper for Lemma 18.28.9: in a morphism of short exact rows, monicity of the two outer
vertical maps forces monicity of the middle vertical map by the four lemma. -/
private theorem shortComplex_middle_mono_of_outer_mono
    {A : Type*} [Category A] [Abelian A]
    {R₁ R₂ : ShortComplex A}
    (φ : R₁ ⟶ R₂)
    (hR₁ : R₁.ShortExact)
    (hR₂ : R₂.ShortExact)
    [Mono φ.τ₁] [Mono φ.τ₃] :
    Mono φ.τ₂ := by
  -- Proof comment: chase a generic morphism into the middle term through the exact left row and
  -- cancel it first against the right outer mono and then against the left outer mono.
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z x hx
  have hxg : x ≫ R₁.g = 0 := by
    have haux : x ≫ R₁.g ≫ φ.τ₃ = 0 := by
      calc
        x ≫ R₁.g ≫ φ.τ₃ = x ≫ φ.τ₂ ≫ R₂.g := by
          simpa [Category.assoc] using congrArg (fun k ↦ x ≫ k) φ.comm₂₃.symm
        _ = 0 := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ R₂.g) hx
    exact (cancel_mono φ.τ₃).1 (by simpa [Category.assoc] using haux)
  let y : Z ⟶ R₁.X₁ :=
    hR₁.fIsKernel.lift (Limits.KernelFork.ofι x hxg)
  have hy : y ≫ R₁.f = x := by
    simpa using
      hR₁.fIsKernel.fac (Limits.KernelFork.ofι x hxg) Limits.WalkingParallelPair.zero
  let _ : Mono R₂.f := hR₂.mono_f
  have hya : y ≫ φ.τ₁ = 0 := by
    have haux : y ≫ φ.τ₁ ≫ R₂.f = 0 := by
      calc
        y ≫ φ.τ₁ ≫ R₂.f = y ≫ R₁.f ≫ φ.τ₂ := by
          simpa [Category.assoc] using congrArg (fun k ↦ y ≫ k) φ.comm₁₂
        _ = x ≫ φ.τ₂ := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ φ.τ₂) hy
        _ = 0 := hx
    exact (cancel_mono R₂.f).1 (by simpa [Category.assoc] using haux)
  have hyZero : y = 0 := by
    exact (cancel_mono φ.τ₁).1 (by simpa using hya)
  simpa [hyZero] using hy.symm

end CategoryTheory

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Helper for Lemma 18.28.9: localizing a presheaf module to the slice `C/U`. -/
private abbrev localizedPushforward
    (U : C) (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    PresheafOfModules ((Over.forget U).op ⋙ ringPresheaf 𝒪) :=
  (PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ ringPresheaf 𝒪))).obj ℱ

/-- Helper for Lemma 18.28.9: sections of the localized restriction on `C/U` are determined by the
value at the terminal object `U ⟶ U`. -/
private noncomputable def localizedSectionsEquivEvaluation
    (U : C) (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    (localizedPushforward (𝒪 := 𝒪) U ℱ).sections ≃
      (PresheafOfModules.evaluation (ringPresheaf 𝒪) (op U)).obj ℱ where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
  invFun m :=
    (localizedPushforward (𝒪 := 𝒪) U ℱ).sectionsMk
      (fun X ↦ (localizedPushforward (𝒪 := 𝒪) U ℱ).map ((Over.mkIdTerminal.from X.unop).op) m)
      (fun X Y f ↦ by
        -- Proof comment: every object of `C/U` has a unique morphism to the terminal object.
        have h :
            (Over.mkIdTerminal.from X.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from X.unop)
            (Over.mkIdTerminal.from Y.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- Proof comment: a section is determined by its restrictions from the terminal value.
    ext X
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from X.unop).op)
  right_inv m := by
    -- Proof comment: evaluating the reconstructed section at the terminal object returns `m`.
    change
      (localizedPushforward (𝒪 := 𝒪) U ℱ).map
          ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using
      (localizedPushforward (𝒪 := 𝒪) U ℱ).congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 18.28.9: maps from `j_{U!}\mathcal O_U` into a presheaf module are
equivalent to sections over `U`. -/
private noncomputable def localizedStructureModuleExtensionByZero_homEquiv
    (U : C) (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    (PresheafOfModules.localizedStructureModuleExtensionByZero 𝒪 U ⟶ ℱ) ≃
      (PresheafOfModules.evaluation (ringPresheaf 𝒪) (op U)).obj ℱ :=
  (((PresheafOfModules.pullbackPushforwardAdjunction
      (𝟙 ((Over.forget U).op ⋙ ringPresheaf 𝒪))).homEquiv
      (PresheafOfModules.localizedStructureModule 𝒪 U) ℱ).trans
    (PresheafOfModules.unitHomEquiv (localizedPushforward (𝒪 := 𝒪) U ℱ))).trans
    (localizedSectionsEquivEvaluation (𝒪 := 𝒪) U ℱ)

/-- Helper for Lemma 18.28.9: the lower-shriek Hom/evaluation equivalence is natural in the
target module. -/
private theorem localizedStructureModuleExtensionByZeroHomEquivNaturality
    (U : C) {ℱ 𝒢 : PresheafOfModules (ringPresheaf 𝒪)}
    (β : PresheafOfModules.localizedStructureModuleExtensionByZero 𝒪 U ⟶ ℱ) (α : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) U 𝒢 (β ≫ α) =
      ((PresheafOfModules.evaluation (ringPresheaf 𝒪) (op U)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) U ℱ β) := by
  -- Proof comment: the owner equivalence is assembled from target-functorial constructions.
  rfl

/-- Helper for Lemma 18.28.9: morphisms out of a coproduct of lower-shriek modules are the same as
families of chosen sections. -/
private noncomputable def localizedStructureModuleExtensionByZeroCoproductHomEquiv
    {I : Type u} (U : I → C) (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    ((∐ fun i : I ↦ PresheafOfModules.localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ ℱ) ≃
      (∀ i : I, (PresheafOfModules.evaluation (ringPresheaf 𝒪) (op (U i))).obj ℱ) where
  toFun α i :=
    localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) ℱ
      (Sigma.ι (fun i : I ↦ PresheafOfModules.localizedStructureModuleExtensionByZero 𝒪 (U i)) i ≫
        α)
  invFun s :=
    Sigma.desc
      (fun i : I ↦
        (localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) ℱ).symm (s i))
  left_inv α := by
    -- Proof comment: a coproduct morphism is determined by its restrictions to the summands.
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_desc]
    exact Equiv.symm_apply_apply
      (localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) ℱ)
      (Sigma.ι (fun i : I ↦ PresheafOfModules.localizedStructureModuleExtensionByZero 𝒪 (U i)) i ≫
        α)
  right_inv s := by
    -- Proof comment: evaluating the reconstructed morphism on each summand recovers the target
    -- family of sections.
    funext i
    change
      localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) ℱ
          (Sigma.ι
              (fun k : I ↦ PresheafOfModules.localizedStructureModuleExtensionByZero 𝒪 (U k)) i ≫
            Sigma.desc
              (fun k : I ↦
                (localizedStructureModuleExtensionByZero_homEquiv
                  (𝒪 := 𝒪) (U k) ℱ).symm (s k))) =
        s i
    rw [Limits.Sigma.ι_desc]
    exact Equiv.apply_symm_apply
      (localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) ℱ)
      (s i)

/-- Helper for Lemma 18.28.9: evaluating a short exact row of presheaves of modules at any object
gives a short exact row of modules. -/
private theorem evaluationShortExactOfShortExact
    {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}
    (hS : S.ShortExact) (X : Cᵒᵖ) :
    (S.map (PresheafOfModules.evaluation (ringPresheaf 𝒪) X)).ShortExact := by
  let F := PresheafOfModules.evaluation (ringPresheaf 𝒪) X
  let G : ModuleCat ((ringPresheaf 𝒪).obj X) ⥤ AddCommGrpCat.{u} := forget₂ _ _
  have hToPresheaf :
      exactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (Cᵒᵖ ⥤ AddCommGrpCat.{u})
        (PresheafOfModules.toPresheaf (ringPresheaf 𝒪)) :=
    (ExactFunctor.of (PresheafOfModules.toPresheaf (ringPresheaf 𝒪))).property
  have hUnderlying :
      (S.map (PresheafOfModules.toPresheaf (ringPresheaf 𝒪))).ShortExact := by
    -- Proof comment: first forget the module structure, where short exactness is transported by
    -- the exact underlying-presheaf functor.
    exact
      (((Functor.exact_tfae (PresheafOfModules.toPresheaf (ringPresheaf 𝒪))).out 3 0).1
        (by simpa [exactFunctor_iff] using hToPresheaf)) S hS
  have hForget : ((S.map F).map G).ShortExact := by
    -- Proof comment: after forgetting module structure, evaluation is ordinary functor-category
    -- evaluation, so pointwise short exactness is immediate.
    simpa [F, PresheafOfModules.evaluation] using
      CategoryTheory.ShortComplex.shortExact_iff_pointwise_shortExact_functor_category.1
        (S := S.map (PresheafOfModules.toPresheaf (ringPresheaf 𝒪)))
        hUnderlying X
  -- Proof comment: the faithful forgetful functor reflects short exactness back to modules.
  exact ShortComplex.reflects_shortExact_of_faithful G hForget

/-- Helper for Lemma 18.28.9: short exactness of a mapped short complex is invariant under a
natural isomorphism of functors. -/
private theorem shortExact_iff_of_functor_iso
    {A : Type*} {B : Type*}
    [Category A] [Category B]
    [CategoryTheory.Limits.HasZeroMorphisms A] [CategoryTheory.Limits.HasZeroMorphisms B]
    {F G : A ⥤ B}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (e : F ≅ G)
    (T : ShortComplex A) :
    (T.map F).ShortExact ↔ (T.map G).ShortExact := by
  let i : T.map F ≅ T.map G :=
    ShortComplex.isoMk
      (e.app T.X₁)
      (e.app T.X₂)
      (e.app T.X₃)
      (by simpa using e.hom.naturality T.f)
      (by simpa using e.hom.naturality T.g)
  constructor
  · -- Proof comment: transport short exactness forward across the induced short-complex
    -- isomorphism.
    intro h
    exact ShortComplex.shortExact_of_iso i h
  · -- Proof comment: transport short exactness backward along the inverse isomorphism.
    intro h
    exact ShortComplex.shortExact_of_iso i.symm h

/-- Helper for Lemma 18.28.9: flatness of `X` makes left tensoring exact by transporting the
exactness of right tensoring across the braiding isomorphism. -/
private theorem tensorLeft_exact_of_isFlat
    (X : PresheafOfModules (ringPresheaf 𝒪))
    [IsFlat X] :
    exactFunctor
      (PresheafOfModules (ringPresheaf 𝒪))
      (PresheafOfModules (ringPresheaf 𝒪))
      (tensorLeft X) := by
  let hExact := (inferInstance : IsFlat X).exact_tensor
  -- Proof comment: `tensorLeft X` is naturally isomorphic to `tensorRight X` in the braided
  -- monoidal structure, so exactness transports across that comparison.
  rw [CategoryTheory.exactFunctor_iff] at hExact ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (tensorRight X) := hExact.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X) := hExact.2
  exact
    ⟨CategoryTheory.Limits.preservesFiniteLimits_of_natIso
        (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X).symm,
      CategoryTheory.Limits.preservesFiniteColimits_of_natIso
        (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X).symm⟩

/-- Helper for Lemma 18.28.9: if `X` is flat, then tensoring a short exact sequence on the left by
`X` stays short exact. -/
private theorem shortExact_map_tensorLeft_of_isFlat
    (X : PresheafOfModules (ringPresheaf 𝒪))
    [IsFlat X]
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorLeft X)).ShortExact := by
  let hExact := tensorLeft_exact_of_isFlat (𝒪 := 𝒪) X
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (tensorLeft X) :=
    (CategoryTheory.exactFunctor_iff (tensorLeft X)).1 hExact |>.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorLeft X) :=
    (CategoryTheory.exactFunctor_iff (tensorLeft X)).1 hExact |>.2
  -- Proof comment: once left tensoring is exact, mapped short exactness is immediate.
  exact hT.map_of_exact (tensorLeft X)

/-- Helper for Lemma 18.28.9: left tensoring is always right exact, so it carries a short exact
sequence to an exact sequence whose right map remains an epimorphism. -/
private theorem tensorLeft_mapsShortExact_to_exact_epi
    (X : PresheafOfModules (ringPresheaf 𝒪))
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (ComposableArrows.mk₂ ((tensorLeft X).map T.f) ((tensorLeft X).map T.g)).Exact ∧
      Epi ((tensorLeft X).map T.g) := by
  let e := CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorLeft X) :=
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e.symm
  let hRight :
      CategoryTheory.rightExactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (PresheafOfModules (ringPresheaf 𝒪))
        (tensorLeft X) := by
    simpa [CategoryTheory.rightExactFunctor_iff] using
      (inferInstance :
        CategoryTheory.Limits.PreservesFiniteColimits (tensorLeft X))
  -- Proof comment: braiding identifies left tensor with the right-exact right tensor functor.
  exact
    (CategoryTheory.functor_rightExact_iff_maps_shortExact_to_exact_epi
      (A := PresheafOfModules (ringPresheaf 𝒪))
      (B := PresheafOfModules (ringPresheaf 𝒪))
      (F := tensorLeft X)).1 hRight T hT

/-- Helper for Lemma 18.28.9: the flat-cover proof reduces the presheaf theorem to showing that
the left tensor map stays monic after resolving the tensor factor by a flat epimorphism. -/
private theorem tensorRightLeftMono_of_flat_cover
    {𝒢 𝒢' : PresheafOfModules (ringPresheaf 𝒪)}
    (π : 𝒢' ⟶ 𝒢)
    [Epi π] [IsFlat 𝒢']
    (S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hS : S.ShortExact)
    [IsFlat S.X₃] :
    Mono ((tensorRight 𝒢).map S.f) := by
  let T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)) := ShortComplex.kernelSequence π
  have hT : T.ShortExact := by
    -- Proof comment: the flat cover is the canonical short exact kernel sequence of `π`.
    exact ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact π) inferInstance inferInstance
  let hRowGp : (S.map (tensorRight 𝒢')).ShortExact :=
    shortExact_map_tensorRight_of_isFlat (𝒪 := 𝒪) 𝒢' S hS
  let hRowK := tensorRight_mapsShortExact_to_exact_epi (𝒪 := 𝒪) T.X₁ S hS
  let hCol₁ := tensorLeft_mapsShortExact_to_exact_epi (𝒪 := 𝒪) S.X₁ T hT
  let hCol₂ := tensorLeft_mapsShortExact_to_exact_epi (𝒪 := 𝒪) S.X₂ T hT
  let hCol₃ : (T.map (tensorLeft S.X₃)).ShortExact :=
    shortExact_map_tensorLeft_of_isFlat (𝒪 := 𝒪) S.X₃ T hT
  let colMap₁₂ :
      T.map (tensorLeft S.X₁) ⟶ T.map (tensorLeft S.X₂) :=
    T.mapNatTrans
      ((CategoryTheory.MonoidalCategory.tensoringLeft
        (PresheafOfModules (ringPresheaf 𝒪))).map S.f)
  let colMap₂₃ :
      T.map (tensorLeft S.X₂) ⟶ T.map (tensorLeft S.X₃) :=
    T.mapNatTrans
      ((CategoryTheory.MonoidalCategory.tensoringLeft
        (PresheafOfModules (ringPresheaf 𝒪))).map S.g)
  let k₁ : ((T.map (tensorLeft S.X₁)).X₁) ⟶ ((T.map (tensorLeft S.X₁)).X₂) :=
    (tensorLeft S.X₁).map T.f
  let k₂ : ((T.map (tensorLeft S.X₂)).X₁) ⟶ ((T.map (tensorLeft S.X₂)).X₂) :=
    (tensorLeft S.X₂).map T.f
  let k₃ : ((T.map (tensorLeft S.X₃)).X₁) ⟶ ((T.map (tensorLeft S.X₃)).X₂) :=
    (tensorLeft S.X₃).map T.f
  let π₁ : ((T.map (tensorLeft S.X₁)).X₂) ⟶ ((T.map (tensorLeft S.X₁)).X₃) :=
    (tensorLeft S.X₁).map T.g
  let π₂ : ((T.map (tensorLeft S.X₂)).X₂) ⟶ ((T.map (tensorLeft S.X₂)).X₃) :=
    (tensorLeft S.X₂).map T.g
  let π₃ : ((T.map (tensorLeft S.X₃)).X₂) ⟶ ((T.map (tensorLeft S.X₃)).X₃) :=
    (tensorLeft S.X₃).map T.g
  let fK : ((S.map (tensorRight T.X₁)).X₁) ⟶ ((S.map (tensorRight T.X₁)).X₂) :=
    (tensorRight T.X₁).map S.f
  let fGp : ((S.map (tensorRight T.X₂)).X₁) ⟶ ((S.map (tensorRight T.X₂)).X₂) :=
    (tensorRight T.X₂).map S.f
  let fG : ((S.map (tensorRight T.X₃)).X₁) ⟶ ((S.map (tensorRight T.X₃)).X₂) :=
    (tensorRight T.X₃).map S.f
  let gK : ((S.map (tensorRight T.X₁)).X₂) ⟶ ((S.map (tensorRight T.X₁)).X₃) :=
    (tensorRight T.X₁).map S.g
  let gGp : ((S.map (tensorRight T.X₂)).X₂) ⟶ ((S.map (tensorRight T.X₂)).X₃) :=
    (tensorRight T.X₂).map S.g
  -- Proof comment: chase a refined lift through the flat-cover columns; the flat `𝒢'` row gives
  -- the key monomorphism, and the flat `S.X₃` column forces the correction term to come from the
  -- kernel row.
  rw [Preadditive.mono_iff_cancel_zero]
  intro A x hx
  obtain ⟨A₁, ρ₁, _hρ₁, x', hx'⟩ := surjective_up_to_refinements_of_epi π₁ x
  have hx'fπ : x' ≫ fGp ≫ π₂ = 0 := by
    calc
      x' ≫ fGp ≫ π₂ = x' ≫ π₁ ≫ fG := by
        simpa [colMap₁₂, fGp, fG, π₁, π₂, Category.assoc] using colMap₁₂.comm₂₃.symm
      _ = ρ₁ ≫ x ≫ fG := by
        simpa [fG, Category.assoc] using congrArg (fun t ↦ t ≫ fG) hx'
      _ = 0 := by
        simpa [fG, Category.assoc] using congrArg (fun t ↦ ρ₁ ≫ t) hx
  have hCol₂Exact : (T.map (tensorLeft S.X₂)).Exact :=
    (T.map (tensorLeft S.X₂)).exact_iff_exact_toComposableArrows.2 hCol₂.1
  obtain ⟨A₂, ρ₂, _hρ₂, y₂, hy₂⟩ := hCol₂Exact.exact_up_to_refinements (x' ≫ fGp) hx'fπ
  have hy₂gk₃ : y₂ ≫ gK ≫ k₃ = 0 := by
    calc
      y₂ ≫ gK ≫ k₃ = y₂ ≫ k₂ ≫ gGp := by
        simpa [colMap₂₃, gK, gGp, k₂, k₃, Category.assoc] using colMap₂₃.comm₁₂
      _ = ρ₂ ≫ x' ≫ fGp ≫ gGp := by
        simpa [gGp, Category.assoc] using congrArg (fun t ↦ t ≫ gGp) hy₂
      _ = 0 := by
        simpa [fGp, gGp, T, Category.assoc] using congrArg (fun t ↦ ρ₂ ≫ x' ≫ t)
          (S.map (tensorRight T.X₂)).zero
  have hy₂gk : y₂ ≫ gK = 0 := by
    exact (cancel_mono k₃).1 (by simpa [gK, k₃, Category.assoc] using hy₂gk₃)
  have hRowKExact : (S.map (tensorRight T.X₁)).Exact :=
    (S.map (tensorRight T.X₁)).exact_iff_exact_toComposableArrows.2 hRowK.1
  obtain ⟨A₃, ρ₃, _hρ₃, y₁, hy₁⟩ := hRowKExact.exact_up_to_refinements y₂ hy₂gk
  have hLiftEqComp : ρ₃ ≫ ρ₂ ≫ x' ≫ fGp = y₁ ≫ k₁ ≫ fGp := by
    calc
      ρ₃ ≫ ρ₂ ≫ x' ≫ fGp = ρ₃ ≫ y₂ ≫ k₂ := by
        simpa [fGp, k₂, Category.assoc] using congrArg (fun t ↦ ρ₃ ≫ t) hy₂.symm
      _ = y₁ ≫ fK ≫ k₂ := by
        simpa [fK, Category.assoc] using congrArg (fun t ↦ t ≫ k₂) hy₁
      _ = y₁ ≫ k₁ ≫ fGp := by
        simpa [colMap₁₂, fK, fGp, k₁, k₂, Category.assoc] using
          congrArg (fun t ↦ y₁ ≫ t) colMap₁₂.comm₁₂.symm
  have hLiftEq : ρ₃ ≫ ρ₂ ≫ x' = y₁ ≫ k₁ := by
    exact (cancel_mono fGp).1 (by simpa [fGp, Category.assoc] using hLiftEqComp)
  have hRefinedZero : ρ₃ ≫ ρ₂ ≫ ρ₁ ≫ x = 0 := by
    calc
      ρ₃ ≫ ρ₂ ≫ ρ₁ ≫ x = ρ₃ ≫ ρ₂ ≫ x' ≫ π₁ := by
        simpa [π₁, Category.assoc] using congrArg (fun t ↦ ρ₃ ≫ ρ₂ ≫ t) hx'.symm
      _ = y₁ ≫ k₁ ≫ π₁ := by
        simpa [π₁, Category.assoc] using congrArg (fun t ↦ t ≫ π₁) hLiftEq
      _ = 0 := by
        simpa [k₁, π₁, T, Category.assoc] using congrArg ((tensorLeft S.X₁).map) T.zero
  exact
    (cancel_epi ρ₁).1 <|
      (cancel_epi ρ₂).1 <|
        (cancel_epi ρ₃).1 <|
          by simpa [Category.assoc] using hRefinedZero

/-- Tensoring presheaves of modules on the right by a fixed module preserves zero morphisms. -/
instance tensorRight_preservesZeroMorphisms
    (𝒢 : PresheafOfModules (ringPresheaf 𝒪)) :
    (tensorRight 𝒢).PreservesZeroMorphisms := by
  -- Proof comment: `tensorRight 𝒢` is additive, so it preserves zero morphisms formally.
  exact Functor.preservesZeroMorphisms_of_additive (tensorRight 𝒢)

/-- Helper for Lemma 18.28.9: if the tensor factor is flat, then right tensoring preserves short
exact sequences of presheaf modules. -/
private theorem shortExact_map_tensorRight_of_isFlat
    (X : PresheafOfModules (ringPresheaf 𝒪))
    [IsFlat X]
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight X)).ShortExact := by
  -- Proof comment: this is exactly the defining exactness property packaged in `IsFlat X`.
  let hExact := IsFlat.exact_tensor (ℱ := X)
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (tensorRight X) :=
    (CategoryTheory.exactFunctor_iff (tensorRight X)).1 hExact |>.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X) :=
    (CategoryTheory.exactFunctor_iff (tensorRight X)).1 hExact |>.2
  exact hT.map_of_exact (tensorRight X)

/-- Helper for Lemma 18.28.9: right tensoring is always right exact, so it carries a short exact
sequence to an exact sequence whose right map remains an epimorphism. -/
private theorem tensorRight_mapsShortExact_to_exact_epi
    (X : PresheafOfModules (ringPresheaf 𝒪))
    (T : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hT : T.ShortExact) :
    (ComposableArrows.mk₂ ((tensorRight X).map T.f) ((tensorRight X).map T.g)).Exact ∧
      Epi ((tensorRight X).map T.g) := by
  let hRight :
      CategoryTheory.rightExactFunctor
        (PresheafOfModules (ringPresheaf 𝒪))
        (PresheafOfModules (ringPresheaf 𝒪))
        (tensorRight X) := by
    simpa [CategoryTheory.rightExactFunctor_iff] using
      (inferInstance :
        CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X))
  -- Proof comment: the Chapter 12 right-exactness criterion supplies the exact/epi package.
  exact
    (CategoryTheory.functor_rightExact_iff_maps_shortExact_to_exact_epi
      (A := PresheafOfModules (ringPresheaf 𝒪))
      (B := PresheafOfModules (ringPresheaf 𝒪))
      (F := tensorRight X)).1 hRight T hT

-- Proof sketch: resolve the right tensor factor by a short exact sequence with flat middle term,
-- apply the exactness built into flatness of `S.X₃`, and conclude with the snake lemma exactly as
-- in the textbook.
/-- Lemma 18.28.9 (1): if `0 ⟶ \mathcal F'' ⟶ \mathcal F' ⟶ \mathcal F ⟶ 0` is a short exact
sequence of presheaves of `\mathcal O`-modules and `\mathcal F` is flat, then tensoring on the
right by any presheaf `\mathcal G` preserves short exactness. -/
theorem shortExact_tensor_right_of_flat_quotient
    (𝒢 : PresheafOfModules (ringPresheaf 𝒪))
    (S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪)))
    (hS : S.ShortExact)
    [IsFlat S.X₃] :
    (S.map (tensorRight 𝒢)).ShortExact := by
  obtain ⟨𝒢', _h𝒢', π, hπ⟩ := exists_epi_from_flat (𝒪 := 𝒪) 𝒢
  let _ : Epi π := hπ
  have hMono :
      Mono ((tensorRight 𝒢).map S.f) :=
    tensorRightLeftMono_of_flat_cover (𝒪 := 𝒪) (π := π) S hS
  let hExactEpi := tensorRight_mapsShortExact_to_exact_epi (𝒪 := 𝒪) 𝒢 S hS
  -- Proof comment: right exactness supplies exactness and the epimorphic right map, and the
  -- flat-cover mono chase supplies the missing monomorphism on the left map.
  exact ShortComplex.ShortExact.mk'
    ((S.map (tensorRight 𝒢)).exact_iff_exact_toComposableArrows.2 hExactEpi.1)
    hMono
    hExactEpi.2

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/-- Helper for Lemma 18.28.9: forgetting sheaf module structure to the underlying presheaf module
category preserves short exact rows. -/
private theorem forgetShortExactOfShortExact
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (T.map (SheafOfModules.forget (ringSheaf J 𝒪))).ShortExact := by
  let F := SheafOfModules.forget (ringSheaf J 𝒪)
  let hExact :
      exactFunctor (Mod(𝒪)) (PresheafOfModules (ringSheaf J 𝒪).obj) F :=
    (ExactFunctor.of F).property
  let _ : CategoryTheory.Limits.PreservesFiniteLimits F :=
    (CategoryTheory.exactFunctor_iff F).1 hExact |>.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F :=
    (CategoryTheory.exactFunctor_iff F).1 hExact |>.2
  -- Proof comment: once the forgetful functor is recorded as exact, mapped short exactness is
  -- immediate.
  exact hT.map_of_exact F

/-- Tensoring sheaves of modules on the right by a fixed module preserves zero morphisms. -/
instance tensorRight_preservesZeroMorphisms
    (𝒢 : Mod(𝒪)) :
    (tensorRight 𝒢).PreservesZeroMorphisms := by
  -- Proof comment: `tensorRight 𝒢` is additive, hence preserves zero morphisms.
  exact Functor.preservesZeroMorphisms_of_additive (tensorRight 𝒢)

/-- Helper for Lemma 18.28.9: if the tensor factor is flat, then right tensoring preserves short
exact sequences of sheaf modules. -/
private theorem shortExact_map_tensorRight_of_isFlat
    (X : Mod(𝒪))
    [IsFlat 𝒪 X]
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorRight X)).ShortExact := by
  -- Proof comment: flatness of `X` is defined by exactness of `tensorRight X`.
  let hExact := (inferInstance : IsFlat 𝒪 X).exact_tensor
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (tensorRight X) :=
    (CategoryTheory.exactFunctor_iff (tensorRight X)).1 hExact |>.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X) :=
    (CategoryTheory.exactFunctor_iff (tensorRight X)).1 hExact |>.2
  exact hT.map_of_exact (tensorRight X)

/-- Helper for Lemma 18.28.9: right tensoring of sheaf modules is right exact, so it preserves
exactness and epimorphy of the right map in a short exact sequence. -/
private theorem tensorRight_mapsShortExact_to_exact_epi
    (X : Mod(𝒪))
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (ComposableArrows.mk₂ ((tensorRight X).map T.f) ((tensorRight X).map T.g)).Exact ∧
      Epi ((tensorRight X).map T.g) := by
  let hRight :
      CategoryTheory.rightExactFunctor
        (Mod(𝒪))
        (Mod(𝒪))
        (tensorRight X) := by
    simpa [CategoryTheory.rightExactFunctor_iff] using
      (inferInstance :
        CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X))
  -- Proof comment: use the standard right-exact functor criterion on short exact rows.
  exact
    (CategoryTheory.functor_rightExact_iff_maps_shortExact_to_exact_epi
      (A := Mod(𝒪))
      (B := Mod(𝒪))
      (F := tensorRight X)).1 hRight T hT

/-- Helper for Lemma 18.28.9: short exactness of a mapped short complex is invariant under a
natural isomorphism of functors. -/
private theorem shortExact_iff_of_functor_iso
    {A : Type*} {B : Type*}
    [Category A] [Category B]
    [CategoryTheory.Limits.HasZeroMorphisms A] [CategoryTheory.Limits.HasZeroMorphisms B]
    {F G : A ⥤ B}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (e : F ≅ G)
    (T : ShortComplex A) :
    (T.map F).ShortExact ↔ (T.map G).ShortExact := by
  let i : T.map F ≅ T.map G :=
    ShortComplex.isoMk
      (e.app T.X₁)
      (e.app T.X₂)
      (e.app T.X₃)
      (by simpa using e.hom.naturality T.f)
      (by simpa using e.hom.naturality T.g)
  constructor
  · -- Proof comment: transport short exactness forward across the induced short-complex
    -- isomorphism.
    intro h
    exact ShortComplex.shortExact_of_iso i h
  · -- Proof comment: transport short exactness backward along the inverse isomorphism.
    intro h
    exact ShortComplex.shortExact_of_iso i.symm h

/-- Helper for Lemma 18.28.9: flatness of `X` makes left tensoring exact by transporting the
exactness of right tensoring across the braiding isomorphism. -/
private theorem tensorLeft_exact_of_isFlat
    (X : Mod(𝒪))
    [IsFlat 𝒪 X] :
    exactFunctor
      (Mod(𝒪))
      (Mod(𝒪))
      (tensorLeft X) := by
  let hExact := (inferInstance : IsFlat 𝒪 X).exact_tensor
  -- Proof comment: `tensorLeft X` is naturally isomorphic to `tensorRight X` in the braided
  -- monoidal structure, so exactness transports across that comparison.
  rw [CategoryTheory.exactFunctor_iff] at hExact ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (tensorRight X) := hExact.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorRight X) := hExact.2
  exact
    ⟨CategoryTheory.Limits.preservesFiniteLimits_of_natIso
        (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X).symm,
      CategoryTheory.Limits.preservesFiniteColimits_of_natIso
        (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X).symm⟩

/-- Helper for Lemma 18.28.9: if `X` is flat, then tensoring a short exact sequence on the left by
`X` stays short exact. -/
private theorem shortExact_map_tensorLeft_of_isFlat
    (X : Mod(𝒪))
    [IsFlat 𝒪 X]
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (T.map (tensorLeft X)).ShortExact := by
  let hExact := tensorLeft_exact_of_isFlat (J := J) (𝒪 := 𝒪) X
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (tensorLeft X) :=
    (CategoryTheory.exactFunctor_iff (tensorLeft X)).1 hExact |>.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorLeft X) :=
    (CategoryTheory.exactFunctor_iff (tensorLeft X)).1 hExact |>.2
  -- Proof comment: once left tensoring is exact, mapped short exactness is immediate.
  exact hT.map_of_exact (tensorLeft X)

/-- Helper for Lemma 18.28.9: left tensoring of sheaf modules is always right exact, so it
carries a short exact sequence to an exact sequence whose right map remains an epimorphism. -/
private theorem tensorLeft_mapsShortExact_to_exact_epi
    (X : Mod(𝒪))
    (T : ShortComplex (Mod(𝒪)))
    (hT : T.ShortExact) :
    (ComposableArrows.mk₂ ((tensorLeft X).map T.f) ((tensorLeft X).map T.g)).Exact ∧
      Epi ((tensorLeft X).map T.g) := by
  let e := CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight X
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (tensorLeft X) :=
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e.symm
  let hRight :
      CategoryTheory.rightExactFunctor
        (Mod(𝒪))
        (Mod(𝒪))
        (tensorLeft X) := by
    simpa [CategoryTheory.rightExactFunctor_iff] using
      (inferInstance :
        CategoryTheory.Limits.PreservesFiniteColimits (tensorLeft X))
  -- Proof comment: braiding again identifies left tensor with the standard right-exact functor.
  exact
    (CategoryTheory.functor_rightExact_iff_maps_shortExact_to_exact_epi
      (A := Mod(𝒪))
      (B := Mod(𝒪))
      (F := tensorLeft X)).1 hRight T hT

/-- Helper for Lemma 18.28.9: forgetting sheaf structure commutes with tensoring on the right. -/
private noncomputable def tensorRightCommIso
    (X : Mod(𝒪)) :
    SheafOfModules.forget (ringSheaf J 𝒪) ⋙
        CategoryTheory.MonoidalCategory.tensorRight
          ((SheafOfModules.forget (ringSheaf J 𝒪)).obj X) ≅
      CategoryTheory.MonoidalCategory.tensorRight X ⋙
        SheafOfModules.forget (ringSheaf J 𝒪) := by
  -- Proof comment: this is the canonical monoidal comparison for the forgetful functor,
  -- specialized to tensoring on the right by `X`.
  refine NatIso.ofComponents
    (fun Y ↦ Functor.Monoidal.μIso (SheafOfModules.forget (ringSheaf J 𝒪)) Y X) ?_
  intro Y Z f
  simpa using
    Functor.Monoidal.μIso_hom_natural_right
      (F := SheafOfModules.forget (ringSheaf J 𝒪)) Y f

/-- Helper for Lemma 18.28.9: the sheaf theorem reduces to the same flat-cover mono chase inside
the ringed-site module category. -/
private theorem sheafTensorRightLeftMono_of_flat_cover
    {𝒢 𝒢' : Mod(𝒪)}
    (π : 𝒢' ⟶ 𝒢)
    [Epi π] [IsFlat 𝒪 𝒢']
    (S : ShortComplex (Mod(𝒪)))
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] :
    Mono ((tensorRight 𝒢).map S.f) := by
  let T : ShortComplex (Mod(𝒪)) := ShortComplex.kernelSequence π
  have hT : T.ShortExact := by
    -- Proof comment: use the canonical short exact kernel sequence of the flat cover.
    exact ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact π) inferInstance inferInstance
  let hRowGp : (S.map (tensorRight 𝒢')).ShortExact :=
    shortExact_map_tensorRight_of_isFlat (J := J) (𝒪 := 𝒪) 𝒢' S hS
  let hRowK := tensorRight_mapsShortExact_to_exact_epi (J := J) (𝒪 := 𝒪) T.X₁ S hS
  let hCol₁ := tensorLeft_mapsShortExact_to_exact_epi (J := J) (𝒪 := 𝒪) S.X₁ T hT
  let hCol₂ := tensorLeft_mapsShortExact_to_exact_epi (J := J) (𝒪 := 𝒪) S.X₂ T hT
  let hCol₃ : (T.map (tensorLeft S.X₃)).ShortExact :=
    shortExact_map_tensorLeft_of_isFlat (J := J) (𝒪 := 𝒪) S.X₃ T hT
  let colMap₁₂ :
      T.map (tensorLeft S.X₁) ⟶ T.map (tensorLeft S.X₂) :=
    T.mapNatTrans
      ((CategoryTheory.MonoidalCategory.tensoringLeft (Mod(𝒪))).map S.f)
  let colMap₂₃ :
      T.map (tensorLeft S.X₂) ⟶ T.map (tensorLeft S.X₃) :=
    T.mapNatTrans
      ((CategoryTheory.MonoidalCategory.tensoringLeft (Mod(𝒪))).map S.g)
  let k₁ : ((T.map (tensorLeft S.X₁)).X₁) ⟶ ((T.map (tensorLeft S.X₁)).X₂) :=
    (tensorLeft S.X₁).map T.f
  let k₂ : ((T.map (tensorLeft S.X₂)).X₁) ⟶ ((T.map (tensorLeft S.X₂)).X₂) :=
    (tensorLeft S.X₂).map T.f
  let k₃ : ((T.map (tensorLeft S.X₃)).X₁) ⟶ ((T.map (tensorLeft S.X₃)).X₂) :=
    (tensorLeft S.X₃).map T.f
  let π₁ : ((T.map (tensorLeft S.X₁)).X₂) ⟶ ((T.map (tensorLeft S.X₁)).X₃) :=
    (tensorLeft S.X₁).map T.g
  let π₂ : ((T.map (tensorLeft S.X₂)).X₂) ⟶ ((T.map (tensorLeft S.X₂)).X₃) :=
    (tensorLeft S.X₂).map T.g
  let π₃ : ((T.map (tensorLeft S.X₃)).X₂) ⟶ ((T.map (tensorLeft S.X₃)).X₃) :=
    (tensorLeft S.X₃).map T.g
  let fK : ((S.map (tensorRight T.X₁)).X₁) ⟶ ((S.map (tensorRight T.X₁)).X₂) :=
    (tensorRight T.X₁).map S.f
  let fGp : ((S.map (tensorRight T.X₂)).X₁) ⟶ ((S.map (tensorRight T.X₂)).X₂) :=
    (tensorRight T.X₂).map S.f
  let fG : ((S.map (tensorRight T.X₃)).X₁) ⟶ ((S.map (tensorRight T.X₃)).X₂) :=
    (tensorRight T.X₃).map S.f
  let gK : ((S.map (tensorRight T.X₁)).X₂) ⟶ ((S.map (tensorRight T.X₁)).X₃) :=
    (tensorRight T.X₁).map S.g
  let gGp : ((S.map (tensorRight T.X₂)).X₂) ⟶ ((S.map (tensorRight T.X₂)).X₃) :=
    (tensorRight T.X₂).map S.g
  -- Proof comment: repeat the presheaf refinement chase inside the sheaf module category.
  rw [Preadditive.mono_iff_cancel_zero]
  intro A x hx
  obtain ⟨A₁, ρ₁, _hρ₁, x', hx'⟩ := surjective_up_to_refinements_of_epi π₁ x
  have hx'fπ : x' ≫ fGp ≫ π₂ = 0 := by
    calc
      x' ≫ fGp ≫ π₂ = x' ≫ π₁ ≫ fG := by
        simpa [colMap₁₂, fGp, fG, π₁, π₂, Category.assoc] using colMap₁₂.comm₂₃.symm
      _ = ρ₁ ≫ x ≫ fG := by
        simpa [fG, Category.assoc] using congrArg (fun t ↦ t ≫ fG) hx'
      _ = 0 := by
        simpa [fG, Category.assoc] using congrArg (fun t ↦ ρ₁ ≫ t) hx
  have hCol₂Exact : (T.map (tensorLeft S.X₂)).Exact :=
    (T.map (tensorLeft S.X₂)).exact_iff_exact_toComposableArrows.2 hCol₂.1
  obtain ⟨A₂, ρ₂, _hρ₂, y₂, hy₂⟩ := hCol₂Exact.exact_up_to_refinements (x' ≫ fGp) hx'fπ
  have hy₂gk₃ : y₂ ≫ gK ≫ k₃ = 0 := by
    calc
      y₂ ≫ gK ≫ k₃ = y₂ ≫ k₂ ≫ gGp := by
        simpa [colMap₂₃, gK, gGp, k₂, k₃, Category.assoc] using colMap₂₃.comm₁₂
      _ = ρ₂ ≫ x' ≫ fGp ≫ gGp := by
        simpa [gGp, Category.assoc] using congrArg (fun t ↦ t ≫ gGp) hy₂
      _ = 0 := by
        simpa [fGp, gGp, T, Category.assoc] using congrArg (fun t ↦ ρ₂ ≫ x' ≫ t)
          (S.map (tensorRight T.X₂)).zero
  have hy₂gk : y₂ ≫ gK = 0 := by
    exact (cancel_mono k₃).1 (by simpa [gK, k₃, Category.assoc] using hy₂gk₃)
  have hRowKExact : (S.map (tensorRight T.X₁)).Exact :=
    (S.map (tensorRight T.X₁)).exact_iff_exact_toComposableArrows.2 hRowK.1
  obtain ⟨A₃, ρ₃, _hρ₃, y₁, hy₁⟩ := hRowKExact.exact_up_to_refinements y₂ hy₂gk
  have hLiftEqComp : ρ₃ ≫ ρ₂ ≫ x' ≫ fGp = y₁ ≫ k₁ ≫ fGp := by
    calc
      ρ₃ ≫ ρ₂ ≫ x' ≫ fGp = ρ₃ ≫ y₂ ≫ k₂ := by
        simpa [fGp, k₂, Category.assoc] using congrArg (fun t ↦ ρ₃ ≫ t) hy₂.symm
      _ = y₁ ≫ fK ≫ k₂ := by
        simpa [fK, Category.assoc] using congrArg (fun t ↦ t ≫ k₂) hy₁
      _ = y₁ ≫ k₁ ≫ fGp := by
        simpa [colMap₁₂, fK, fGp, k₁, k₂, Category.assoc] using
          congrArg (fun t ↦ y₁ ≫ t) colMap₁₂.comm₁₂.symm
  have hLiftEq : ρ₃ ≫ ρ₂ ≫ x' = y₁ ≫ k₁ := by
    exact (cancel_mono fGp).1 (by simpa [fGp, Category.assoc] using hLiftEqComp)
  have hRefinedZero : ρ₃ ≫ ρ₂ ≫ ρ₁ ≫ x = 0 := by
    calc
      ρ₃ ≫ ρ₂ ≫ ρ₁ ≫ x = ρ₃ ≫ ρ₂ ≫ x' ≫ π₁ := by
        simpa [π₁, Category.assoc] using congrArg (fun t ↦ ρ₃ ≫ ρ₂ ≫ t) hx'.symm
      _ = y₁ ≫ k₁ ≫ π₁ := by
        simpa [π₁, Category.assoc] using congrArg (fun t ↦ t ≫ π₁) hLiftEq
      _ = 0 := by
        simpa [k₁, π₁, T, Category.assoc] using congrArg ((tensorLeft S.X₁).map) T.zero
  exact
    (cancel_epi ρ₁).1 <|
      (cancel_epi ρ₂).1 <|
        (cancel_epi ρ₃).1 <|
          by simpa [Category.assoc] using hRefinedZero

-- Proof sketch: argue exactly as in the presheaf case, replacing the presheaf tensor product by
-- the sheaf tensor product and using flatness of `S.X₃` as a sheaf of modules.
/-- Lemma 18.28.9 (2): if `(\mathcal C, J)` is a site, `0 ⟶ \mathcal F'' ⟶ \mathcal F' ⟶
\mathcal F ⟶ 0` is a short exact sequence of sheaves of `\mathcal O`-modules, and `\mathcal F`
is flat, then tensoring on the right by any sheaf `\mathcal G` preserves short exactness. -/
theorem shortExact_tensor_right_of_flat_quotient
    (𝒢 : Mod(𝒪))
    (S : ShortComplex (Mod(𝒪)))
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] :
    (S.map (tensorRight 𝒢)).ShortExact := by
  obtain ⟨𝒢', _h𝒢', π, hπ⟩ :=
    SheafOfModules.RingedSite.exists_epi_from_flat (J := J) (𝒪 := 𝒪) 𝒢
  let _ : Epi π := hπ
  have hMono :
      Mono ((tensorRight 𝒢).map S.f) :=
    sheafTensorRightLeftMono_of_flat_cover (J := J) (𝒪 := 𝒪) (π := π) S hS
  let hExactEpi := tensorRight_mapsShortExact_to_exact_epi (J := J) (𝒪 := 𝒪) 𝒢 S hS
  -- Proof comment: right exactness handles exactness and epimorphy, and the flat-cover diagram
  -- supplies the remaining monomorphism on the left map.
  exact ShortComplex.ShortExact.mk'
    ((S.map (tensorRight 𝒢)).exact_iff_exact_toComposableArrows.2 hExactEpi.1)
    hMono
    hExactEpi.2

end SheafOfModules.RingedSite
