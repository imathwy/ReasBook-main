import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_10_1
import StacksProject_2024.stacks_project.Chap12.Lemma_12_5_20
import StacksProject_2024.stacks_project.Chap12.Remark_12_29_2
import StacksProject_2024.stacks_project.Chap18.Lemma_18_24_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite CategoryTheory.ObjectProperty CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{max u v})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]

/- Domain-style sampling for Lemma 18.24.4:
- primary domain: weak Serre subcategories of module categories on a ringed site, specialized here
  to the chaotic topology and the quasi-coherent owner predicate;
- sampled owner declarations:
  `ObjectProperty.IsWeakSerreClass`,
  `ringedSiteModuleCategory`,
  `SheafOfModules.isQuasicoherent`,
  `SheafOfModules.RingedSite.IsQuasicoherent`;
- best owner abstraction:
  the chapter owner category `ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪` together
  with the ambient object-property owner
  `SheafOfModules.isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)`;
- primitive data:
  the chaotic-site ring sheaf `𝒪` and the flatness hypothesis on each restriction map
  `𝒪(V) ⟶ 𝒪(U)`;
- derived API:
  the instance-valued predicate `ℱ.IsQuasicoherent` and the resulting weak-Serre closure theorem.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that quasi-coherent `\mathcal O`-modules form a weak
  Serre subcategory under the flatness hypothesis;
- `core/canonical`: `ringedSiteModuleCategory`, `ObjectProperty.IsWeakSerreClass`, and
  `SheafOfModules.isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)`;
- `bridge/view`: the instance form `ℱ.IsQuasicoherent` attached to that owner predicate.

The theorem below therefore keeps the source-facing weak-Serre statement, but states it over the
canonical object property `SheafOfModules.isQuasicoherent (ringSheaf (⊥ :
GrothendieckTopology C) 𝒪)` instead of an ad hoc lambda. -/

/-- Helper for Lemma 18.24.4: exactness of the three consecutive short complexes in a five-term
row assembles into exactness of the corresponding `ComposableArrows ... 4`. -/
private lemma mk₄_exact
    {A : Type*} [Category A] [Abelian A]
    {X₀ X₁ X₂ X₃ X₄ : A}
    {f : X₀ ⟶ X₁} {g : X₁ ⟶ X₂} {h : X₂ ⟶ X₃} {i : X₃ ⟶ X₄}
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) (hhi : h ≫ i = 0)
    (hex₀ : (ShortComplex.mk f g hfg).Exact)
    (hex₁ : (ShortComplex.mk g h hgh).Exact)
    (hex₂ : (ShortComplex.mk h i hhi).Exact) :
    (ComposableArrows.mk₄ f g h i).Exact := by
  -- Proof comment: the source-facing five-term exactness condition is definitionally the same as
  -- exactness of the three adjacent short complexes together with the vanishing composites.
  refine ⟨?_, ?_⟩
  · refine ⟨?_⟩
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
      omega
    rcases hj' with rfl | rfl | rfl
    · dsimp [ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂]
      exact hfg
    · dsimp [ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂]
      exact hgh
    · dsimp [ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂]
      exact hhi
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by
      omega
    rcases hj' with rfl | rfl | rfl
    · simpa using hex₀
    · simpa using hex₁
    · simpa using hex₂

/-- Helper for Lemma 18.24.4: exact functors remain exact after composition. -/
private theorem exactFunctor_comp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    {F : A ⥤ B} {G : B ⥤ D}
    (hF : exactFunctor A B F) (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := by
  -- Proof comment: exactness is preservation of finite limits and finite colimits, and both
  -- preservation properties compose.
  rw [exactFunctor_iff] at hF hG ⊢
  let _ : Limits.PreservesFiniteLimits F := hF.1
  let _ : Limits.PreservesFiniteColimits F := hF.2
  let _ : Limits.PreservesFiniteLimits G := hG.1
  let _ : Limits.PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.24.4: evaluation on the chaotic site at a fixed object, viewed as a
module-valued functor. -/
private abbrev chaoticEvaluation (U : C) :
    ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪 ⥤
      ModuleCat.{max u v} (𝒪.obj.obj (op U)) :=
  SheafOfModules.evaluation (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) (op U)

/-- Helper for Lemma 18.24.4: extension of scalars along a chaotic-site restriction map. -/
private abbrev chaoticExtendScalars {U V : C} (f : U ⟶ V) :
    ModuleCat.{max u v} (𝒪.obj.obj (op V)) ⥤ ModuleCat.{max u v} (𝒪.obj.obj (op U)) :=
  ModuleCat.extendScalars.{max u v, max u v, max u v} ((𝒪.obj.map f.op).hom)

/-- Helper for Lemma 18.24.4: evaluate at `V` and then extend scalars along `U ⟶ V`. -/
private abbrev chaoticUpperFunctor {U V : C} (f : U ⟶ V) :
    ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪 ⥤
      ModuleCat.{max u v} (𝒪.obj.obj (op U)) :=
  chaoticEvaluation (𝒪 := 𝒪) V ⋙ chaoticExtendScalars (𝒪 := 𝒪) f

/-- Helper for Lemma 18.24.4: evaluation on the chaotic site preserves zero morphisms. -/
private instance chaoticEvaluation_preservesZeroMorphisms (U : C) :
    (chaoticEvaluation (𝒪 := 𝒪) U).PreservesZeroMorphisms where
  map_zero := by
    intro ℱ 𝒢
    rfl

/-- Helper for Lemma 18.24.4: the composed evaluation-plus-base-change functor preserves zero
morphisms. -/
private instance chaoticUpperFunctor_preservesZeroMorphisms {U V : C} (f : U ⟶ V) :
    (chaoticUpperFunctor (𝒪 := 𝒪) f).PreservesZeroMorphisms where
  map_zero := by
    intro ℱ 𝒢
    rfl

/-- Helper for Lemma 18.24.4: evaluation at a fixed object on the chaotic site is exact. -/
private theorem chaoticEvaluation_exact (U : C) :
    exactFunctor _ _ (chaoticEvaluation (𝒪 := 𝒪) U) := by
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.24.4: flat restriction maps make chaotic-site extension of scalars
exact. -/
private theorem chaoticExtendScalars_exact {U V : C} (f : U ⟶ V)
    (hflat : RingHom.Flat ((𝒪.obj.map f.op).hom)) :
    exactFunctor _ _ (chaoticExtendScalars (𝒪 := 𝒪) f) := by
  simpa [chaoticExtendScalars] using extendScalars_exact_of_flat ((𝒪.obj.map f.op).hom) hflat

/-- Helper for Lemma 18.24.4: apply a functor to each arrow in a five-term composable sequence. -/
private abbrev mapComposableArrows₄
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    (F : A ⥤ B) (S : ComposableArrows A 4) :
    ComposableArrows B 4 :=
  ComposableArrows.mk₄
    (F.map (S.map' 0 1))
    (F.map (S.map' 1 2))
    (F.map (S.map' 2 3))
    (F.map (S.map' 3 4))

/-- Helper for Lemma 18.24.4: the sectionwise tensor-comparison maps are natural in the module
sheaf argument. -/
private lemma chaoticTensorSectionsMap_naturality
    {ℱ 𝒢 : ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪}
    (α : ℱ ⟶ 𝒢) {U V : C} (f : U ⟶ V) :
    ((chaoticUpperFunctor (𝒪 := 𝒪) f).map α) ≫ chaoticTensorSectionsMap 𝒪 𝒢 f =
      chaoticTensorSectionsMap 𝒪 ℱ f ≫ ((chaoticEvaluation (𝒪 := 𝒪) U).map α) := by
  let adj := ModuleCat.extendRestrictScalarsAdj ((𝒪.obj.map f.op).hom)
  let evalU := chaoticEvaluation (𝒪 := 𝒪) U
  let evalV := chaoticEvaluation (𝒪 := 𝒪) V
  let upperFunctor := chaoticUpperFunctor (𝒪 := 𝒪) f
  -- Proof comment: transpose both sides across the extension/restriction adjunction and use the
  -- ordinary naturality square for the restriction map of `α`.
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simpa [adj, evalU, evalV, upperFunctor, chaoticEvaluation, chaoticUpperFunctor,
    chaoticExtendScalars, chaoticTensorSectionsMap_def] using α.1.naturality f.op

/-- Helper for Lemma 18.24.4: the five lemma upgrades the middle comparison map to an
isomorphism once the two rows are exact and the four outer comparisons have the expected
epi/iso/iso/mono hypotheses. -/
private lemma middleComparison_isIso
    {A : Type*} [Category A] [Abelian A]
    {S T : ComposableArrows A 4} (Ψ : S ⟶ T)
    (hS : S.Exact) (hT : T.Exact)
    [Epi (ComposableArrows.app' Ψ 0)]
    [IsIso (ComposableArrows.app' Ψ 1)]
    [IsIso (ComposableArrows.app' Ψ 3)]
    [Mono (ComposableArrows.app' Ψ 4)] :
    IsIso (ComposableArrows.app' Ψ 2) := by
  -- Proof comment: this is exactly the abelian five lemma on a length-four composable-arrow row.
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hS hT Ψ inferInstance inferInstance
    inferInstance inferInstance

-- Proof sketch: use the five-term exact-sequence criterion for weak Serre subcategories. For an
-- exact sequence in `Mod(\mathcal O)`, exactness of sections on the chaotic site and flatness of
-- every restriction map make the tensor-comparison rows exact. Applying the tensor criterion for
-- quasi-coherence and then the five lemma shows the middle term is quasi-coherent whenever the
-- outer four terms are.
/-- Lemma 18.24.4: if every restriction map `\mathcal O(V) \to \mathcal O(U)` on the chaotic site
is flat, then quasi-coherent `\mathcal O`-modules form a weak Serre subcategory of
`\operatorname{Mod}(\mathcal O)`. -/
theorem quasicoherentModuleProperty_isWeakSerreSubcategory
    (hflat : ∀ ⦃U V : C⦄ (f : U ⟶ V), RingHom.Flat ((𝒪.obj.map f.op).hom)) :
    IsWeakSerreClass (isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) :=
  by
    refine
      { toNonempty := ⟨(0 : ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪), inferInstance⟩
        prop_X₂_of_exact₄ := ?_ }
    intro S hS h₀ h₁ h₃ h₄
    -- Proof comment: Lemma 18.24.3 is stated for the instance-valued owner
    -- `ℱ.IsQuasicoherent`, so first unfold the object property on the five relevant terms.
    change (S.obj 0).IsQuasicoherent at h₀
    change (S.obj 1).IsQuasicoherent at h₁
    change (S.obj 3).IsQuasicoherent at h₃
    change (S.obj 4).IsQuasicoherent at h₄
    change (S.obj 2).IsQuasicoherent
    rw [SheafOfModules.isQuasicoherent_iff_tensor_sections_map_isIso 𝒪] at h₀ h₁ h₃ h₄ ⊢
    intro U V f
    let hLowerFunctor := chaoticEvaluation_exact (𝒪 := 𝒪) U
    let hUpperFunctor :
        exactFunctor _ _ (chaoticUpperFunctor (𝒪 := 𝒪) f) :=
      exactFunctor_comp
        (chaoticEvaluation_exact (𝒪 := 𝒪) V)
        (chaoticExtendScalars_exact (𝒪 := 𝒪) f (hflat f))
    letI : PreservesFiniteLimits (chaoticEvaluation (𝒪 := 𝒪) U) :=
      (exactFunctor_iff _).1 hLowerFunctor |>.1
    letI : PreservesFiniteColimits (chaoticEvaluation (𝒪 := 𝒪) U) :=
      (exactFunctor_iff _).1 hLowerFunctor |>.2
    letI : PreservesFiniteLimits (chaoticUpperFunctor (𝒪 := 𝒪) f) :=
      (exactFunctor_iff _).1 hUpperFunctor |>.1
    letI : PreservesFiniteColimits (chaoticUpperFunctor (𝒪 := 𝒪) f) :=
      (exactFunctor_iff _).1 hUpperFunctor |>.2
    have hLower :
        (mapComposableArrows₄ (chaoticEvaluation (𝒪 := 𝒪) U) S).Exact := by
      -- Proof comment: exactness survives evaluation at `U` on each adjacent short complex.
      refine mk₄_exact ?_ ?_ ?_ ?_ ?_ ?_
      · simpa [mapComposableArrows₄, chaoticEvaluation, Functor.map_comp] using
          congrArg (chaoticEvaluation (𝒪 := 𝒪) U).map (hS.toIsComplex.zero 0)
      · simpa [mapComposableArrows₄, chaoticEvaluation, Functor.map_comp] using
          congrArg (chaoticEvaluation (𝒪 := 𝒪) U).map (hS.toIsComplex.zero 1)
      · simpa [mapComposableArrows₄, chaoticEvaluation, Functor.map_comp] using
          congrArg (chaoticEvaluation (𝒪 := 𝒪) U).map (hS.toIsComplex.zero 2)
      · simpa [mapComposableArrows₄, chaoticEvaluation] using
          (hS.exact 0).map (chaoticEvaluation (𝒪 := 𝒪) U)
      · simpa [mapComposableArrows₄, chaoticEvaluation] using
          (hS.exact 1).map (chaoticEvaluation (𝒪 := 𝒪) U)
      · simpa [mapComposableArrows₄, chaoticEvaluation] using
          (hS.exact 2).map (chaoticEvaluation (𝒪 := 𝒪) U)
    have hUpper :
        (mapComposableArrows₄ (chaoticUpperFunctor (𝒪 := 𝒪) f) S).Exact := by
      -- Proof comment: evaluate at `V` first, then extend scalars along the flat restriction map.
      refine mk₄_exact ?_ ?_ ?_ ?_ ?_ ?_
      · simpa [mapComposableArrows₄, chaoticUpperFunctor, chaoticEvaluation, chaoticExtendScalars,
          Functor.map_comp] using
          congrArg (chaoticUpperFunctor (𝒪 := 𝒪) f).map (hS.toIsComplex.zero 0)
      · simpa [mapComposableArrows₄, chaoticUpperFunctor, chaoticEvaluation, chaoticExtendScalars,
          Functor.map_comp] using
          congrArg (chaoticUpperFunctor (𝒪 := 𝒪) f).map (hS.toIsComplex.zero 1)
      · simpa [mapComposableArrows₄, chaoticUpperFunctor, chaoticEvaluation, chaoticExtendScalars,
          Functor.map_comp] using
          congrArg (chaoticUpperFunctor (𝒪 := 𝒪) f).map (hS.toIsComplex.zero 2)
      · simpa [mapComposableArrows₄, chaoticUpperFunctor, chaoticEvaluation, chaoticExtendScalars]
          using (hS.exact 0).map (chaoticUpperFunctor (𝒪 := 𝒪) f)
      · simpa [mapComposableArrows₄, chaoticUpperFunctor, chaoticEvaluation, chaoticExtendScalars]
          using (hS.exact 1).map (chaoticUpperFunctor (𝒪 := 𝒪) f)
      · simpa [mapComposableArrows₄, chaoticUpperFunctor, chaoticEvaluation, chaoticExtendScalars]
          using (hS.exact 2).map (chaoticUpperFunctor (𝒪 := 𝒪) f)
    let Ψ :
        mapComposableArrows₄ (chaoticUpperFunctor (𝒪 := 𝒪) f) S ⟶
          mapComposableArrows₄ (chaoticEvaluation (𝒪 := 𝒪) U) S :=
      ComposableArrows.homMk₄
        (chaoticTensorSectionsMap 𝒪 (S.obj 0) f)
        (chaoticTensorSectionsMap 𝒪 (S.obj 1) f)
        (chaoticTensorSectionsMap 𝒪 (S.obj 2) f)
        (chaoticTensorSectionsMap 𝒪 (S.obj 3) f)
        (chaoticTensorSectionsMap 𝒪 (S.obj 4) f)
        (by
          -- Proof comment: each ladder square is just naturality of the tensor-comparison map.
          simpa [mapComposableArrows₄, chaoticUpperFunctor, chaoticEvaluation, chaoticExtendScalars]
            using
            chaoticTensorSectionsMap_naturality (𝒪 := 𝒪) (S.map' 0 1) f)
        (by
          simpa [mapComposableArrows₄, chaoticUpperFunctor, chaoticEvaluation, chaoticExtendScalars]
            using
            chaoticTensorSectionsMap_naturality (𝒪 := 𝒪) (S.map' 1 2) f)
        (by
          simpa [mapComposableArrows₄, chaoticUpperFunctor, chaoticEvaluation, chaoticExtendScalars]
            using
            chaoticTensorSectionsMap_naturality (𝒪 := 𝒪) (S.map' 2 3) f)
        (by
          simpa [mapComposableArrows₄, chaoticUpperFunctor, chaoticEvaluation, chaoticExtendScalars]
            using
            chaoticTensorSectionsMap_naturality (𝒪 := 𝒪) (S.map' 3 4) f)
    have h₀iso : IsIso (ComposableArrows.app' Ψ 0) := by
      simpa [Ψ] using h₀ f
    have h₁iso : IsIso (ComposableArrows.app' Ψ 1) := by
      simpa [Ψ] using h₁ f
    have h₃iso : IsIso (ComposableArrows.app' Ψ 3) := by
      simpa [Ψ] using h₃ f
    have h₄iso : IsIso (ComposableArrows.app' Ψ 4) := by
      simpa [Ψ] using h₄ f
    have h₀epi : Epi (ComposableArrows.app' Ψ 0) := by
      letI : IsIso (ComposableArrows.app' Ψ 0) := h₀iso
      infer_instance
    have h₄mono : Mono (ComposableArrows.app' Ψ 4) := by
      letI : IsIso (ComposableArrows.app' Ψ 4) := h₄iso
      infer_instance
    -- Proof comment: with exact rows and outer comparison isomorphisms in place, the five lemma
    -- gives the desired isomorphism on the middle tensor-comparison map.
    letI : Epi (ComposableArrows.app' Ψ 0) := h₀epi
    letI : IsIso (ComposableArrows.app' Ψ 1) := h₁iso
    letI : IsIso (ComposableArrows.app' Ψ 3) := h₃iso
    letI : Mono (ComposableArrows.app' Ψ 4) := h₄mono
    have h₂iso : IsIso (ComposableArrows.app' Ψ 2) :=
      middleComparison_isIso Ψ hUpper hLower
    simpa [Ψ] using h₂iso

/-- Under flat restriction maps on the chaotic site, quasi-coherent `\mathcal O`-modules carry
the canonical weak-Serre structure. -/
instance isQuasicoherent_isWeakSerreClass
    [Fact (∀ ⦃U V : C⦄ (f : U ⟶ V), RingHom.Flat ((𝒪.obj.map f.op).hom))] :
    IsWeakSerreClass (isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)) :=
  quasicoherentModuleProperty_isWeakSerreSubcategory 𝒪 Fact.out

end SheafOfModules
