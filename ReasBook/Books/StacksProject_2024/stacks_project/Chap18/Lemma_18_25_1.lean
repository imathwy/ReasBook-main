import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap10.Lemma_10_107_14
import StacksProject_2024.Chap07.Definition_7_43_7
import StacksProject_2024.Chap07.Lemma_7_43_8
import StacksProject_2024.Chap15.Lemma_15_67_20
import StacksProject_2024.Chap18.Definition_18_7_1
import StacksProject_2024.Chap18.Definition_18_13_1
import StacksProject_2024.Chap18.Lemma_18_14_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismOfTopoiIn
open scoped MorphismOfTopoiIn RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)

/-- Helper for Lemma 18.25.1: the source module category at the universe level used by the
canonical pullback-pushforward adjunction. -/
private abbrev ModXv := SheafOfModules.{max u v} X.structureSheaf

/-- Helper for Lemma 18.25.1: the target module category at the universe level used by the
canonical pullback-pushforward adjunction. -/
private abbrev ModYv := SheafOfModules.{max u v} Y.structureSheaf

section LocalHelpers

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒪 𝒪' : Sheaf J RingCat.{max u v}}

/-- Helper for Lemma 18.25.1: once the underlying natural transformation of ring-valued sheaves
is epic, each section map is epic in `RingCat`. -/
lemma ring_sheaf_epi_app_of_epi_hom
    (α : 𝒪 ⟶ 𝒪') [Epi α.hom] (U : Cᵒᵖ) :
    Epi (α.hom.app U) := by
  -- Evaluate the epimorphism objectwise using the standard natural-transformation criterion.
  exact (NatTrans.epi_iff_epi_app' RingCat α.hom).1 inferInstance U

end LocalHelpers

/-- Helper for Lemma 18.25.1: under local surjectivity of a sheaf morphism of rings, restriction
of scalars on sheaves of modules is fully faithful. -/
noncomputable def restrictHomEquivOfIsLocallySurjective
    {𝒪₁ 𝒪₂ : Sheaf Y.siteTopology RingCat.{max u v}}
    (α : 𝒪₁ ⟶ 𝒪₂) (𝒢₁ 𝒢₂ : SheafOfModules 𝒪₂)
    [Sheaf.IsLocallySurjective α] :
    (𝒢₁ ⟶ 𝒢₂) ≃
      ((SheafOfModules.restrictScalars α).obj 𝒢₁ ⟶
        (SheafOfModules.restrictScalars α).obj 𝒢₂) where
  toFun g :=
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective α.hom 𝒢₂.isSheaf) g.val⟩
  invFun g :=
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective α.hom 𝒢₂.isSheaf).symm g.val⟩
  left_inv g := by
    apply SheafOfModules.hom_ext
    exact
      (PresheafOfModules.restrictHomEquivOfIsLocallySurjective α.hom 𝒢₂.isSheaf).left_inv g.val
  right_inv g := by
    apply SheafOfModules.hom_ext
    exact
      (PresheafOfModules.restrictHomEquivOfIsLocallySurjective α.hom 𝒢₂.isSheaf).right_inv g.val

/-- Helper for Lemma 18.25.1: restriction of scalars along a locally surjective morphism of ring
sheaves is fully faithful. -/
noncomputable instance restrictScalars_fullyFaithful_ofIsLocallySurjective
    {𝒪₁ 𝒪₂ : Sheaf Y.siteTopology RingCat.{max u v}}
    (α : 𝒪₁ ⟶ 𝒪₂) [Sheaf.IsLocallySurjective α] :
    (SheafOfModules.restrictScalars α).FullyFaithful where
  preimage {𝒢₁ 𝒢₂} g := (restrictHomEquivOfIsLocallySurjective α 𝒢₁ 𝒢₂).symm g
  map_preimage {𝒢₁ 𝒢₂} g := by
    simpa [restrictHomEquivOfIsLocallySurjective] using
      (restrictHomEquivOfIsLocallySurjective α 𝒢₁ 𝒢₂).apply_symm_apply g
  preimage_map {𝒢₁ 𝒢₂} g := by
    simpa [restrictHomEquivOfIsLocallySurjective] using
      (restrictHomEquivOfIsLocallySurjective α 𝒢₁ 𝒢₂).symm_apply_apply g

/-- Helper for Lemma 18.25.1: an epimorphism of ring sheaves makes restriction of scalars fully
faithful. -/
/-- Helper for Lemma 18.25.1: an epic structure-sheaf map is locally surjective as a morphism of
sheaves of rings. This is the sheaf-level bridge needed to reuse the local restriction-of-scalars
API without importing the broken earlier item file. -/
lemma structureSheafMap_isLocallySurjective_of_epi
    [Epi f.structureSheafMap] :
    Sheaf.IsLocallySurjective f.structureSheafMap := by
  -- Proof comment: use the standard sheaf-theoretic equivalence between epimorphisms and local
  -- surjectivity, specialized to the structure-sheaf map.
  exact (Sheaf.isLocallySurjective_iff_epi f.structureSheafMap).2 inferInstance

/-- Helper for Lemma 18.25.1: an epimorphism of ring sheaves makes restriction of scalars fully
faithful. -/
noncomputable instance structureSheafMap_restrictScalars_fullyFaithful_of_epi
    [Epi f.structureSheafMap] :
    (SheafOfModules.restrictScalars f.structureSheafMap).FullyFaithful := by
  let _ : Sheaf.IsLocallySurjective f.structureSheafMap :=
    structureSheafMap_isLocallySurjective_of_epi (f := f)
  -- Proof comment: once local surjectivity is available, the owner-level fully faithful
  -- restriction-of-scalars result in this file applies directly.
  exact restrictScalars_fullyFaithful_ofIsLocallySurjective f.structureSheafMap

/-- Helper for Lemma 18.25.1: a morphism of `ModY` is an isomorphism once all of its section maps
are isomorphisms. This is the standard objectwise-to-global reflection step through additive
sheaves and then presheaves. -/
theorem isIso_of_modY_evaluation_isIso
    {ℱ 𝒢 : ModYv} (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ U : Yᵒᵖ, IsIso ((SheafOfModules.evaluation Y.structureSheaf U).map φ)) :
    IsIso φ := by
  have hIsoPresheaf :
      IsIso
        ((sheafToPresheaf Y.siteTopology AddCommGrpCat).map
          ((SheafOfModules.toSheaf Y.structureSheaf).map φ)) := by
    -- Proof comment: after forgetting module structure and the sheaf condition, the hypothesis
    -- says that each component of the underlying natural transformation is an isomorphism.
    refine (NatTrans.isIso_iff_isIso_app _).2 ?_
    intro U
    let _ : IsIso ((SheafOfModules.evaluation Y.structureSheaf U).map φ) := hφ U
    let _ := Functor.map_isIso
      (forget₂ (ModuleCat (Y.structureSheaf.1.obj U)) AddCommGrpCat)
      ((SheafOfModules.evaluation Y.structureSheaf U).map φ)
    simpa [SheafOfModules.evaluation, SheafOfModules.toSheaf]
  have hIsoToSheaf :
      IsIso ((SheafOfModules.toSheaf Y.structureSheaf).map φ) := by
    -- Proof comment: the sheaf-to-presheaf forgetful functor reflects isomorphisms.
    letI :
        IsIso
          ((sheafToPresheaf Y.siteTopology AddCommGrpCat).map
            ((SheafOfModules.toSheaf Y.structureSheaf).map φ)) :=
      hIsoPresheaf
    exact isIso_of_reflects_iso
      ((SheafOfModules.toSheaf Y.structureSheaf).map φ)
      (sheafToPresheaf Y.siteTopology AddCommGrpCat)
  -- Proof comment: finally reflect the additive-sheaf isomorphism back to module sheaves.
  letI : IsIso ((SheafOfModules.toSheaf Y.structureSheaf).map φ) := hIsoToSheaf
  exact isIso_of_reflects_iso φ (SheafOfModules.toSheaf Y.structureSheaf)

/-- Helper for Lemma 18.25.1: evaluating the sheaf-level pullback-pushforward unit on `U`
recovers the ordinary module-theoretic unit for restriction and extension of scalars along the
section ring map `f^\sharp(U)`. -/
lemma evaluation_pullbackPushforwardUnit_app_eq_extendRestrictScalars_unit
    (𝒢 : ModYv) (U : Yᵒᵖ) :
    (SheafOfModules.evaluation Y.structureSheaf U).map
        ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).unit.app 𝒢) =
      (ModuleCat.extendRestrictScalarsAdj ((f.structureSheafMap.1.app U).hom)).unit.app
        ((SheafOfModules.evaluation Y.structureSheaf U).obj 𝒢) := by
  -- Proof comment: both sides are the same owner-level unit map after evaluating the sheaf
  -- adjunction on the object `U`.
  rfl

/-- Helper for Lemma 18.25.1: for a surjective ring map, the unit of extension-restriction of
scalars is an isomorphism on any module annihilated by the kernel. -/
theorem moduleUnit_isIso_of_surjective_of_kernel_smul_eq_zero
    {R S : Type u} [CommRing R] [CommRing S]
    (α : R →+* S) (M : ModuleCat R)
    (hαsurj : Function.Surjective α)
    (hkill : ∀ r : R, ∀ m : M, α r = 0 → r • m = 0) :
    IsIso ((ModuleCat.extendRestrictScalarsAdj α).unit.app M) := by
  let _ : Algebra R S := α.toAlgebra
  have hkillTop : RingHom.ker α • (⊤ : Submodule R M) = ⊥ := by
    -- Proof comment: the kernel elements annihilate every section, hence kill the top submodule.
    refine (Submodule.le_annihilator_iff).mpr ?_
    simpa [Submodule.annihilator_top] using
      (show RingHom.ker α ≤ Module.annihilator R (M : Type u) from by
        intro r hr
        exact fun m ↦ hkill r m hr)
  let N : ModuleCat S :=
    descended_module_of_ker_smul_eq_zero
      (R' := R) (R := S) hαsurj M hkillTop
  have hdesc :
      ((ModuleCat.restrictScalars α).obj N) ≅ M :=
    restrictScalars_descended_module_of_ker_smul_eq_zero_iso
      (R' := R) (R := S) hαsurj M hkillTop
  have hess : (ModuleCat.restrictScalars α).essImage M := by
    -- Proof comment: the descended `S`-module provides an explicit essential-image witness for
    -- restriction of scalars.
    exact ⟨N, ⟨hdesc⟩⟩
  have hαepi : Epi (CommRingCat.ofHom α) :=
    ConcreteCategory.epi_of_surjective (CommRingCat.ofHom α) hαsurj
  letI : Epi (CommRingCat.ofHom α) := hαepi
  let hFF : (ModuleCat.restrictScalars α).FullyFaithful := restrictScalars_fullyFaithful_of_epi α
  letI : (ModuleCat.restrictScalars α).Full := hFF.full
  letI : (ModuleCat.restrictScalars α).Faithful := hFF.faithful
  -- Proof comment: once restriction of scalars is fully faithful, the generic adjunction-unit
  -- criterion identifies essential-image membership with invertibility of the unit.
  exact
    (((ModuleCat.extendRestrictScalarsAdj α).isIso_unit_app_iff_mem_essImage :
      IsIso ((ModuleCat.extendRestrictScalarsAdj α).unit.app M) ↔
        (ModuleCat.restrictScalars α).essImage M)).2 hess

/-- Helper for Lemma 18.25.1: if every section annihilated by `f^\sharp` acts trivially on
`\mathcal G`, then the adjunction unit `\mathcal G \to f_* f^* \mathcal G` is an isomorphism. -/
theorem pullbackPushforwardUnit_app_isIso_of_sectionwise_annihilation
    [PreservesFiniteLimits
      (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)]
    [IsClosedImmersion f.toMorphismOfTopoi] [Epi f.structureSheafMap]
    [(SheafOfModules.pushforward.{max u v} f.structureSheafMap).IsRightAdjoint]
    (𝒢 : ModYv)
    (hsec :
      ∀ U : Yᵒᵖ,
        ∀ s : Y.structureSheaf.1.obj U,
          ∀ m : 𝒢.val.obj U,
            f.structureSheafMap.1.app U s = 0 → s • m = 0) :
    IsIso ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).unit.app 𝒢) := by
  -- Proof comment: reflect the desired isomorphism from the sectionwise evaluation functors.
  apply isIso_of_modY_evaluation_isIso
  intro U
  letI : Epi f.structureSheafMap.hom :=
    (sheafToPresheaf Y.siteTopology RingCat.{max u v}).map_epi f.structureSheafMap
  have hUepi : Epi (f.structureSheafMap.1.app U) :=
    ring_sheaf_epi_app_of_epi_hom (α := f.structureSheafMap) U
  have hαsurj : Function.Surjective ((f.structureSheafMap.1.app U).hom) := by
    -- Proof comment: epimorphy in `RingCat` is surjectivity on underlying ring homomorphisms.
    exact ConcreteCategory.surjective_of_epi (f.structureSheafMap.1.app U)
  have hunit :
      IsIso
        ((ModuleCat.extendRestrictScalarsAdj ((f.structureSheafMap.1.app U).hom)).unit.app
          (𝒢.val.obj U)) :=
    moduleUnit_isIso_of_surjective_of_kernel_smul_eq_zero
      ((f.structureSheafMap.1.app U).hom) (𝒢.val.obj U) hαsurj
      (fun s m hs ↦ hsec U s m hs)
  -- Proof comment: after the evaluation bridge lemma, the sectionwise unit is exactly the
  -- module-theoretic unit already shown to be an isomorphism.
  simpa [evaluation_pullbackPushforwardUnit_app_eq_extendRestrictScalars_unit
    (f := f) (𝒢 := 𝒢) (U := U)] using hunit

/-- Helper for Lemma 18.25.1: `toSheaf` reflects epimorphisms of module sheaves because it is
faithful. -/
theorem epi_of_toSheaf_map_epi
    {ℱ 𝒢 : ModYv} (φ : ℱ ⟶ 𝒢)
    [Epi ((SheafOfModules.toSheaf Y.structureSheaf).map φ)] :
    Epi φ := by
  refine ⟨?_⟩
  intro Z g h hgh
  apply (SheafOfModules.toSheaf Y.structureSheaf).map_injective
  apply (cancel_epi ((SheafOfModules.toSheaf Y.structureSheaf).map φ)).1
  simpa using congrArg ((SheafOfModules.toSheaf Y.structureSheaf).map) hgh

/-- Helper for Lemma 18.25.1: if the additive direct image preserves epimorphisms, then the
module direct image preserves epimorphisms as well. -/
theorem pushforward_preservesEpimorphisms_of_underlyingPreservesEpimorphisms
    [Functor.PreservesEpimorphisms
      (f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v}
        Y.siteTopology X.siteTopology)] :
    Functor.PreservesEpimorphisms (SheafOfModules.pushforward f.structureSheafMap) := by
  let G : ModYv ⥤ Sheaf Y.siteTopology AddCommGrpCat.{max u v} :=
    SheafOfModules.toSheaf Y.structureSheaf
  let GX : ModXv ⥤ Sheaf X.siteTopology AddCommGrpCat.{max u v} :=
    SheafOfModules.toSheaf X.structureSheaf
  let Fadd :
      Sheaf X.siteTopology AddCommGrpCat.{max u v} ⥤
        Sheaf Y.siteTopology AddCommGrpCat.{max u v} :=
    f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v}
      Y.siteTopology X.siteTopology
  -- The source forgetful functor is exact, hence preserves finite colimits and therefore epis.
  let _ : PreservesFiniteColimits GX :=
    ((exactFunctor_iff GX).1 (ExactFunctor.of GX).property).2
  constructor
  intro M N g hg
  -- After forgetting the target module structure, the composite is the additive pushforward.
  have hmapUnderlying : Epi ((GX ⋙ Fadd).map g) := by
    letI : Epi g := hg
    infer_instance
  have hmap :
      Epi
        (G.map ((SheafOfModules.pushforward f.structureSheafMap).map g)) := by
    simpa [G, GX, Fadd, SheafOfModules.pushforward, PresheafOfModules.pushforward] using
      hmapUnderlying
  -- Since `toSheaf` is faithful, an epi after forgetting was already an epi before forgetting.
  letI : Epi (G.map ((SheafOfModules.pushforward f.structureSheafMap).map g)) := hmap
  exact epi_of_toSheaf_map_epi
    (φ := (SheafOfModules.pushforward f.structureSheafMap).map g)

/- Domain-style sampling for Lemma 18.25.1:
- primary domain: pushforward of sheaves of modules along a closed immersion of ringed sites,
  using the site-presented underlying morphism of topoi only as bridge data;
- sampled owner declarations:
  `RingedSite.Hom`,
  `RingedSite.Hom.toMorphismOfTopoi`,
  `CategoryTheory.MorphismOfTopoiIn.closedImmersion_pushforwardFullyFaithful`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction: the bundled morphism of ringed sites `f : X ⟶ Y`; the closed-immersion
  hypothesis belongs on the canonical bridge `f.toMorphismOfTopoi`, while the module-theoretic
  consequences live on the canonical owner functor
  `SheafOfModules.pushforward f.structureSheafMap`;
- primitive data: `f`, the finite-limit hypothesis needed to form `f.toMorphismOfTopoi`, and the
  epimorphism hypothesis on `f.structureSheafMap`;
- derived API: exactness and full faithfulness of module pushforward, the source-facing
  annihilation criterion for the kernel of `f^\sharp`, and the adjunction-unit reformulation from
  the generic fully faithful right-adjoint criterion.

Source/core/bridge triage:
- `source-facing`: the closed-immersion consequences for module pushforward recorded in this file;
- `core/canonical`: `IsClosedImmersion f.toMorphismOfTopoi`,
  `SheafOfModules.pushforward f.structureSheafMap`, and
  `SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap`;
- `bridge/view`: the transfer from the underlying topos pushforward to module pushforward, and the
  generic essential-image criterion specialized to the ringed-site owner `f`. -/

-- Proof sketch: use Lemma `18.15.2` on the underlying topos pushforward `f.toMorphismOfTopoi _*`
-- together with the closed-immersion preservation properties from Lemma `7.43.8`, then pass from
-- abelian sheaves to module sheaves through the canonical forgetful comparison.
/-- Lemma 18.25.1 (1): if the underlying morphism of topoi of `f` is a closed immersion and the
pushforward-form structure-sheaf map `f.structureSheafMap` is an epimorphism, then pushforward of
module sheaves along `f` is exact. -/
theorem pushforward_exact_of_isClosedImmersion_of_epi_structureSheafMap
    [PreservesFiniteLimits
      (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)]
    [IsClosedImmersion f.toMorphismOfTopoi] [Epi f.structureSheafMap] :
    exactFunctor ModXv ModYv (SheafOfModules.pushforward f.structureSheafMap) := by
  let F : ModXv ⥤ ModYv := SheafOfModules.pushforward f.structureSheafMap
  let _ : (PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint := by
    exact PresheafOfModules.instIsRightAdjointPushforward (φ := f.structureSheafMap.hom)
  let _ : F.IsRightAdjoint := by
    simpa [F] using
      (SheafOfModules.instIsRightAdjointPushforward (φ := f.structureSheafMap))
  let _ : PreservesFiniteLimits F := inferInstance
  let _ : Abelian (SheafOfModules X.structureSheaf) := SheafOfModules.instAbelian X.structureSheaf
  let _ : Abelian (SheafOfModules Y.structureSheaf) := SheafOfModules.instAbelian Y.structureSheaf
  have hLeft : leftExactFunctor _ _ F := by
    simpa [leftExactFunctor_iff] using (inferInstance : PreservesFiniteLimits F)
  let _ : F.Additive :=
    CategoryTheory.functor_additive_of_leftExact_or_rightExact (F := F) (.inl hLeft)
  let _ : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  let _ :
      Functor.PreservesEpimorphisms
        (f.base.sheafPushforwardContinuous AddCommGrpCat.{max u v}
          Y.siteTopology X.siteTopology) := by
    -- Proof comment: closed immersions preserve epimorphisms for the additive-sheaf direct image.
    let i : MorphismOfTopoiIn Y.siteTopology X.siteTopology := f.toMorphismOfTopoi
    simpa [i, RingedSite.Hom.toMorphismOfTopoi] using
      (inferInstance : Functor.PreservesEpimorphisms (i _*))
  let _ : Functor.PreservesEpimorphisms F :=
    pushforward_preservesEpimorphisms_of_underlyingPreservesEpimorphisms f
  let _ : F.PreservesHomology :=
    CategoryTheory.Functor.preservesHomology_of_preservesEpis_and_kernels F
  let _ : PreservesFiniteColimits F :=
    CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology F
  -- A right adjoint already preserves finite limits, so finite colimits now give exactness.
  exact (exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩

-- Proof sketch: for a closed immersion of topoi, the direct-image functor on sheaves of sets is
-- fully faithful by Lemma `7.43.8`; the epimorphism hypothesis on `f.structureSheafMap` upgrades
-- the recovered maps on underlying sheaves to module maps by the fully faithful restriction of
-- scalars result of Lemma `18.11.4`.
/-- Lemma 18.25.1 (2): under the same hypotheses, pushforward of module sheaves along `f` is
fully faithful. -/
noncomputable instance pushforward_fullyFaithful_of_isClosedImmersion_of_epi_structureSheafMap
    [PreservesFiniteLimits
      (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)]
    [IsClosedImmersion f.toMorphismOfTopoi] [Epi f.structureSheafMap] :
    (SheafOfModules.pushforward f.structureSheafMap).FullyFaithful := by
  let 𝒪Xpush : Sheaf Y.siteTopology RingCat.{max u v} :=
    (f.base.sheafPushforwardContinuous RingCat.{max u v}
      Y.siteTopology X.siteTopology).obj X.structureSheaf
  let P : ModXv ⥤ SheafOfModules 𝒪Xpush :=
    SheafOfModules.pushforward (𝟙 𝒪Xpush)
  let G : SheafOfModules 𝒪Xpush ⥤ ModYv :=
    SheafOfModules.restrictScalars f.structureSheafMap
  let _ : Functor.FullyFaithful P := by
    -- Proof comment: with the identity structure-sheaf map, pushforward only remembers the
    -- closed-immersion direct image on module sheaves over `f_* \mathcal O_X`.
    let i : MorphismOfTopoiIn Y.siteTopology X.siteTopology := f.toMorphismOfTopoi
    have hP : Functor.FullyFaithful (i _*) := by
      infer_instance
    simpa [i, P, 𝒪Xpush, SheafOfModules.pushforward, PresheafOfModules.pushforward,
      RingedSite.Hom.toMorphismOfTopoi] using hP
  let _ : Functor.FullyFaithful G := by
    -- Proof comment: the epi hypothesis on `f^\sharp` gives full faithfulness of restriction of
    -- scalars along `f^\sharp`.
    exact structureSheafMap_restrictScalars_fullyFaithful_of_epi (f := f)
  -- Proof comment: `f_*` is the intermediate pushforward into `f_* \mathcal O_X`-modules,
  -- followed by restriction of scalars along `f^\sharp`, so full faithfulness composes.
  change Functor.FullyFaithful (P ⋙ G)
  infer_instance

/-- Helper for Lemma 18.25.1: if `eHom` and `eInv` are inverse morphisms of
`\mathcal O_Y`-module sheaves, then their section maps over any object compose to the identity in
the same order. -/
theorem section_map_comp_eq_id
    {ℱ 𝒢 : ModYv} (eHom : ℱ ⟶ 𝒢) (eInv : 𝒢 ⟶ ℱ)
    (hHomInv : eHom ≫ eInv = 𝟙 ℱ) (U : Yᵒᵖ) :
    (SheafOfModules.Hom.val eHom).app U ≫ (SheafOfModules.Hom.val eInv).app U =
      𝟙 (ℱ.val.obj U) := by
  -- Evaluate the inverse identity of module-sheaf morphisms on the chosen object.
  simpa using congrArg
    (fun g => (SheafOfModules.Hom.val g).app U) hHomInv

/-- Helper for Lemma 18.25.1: if `eHom` and `eInv` are inverse morphisms of
`\mathcal O_Y`-module sheaves, then their section maps over any object compose to the identity in
the opposite order. -/
theorem section_inv_comp_eq_id
    {ℱ 𝒢 : ModYv} (eHom : ℱ ⟶ 𝒢) (eInv : 𝒢 ⟶ ℱ)
    (hInvHom : eInv ≫ eHom = 𝟙 𝒢) (U : Yᵒᵖ) :
    (SheafOfModules.Hom.val eInv).app U ≫ (SheafOfModules.Hom.val eHom).app U =
      𝟙 (𝒢.val.obj U) := by
  -- Evaluate the opposite inverse identity on the chosen object.
  simpa using congrArg
    (fun g => (SheafOfModules.Hom.val g).app U) hInvHom

/-- Helper for Lemma 18.25.1: on pushed-forward sections, any scalar whose image under
`f^\sharp(U)` is zero acts trivially. This is the sectionwise form of the restriction-of-scalars
action on `(f_* \mathcal F)(U)`. -/
theorem pushforward_sections_smul_eq_zero_of_structureSheafMap_app_eq_zero
    (ℱ : ModXv) (U : Yᵒᵖ) (s : Y.structureSheaf.1.obj U)
    (hs : f.structureSheafMap.1.app U s = 0)
    (m : ((SheafOfModules.pushforward f.structureSheafMap).obj ℱ).val.obj U) :
    s • m = 0 := by
  have hsmul :=
    ModuleCat.restrictScalars.smul_def (f.structureSheafMap.1.app U).hom s
      (show ((SheafOfModules.pushforward f.structureSheafMap).obj ℱ).val.obj U from m)
  -- Normalize the restriction-of-scalars action and use the vanishing hypothesis.
  rw [hs, zero_smul] at hsmul
  simpa using hsmul

/-- Helper for Lemma 18.25.1: the sectionwise kernel-annihilation condition is invariant under
isomorphism of `\mathcal O_Y`-module sheaves. This packages the repeated transport step needed to
move the vanishing statement across essential-image isomorphisms. -/
theorem structureSheafMap_eq_zero_smul_eq_zero_of_iso
    {𝒢₁ 𝒢₂ : ModYv} (e : 𝒢₁ ≅ 𝒢₂)
    (hsec :
      ∀ U : Yᵒᵖ,
        ∀ s : Y.structureSheaf.1.obj U,
          ∀ m : 𝒢₁.val.obj U,
            f.structureSheafMap.1.app U s = 0 → s • m = 0) :
    ∀ U : Yᵒᵖ,
      ∀ s : Y.structureSheaf.1.obj U,
        ∀ m : 𝒢₂.val.obj U,
          f.structureSheafMap.1.app U s = 0 → s • m = 0 := by
  intro U s m hs
  let n : 𝒢₁.val.obj U := ModuleCat.Hom.hom ((SheafOfModules.Hom.val e.inv).app U) m
  have hm :
      ModuleCat.Hom.hom ((SheafOfModules.Hom.val e.hom).app U) n = m := by
    -- Evaluate the inverse identity on sections and then on the chosen element `m`.
    simpa [n] using congrArg
      (fun g => ModuleCat.Hom.hom g m)
      (section_inv_comp_eq_id e.hom e.inv e.inv_hom_id U)
  -- Proof comment: move the target section across the isomorphism, apply the vanishing statement
  -- on `𝒢₁`, and then transport the resulting zero back to `𝒢₂`.
  rw [← hm]
  calc
    s • ModuleCat.Hom.hom ((SheafOfModules.Hom.val e.hom).app U) n
        = ModuleCat.Hom.hom ((SheafOfModules.Hom.val e.hom).app U) (s • n) := by
            symm
            exact ((SheafOfModules.Hom.val e.hom).app U).hom.map_smul _ _
    _ = ModuleCat.Hom.hom ((SheafOfModules.Hom.val e.hom).app U) 0 := by
          congr 1
          exact hsec U s n hs
    _ = 0 := by
          simp

/-- Helper for Lemma 18.25.1: every module sheaf already in the essential image of pushforward is
annihilated sectionwise by the kernel of `f^\sharp`. This proves the easy direction
`\mathcal G \cong f_* \mathcal F \Rightarrow \mathcal I \mathcal G = 0`. -/
theorem structureSheafMap_eq_zero_smul_eq_zero_of_mem_essImage
    {𝒢 : ModYv} (h𝒢 : (SheafOfModules.pushforward f.structureSheafMap).essImage 𝒢) :
    ∀ U : Yᵒᵖ,
      ∀ s : Y.structureSheaf.1.obj U,
          ∀ m : 𝒢.val.obj U,
          f.structureSheafMap.1.app U s = 0 → s • m = 0 := by
  obtain ⟨ℱ, ⟨e⟩⟩ := h𝒢
  -- Proof comment: transport the sectionwise vanishing statement from the genuine pushforward
  -- model across the essential-image isomorphism `e`.
  exact
    structureSheafMap_eq_zero_smul_eq_zero_of_iso f e
      (fun U s m hs ↦
        pushforward_sections_smul_eq_zero_of_structureSheafMap_app_eq_zero
          f ℱ U s hs m)

/-- Helper for Lemma 18.25.1: for the canonical adjunction `f^* ⊣ f_*`, once `f_*` is fully
faithful, essential-image membership is equivalent to invertibility of the adjunction unit. -/
theorem pushforward_essImage_iff_unit_isIso
    [(SheafOfModules.pushforward.{max u v} f.structureSheafMap).IsRightAdjoint]
    (hFF : (f _*).FullyFaithful)
    (𝒢 : ModYv) :
    (SheafOfModules.pushforward f.structureSheafMap).essImage 𝒢 ↔
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).unit.app 𝒢) := by
  let hFF' : (SheafOfModules.pushforward f.structureSheafMap).FullyFaithful := by
    change (f _*).FullyFaithful
    exact hFF
  letI : (SheafOfModules.pushforward f.structureSheafMap).Full := hFF'.full
  letI : (SheafOfModules.pushforward f.structureSheafMap).Faithful := hFF'.faithful
  simpa using
    (((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).isIso_unit_app_iff_mem_essImage :
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).unit.app 𝒢) ↔
        (SheafOfModules.pushforward f.structureSheafMap).essImage 𝒢)).symm

/-- Lemma 18.25.1: if `f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)` is a morphism of ringed
sites whose underlying morphism of topoi is a closed immersion and whose structure-sheaf map
`f^\sharp : \mathcal O_Y \to f_* \mathcal O_X` is surjective, then an `\mathcal O_Y`-module lies
in the essential image of pushforward exactly when every local section of `\mathcal O_Y` mapping
to zero under `f^\sharp` acts by zero. This is the sectionwise form of the textbook condition
`\mathcal I \mathcal G = 0` for `\mathcal I = \ker(f^\sharp)`. -/
theorem pushforward_essImage_iff_structureSheafMap_eq_zero_smul_eq_zero_of_isClosedImmersion_of_epi_structureSheafMap
    [PreservesFiniteLimits
      (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)]
    [IsClosedImmersion f.toMorphismOfTopoi] [Epi f.structureSheafMap]
    (𝒢 : ModYv) :
    (SheafOfModules.pushforward f.structureSheafMap).essImage 𝒢 ↔
      ∀ U : Yᵒᵖ,
        ∀ s : Y.structureSheaf.1.obj U,
          ∀ m : 𝒢.val.obj U,
            f.structureSheafMap.1.app U s = 0 → s • m = 0 := by
  constructor
  · -- This is the sectionwise kernel-annihilation argument for an actual pushforward.
    exact structureSheafMap_eq_zero_smul_eq_zero_of_mem_essImage f
  · intro hsec
    let _ : (PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint := by
      exact PresheafOfModules.instIsRightAdjointPushforward (φ := f.structureSheafMap.hom)
    let _ : (SheafOfModules.pushforward.{max u v} f.structureSheafMap).IsRightAdjoint := by
      exact SheafOfModules.instIsRightAdjointPushforward (φ := f.structureSheafMap)
    have hunit :
        IsIso ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).unit.app 𝒢) :=
      pullbackPushforwardUnit_app_isIso_of_sectionwise_annihilation f 𝒢 hsec
    have hFF : (f _*).FullyFaithful :=
      pushforward_fullyFaithful_of_isClosedImmersion_of_epi_structureSheafMap f
    -- Proof comment: for a fully faithful right adjoint, the generic unit-isomorphism criterion
    -- converts the sectionwise unit isomorphism into essential-image membership.
    exact (pushforward_essImage_iff_unit_isIso f hFF 𝒢).2 hunit

-- Proof sketch: for a fully faithful right adjoint, an object lies in the essential image
-- exactly when the adjunction unit is an isomorphism. Here the right adjoint is the canonical
-- pushforward functor attached to `f.structureSheafMap`.
/-- Core companion: for the canonical adjunction `f^* ⊣ f_*`, once `f_*` is fully faithful,
membership in the essential image of `f_*` is equivalent to invertibility of the adjunction unit
`\mathcal G \to f_* f^* \mathcal G`. -/
theorem pushforward_essImage_iff_unit_isIso_of_isClosedImmersion_of_epi_structureSheafMap
    [PreservesFiniteLimits
      (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)]
    [IsClosedImmersion f.toMorphismOfTopoi] [Epi f.structureSheafMap]
    [(SheafOfModules.pushforward.{max u v} f.structureSheafMap).IsRightAdjoint]
    (𝒢 : ModYv) :
    (SheafOfModules.pushforward f.structureSheafMap).essImage 𝒢 ↔
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).unit.app 𝒢) := by
  exact
    pushforward_essImage_iff_unit_isIso f
      (pushforward_fullyFaithful_of_isClosedImmersion_of_epi_structureSheafMap f) 𝒢

end RingedSite.Hom
