import Mathlib
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import StacksProject_2024.Chap06.Definition_6_10_1
import StacksProject_2024.Chap12.Definition_12_27_5
import StacksProject_2024.Chap18.Lemma_18_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

noncomputable section

/- Domain-style sampling for Theorem 19.8.4:
- primary domain: enough injectives in categories of sheaves of modules on a ringed site, as the
  immediate input for the Chapter 13 resolution-functor existence theorem;
- sampled owner declarations:
  `Mod(𝒪)`,
  `EnoughInjectives`,
  `ModuleCat.enoughInjectives`,
  `siteAbelianSheaf_hasEnoughInjectives`;
- best owner abstraction: the source-facing owner here is `EnoughInjectives (Mod(𝒪))`; this is the
  canonical common input for the Chapter 13 existence theorems, and no earlier project owner
  supplies the same arbitrary-`RingCat` statement directly;
- primitive data: the enough-injectives theorem for `Mod(𝒪)`;
- derived API: the Chapter 13 resolution-functor and homotopy-resolution consequences that use the
  `EnoughInjectives` instance.

Source/core/bridge triage:
- `source-facing`: Theorem 19.8.4, asserting enough injectives in `Mod(𝒪)`;
- `core/canonical`: `EnoughInjectives`;
- `bridge/view`: the Chapter 13 existence theorems that consume the `EnoughInjectives` instance.

The commutative-ring generator constructions from Chapter 18 live at a stricter `CommRingCat`
layer, so they are companion specializations rather than a replacement owner for this arbitrary
ring-sheaf theorem.
-/

/-- Helper for Theorem 19.8.4: sheafification sends a separator in presheaf modules to a separator
in sheaves of modules. -/
private theorem sheafification_obj_isSeparator
    {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v})
    {G : PresheafOfModules 𝒪.obj} (hG : IsSeparator G) :
    IsSeparator ((PresheafOfModules.sheafification (𝟙 𝒪.obj)).obj G) := by
  let F := SheafOfModules.forget 𝒪 ⋙ PresheafOfModules.restrictScalars (𝟙 𝒪.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 𝒪.obj)
  rw [CategoryTheory.isSeparator_def] at hG ⊢
  intro A B f g hfg
  have hmap : F.map f = F.map g := by
    apply hG
    intro h
    let k : (PresheafOfModules.sheafification (𝟙 𝒪.obj)).obj G ⟶ A :=
      (adj.homEquiv G A).symm h
    have hkfg : k ≫ f = k ≫ g := hfg k
    have hk : (adj.homEquiv G A) k = h := by
      simpa [k] using (Equiv.apply_symm_apply (adj.homEquiv G A) h)
    have hkf : (adj.homEquiv G B) (k ≫ f) = h ≫ F.map f := by
      calc
        (adj.homEquiv G B) (k ≫ f) = (adj.homEquiv G A) k ≫ F.map f := by
          simpa [F] using (adj.homEquiv_naturality_right k f)
        _ = h ≫ F.map f := by
          simpa using congrArg (fun t ↦ t ≫ F.map f) hk
    have hkg : (adj.homEquiv G B) (k ≫ g) = h ≫ F.map g := by
      calc
        (adj.homEquiv G B) (k ≫ g) = (adj.homEquiv G A) k ≫ F.map g := by
          simpa [F] using (adj.homEquiv_naturality_right k g)
        _ = h ≫ F.map g := by
          simpa using congrArg (fun t ↦ t ≫ F.map g) hk
    calc
      h ≫ F.map f = (adj.homEquiv G B) (k ≫ f) := hkf.symm
      _ = (adj.homEquiv G B) (k ≫ g) := by
        simpa using congrArg (fun t ↦ (adj.homEquiv G B) t) hkfg
      _ = h ≫ F.map g := hkg
  exact CategoryTheory.Functor.map_injective F hmap

/-- Helper for Theorem 19.8.4: sheaves of modules on a ringed site admit a separator obtained by
sheafifying the coproduct of the free-Yoneda presheaf-module family. -/
private theorem ringedSiteModuleCategory_hasSeparator
    {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v}) :
    HasSeparator (SheafOfModules.{max u v} 𝒪) := by
  letI : LocallySmall.{max u v} C := inferInstance
  let R := 𝒪
  let F : C → PresheafOfModules R.obj := fun X ↦
    ((CategoryTheory.yoneda ⋙ PresheafOfModules.free R.obj).obj X)
  have hF : ObjectProperty.IsSeparating (.ofObj F) := by
    simpa [F, PresheafOfModules.freeYoneda] using
      (PresheafOfModules.freeYoneda.isSeparating.{max u v, u} (R := R.obj))
  have hSep : IsSeparator (∐ F) := by
    exact CategoryTheory.ObjectProperty.IsSeparating.isSeparator_coproduct (f := F) hF
  refine ⟨⟨(PresheafOfModules.sheafification (𝟙 R.obj)).obj (∐ F), ?_⟩⟩
  exact sheafification_obj_isSeparator 𝒪 hSep

/-- Helper for Theorem 19.8.4: the category of sheaves of modules on a ringed site is
Grothendieck abelian. -/
private theorem ringedSiteModuleCategory_isGrothendieckAbelian
    {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v}) :
    IsGrothendieckAbelian.{max u v} (SheafOfModules.{max u v} 𝒪) := by
  refine
    { locallySmall := inferInstance
      hasFilteredColimitsOfSize := by
        let _ : Limits.HasColimitsOfSize.{max u v, max u v} (SheafOfModules.{max u v} 𝒪) := by
          infer_instance
        exact Limits.hasFilteredColimitsOfSize_of_hasColimitsOfSize
      ab5OfSize := by
        let _ : AB5 (SheafOfModules.{max u v} 𝒪) :=
          (mod_forgetful_has_limits_colimits_and_ab5 (𝒪 := 𝒪)).2.2
        exact AB5OfSize_shrink (C := SheafOfModules.{max u v} 𝒪)
      hasSeparator := ringedSiteModuleCategory_hasSeparator 𝒪 }

/-- Theorem 19.8.4: for a site `\mathcal C` and a sheaf of rings `\mathcal O` on `\mathcal C`,
the category of sheaves of `\mathcal O`-modules has enough injectives. -/
instance modulesOnRingedSite_hasEnoughInjectives
    {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v}) :
    EnoughInjectives (SheafOfModules.{max u v} 𝒪) := by
  letI : IsGrothendieckAbelian.{max u v} (SheafOfModules.{max u v} 𝒪) :=
    ringedSiteModuleCategory_isGrothendieckAbelian 𝒪
  letI : HasFunctorialInjectiveEmbeddings (SheafOfModules.{max u v} 𝒪) :=
    hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian
      (C := SheafOfModules.{max u v} 𝒪)
  infer_instance
