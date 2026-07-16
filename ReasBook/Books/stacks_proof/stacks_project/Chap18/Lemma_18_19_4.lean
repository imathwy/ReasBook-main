import Mathlib.CategoryTheory.Limits.ExactFunctor
import stacks_proof.stacks_project.Chap07.Lemma_7_41_4
import stacks_proof.stacks_project.Chap18.Lemma_18_14_1
import stacks_proof.stacks_project.Chap18.Lemma_18_15_1
import stacks_proof.stacks_project.Chap18.Lemma_18_15_2
import stacks_proof.stacks_project.Chap18.Lemma_18_19_2
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] [CategoryTheory.Limits.HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/- Domain-style sampling for Lemma 18.19.4:
- primary domain: exactness reflection for extension by zero from the localized ringed site
  `(C/U, J.over U, 𝒪_U)` to `(C, J, 𝒪)`;
- sampled owner declarations:
  `ringedSiteLocalizedExtensionByZero`,
  `ringedSiteModuleCategory`,
  `ringedSiteLocalizedExtensionByZero_exact`,
  `ShortComplex.Exact.map`,
  `Functor.reflects_exact_of_faithful`;
- best owner abstraction: the source-facing chapter owner
  `ringedSiteLocalizedExtensionByZero J 𝒪 U`;
- primitive data: only the site `(C, J)`, the structure sheaf `𝒪`, and the object `U : C`;
- derived API: the source-facing exactness comparison for short complexes under `j_{U!}`,
  with the forward direction obtained from the exact functor owner and the converse from faithful
  exactness reflection.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that a short complex over `𝒪_U` is exact iff its
  extension by zero is exact over `𝒪`;
- `core/canonical`: the identity-structure-map pullback owner for localization extension by zero;
- `bridge/view`: the exactness comparison theorem below.

This lemma is a bridge/view statement: the source-facing `j_{U!}` is the canonical pullback owner
surfaced by `ringedSiteLocalizedExtensionByZero J 𝒪 U`, so the file should reuse that owner
directly instead of introducing the opposite direct image `j_{U,*}` or extra local
wrapper/instance noise. -/

-- Route correction: the previous proof tried to force the additive-sheaf comparison directly.
-- The stable remaining route is to package the needed exactness data for `j_{U!}` once and then
-- invoke `ShortComplex.exact_map_iff_of_faithful`.
/-- Helper for Lemma 18.19.4: after forgetting module structure, localized extension by zero is
definitionally the additive-sheaf pushforward along `Over.star U`. -/
private theorem localizedExtensionByZeroCompToSheaf :
    ringedSiteLocalizedExtensionByZero J 𝒪 U ⋙
        SheafOfModules.toSheaf (ringSheaf J 𝒪) =
      SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U)) ⋙
        (Over.star U).sheafPushforwardContinuous AddCommGrpCat.{u} J (J.over U) := by
  rfl

/-- Helper for Lemma 18.19.4: a morphism of additive sheaves is epic exactly when its underlying
map of set-valued sheaves is epic. -/
private theorem sheafAddCommGrp_epi_iff_forget_epi
    {K : GrothendieckTopology C}
    {X Y : Sheaf K AddCommGrpCat.{u}} (φ : X ⟶ Y) :
    Epi φ ↔ Epi ((sheafCompose K (forget AddCommGrpCat.{u})).map φ) := by
  constructor
  · intro hφ
    -- Proof comment: forgetting additive structure preserves epimorphisms.
    letI : Epi φ := hφ
    exact (sheafCompose K (forget AddCommGrpCat.{u})).map_epi φ
  · intro hφ
    -- Proof comment: the faithful forgetful functor reflects epimorphisms back to abelian
    -- sheaves.
    exact (sheafCompose K (forget AddCommGrpCat.{u})).epi_of_epi_map hφ

/-- Helper for Lemma 18.19.4: additive sheaf pushforward along `Over.star U` reflects
epimorphisms. -/
private theorem localizedAdditivePushforwardReflectsEpimorphisms :
    ((Over.star U).sheafPushforwardContinuous AddCommGrpCat.{u} J
      (J.over U)).ReflectsEpimorphisms := by
  let GAdd : Sheaf (J.over U) AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
    (Over.star U).sheafPushforwardContinuous AddCommGrpCat.{u} J (J.over U)
  let GType : Sheaf (J.over U) (Type u) ⥤ Sheaf J (Type u) :=
    (Over.star U).sheafPushforwardContinuous (Type u) J (J.over U)
  let QOver : Sheaf (J.over U) AddCommGrpCat.{u} ⥤ Sheaf (J.over U) (Type u) :=
    sheafCompose (J.over U) (forget AddCommGrpCat.{u})
  let QBase : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf J (Type u) :=
    sheafCompose J (forget AddCommGrpCat.{u})
  letI : GType.ReflectsEpimorphisms := by
    infer_instance
  refine ⟨fun {X Y} f hf ↦ ?_⟩
  -- Proof comment: forget the pushed-forward map to sets, reflect epimorphy there, and lift
  -- it back to additive sheaves.
  have hForgetBase : Epi (QBase.map (GAdd.map f)) :=
    (sheafAddCommGrp_epi_iff_forget_epi (φ := GAdd.map f)).1 hf
  have hType : Epi (GType.map (QOver.map f)) := by
    simpa [GAdd, GType, QOver, QBase, sheaf_pushforward_forget] using hForgetBase
  have hForgetOver : Epi (QOver.map f) :=
    Functor.epi_of_epi_map GType hType
  exact (sheafAddCommGrp_epi_iff_forget_epi (φ := f)).2 hForgetOver

/-- Helper for Lemma 18.19.4: if the underlying additive-sheaf morphism of an
`\mathcal O_U`-module morphism is epic, then the original module morphism is epic. -/
private theorem epi_of_localizedToSheaf_map_epi
    {M N : SheafOfModules (ringSheaf (J.over U) (𝒪.over U))}
    (φ : M ⟶ N)
    [Epi ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).map φ)] :
    Epi φ := by
  -- Proof comment: `toSheaf` is faithful, so right-cancellability reflects back to module
  -- sheaves.
  refine ⟨?_⟩
  intro Z g h hgh
  apply (SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).map_injective
  apply (cancel_epi
    ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).map φ)).1
  simpa using congrArg
    ((SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))).map) hgh

/-- Helper for Lemma 18.19.4: localized extension by zero reflects epimorphisms. -/
private theorem localizedExtensionByZeroReflectsEpimorphisms :
    (ringedSiteLocalizedExtensionByZero J 𝒪 U).ReflectsEpimorphisms := by
  let F : SheafOfModules (ringSheaf (J.over U) (𝒪.over U)) ⥤
      SheafOfModules (ringSheaf J 𝒪) :=
    ringedSiteLocalizedExtensionByZero J 𝒪 U
  let FOver :
      SheafOfModules (ringSheaf (J.over U) (𝒪.over U)) ⥤
        Sheaf (J.over U) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))
  let FBase : SheafOfModules (ringSheaf J 𝒪) ⥤ Sheaf J AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf (ringSheaf J 𝒪)
  let G : Sheaf (J.over U) AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
    (Over.star U).sheafPushforwardContinuous AddCommGrpCat.{u} J (J.over U)
  letI : G.ReflectsEpimorphisms :=
    localizedAdditivePushforwardReflectsEpimorphisms (C := C) (J := J) (𝒪 := 𝒪) (U := U)
  refine ⟨fun {X Y} f hf ↦ ?_⟩
  -- Proof comment: forget the pushed-forward module map to additive sheaves, identify it with
  -- additive pushforward of the forgotten map, reflect epimorphy there, and lift it back to
  -- module sheaves.
  have hBase : Epi ((F ⋙ FBase).map f) := by
    letI : Epi (F.map f) := hf
    simpa [F, FBase, Functor.comp_map] using
      (FBase.map_epi (F.map f) : Epi (FBase.map (F.map f)))
  rw [localizedExtensionByZeroCompToSheaf (C := C) (J := J) (𝒪 := 𝒪) (U := U)] at hBase
  have hFiber : Epi (G.map (FOver.map f)) := by
    simpa [FOver, G, Functor.comp_map] using hBase
  have hToSheaf : Epi (FOver.map f) :=
    Functor.epi_of_epi_map G hFiber
  letI : Epi (FOver.map f) := hToSheaf
  exact epi_of_localizedToSheaf_map_epi (C := C) (J := J) (𝒪 := 𝒪) (U := U) f

/-- Helper for Lemma 18.19.4: localized extension by zero is faithful and preserves finite
limits and colimits. -/
private theorem localizedExtensionByZero_faithfulExactData :
    (ringedSiteLocalizedExtensionByZero J 𝒪 U).Faithful ∧
      PreservesFiniteLimits (ringedSiteLocalizedExtensionByZero J 𝒪 U) ∧
      PreservesFiniteColimits (ringedSiteLocalizedExtensionByZero J 𝒪 U) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: the localized direct image is right adjoint to restriction, so once it
    -- reflects epimorphisms the generic adjunction theorem makes it faithful.
    have hReflect :
        (ringedSiteLocalizedExtensionByZero J 𝒪 U).ReflectsEpimorphisms :=
      localizedExtensionByZeroReflectsEpimorphisms
        (C := C) (J := J) (𝒪 := 𝒪) (U := U)
    exact CategoryTheory.Adjunction.faithful_R_of_reflectsEpimorphisms
      (SheafOfModules.overPushforwardOverAdj (R := ringSheaf J 𝒪) U) hReflect
  · -- Proof comment: `j_{U!}` is a right adjoint, so finite limits are automatic.
    change PreservesFiniteLimits
      (SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := ringSheaf J 𝒪) U))
    infer_instance
  · let F : ringedSiteModuleCategory (J.over U) (𝒪.over U) ⥤ ringedSiteModuleCategory J 𝒪 :=
        ringedSiteLocalizedExtensionByZero J 𝒪 U
    let G : Sheaf (J.over U) AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
      (Over.star U).sheafPushforwardContinuous AddCommGrpCat.{u} J (J.over U)
    let POver := sheafToPresheaf (J.over U) AddCommGrpCat.{u}
    let PBase := sheafToPresheaf J AddCommGrpCat.{u}
    let W : ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
      (Functor.whiskeringLeft _ _ _).obj (Over.star U).op
    let eP : G ⋙ PBase ≅ POver ⋙ W :=
      Functor.sheafPushforwardContinuousCompSheafToPresheafIso
        (F := Over.star U) (A := AddCommGrpCat.{u}) (J := J) (K := J.over U)
    have hG : PreservesFiniteColimits G := by
      let _ : PreservesFiniteColimits POver := by
        infer_instance
      let _ : PreservesFiniteColimits W := by
        infer_instance
      let _ : PreservesFiniteColimits (POver ⋙ W) := comp_preservesFiniteColimits POver W
      let _ : PreservesFiniteColimits (G ⋙ PBase) := preservesFiniteColimits_of_natIso eP.symm
      let _ : ReflectsFiniteColimits PBase := by
        infer_instance
      exact preservesFiniteColimits_of_reflects_of_preserves G PBase
    let TOver : ringedSiteModuleCategory (J.over U) (𝒪.over U) ⥤
        Sheaf (J.over U) AddCommGrpCat.{u} :=
      SheafOfModules.toSheaf (ringSheaf (J.over U) (𝒪.over U))
    let TBase : ringedSiteModuleCategory J 𝒪 ⥤ Sheaf J AddCommGrpCat.{u} :=
      SheafOfModules.toSheaf (ringSheaf J 𝒪)
    let _ : PreservesFiniteColimits TOver := by
      infer_instance
    let _ : PreservesFiniteColimits G := hG
    have hComp : PreservesFiniteColimits (TOver ⋙ G) := by
      exact comp_preservesFiniteColimits TOver G
    let _ : PreservesFiniteColimits (F ⋙ TBase) := by
      rw [localizedExtensionByZeroCompToSheaf (C := C) (J := J) (𝒪 := 𝒪) (U := U)]
      exact hComp
    let _ : ReflectsFiniteColimits TBase := by
      infer_instance
    exact preservesFiniteColimits_of_reflects_of_preserves F TBase

/-- Lemma 18.19.4: a short complex of `\mathcal O_U`-modules on the localized ringed site
`(\mathcal C/U, \mathcal O_U)` is exact if and only if its image under extension by zero
`j_{U!} : \mathrm{Mod}(\mathcal O_U) ⥤ \mathrm{Mod}(\mathcal O)` is exact. In canonical mathlib
chapter form, `j_{U!}` is `ringedSiteLocalizedExtensionByZero J 𝒪 U`. -/
@[stacks 0E8G]
theorem ringedSiteLocalizedExtensionByZero_exact_iff
    (S : ShortComplex (ringedSiteModuleCategory (J.over U) (𝒪.over U))) :
    S.Exact ↔ (S.map (ringedSiteLocalizedExtensionByZero J 𝒪 U)).Exact := by
  let F : SheafOfModules (ringSheaf (J.over U) (𝒪.over U)) ⥤ SheafOfModules (ringSheaf J 𝒪) :=
    ringedSiteLocalizedExtensionByZero J 𝒪 U
  let hData := localizedExtensionByZero_faithfulExactData (C := C) (J := J) (𝒪 := 𝒪) (U := U)
  letI : F.Faithful :=
    by simpa [F] using hData.1
  letI : PreservesFiniteLimits F :=
    by simpa [F] using hData.2.1
  letI : PreservesFiniteColimits F :=
    by simpa [F] using hData.2.2
  -- Proof comment: once `j_{U!}` is known exact and faithful, the exactness comparison is the
  -- canonical faithful-exact functor theorem.
  simpa [F] using (S.exact_map_iff_of_faithful F).symm

end
