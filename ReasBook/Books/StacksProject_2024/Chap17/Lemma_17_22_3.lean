import Mathlib
import StacksProject_2024.Chap17.Definition_17_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open TopCat.Sheaf

noncomputable section

universe u

namespace TopCat.Sheaf

/- Domain-style sampling for Lemma 17.22.3:
- primary domain: change of rings for sheaves of modules on a topological space, with the
  source-facing right-hand object `ℋom_{𝒪₁}(𝒪₂, 𝒢)`;
- sampled owner declarations:
  `TopCat.Sheaf.ringSheafMap`,
  `PresheafOfModules.pushforward₀`,
  `PresheafOfModules.sheafification`,
  `ModuleCat.restrictCoextendScalarsAdj`;
- best owner abstraction: the concrete change-of-rings coextension object, obtained by
  sheafifying the local-Hom presheaf `U ↦ Hom_{𝒪₁|U}(𝒪₂|U, 𝒢|U)`, rather than an arbitrary chosen
  right adjoint;
- primitive data: a morphism of sheaves of commutative rings `α : 𝒪₁ ⟶ 𝒪₂` and an
  `𝒪₁`-module sheaf `𝒢`;
- derived API: the sheaf `coextendScalars α 𝒢`, viewed source-faithfully as
  `ℋom_{𝒪₁}(𝒪₂, 𝒢)`, and the global Hom-set bijection.

Source/core/bridge triage:
- `source-facing`: the sheaf `ℋom_{𝒪₁}(𝒪₂, 𝒢)` and the bijection
  `Hom_{𝒪₁}(ℱ_{𝒪₁}, 𝒢) ≃ Hom_{𝒪₂}(ℱ, ℋom_{𝒪₁}(𝒪₂, 𝒢))`;
- `core/canonical`: the sectionwise module-level owner
  `ModuleCat.restrictCoextendScalarsAdj`, together with sheafification on the local-Hom
  presheaf;
- `bridge/view`: restriction to slice sites and the resulting local-Hom presheaf below.

This file therefore targets the `source-facing` layer: it exposes the concrete change-of-rings
internal-Hom object and then states the textbook global Hom-set equivalence for that object. -/

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
variable (α : 𝒪₁ ⟶ 𝒪₂)

private abbrev overRingPresheaf (𝒪 : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X) :
    (Over U)ᵒᵖ ⥤ RingCat.{u} :=
  (Over.forget U).op ⋙ (ringSheaf 𝒪).obj

private abbrev overPresheafModule (𝒪 : TopCat.Sheaf CommRingCat.{u} X)
    (ℳ : PresheafOfModules (ringSheaf 𝒪).obj) (U : Opens X) :
    PresheafOfModules (overRingPresheaf 𝒪 U) :=
  (PresheafOfModules.pushforward₀ (Over.forget U) (ringSheaf 𝒪).obj).obj ℳ

private abbrev restrictedUnit :
    PresheafOfModules (ringSheaf 𝒪₁).obj :=
  ((SheafOfModules.restrictScalars (ringSheafMap α)).obj
    (SheafOfModules.unit (ringSheaf 𝒪₂))).val

private instance restrictedUnit_objModule (U : (Opens X)ᵒᵖ) :
    Module ((ringSheaf 𝒪₁).obj.obj U) ((restrictedUnit α).obj U) :=
  inferInstance

private instance overRestrictedUnit_objModule (U : Opens X) (V : (Over U)ᵒᵖ) :
    Module ((overRingPresheaf 𝒪₁ U).obj V)
      ((overPresheafModule 𝒪₁ (restrictedUnit α) U).obj V) :=
  inferInstance

private abbrev overHom (𝒢 : SheafOfModules (ringSheaf 𝒪₁)) (U : Opens X) :=
  overPresheafModule 𝒪₁ (restrictedUnit α) U ⟶ overPresheafModule 𝒪₁ 𝒢.val U

private abbrev localHomMap {𝒢 : SheafOfModules (ringSheaf 𝒪₁)} {U V : (Opens X)ᵒᵖ}
    (f : U ⟶ V) :
    overHom α 𝒢 U.unop → overHom α 𝒢 V.unop :=
  (PresheafOfModules.pushforward₀ (Over.map f.unop) (overRingPresheaf 𝒪₁ U.unop)).map

/-- Multiplication by a local section of `𝒪₂` on the restricted unit sheaf, over a slice site. -/
private def sourceSectionMulAppFun (U : Opens X) (r : (ringSheaf 𝒪₂).obj.obj (op U))
    (V : (Over U)ᵒᵖ) :
    (overPresheafModule 𝒪₁ (restrictedUnit α) U).obj V →
      (overPresheafModule 𝒪₁ (restrictedUnit α) U).obj V :=
  fun m ↦
    let rV : (ringSheaf 𝒪₂).obj.obj (op V.unop.left) :=
      (ringSheaf 𝒪₂).obj.map (op V.unop.hom) r
    let m' : (ringSheaf 𝒪₂).obj.obj (op V.unop.left) := m
    show (overPresheafModule 𝒪₁ (restrictedUnit α) U).obj V from m' * rV

private theorem sourceSectionMulAppFun_map_add (U : Opens X)
    (r : (ringSheaf 𝒪₂).obj.obj (op U)) (V : (Over U)ᵒᵖ)
    (x y : (overPresheafModule 𝒪₁ (restrictedUnit α) U).obj V) :
    sourceSectionMulAppFun α U r V (x + y) =
      sourceSectionMulAppFun α U r V x + sourceSectionMulAppFun α U r V y := by
  sorry

private theorem sourceSectionMulAppFun_map_smul (U : Opens X)
    (r : (ringSheaf 𝒪₂).obj.obj (op U)) (V : (Over U)ᵒᵖ)
    (a : (overRingPresheaf 𝒪₁ U).obj V)
    (x : (overPresheafModule 𝒪₁ (restrictedUnit α) U).obj V) :
    sourceSectionMulAppFun α U r V (a • x) =
      a • sourceSectionMulAppFun α U r V x := by
  sorry

private def sourceSectionMulApp (U : Opens X) (r : (ringSheaf 𝒪₂).obj.obj (op U))
    (V : (Over U)ᵒᵖ) :
    (overPresheafModule 𝒪₁ (restrictedUnit α) U).obj V ⟶
      (overPresheafModule 𝒪₁ (restrictedUnit α) U).obj V :=
  let M : ModuleCat ((overRingPresheaf 𝒪₁ U).obj V) :=
    (overPresheafModule 𝒪₁ (restrictedUnit α) U).obj V
  let f : M →ₗ[(overRingPresheaf 𝒪₁ U).obj V] M :=
    { toFun := sourceSectionMulAppFun α U r V
      map_add' := sourceSectionMulAppFun_map_add α U r V
      map_smul' := sourceSectionMulAppFun_map_smul α U r V }
  ((ModuleCat.homEquiv : (M ⟶ M) ≃ (M →ₗ[(overRingPresheaf 𝒪₁ U).obj V] M)).symm f)

private theorem sourceSectionMul_naturality (U : Opens X)
    (r : (ringSheaf 𝒪₂).obj.obj (op U)) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) :
    (overPresheafModule 𝒪₁ (restrictedUnit α) U).map f ≫
      (ModuleCat.restrictScalars (((overRingPresheaf 𝒪₁ U).map f).hom)).map
        (sourceSectionMulApp α U r W) =
      sourceSectionMulApp α U r V ≫
        (overPresheafModule 𝒪₁ (restrictedUnit α) U).map f := by
  let _ := r
  sorry

private def sourceSectionMul (U : Opens X) (r : (ringSheaf 𝒪₂).obj.obj (op U)) :
    overPresheafModule 𝒪₁ (restrictedUnit α) U ⟶
      overPresheafModule 𝒪₁ (restrictedUnit α) U where
  app V := sourceSectionMulApp α U r V
  naturality f := sourceSectionMul_naturality α U r f

private instance overHomSMul (𝒢 : SheafOfModules (ringSheaf 𝒪₁)) (U : Opens X) :
    SMul ((ringSheaf 𝒪₂).obj.obj (op U)) (overHom α 𝒢 U) where
  smul r φ := sourceSectionMul α U r ≫ φ

private instance overHomModule (𝒢 : SheafOfModules (ringSheaf 𝒪₁)) (U : Opens X) :
    Module ((ringSheaf 𝒪₂).obj.obj (op U)) (overHom α 𝒢 U) where
  one_smul φ := by
    sorry
  mul_smul r s φ := by
    sorry
  smul_add r φ ψ := by
    sorry
  smul_zero r := by
    sorry
  add_smul r s φ := by
    sorry
  zero_smul φ := by
    sorry

private def coextendScalarsToPresheaf (𝒢 : SheafOfModules (ringSheaf 𝒪₁)) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (overHom α 𝒢 U.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := localHomMap α f
      map_zero' := by
        sorry
      map_add' := by
        sorry }
  map_id := by
    sorry
  map_comp := by
    sorry

private instance coextendScalarsToPresheaf_objModule
    (𝒢 : SheafOfModules (ringSheaf 𝒪₁)) (U : (Opens X)ᵒᵖ) :
    Module ((ringSheaf 𝒪₂).obj.obj U) ((coextendScalarsToPresheaf α 𝒢).obj U) :=
  overHomModule α 𝒢 U.unop

/-- The presheaf `U ↦ Hom_{𝒪₁|U}(𝒪₂|U, 𝒢|U)` with its canonical `𝒪₂`-module structure. -/
def coextendScalarsPresheaf (𝒢 : SheafOfModules (ringSheaf 𝒪₁)) :
    PresheafOfModules (ringSheaf 𝒪₂).obj :=
  PresheafOfModules.ofPresheaf (coextendScalarsToPresheaf α 𝒢)
    (fun f r φ ↦ by
      sorry)

/-- The local-Hom presheaf `coextendScalarsPresheaf α 𝒢` is a sheaf. -/
theorem coextendScalars_isSheaf (𝒢 : SheafOfModules (ringSheaf 𝒪₁)) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (coextendScalarsPresheaf α 𝒢).presheaf := by
  sorry

/-- The sheaf `\mathcal H\!\mathit{om}_{\mathcal O_1}(\mathcal O_2, \mathcal G)`. -/
noncomputable def coextendScalars (𝒢 : SheafOfModules (ringSheaf 𝒪₁)) :
    SheafOfModules (ringSheaf 𝒪₂) where
  val := coextendScalarsPresheaf α 𝒢
  isSheaf := coextendScalars_isSheaf α 𝒢

variable (ℱ : SheafOfModules (ringSheaf 𝒪₂)) (𝒢 : SheafOfModules (ringSheaf 𝒪₁))

private abbrev idOver (U : (Opens X)ᵒᵖ) : Over U.unop :=
  Over.mk (𝟙 U.unop)

private def toCoextendScalarsPresheafApp
    (τ : ((SheafOfModules.restrictScalars (ringSheafMap α)).obj ℱ).val ⟶ 𝒢.val)
    (U : (Opens X)ᵒᵖ) :
    ℱ.val.obj U ⟶ (coextendScalarsPresheaf α 𝒢).obj U :=
  let M : ModuleCat ((ringSheaf 𝒪₂).obj.obj U) := ℱ.val.obj U
  let N : ModuleCat ((ringSheaf 𝒪₂).obj.obj U) := (coextendScalarsPresheaf α 𝒢).obj U
  let f : M →ₗ[(ringSheaf 𝒪₂).obj.obj U] N :=
    { toFun := fun s ↦
        { app := fun V ↦
            let M₁ : ModuleCat ((overRingPresheaf 𝒪₁ U.unop).obj V) :=
              (overPresheafModule 𝒪₁ (restrictedUnit α) U.unop).obj V
            let M₂ : ModuleCat ((overRingPresheaf 𝒪₁ U.unop).obj V) :=
              (overPresheafModule 𝒪₁ 𝒢.val U.unop).obj V
            let g : M₁ →ₗ[(overRingPresheaf 𝒪₁ U.unop).obj V] M₂ :=
              { toFun := fun r ↦
                  let r' : (ringSheaf 𝒪₂).obj.obj (op V.unop.left) := r
                  let sV : ℱ.val.obj (op V.unop.left) := ℱ.val.map (op V.unop.hom) s
                  τ.app (op V.unop.left) (r' • sV)
                map_add' := by
                  sorry
                map_smul' := by
                  sorry }
            ((ModuleCat.homEquiv :
                (M₁ ⟶ M₂) ≃ (M₁ →ₗ[(overRingPresheaf 𝒪₁ U.unop).obj V] M₂)).symm g)
          naturality := by
            intro V W f
            ext r
            sorry }
      map_add' := by
        sorry
      map_smul' := by
        sorry }
  ((ModuleCat.homEquiv : (M ⟶ N) ≃ (M →ₗ[(ringSheaf 𝒪₂).obj.obj U] N)).symm f)

private def toCoextendScalarsPresheaf
    (τ : ((SheafOfModules.restrictScalars (ringSheafMap α)).obj ℱ).val ⟶ 𝒢.val) :
    ℱ.val ⟶ coextendScalarsPresheaf α 𝒢 where
  app U := toCoextendScalarsPresheafApp α ℱ 𝒢 τ U
  naturality f := by
    sorry

private def fromCoextendScalarsPresheafApp
    (η : ℱ.val ⟶ coextendScalarsPresheaf α 𝒢) (U : (Opens X)ᵒᵖ) :
    ((SheafOfModules.restrictScalars (ringSheafMap α)).obj ℱ).val.obj U ⟶ 𝒢.val.obj U :=
  let M : ModuleCat ((ringSheaf 𝒪₁).obj.obj U) :=
    ((SheafOfModules.restrictScalars (ringSheafMap α)).obj ℱ).val.obj U
  let N : ModuleCat ((ringSheaf 𝒪₁).obj.obj U) := 𝒢.val.obj U
  let f : M →ₗ[(ringSheaf 𝒪₁).obj.obj U] N :=
    { toFun := fun s ↦
        let oneU : (ringSheaf 𝒪₂).obj.obj U := 1
        (η.app U s).app (op (Over.mk (𝟙 U.unop))) oneU
      map_add' := by
        sorry
      map_smul' := by
        sorry }
  ((ModuleCat.homEquiv : (M ⟶ N) ≃ (M →ₗ[(ringSheaf 𝒪₁).obj.obj U] N)).symm f)

private def fromCoextendScalarsPresheaf
    (η : ℱ.val ⟶ coextendScalarsPresheaf α 𝒢) :
    ((SheafOfModules.restrictScalars (ringSheafMap α)).obj ℱ).val ⟶ 𝒢.val where
  app U := fromCoextendScalarsPresheafApp α ℱ 𝒢 η U
  naturality f := by
    sorry

private def coextendScalarsPresheafHomEquiv :
    (((SheafOfModules.restrictScalars (ringSheafMap α)).obj ℱ).val ⟶ 𝒢.val) ≃
      (ℱ.val ⟶ coextendScalarsPresheaf α 𝒢) where
  toFun := toCoextendScalarsPresheaf α ℱ 𝒢
  invFun := fromCoextendScalarsPresheaf α ℱ 𝒢
  left_inv := by
    sorry
  right_inv := by
    sorry

/-- Lemma 17.22.3: restriction of scalars along `α : 𝒪₁ ⟶ 𝒪₂` is left adjoint to the concrete
change-of-rings internal-Hom object `coextendScalars α 𝒢 = \mathcal H\!\mathit{om}_{𝒪₁}(𝒪₂, 𝒢)`,
so there is a canonical bifunctorial bijection
`Hom_{𝒪₁}(ℱ_{𝒪₁}, 𝒢) ≃ Hom_{𝒪₂}(ℱ, \mathcal H\!\mathit{om}_{𝒪₁}(𝒪₂, 𝒢))`. -/
noncomputable def restrictScalars_homEquiv_coextendScalars :
    (((SheafOfModules.restrictScalars (ringSheafMap α)).obj ℱ) ⟶ 𝒢) ≃
      (ℱ ⟶ coextendScalars α 𝒢) :=
  ((SheafOfModules.fullyFaithfulForget (ringSheaf 𝒪₁)).homEquiv :
      (((SheafOfModules.restrictScalars (ringSheafMap α)).obj ℱ) ⟶ 𝒢) ≃
        (((SheafOfModules.restrictScalars (ringSheafMap α)).obj ℱ).val ⟶ 𝒢.val)).trans <|
    (coextendScalarsPresheafHomEquiv α ℱ 𝒢).trans <|
      (((SheafOfModules.fullyFaithfulForget (ringSheaf 𝒪₂)).homEquiv :
          (ℱ ⟶ coextendScalars α 𝒢) ≃ (ℱ.val ⟶ (coextendScalars α 𝒢).val))).symm

end TopCat.Sheaf
