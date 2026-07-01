import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u v

namespace PresheafOfModules

/-- A sheaf of commutative rings viewed as a `RingCat`-valued sheaf. -/
private abbrev ringSheaf {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (𝒪 : Sheaf J CommRingCat.{max u v}) : Sheaf J RingCat.{max u v} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

/- Domain-style sampling for Lemma 18.27.1:
- primary domain: local `𝒪`-linear Hom on slice sites for presheaves and sheaves of modules over a
  commutative ring sheaf;
- sampled owner declarations:
  `PresheafOfModules.pushforward₀`,
  `PresheafOfModules.ofPresheaf`,
  `SheafOfModules.toSheaf`,
  `CategoryTheory.sheafHom`;
- best owner abstraction: the source-facing owner is a `PresheafOfModules (ringSheaf J 𝒪).obj`,
  and hence a `SheafOfModules (ringSheaf J 𝒪)` after proving the sheaf condition;
- primitive data: a commutative ring sheaf `𝒪`, a presheaf of `𝒪`-modules `ℱ`, and a sheaf of
  `𝒪`-modules `𝒢`;
- derived API: restriction to slice sites via `pushforward₀`, multiplication by a local section on
  a restricted presheaf of modules, the local Hom presheaf, and the resulting sheaf object.

Source/core/bridge triage:
- `source-facing`: the local `\mathcal O`-module
  `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal F, \mathcal G)`;
- `core/canonical`: `PresheafOfModules (ringSheaf J 𝒪).obj` together with restriction to slices by
  `PresheafOfModules.pushforward₀`;
- `bridge/view`: the codomain sheaf `𝒢` is used through its underlying presheaf of modules
  `𝒢.val`, while `SheafOfModules.toSheaf` remains only an underlying-abelian-sheaf forgetful view.

This rewrite targets the `source-facing` owner layer. It removes the previous bespoke
`Type`-valued wrapper and keeps the local Hom object as a genuine presheaf, hence sheaf, of
`𝒪`-modules. -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J CommRingCat.{max u v})

private abbrev overRingPresheaf (U : C) : (Over U)ᵒᵖ ⥤ RingCat.{max u v} :=
  (Over.forget U).op ⋙ (ringSheaf J 𝒪).obj

/-- The restriction of a presheaf of `𝒪`-modules to the slice site `C / U`. -/
private abbrev overPresheafModule (ℱ : PresheafOfModules (ringSheaf J 𝒪).obj) (U : C) :
    PresheafOfModules (overRingPresheaf 𝒪 U) :=
  (pushforward₀ (Over.forget U) (ringSheaf J 𝒪).obj).obj ℱ

/-- Multiplication by a local section on the restriction of a presheaf of `𝒪`-modules to
`C / U`, evaluated at an object of the slice. -/
def localSectionMulAppFun (ℳ : PresheafOfModules (ringSheaf J 𝒪).obj) (U : C)
    (r : (ringSheaf J 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ) :
    (overPresheafModule 𝒪 ℳ U).obj V → (overPresheafModule 𝒪 ℳ U).obj V :=
  fun m ↦
    let rV : (overRingPresheaf 𝒪 U).obj V :=
      show (overRingPresheaf 𝒪 U).obj V from
        ((ringSheaf J 𝒪).obj.map (op V.unop.hom) r)
    rV • m

/-- Objectwise multiplication by a local section preserves addition. -/
theorem localSectionMulAppFun_map_add (ℳ : PresheafOfModules (ringSheaf J 𝒪).obj) (U : C)
    (r : (ringSheaf J 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ)
    (x y : (overPresheafModule 𝒪 ℳ U).obj V) :
    localSectionMulAppFun 𝒪 ℳ U r V (x + y) =
      localSectionMulAppFun 𝒪 ℳ U r V x + localSectionMulAppFun 𝒪 ℳ U r V y := by
  sorry

/-- Objectwise multiplication by a local section is linear over the localized structure ring. -/
theorem localSectionMulAppFun_map_smul (ℳ : PresheafOfModules (ringSheaf J 𝒪).obj) (U : C)
    (r : (ringSheaf J 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ)
    (a : (overRingPresheaf 𝒪 U).obj V) (x : (overPresheafModule 𝒪 ℳ U).obj V) :
    localSectionMulAppFun 𝒪 ℳ U r V (a • x) =
      a • localSectionMulAppFun 𝒪 ℳ U r V x := by
  sorry

/-- Multiplication by a local section as an endomorphism of the restriction to `C / U`. -/
def localSectionMulApp (ℳ : PresheafOfModules (ringSheaf J 𝒪).obj) (U : C)
    (r : (ringSheaf J 𝒪).obj.obj (op U)) (V : (Over U)ᵒᵖ) :
    (overPresheafModule 𝒪 ℳ U).obj V ⟶ (overPresheafModule 𝒪 ℳ U).obj V :=
  let X : ModuleCat ((overRingPresheaf 𝒪 U).obj V) := (overPresheafModule 𝒪 ℳ U).obj V
  let f : X →ₗ[(overRingPresheaf 𝒪 U).obj V] X :=
    { toFun := localSectionMulAppFun 𝒪 ℳ U r V
      map_add' := localSectionMulAppFun_map_add 𝒪 ℳ U r V
      map_smul' := localSectionMulAppFun_map_smul 𝒪 ℳ U r V }
  ((ModuleCat.homEquiv : (X ⟶ X) ≃ (X →ₗ[(overRingPresheaf 𝒪 U).obj V] X)).symm f)

/-- Multiplication by a local section is natural on the localized presheaf of modules. -/
theorem localSectionMul_naturality (ℳ : PresheafOfModules (ringSheaf J 𝒪).obj) (U : C)
    (r : (ringSheaf J 𝒪).obj.obj (op U)) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    (overPresheafModule 𝒪 ℳ U).map f ≫
      (ModuleCat.restrictScalars (((overRingPresheaf 𝒪 U).map f).hom)).map
        (localSectionMulApp 𝒪 ℳ U r Y) =
      localSectionMulApp 𝒪 ℳ U r X ≫ (overPresheafModule 𝒪 ℳ U).map f := by
  sorry

/-- Multiplication by a local section as an endomorphism of the restriction to `C / U`. -/
def localSectionMul (ℳ : PresheafOfModules (ringSheaf J 𝒪).obj) (U : C)
    (r : (ringSheaf J 𝒪).obj.obj (op U)) :
    overPresheafModule 𝒪 ℳ U ⟶ overPresheafModule 𝒪 ℳ U where
  app V := localSectionMulApp 𝒪 ℳ U r V
  naturality f := localSectionMul_naturality 𝒪 ℳ U r f

/-- The localized multiplication endomorphism for the zero section is zero. -/
theorem localSectionMul_zero (ℳ : PresheafOfModules (ringSheaf J 𝒪).obj) (U : C) :
    localSectionMul 𝒪 ℳ U 0 = 0 := by
  sorry

/-- The localized multiplication endomorphism is additive in the section. -/
theorem localSectionMul_add (ℳ : PresheafOfModules (ringSheaf J 𝒪).obj) (U : C)
    (r s : (ringSheaf J 𝒪).obj.obj (op U)) :
    localSectionMul 𝒪 ℳ U (r + s) =
      localSectionMul 𝒪 ℳ U r + localSectionMul 𝒪 ℳ U s := by
  sorry

/-- The localized multiplication endomorphism for the unit section is the identity. -/
theorem localSectionMul_one (ℳ : PresheafOfModules (ringSheaf J 𝒪).obj) (U : C) :
    localSectionMul 𝒪 ℳ U 1 = 𝟙 _ := by
  sorry

/-- Localized multiplication is multiplicative in the section. -/
theorem localSectionMul_mul (ℳ : PresheafOfModules (ringSheaf J 𝒪).obj) (U : C)
    (r s : (ringSheaf J 𝒪).obj.obj (op U)) :
    localSectionMul 𝒪 ℳ U (r * s) =
      localSectionMul 𝒪 ℳ U s ≫ localSectionMul 𝒪 ℳ U r := by
  sorry

variable (ℱ : PresheafOfModules (ringSheaf J 𝒪).obj) (𝒢 : SheafOfModules (ringSheaf J 𝒪))

private abbrev overHom (U : C) :=
  overPresheafModule 𝒪 ℱ U ⟶ overPresheafModule 𝒪 𝒢.val U

private abbrev localHomMap {U V : Cᵒᵖ} (f : U ⟶ V) :
    overHom 𝒪 ℱ 𝒢 U.unop → overHom 𝒪 ℱ 𝒢 V.unop :=
  (pushforward₀ (Over.map f.unop) (overRingPresheaf 𝒪 U.unop)).map

private instance overHomSMul (U : C) :
    SMul ((ringSheaf J 𝒪).obj.obj (op U)) (overHom 𝒪 ℱ 𝒢 U) where
  smul r φ := φ ≫ localSectionMul 𝒪 𝒢.val U r

private instance overHomModule (U : C) :
    Module ((ringSheaf J 𝒪).obj.obj (op U)) (overHom 𝒪 ℱ 𝒢 U) where
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

/-- The underlying abelian-group-valued presheaf of the local `𝒪`-module Hom object. -/
private def localHomToPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj U := AddCommGrpCat.of (overHom 𝒪 ℱ 𝒢 U.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := localHomMap 𝒪 ℱ 𝒢 f
      map_zero' := by
        sorry
      map_add' := by
        sorry }
  map_id := by
    sorry
  map_comp := by
    sorry

private instance localHomToPresheaf_objModule (U : Cᵒᵖ) :
    Module ((ringSheaf J 𝒪).obj.obj U) ((localHomToPresheaf 𝒪 ℱ 𝒢).obj U) :=
  overHomModule 𝒪 ℱ 𝒢 U.unop

/-- The local `𝒪`-linear Hom presheaf. -/
def localHomPresheaf : PresheafOfModules (ringSheaf J 𝒪).obj :=
  ofPresheaf (localHomToPresheaf 𝒪 ℱ 𝒢)
    (fun f r φ ↦ by
      sorry)

/-- Lemma 18.27.1: for a site `(\mathcal C, J)`, a sheaf of commutative rings
`\mathcal O`, a presheaf of `\mathcal O`-modules `\mathcal F`, and a sheaf of
`\mathcal O`-modules `\mathcal G`, the local Hom object
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal F, \mathcal G)` is a sheaf of
`\mathcal O`-modules. Its underlying presheaf owner is `localHomPresheaf 𝒪 ℱ 𝒢`. -/
theorem internalHom_isSheaf :
    Presheaf.IsSheaf J (localHomPresheaf 𝒪 ℱ 𝒢).presheaf := by
  sorry

/-- The sheaf of `\mathcal O`-modules `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal F,
\mathcal G)` from Lemma 18.27.1. -/
def localHomSheaf : SheafOfModules (ringSheaf J 𝒪) where
  val := localHomPresheaf 𝒪 ℱ 𝒢
  isSheaf := internalHom_isSheaf 𝒪 ℱ 𝒢

end PresheafOfModules
