import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_27_1 (from Chap18) -/
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

/-! ### Lemma_18_27_2 (from Chap18) -/
open CategoryTheory

/- Domain-style sampling for Lemma 18.27.2:
- primary domain: prestacks on a site, viewed as pseudofunctors `Cᵒᵖ ⥤ᵖ Cat`, together with the
  Hom-presheaves on slice categories and their compatibility with restriction;
- sampled owner API:
  `Pseudofunctor.presheafHom`,
  `Pseudofunctor.presheafHomObjHomEquiv`,
  `Pseudofunctor.overMapCompPresheafHomIso`,
  `Pseudofunctor.sheafHom`;
- best owner abstraction: the Hom-presheaf owner `Pseudofunctor.presheafHom`, with
  `Pseudofunctor.overMapCompPresheafHomIso` as the canonical restriction-compatibility isomorphism;
- primitive data: a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, a base object `S : C`,
  two fiber objects `M N : F.obj (.mk (Opposite.op S))`, and a morphism `q : S' ⟶ S`;
- derived API: the slice-site Hom-presheaf `F.presheafHom M N`, its value at the identity object,
  the restriction isomorphism along `Over.map q`, and under prestack hypotheses the associated
  sheaf `F.sheafHom`.

Source/core/bridge triage:
- `source-facing`: internal Hom for modules on localized ringed sites commutes with restriction to
  a slice site;
- `core/canonical`: `Pseudofunctor.overMapCompPresheafHomIso`;
- `bridge/view`: specializing the generic prestack statement to the pseudofunctor of localized
  module categories and then using `Presieve.isSheafFor_iff_of_iso` in descent arguments.

This file is therefore a core/canonical recall file. No chapter-local compatibility wrapper should
survive here, since the exact comparison isomorphism already lives upstream in mathlib.
-/
/- Lemma 18.27.2: for the prestack on a ringed site sending an object `U` to the category of
sheaves of `\mathcal O_U`-modules on the localized site `(C/U, J.over U)`, formation of the
internal Hom commutes with restriction to `U`. In canonical mathlib form, this is exactly the
generic compatibility isomorphism of the prestack Hom-presheaf with pullback to a slice site,
applied to the pseudofunctor of localized module categories. -/
recall Pseudofunctor.overMapCompPresheafHomIso

/-! ### Remark_18_27_3 (from Chap18) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Functor.LaxMonoidal
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Remark 18.27.3:
- primary domain: pullback of internal-Hom sheaves along a morphism of ringed sites;
- sampled owner declarations:
  `CategoryTheory.expComparison`,
  `SheafOfModules.pullback`,
  `RingedSite.Hom.(^*)`,
  `MonoidalClosed.curry`,
  `ihom.ev`;
- best owner abstraction: the ambient owner is the pullback functor `(f^*)`; when mathlib's
  Cartesian-closed comparison owner `CategoryTheory.expComparison` is available, this remark is
  its ringed-site component. In the tensor/internal-Hom setting used here, the public declaration
  remains the thin bridge obtained by currying the pullback of evaluation after the monoidal
  comparison of `(f^*)`;
- primitive data: a morphism of ringed sites `f` and two module sheaves `ℱ 𝒢`;
- derived API: the comparison morphism
  `f^*\mathcal H\!\mathit{om}(\mathcal F, \mathcal G) ⟶
    \mathcal H\!\mathit{om}(f^*\mathcal F, f^*\mathcal G)`.

Source/core/bridge triage:
- `source-facing`: the canonical pullback-to-internal-Hom comparison morphism;
- `core/canonical`: the pullback owner `(f^*)`, and, under the stronger Cartesian-closed
  assumptions used by mathlib's generic comparison API, `CategoryTheory.expComparison`;
- `bridge/view`: `pullbackInternalHomComparison`, which packages the comparison at the source
  statement level without exposing extra owner-side ambient assumptions. -/

variable {X Y : RingedSite} (f : X ⟶ Y)
variable [MonoidalCategory (SheafOfModules Y.structureSheaf)]
variable [MonoidalClosed (SheafOfModules Y.structureSheaf)]
variable [MonoidalCategory (SheafOfModules X.structureSheaf)]
variable [MonoidalClosed (SheafOfModules X.structureSheaf)]
variable [(f^*).Monoidal]

/-- Remark 18.27.3: a morphism of ringed sites carries the internal Hom sheaf of two
`\mathcal O_Y`-modules to the internal Hom sheaf of their pullbacks via a canonical comparison
morphism. -/
noncomputable def pullbackInternalHomComparison
    (ℱ 𝒢 : SheafOfModules Y.structureSheaf) :
    (f^*).obj ((ihom ℱ).obj 𝒢) ⟶
      (ihom ((f^*).obj ℱ)).obj ((f^*).obj 𝒢) :=
  MonoidalClosed.curry
    (μ (f^*) ℱ ((ihom ℱ).obj 𝒢) ≫
      (f^*).map ((ihom.ev ℱ).app 𝒢))

end RingedSite.Hom

/-! ### Lemma_18_27_4 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open Opposite

noncomputable section

universe u v

namespace CategoryTheory

/- Domain-style sampling for Lemma 18.27.4:
- primary domain: internal Hom in monoidal closed categories of presheaves and sheaves of modules
  over commutative ring objects;
- inspected owner declarations:
  `CategoryTheory.ihom`,
  `CategoryTheory.ihom.adjunction`,
  `CategoryTheory.MonoidalClosed.internalHom`,
  `CategoryTheory.MonoidalClosed.internalHomAdjunction₂`;
- best owner abstraction:
  `ihom` for the target-variable internal Hom, and
  `((MonoidalClosed.internalHom).flip.obj 𝒢)` for the source-variable contravariant internal Hom;
- primitive data:
  a monoidal closed module category together with a fixed module object;
- derived API:
  preservation of limits by `ihom ℱ`, and preservation of limits by the contravariant
  source-variable owner `((MonoidalClosed.internalHom).flip.obj 𝒢)`.

Source/core/bridge triage:
- `source-facing`: the four Stacks clauses asserting that internal Hom preserves limits in the
  target variable and sends colimits in the source variable to limits;
- `core/canonical`: `ihom`, `ihom.adjunction`, `MonoidalClosed.internalHom`, and
  `MonoidalClosed.internalHomAdjunction₂`;
- `bridge/view`: the braided transport that identifies the source-variable internal Hom with the
  same owner after exchanging tensor factors.

The target-variable clauses are exact uses of the owner theorem
`Adjunction.rightAdjoint_preservesLimits`, so they should appear only as direct canonical use. The
source-variable clauses are organized around the actual contravariant internal-Hom owner
`((MonoidalClosed.internalHom).flip.obj 𝒢)`, not the opposite-valued bridge
`(((MonoidalClosed.internalHom).flip.obj 𝒢).rightOp)`.
-/

section Generic

variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
variable [MonoidalClosed A]

-- Proof sketch: for fixed target `G`, the contravariant internal-Hom owner
-- `((MonoidalClosed.internalHom).flip.obj G)` is right adjoint to its `rightOp`, by currying in
-- one variable, transporting across the braiding, and currying back. Hence it preserves limits.
/-- For a fixed target object `G` in a braided monoidal closed category, the source-variable
contravariant internal-Hom functor preserves limits. -/
theorem internalHom_flip_obj_preservesLimits (G : A) :
    PreservesLimits ((MonoidalClosed.internalHom).flip.obj G) := by
  sorry

end Generic

section PresheafModulesTarget

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable [MonoidalCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable [MonoidalClosed (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))

/- Lemma 18.27.4 (1): for a presheaf of commutative rings `𝒪` and a fixed presheaf module `ℱ`,
the target-variable internal-Hom functor `𝒢 ↦ ℋom_𝒪(ℱ, 𝒢)` commutes with arbitrary limits. This is
exactly the canonical right-adjoint preservation theorem applied to `ihom.adjunction ℱ`. -/
#check ((ihom.adjunction ℱ).rightAdjoint_preservesLimits : PreservesLimits (ihom ℱ))

end PresheafModulesTarget

section PresheafModulesSource

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable [MonoidalCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable [BraidedCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable [MonoidalClosed (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable (𝒢 : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))

/- Lemma 18.27.4 (2): for a fixed presheaf module `𝒢`, the source-variable contravariant
internal-Hom functor `ℱ ↦ ℋom_𝒪(ℱ, 𝒢)` is the canonical owner
`((MonoidalClosed.internalHom).flip.obj 𝒢)`, and it preserves limits. Equivalently, it sends
colimits in presheaf modules to limits. -/
#check
  (internalHom_flip_obj_preservesLimits 𝒢 :
    PreservesLimits ((MonoidalClosed.internalHom).flip.obj 𝒢))

end PresheafModulesSource

section RingedSiteTarget

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable [MonoidalCategory (_root_.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (_root_.ringedSiteModuleCategory J 𝒪)]
variable (ℱ : _root_.ringedSiteModuleCategory J 𝒪)

/- Lemma 18.27.4 (3): on a ringed site `(C, J, 𝒪)`, for a fixed sheaf module `ℱ`, the
target-variable internal-Hom functor `𝒢 ↦ ℋom_𝒪(ℱ, 𝒢)` commutes with arbitrary limits. This is
again the direct owner theorem `rightAdjoint_preservesLimits` specialized to `ihom.adjunction ℱ`.
-/
#check ((ihom.adjunction ℱ).rightAdjoint_preservesLimits : PreservesLimits (ihom ℱ))

end RingedSiteTarget

section RingedSiteSource

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable [MonoidalCategory (_root_.ringedSiteModuleCategory J 𝒪)]
variable [BraidedCategory (_root_.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (_root_.ringedSiteModuleCategory J 𝒪)]
variable (𝒢 : _root_.ringedSiteModuleCategory J 𝒪)

/- Lemma 18.27.4 (4): for a fixed sheaf module `𝒢`, the source-variable contravariant internal-Hom
functor `ℱ ↦ ℋom_𝒪(ℱ, 𝒢)` is the canonical owner `((MonoidalClosed.internalHom).flip.obj 𝒢)`, and
it preserves limits. Equivalently, it sends colimits in sheaves of modules to limits. -/
#check
  (internalHom_flip_obj_preservesLimits 𝒢 :
    PreservesLimits ((MonoidalClosed.internalHom).flip.obj 𝒢))

end RingedSiteSource

end CategoryTheory

/-! ### Lemma_18_27_5 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u v

/- Domain-style sampling for Lemma 18.27.5:
- primary domain: left exactness of internal Hom in the monoidal closed category of sheaves of
  modules on a ringed site;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `ShortComplex`,
  `ihom`,
  `MonoidalClosed.pre`,
  `CategoryTheory.functor_leftExact_iff_maps_shortExact_to_exact_mono`;
- best owner abstraction:
  a short complex `S : ShortComplex (ringedSiteModuleCategory J 𝒪)` together with the internal-Hom
  owners `ihom ℱ` in the target variable and `pre` in the source variable;
- primitive data:
  a short exact sequence `S` of `𝒪`-modules and a fixed module in the remaining variable;
- derived API:
  the induced short complexes obtained from `S` by `ihom ℱ` and by source-variable
  precomposition.

Source/core/bridge triage:
- `source-facing`: the two exactness statements for internal Hom applied to a short exact sequence
  of `𝒪`-modules;
- `core/canonical`: `ringedSiteModuleCategory`, `ShortComplex`, `ihom`, and `pre`;
- `bridge/view`: the explicit short complexes built from the induced internal-Hom morphisms.

The local `RingedSiteModules` alias was a duplicate of the chapter owner
`ringedSiteModuleCategory`, and the split arrow data `{f₂₁, f₁, hcomp}` / `{g₀₁, g₁₂, hcomp}` was
derived from the canonical `ShortComplex` owner. This file therefore keeps the source-facing
exactness statements, but refines their public API to the canonical chapter owner and a
`ShortComplex`-first surface. -/

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: `pre` is contravariantly functorial in the source variable, so the composite
-- induced by `S.f ≫ S.g = 0` vanishes.
private theorem ringedSiteModuleInternalHom_pre_app_comp_zero
    {S : ShortComplex (ringedSiteModuleCategory J 𝒪)} (𝒢 : ringedSiteModuleCategory J 𝒪) :
    (MonoidalClosed.pre S.g).app 𝒢 ≫ (MonoidalClosed.pre S.f).app 𝒢 = 0 := by
  sorry

-- Proof sketch: functoriality of `ihom ℱ` sends the zero composite `S.f ≫ S.g = 0` to zero.
private theorem ringedSiteModuleInternalHom_map_comp_zero
    {S : ShortComplex (ringedSiteModuleCategory J 𝒪)} (ℱ : ringedSiteModuleCategory J 𝒪) :
    (ihom ℱ).map S.f ≫ (ihom ℱ).map S.g = 0 := by
  sorry

-- Proof sketch: fix `𝒢` and regard `ℱ ↦ ℋom_𝒪(ℱ, 𝒢)` as the source-variable internal-Hom owner.
-- Lemma 18.27.4 gives the relevant limit preservation, and Lemma 12.7.2 converts that to left
-- exactness on mapped short exact sequences.
/-- Lemma 18.27.5 (1): if `ℱ₂ ⟶ ℱ₁ ⟶ ℱ ⟶ 0` is a short exact sequence of `𝒪`-modules on a ringed
site, then `0 ⟶ ℋom_𝒪(ℱ, 𝒢) ⟶ ℋom_𝒪(ℱ₁, 𝒢) ⟶ ℋom_𝒪(ℱ₂, 𝒢)` is exact. -/
theorem ringedSiteModuleInternalHom_exact_in_source
    {S : ShortComplex (ringedSiteModuleCategory J 𝒪)}
    (hS : S.ShortExact) (𝒢 : ringedSiteModuleCategory J 𝒪) :
    (ShortComplex.mk
        ((MonoidalClosed.pre S.g).app 𝒢)
        ((MonoidalClosed.pre S.f).app 𝒢)
        (ringedSiteModuleInternalHom_pre_app_comp_zero J 𝒪 𝒢)).Exact ∧
      Mono ((MonoidalClosed.pre S.g).app 𝒢) := by
  sorry

-- Proof sketch: for fixed `ℱ`, the functor `𝒢 ↦ ℋom_𝒪(ℱ, 𝒢)` is the right adjoint `ihom ℱ`.
-- Lemma 18.27.4 supplies preservation of limits, and Lemma 12.7.2 converts that to left
-- exactness of the induced Hom sequence.
/-- Lemma 18.27.5 (2): if `0 ⟶ 𝒢 ⟶ 𝒢₁ ⟶ 𝒢₂` is a short exact sequence of `𝒪`-modules on a ringed
site, then `0 ⟶ ℋom_𝒪(ℱ, 𝒢) ⟶ ℋom_𝒪(ℱ, 𝒢₁) ⟶ ℋom_𝒪(ℱ, 𝒢₂)` is exact. -/
theorem ringedSiteModuleInternalHom_exact_in_target
    {S : ShortComplex (ringedSiteModuleCategory J 𝒪)}
    (hS : S.ShortExact) (ℱ : ringedSiteModuleCategory J 𝒪) :
    (ShortComplex.mk
        ((ihom ℱ).map S.f)
        ((ihom ℱ).map S.g)
        (ringedSiteModuleInternalHom_map_comp_zero J 𝒪 ℱ)).Exact ∧
      Mono ((ihom ℱ).map S.f) := by
  sorry

end

/-! ### Lemma_18_27_6 (from Chap18) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Opposite

noncomputable section

universe v u

set_option quotPrecheck false in
local notation:20 X " ⟹ " Y:19 => (ihom X).obj Y

/- Domain-style sampling for Lemma 18.27.6:
- primary domain: tensor-internal-Hom adjunctions in braided monoidal closed categories;
- inspected owner declarations:
  `CategoryTheory.ihom`,
  `MonoidalClosed.curry`,
  `MonoidalClosed.uncurry`,
  `MonoidalClosed.internalHomAdjunction₂.homEquiv`,
  `ringedSiteModuleCategory`;
- best owner abstraction:
  the canonical owner is mathlib's internal-Hom adjunction with internal-Hom object
  `𝒢 ⟹ ℋ`, and the Stacks source orientation `Hom(ℱ ⊗ 𝒢, ℋ) ≃ Hom(ℱ, Hom(𝒢, ℋ))`
  is obtained by transporting that owner along the braiding;
- primitive data:
  objects `ℱ 𝒢 ℋ` in a braided monoidal closed category;
- derived API:
  the source-oriented Hom-set equivalence itself, together with its presheaf and ringed-site
  specializations.

Source/core/bridge triage:
- `source-facing`: the source-oriented equivalence
  `(ℱ ⊗ 𝒢 ⟶ ℋ) ≃ (ℱ ⟶ (𝒢 ⟹ ℋ))`;
- `core/canonical`: `MonoidalClosed.internalHomAdjunction₂.homEquiv`, equivalently
  `MonoidalClosed.curry` / `MonoidalClosed.uncurry`;
- `bridge/view`: transport across the braiding isomorphism
  `β_ ℱ 𝒢 : ℱ ⊗ 𝒢 ≅ 𝒢 ⊗ ℱ`.
-/

section Generic

variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
variable [MonoidalClosed A]
variable (ℱ 𝒢 ℋ : A)

/- Lemma 18.27.6: the textbook bijection
`Hom(ℱ ⊗ 𝒢, ℋ) ≃ Hom(ℱ, Hom(𝒢, ℋ))`
is the canonical internal-Hom adjunction, transported from the owner orientation
`Hom(𝒢 ⊗ ℱ, ℋ) ≃ Hom(ℱ, Hom(𝒢, ℋ))` along the braiding. -/
#check
  (show (ℱ ⊗ 𝒢 ⟶ ℋ) ≃ (ℱ ⟶ (𝒢 ⟹ ℋ)) from
    ((β_ ℱ 𝒢).homCongr (Iso.refl ℋ)).trans
      ((MonoidalClosed.internalHomAdjunction₂.homEquiv :
        (𝒢 ⊗ ℱ ⟶ ℋ) ≃ (ℱ ⟶ (𝒢 ⟹ ℋ)))))

end Generic

section PresheafModules

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable [BraidedCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable [MonoidalClosed (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable (ℱ 𝒢 ℋ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))

/- Presheaf-module specialization of Lemma 18.27.6. -/
#check
  (show (ℱ ⊗ 𝒢 ⟶ ℋ) ≃
      (ℱ ⟶ (𝒢 ⟹ ℋ)) from
    ((β_ ℱ 𝒢).homCongr (Iso.refl ℋ)).trans
      ((MonoidalClosed.internalHomAdjunction₂.homEquiv :
        (𝒢 ⊗ ℱ ⟶ ℋ) ≃
          (ℱ ⟶ (𝒢 ⟹ ℋ)))))

end PresheafModules

section RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [MonoidalCategory (_root_.ringedSiteModuleCategory J 𝒪)]
variable [BraidedCategory (_root_.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (_root_.ringedSiteModuleCategory J 𝒪)]
variable (ℱ 𝒢 ℋ : _root_.ringedSiteModuleCategory J 𝒪)

/- Ringed-site-module specialization of Lemma 18.27.6. -/
#check
  (show (ℱ ⊗ 𝒢 ⟶ ℋ) ≃
      (ℱ ⟶ (𝒢 ⟹ ℋ)) from
    ((β_ ℱ 𝒢).homCongr (Iso.refl ℋ)).trans
      ((MonoidalClosed.internalHomAdjunction₂.homEquiv :
        (𝒢 ⊗ ℱ ⟶ ℋ) ≃
          (ℱ ⟶ (𝒢 ⟹ ℋ)))))

end RingedSite

/-! ### Lemma_18_27_7 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite

noncomputable section

universe u v

/- Domain-style sampling for Lemma 18.27.7:
- primary domain: monoidal closed categories of presheaves and sheaves of modules;
- inspected owner declarations:
  `CategoryTheory.ihom`,
  `CategoryTheory.ihom.adjunction`,
  the canonical instance `PreservesColimits (tensorLeft A)`,
  `ringedSiteModuleCategory`;
- best owner abstraction:
  the public owner is the left-tensor functor `tensorLeft ℱ`, with colimit preservation already
  supplied canonically by the internal-Hom adjunction `ihom.adjunction ℱ`;
- primitive data:
  a fixed module object `ℱ` in the ambient monoidal closed module category;
- derived API:
  the `PreservesColimits (tensorLeft ℱ)` instance, together with its presheaf and ringed-site
  specializations.

Source/core/bridge triage:
- `source-facing`: the Stacks statements that tensoring on the left with a fixed module commutes
  with arbitrary colimits on `PMod(𝒪)` and `Mod(𝒪)`;
- `core/canonical`: `tensorLeft ℱ` and its canonical `PreservesColimits` instance;
- `bridge/view`: the specializations below to presheaf modules and to the chapter owner
  `ringedSiteModuleCategory J 𝒪`.

Primitive-vs-derived split:
- primitive data: only the ambient monoidal closed module category and the chosen object `ℱ`;
- derived API: colimit preservation of `tensorLeft ℱ`. No local theorem wrapper is needed because
  the exact interface is already owned upstream.
-/

section PresheafModules

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable [MonoidalCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable [MonoidalClosed (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))

/- Lemma 18.27.7 (1): for a presheaf of rings `𝒪` and a fixed presheaf of `𝒪`-modules `ℱ`, the
functor `𝒢 ↦ ℱ ⊗ 𝒢` on `PMod(𝒪)` commutes with arbitrary colimits. This is exactly the canonical
instance `PreservesColimits (tensorLeft ℱ)`. -/
#synth PreservesColimits (tensorLeft ℱ)

end PresheafModules

section RingedSiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable [MonoidalCategory (_root_.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (_root_.ringedSiteModuleCategory J 𝒪)]
variable (ℱ : _root_.ringedSiteModuleCategory J 𝒪)

/- Lemma 18.27.7 (2): on a ringed site `(C, J, 𝒪)`, for a fixed sheaf of `𝒪`-modules `ℱ`, the
functor `𝒢 ↦ ℱ ⊗ 𝒢` on `Mod(𝒪)` commutes with arbitrary colimits. This is the same canonical
owner instance `PreservesColimits (tensorLeft ℱ)`, expressed on the chapter owner category
`ringedSiteModuleCategory J 𝒪`. -/
#synth PreservesColimits (tensorLeft ℱ)

end RingedSiteModules

/-! ### Lemma_18_27_8 (from Chap18) -/
open CategoryTheory Opposite

universe v u

variable {C : Type u} [Category.{v} C]
variable {𝒪 𝒪' : Cᵒᵖ ⥤ RingCat.{u}}
variable (p : 𝒪 ⟶ 𝒪') (X : Cᵒᵖ)
variable (𝒢 : PresheafOfModules 𝒪') (ℱ : PresheafOfModules 𝒪)

/- Domain-style sampling for Lemma 18.27.8:
- primary domain: change of rings for presheaves of modules, evaluated sectionwise;
- sampled owner declarations:
  `PresheafOfModules.restrictScalars`,
  `PresheafOfModules.evaluation`,
  `ModuleCat.restrictCoextendScalarsAdj`;
- best owner abstraction: the sectionwise canonical change-of-rings adjunction
  `ModuleCat.restrictCoextendScalarsAdj (p.app X).hom`;
- primitive data: the ring-presheaf morphism `p`, the section `X`, and the module presheaves
  `𝒢`, `ℱ`;
- derived API: the specialized Hom-set equivalence after evaluating at `X`.

Source/core/bridge triage:
- `source-facing`: the sectionwise change-of-rings Hom-bijection used in the internal-Hom
  construction;
- `core/canonical`: `ModuleCat.restrictCoextendScalarsAdj (p.app X).hom`;
- `bridge/view`: the typed specialization of `.homEquiv` to the `X`-sections of
  `PresheafOfModules.restrictScalars p`.

The previous file only wrapped this owner equivalence under a duplicate local name, so the refined
form keeps the canonical owner directly and exposes the textbook sectionwise statement only as its
specialized derived API.
-/

/- Lemma 18.27.8, owner form: for each `X`, the algebra controlling change of rings for
`\mathcal O`- and `\mathcal O'`-module sections is exactly the canonical adjunction
`ModuleCat.restrictCoextendScalarsAdj (p.app X).hom`. -/
recall ModuleCat.restrictCoextendScalarsAdj

/- Lemma 18.27.8 companion: after evaluating at `X`, the canonical adjunction above gives the
sectionwise Hom-set bijection
`Hom_{\mathcal O(X)}(\mathcal G(X), \mathcal F(X)) ≃
  Hom_{\mathcal O'(X)}(\mathcal G(X), \operatorname{Coext}(\mathcal F(X)))`,
with the source viewed via `PresheafOfModules.restrictScalars p`. -/
#check
  (((ModuleCat.restrictCoextendScalarsAdj (p.app X).hom).homEquiv (𝒢.obj X) (ℱ.obj X)) :
    (((PresheafOfModules.restrictScalars p).obj 𝒢).obj X ⟶ ℱ.obj X) ≃
      (𝒢.obj X ⟶ (ModuleCat.coextendScalars (p.app X).hom).obj (ℱ.obj X)))

/-! ### Lemma_18_27_9 (from Chap18) -/
open CategoryTheory MonoidalCategory
open Functor.OplaxMonoidal

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

private abbrev localizedStructureSheaf :=
  (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U)

/- Domain-style sampling for Lemma 18.27.9:
- primary domain: localized extension by zero and restriction for sheaves of modules on a ringed
  site, together with the tensor comparison attached to `j_{U!}`;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `Functor.OplaxMonoidal.δ`;
- best owner abstraction: the canonical pullback/pushforward pair attached to the identity map of
  the localized structure sheaf `localizedStructureSheaf J 𝒪 U`, with localized modules surfaced
  through `ringedSiteModuleCategory (J.over U) (𝒪.over U)`;
- primitive data: the canonical `RingCat`-valued structure sheaf
  `((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)`, the identity morphism of its
  localization at `U`, and the ambient monoidal structures;
- derived API: the source-facing tensor comparison for `j_{U!}`, stated directly on the canonical
  oplax monoidal morphism and counit.

Source/core/bridge triage:
- `source-facing`: the comparison
  `j_{U!}(\mathcal G \otimes_{\mathcal O_U} \mathcal F|_U) ⟶
    j_{U!}\mathcal G ⊗_{\mathcal O} \mathcal F`;
- `core/canonical`: `((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)`,
  `SheafOfModules.pullback
    (𝟙 (localizedStructureSheaf J 𝒪 U))`,
  `SheafOfModules.pushforward
    (𝟙 (localizedStructureSheaf J 𝒪 U))`, and
  `SheafOfModules.pullbackPushforwardAdjunction`;
- `bridge/view`: the source-facing tensor-comparison statement below, specialized from these
  owners. -/

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U))]

local instance : MonoidalCategory (SheafOfModules (localizedStructureSheaf J 𝒪 U)) := by
  change MonoidalCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U))
  infer_instance

variable
  [(SheafOfModules.pushforward (𝟙 (localizedStructureSheaf J 𝒪 U))).LaxMonoidal]

local instance :
    (SheafOfModules.pullback (𝟙 (localizedStructureSheaf J 𝒪 U))).OplaxMonoidal :=
  (SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 (localizedStructureSheaf J 𝒪 U))).leftAdjointOplaxMonoidal

-- Proof sketch: apply Yoneda to the canonical comparison morphism. For every target
-- `\mathcal H`, the adjunction `j_{U!} ⊣ j_U^*`, the tensor-internal-Hom adjunction on the
-- ambient and localized module categories, and the compatibility of internal Hom with
-- restriction from Lemma `18.27.2` identify postcomposition with this comparison morphism with a
-- chain of Hom-set equivalences. Hence the comparison is invertible.
/-- Lemma 18.27.9: for a ringed site `(\mathcal C, \mathcal O)`, an object `U : \mathcal C`, an
`\mathcal O_U`-module `\mathcal G`, and an `\mathcal O`-module `\mathcal F`, the canonical
comparison morphism
`j_{U!}(\mathcal G \otimes_{\mathcal O_U} \mathcal F|_U) \to
j_{U!}\mathcal G \otimes_{\mathcal O} \mathcal F`,
namely the canonical map `δ j_{U!} ≫ (1 \otimes \epsilon_{\mathcal F})`, is an isomorphism. -/
theorem ringedSiteLocalizedExtensionByZero_tensorComparison_isIso
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U))
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsIso
      (δ (SheafOfModules.pullback (𝟙 (localizedStructureSheaf J 𝒪 U))) 𝒢
          ((SheafOfModules.pushforward (𝟙 (localizedStructureSheaf J 𝒪 U))).obj ℱ) ≫
        (𝟙 _ ⊗ₘ
          (SheafOfModules.pullbackPushforwardAdjunction
            (𝟙 (localizedStructureSheaf J 𝒪 U))).counit.app ℱ)) := sorry

end

/-! ### Remark_18_27_10 (from Chap18) -/
open CategoryTheory.MonoidalCategory
open Opposite
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Remark 18.27.10:
- primary domain: localization of sheaves along the category-of-elements projection, free abelian
  sheaves, and the canonical sheaf-level monoidal owner used to express tensoring by `j_! \mathbf
  Z`;
- sampled owner declarations:
  `localizationProjection`,
  `Functor.sheafPullback`,
  `Sheaf.composeAndSheafify`,
  `Sheaf.monoidalCategory`;
- best owner abstraction: this remark is a `bridge/view` statement. Its first clause compares the
  canonical lower-shriek owner
  `(localizationProjection ℱ).sheafPullback AddCommGrpCat (localizationTopology ℱ) J`
  with the canonical free-abelian-sheaf owner
  `Sheaf.composeAndSheafify J AddCommGrpCat.free`; its second clause uses the chosen sheaf
  monoidal owner `Sheaf.monoidalCategory J AddCommGrpCat`, rather than an arbitrary monoidal
  structure on abelian sheaves;
- primitive data: only the sheaf `ℱ`, the localized constant integer sheaf, the abelian sheaf
  `ℋ`, and the canonical localization functors;
- derived API: the two comparison isomorphism statements below. Any exact-interface wrapper around
  these owners would carry no extra mathematics.

Source/core/bridge triage:
- `source-facing`: the source remark identifying `j_! \mathbf Z` with the free abelian sheaf on
  `ℱ`, and identifying `j_! j^{-1} \mathcal H` with `(j_! \mathbf Z) \otimes \mathcal H`;
- `core/canonical`: `localizationProjection`, `localizationTopology`,
  `Functor.sheafPullback`, `Functor.sheafPushforwardContinuous`,
  `Sheaf.composeAndSheafify`, and `Sheaf.monoidalCategory`;
- `bridge/view`: the private short names `jShriek`, `jStar`, and `jShriekInteger`, used only to
  present the source-facing `j_!` surface without introducing a parallel public owner. -/

section Localization

variable [HasWeakSheafify J AddCommGrpCat.{v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
variable (ℱ : Sheaf J (Type v))
variable [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
variable [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
  (localizationTopology ℱ) J).IsRightAdjoint]

private abbrev jShriek :
    Sheaf (localizationTopology ℱ) AddCommGrpCat.{v} ⥤ Sheaf J AddCommGrpCat.{v} :=
  (localizationProjection ℱ).sheafPullback AddCommGrpCat.{v} (localizationTopology ℱ) J

private abbrev jStar :
    Sheaf J AddCommGrpCat.{v} ⥤ Sheaf (localizationTopology ℱ) AddCommGrpCat.{v} :=
  (localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
    (localizationTopology ℱ) J

private abbrev localizedConstantIntegerSheaf :
    Sheaf (localizationTopology ℱ) AddCommGrpCat.{v} :=
  (constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
    (AddCommGrpCat.of (ULift.{v} ℤ))

private abbrev jShriekInteger : Sheaf J AddCommGrpCat.{v} :=
  (jShriek ℱ).obj (localizedConstantIntegerSheaf ℱ)

private noncomputable def addCommGrpForgetCorepresentableByZ :
    (forget AddCommGrpCat.{v}).CorepresentableBy (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  Functor.CorepresentableBy.ofIso
    (Functor.CorepresentableBy.coyoneda (op (AddCommGrpCat.of (ULift.{v} ℤ))))
    AddCommGrpCat.coyonedaObjIsoForget

private noncomputable def addCommGrpForgetCorepresentableByFreePUnit :
    (forget AddCommGrpCat.{v}).CorepresentableBy (AddCommGrpCat.free.obj PUnit) where
  homEquiv {Y} := (AddCommGrpCat.adj.homEquiv PUnit Y).trans (Equiv.funUnique PUnit Y)
  homEquiv_comp {Y Y'} g f := by
    change ((AddCommGrpCat.adj.homEquiv PUnit Y') (f ≫ g)) PUnit.unit =
      (forget AddCommGrpCat.{v}).map g (((AddCommGrpCat.adj.homEquiv PUnit Y) f) PUnit.unit)
    simpa using congrFun (AddCommGrpCat.adj.homEquiv_naturality_right f g) PUnit.unit

private noncomputable def addCommGrpFreePUnitIsoZ :
    AddCommGrpCat.free.obj PUnit ≅ AddCommGrpCat.of (ULift.{v} ℤ) :=
  Functor.CorepresentableBy.uniqueUpToIso
    (addCommGrpForgetCorepresentableByFreePUnit : _
      )
    (addCommGrpForgetCorepresentableByZ : _)

private noncomputable def localizationConstSingletonIsoChosenTerminal
    [HasWeakSheafify (localizationTopology ℱ) (Type v)] :
    ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ≅
      (⊤_ (Sheaf (localizationTopology ℱ) (Type v))) :=
  (sheafificationIso (Sheaf.terminal (localizationTopology ℱ)
      Limits.Types.isTerminalPUnit)).symm ≪≫
    Limits.IsTerminal.uniqueUpToIso
      (Sheaf.isTerminalTerminal (localizationTopology ℱ) Limits.Types.isTerminalPUnit)
      Limits.terminalIsTerminal

private noncomputable def localizationConstSingletonOverTerminalIso
    [HasWeakSheafify (localizationTopology ℱ) (Type v)] :
    (sheafCategoryOfElementsEquivOver ℱ).functor.obj
        ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ≅
      Over.mk (𝟙 ℱ) :=
  (Functor.mapIso (sheafCategoryOfElementsEquivOver ℱ).functor
      (localizationConstSingletonIsoChosenTerminal ℱ)) ≪≫
    PreservesTerminal.iso (sheafCategoryOfElementsEquivOver ℱ).functor ≪≫
    Limits.IsTerminal.uniqueUpToIso Limits.terminalIsTerminal Over.mkIdTerminal

private noncomputable def localizationConstSingletonToInverseImageEquiv
    [HasWeakSheafify (localizationTopology ℱ) (Type v)]
    (𝒢 : Sheaf J (Type v)) :
    (((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ⟶
        ((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
          (localizationTopology ℱ) J).obj 𝒢) ≃
      (ℱ ⟶ 𝒢) :=
  let hFF :
      ((sheafCategoryOfElementsEquivOver ℱ).functor).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful (sheafCategoryOfElementsEquivOver ℱ).functor
  let e₁ :
      (((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ⟶
          ((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
            (localizationTopology ℱ) J).obj 𝒢) ≃
        ((sheafCategoryOfElementsEquivOver ℱ).functor.obj
            ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ⟶
          (sheafCategoryOfElementsEquivOver ℱ).functor.obj
            (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
              (localizationTopology ℱ) J).obj 𝒢)) :=
    Functor.FullyFaithful.homEquiv hFF
  let e₂ :
      ((sheafCategoryOfElementsEquivOver ℱ).functor.obj
          ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ⟶
        (sheafCategoryOfElementsEquivOver ℱ).functor.obj
          (((localizationProjection ℱ).sheafPushforwardContinuous (Type v)
            (localizationTopology ℱ) J).obj 𝒢)) ≃
        (Over.mk (𝟙 ℱ) ⟶ (Over.star ℱ).obj 𝒢) :=
    (localizationConstSingletonOverTerminalIso ℱ).homCongr
      ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).app 𝒢)
  let e₃ : (Over.mk (𝟙 ℱ) ⟶ (Over.star ℱ).obj 𝒢) ≃ (ℱ ⟶ 𝒢) :=
    ((Over.forgetAdjStar ℱ).homEquiv (Over.mk (𝟙 ℱ)) 𝒢).symm
  e₁.trans (e₂.trans e₃)

private noncomputable def localizedConstantIntegerIsoComposeAndSheafifyTerminal
    [HasWeakSheafify (localizationTopology ℱ) (Type v)] :
    (localizedConstantIntegerSheaf ℱ) ≅
      (Sheaf.composeAndSheafify (localizationTopology ℱ) AddCommGrpCat.free).obj
        ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) :=
  let e :
      (Sheaf.composeAndSheafify (localizationTopology ℱ) AddCommGrpCat.free).obj
          ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit) ≅
        (constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.free.obj PUnit) :=
    (presheafToSheafCompComposeAndSheafifyIso (localizationTopology ℱ)
      AddCommGrpCat.free).app ((Functor.const _).obj PUnit) ≪≫
      Functor.mapIso (presheafToSheaf (localizationTopology ℱ) AddCommGrpCat.{v})
        ((Functor.compConstIso _ AddCommGrpCat.free).symm.app PUnit)
  (Functor.mapIso (constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v})
      addCommGrpFreePUnitIsoZ).symm ≪≫
    e.symm

end Localization

-- Proof sketch: identify the localization at `ℱ` with sheaves on the category of elements of
-- `ℱ`, use the adjunction for `(localizationProjection ℱ).sheafPullback AddCommGrpCat
-- (localizationTopology ℱ) J`, and compare the resulting Hom functor with the free-abelian-sheaf
-- adjunction of Lemma `18.5.2`. Yoneda then yields the canonical isomorphism.
/-- Remark 18.27.10: for a sheaf of sets `ℱ` on `(C, J)`, the lower shriek of the constant
integer sheaf along the localization at `ℱ` is canonically isomorphic to the free abelian sheaf
generated by `ℱ`; this is the statement `j_! \mathbf Z = \mathbf Z_\mathcal F^\#`. -/
noncomputable def localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (ℱ : Sheaf J (Type v))
    [HasWeakSheafify (localizationTopology ℱ) (Type v)]
    [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
    [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).IsRightAdjoint] :
    ((localizationProjection ℱ).sheafPullback AddCommGrpCat.{v}
        (localizationTopology ℱ) J).obj
        ((constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of (ULift.{v} ℤ))) ⟶
      ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ℱ) :=
  (((localizationProjection ℱ).sheafAdjunctionContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).homEquiv
      ((constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
        (AddCommGrpCat.of (ULift.{v} ℤ)))
      ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ℱ)).symm
    ((localizedConstantIntegerIsoComposeAndSheafifyTerminal ℱ).hom ≫
      (((Sheaf.adjunction (localizationTopology ℱ) AddCommGrpCat.adj).homEquiv
          ((constantSheaf (localizationTopology ℱ) (Type v)).obj PUnit)
          (((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
              (localizationTopology ℱ) J).obj
            ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ℱ))).symm
        (((localizationConstSingletonToInverseImageEquiv ℱ
            ((sheafForget J).obj ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ℱ))).symm
          ((Sheaf.adjunction J AddCommGrpCat.adj).unit.app ℱ)))))

theorem localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf_isIso
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (ℱ : Sheaf J (Type v))
    [HasWeakSheafify (localizationTopology ℱ) (Type v)]
    [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
    [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).IsRightAdjoint] :
    IsIso (localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf ℱ) := by
  sorry

/-- Remark 18.27.10: for a sheaf of sets `ℱ` on `(C, J)`, the lower shriek of the constant
integer sheaf along the localization at `ℱ` is canonically isomorphic to the free abelian sheaf
generated by `ℱ`; this is the statement `j_! \mathbf Z = \mathbf Z_\mathcal F^\#`. -/
noncomputable abbrev localization_constantInteger_lowerShriek_iso_freeAbelianSheafOnSheaf
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (ℱ : Sheaf J (Type v))
    [HasWeakSheafify (localizationTopology ℱ) (Type v)]
    [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
    [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).IsRightAdjoint] :
    ((localizationProjection ℱ).sheafPullback AddCommGrpCat.{v}
        (localizationTopology ℱ) J).obj
        ((constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of (ULift.{v} ℤ))) ≅
      ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ℱ) :=
  by
    letI := localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf_isIso
      ℱ
    exact asIso
      (localization_constantInteger_lowerShriek_to_freeAbelianSheafOnSheaf ℱ)

-- Proof sketch: use the adjunction for
-- `(localizationProjection ℱ).sheafPullback AddCommGrpCat (localizationTopology ℱ) J`, identify
-- morphisms out of the left-hand side with morphisms from `j_! \mathbf Z` into the internal Hom
-- sheaf by the canonical tensor-internal-Hom adjunction
-- `MonoidalClosed.internalHomAdjunction₂`, and conclude by Yoneda exactly as in the textbook
-- argument.
section Monoidal

attribute [local instance] Sheaf.monoidalCategory

/-- For an abelian sheaf `ℋ`, localization followed by lower shriek is canonically identified with
tensoring `ℋ` by the localized constant integer sheaf `j_! \mathbf Z`, where the tensor product is
taken in the chosen sheaf monoidal owner `Sheaf.monoidalCategory J AddCommGrpCat`. This is part
`(b)` of the remark in the site-of-elements model of the localization at `ℱ`. -/
private theorem localization_lowerShriek_inverseImage_iso_tensor_constantInteger_nonempty
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [MonoidalCategory AddCommGrpCat.{v}]
    [((J.W : MorphismProperty (Cᵒᵖ ⥤ AddCommGrpCat.{v}))).IsMonoidal]
    (ℱ : Sheaf J (Type v))
    [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
    [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).IsRightAdjoint]
    (ℋ : Sheaf J AddCommGrpCat.{v}) :
    Nonempty
      (((localizationProjection ℱ).sheafPullback AddCommGrpCat.{v}
          (localizationTopology ℱ) J).obj
          (((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
              (localizationTopology ℱ) J).obj ℋ) ≅
        ((((localizationProjection ℱ).sheafPullback AddCommGrpCat.{v}
            (localizationTopology ℱ) J).obj
            ((constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
              (AddCommGrpCat.of (ULift.{v} ℤ)))) ⊗ ℋ)) := by
  sorry

/-- For an abelian sheaf `ℋ`, localization followed by lower shriek is canonically identified with
tensoring `ℋ` by the localized constant integer sheaf `j_! \mathbf Z`, where the tensor product is
taken in the chosen sheaf monoidal owner `Sheaf.monoidalCategory J AddCommGrpCat`. This is part
`(b)` of the remark in the site-of-elements model of the localization at `ℱ`. -/
noncomputable def localization_lowerShriek_inverseImage_iso_tensor_constantInteger
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [MonoidalCategory AddCommGrpCat.{v}]
    [((J.W : MorphismProperty (Cᵒᵖ ⥤ AddCommGrpCat.{v}))).IsMonoidal]
    (ℱ : Sheaf J (Type v))
    [HasWeakSheafify (localizationTopology ℱ) AddCommGrpCat.{v}]
    [((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
      (localizationTopology ℱ) J).IsRightAdjoint]
    (ℋ : Sheaf J AddCommGrpCat.{v}) :
    ((localizationProjection ℱ).sheafPullback AddCommGrpCat.{v}
        (localizationTopology ℱ) J).obj
        (((localizationProjection ℱ).sheafPushforwardContinuous AddCommGrpCat.{v}
            (localizationTopology ℱ) J).obj ℋ) ≅
      ((((localizationProjection ℱ).sheafPullback AddCommGrpCat.{v}
          (localizationTopology ℱ) J).obj
          ((constantSheaf (localizationTopology ℱ) AddCommGrpCat.{v}).obj
            (AddCommGrpCat.of (ULift.{v} ℤ)))) ⊗ ℋ) :=
  Classical.choice
    (localization_lowerShriek_inverseImage_iso_tensor_constantInteger_nonempty
      ℱ ℋ)

end Monoidal

end CategoryTheory

/-! ### Lemma_18_27_11 (from Chap18) -/
open CategoryTheory Limits MonoidalClosed

noncomputable section

namespace SheafOfModules

/- Domain-style sampling for Lemma 18.27.11:
- primary domain: internal Hom in `SheafOfModules 𝒪` and its filtered-colimit comparison;
- sampled owner declarations:
  `colimit.post`,
  `isIso_internalHomColimitComparison_of_isFinitePresentation`;
- best owner abstraction: the comparison morphism is the generic owner `colimit.post`, while the
  finite-presentation isomorphism criterion is the source-facing theorem in `SheafOfModules`;
- primitive data: a ring-valued sheaf `𝒪`, a finitely presented module sheaf `ℱ`, and a filtered
  diagram `𝒢`;
- derived API: the comparison morphism and its isomorphism criterion are reused directly here. -/

/- Lemma 18.27.11, core/canonical recall: the comparison morphism
`colim_λ ℋom_𝒪(ℱ, 𝒢_λ) ⟶ ℋom_𝒪(ℱ, colim_λ 𝒢_λ)` is the specialization
`colimit.post 𝒢 (ihom ℱ)` of the generic colimit comparison map. -/
recall colimit.post

/- Lemma 18.27.11, core/canonical recall: for finitely presented `ℱ`, the comparison morphism is
an isomorphism by
`SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation`. -/
recall isIso_internalHomColimitComparison_of_isFinitePresentation

end SheafOfModules

/-! ### Lemma_18_27_12 (from Chap18) -/
open CategoryTheory Limits Opposite

noncomputable section

universe u w

namespace SheafOfModules

/- Domain-style sampling for Lemma 18.27.12:
- primary domain: categorical finite presentability in `SheafOfModules 𝒪`, expressed through
  preservation of filtered colimits by the represented functor `Hom_𝒪(ℱ, -)`;
- sampled owner declarations:
  `CategoryTheory.IsFinitelyPresentable`,
  `CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits`,
  `SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation`,
  `CategoryTheory.GrothendieckTopology.globalSectionsColimitComparison_bijective_of_quasiCompactTestSet`;
- best owner abstraction: the canonical owner is `CategoryTheory.IsFinitelyPresentable ℱ`, with
  the represented functor `coyoneda.obj (op ℱ)` preserving filtered colimits as the standard
  bridge characterization;
- primitive data: a ring-valued sheaf `𝒪`, a finitely presented `\mathcal O`-module `ℱ`, a
  filtered diagram `𝒢`, and the quasi-compact test-set hypothesis on `J`;
- derived API: the fixed-diagram comparison map `colimit.post 𝒢 (coyoneda.obj (op ℱ))`, the
  internal-Hom comparison from Lemma `18.27.11`, and the global-sections comparison from
  Lemma `7.17.8 (4)`.

Source/core/bridge triage:
- `source-facing`: finite presentation of `ℱ` together with the Stacks claim that
  `Hom_𝒪(ℱ, -)` preserves filtered colimits under the quasi-compact test-set hypothesis;
- `core/canonical`: `CategoryTheory.IsFinitelyPresentable ℱ`;
- `bridge/view`: `CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits` and the
  fixed-diagram comparison map `colimit.post 𝒢 (coyoneda.obj (op ℱ))`. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type u)]
variable {𝒪 : Sheaf J RingCat.{u}}
variable {Λ : Type w} [SmallCategory Λ] [IsFiltered Λ]

-- Proof sketch: apply Lemma `18.27.11` to identify the internal Hom into `colim_λ 𝒢_λ` with the
-- filtered colimit of the internal Homs, then apply Sites, Lemma `7.17.8 (4)` to the resulting
-- filtered diagram of internal Hom sheaves. By the standard owner theorem
-- `isFinitelyPresentable_iff_preservesFilteredColimits`, this upgrades finite presentation of `ℱ`
-- to categorical finite presentability.
/-- Lemma 18.27.12: under the quasi-compact test-set hypothesis of Sites, Lemma `7.17.8 (4)`, a
finitely presented `\mathcal O`-module `\mathcal F` is finitely presentable in the category
`SheafOfModules 𝒪`. Equivalently, the represented functor `Hom_\mathcal O(\mathcal F, -)`
preserves filtered colimits. -/
theorem preservesFilteredColimits_coyoneda_of_isFinitePresentation
    (hJ : ∃ S : Set (Sheaf J (Type u)),
      CategoryTheory.GrothendieckTopology.IsQuasiCompactTestSet J S)
    (ℱ : SheafOfModules.{u} 𝒪) [ℱ.IsFinitePresentation] :
    PreservesFilteredColimits (coyoneda.obj (op ℱ)) := sorry

/-- Lemma 18.27.12: under the quasi-compact test-set hypothesis, a finitely presented
`\mathcal O`-module is finitely presentable in the categorical sense. -/
theorem isFinitelyPresentable_of_isFinitePresentation
    (hJ : ∃ S : Set (Sheaf J (Type u)),
      CategoryTheory.GrothendieckTopology.IsQuasiCompactTestSet J S)
    (ℱ : SheafOfModules.{u} 𝒪) [ℱ.IsFinitePresentation] :
    IsFinitelyPresentable.{u} ℱ := by
  exact
    (isFinitelyPresentable_iff_preservesFilteredColimits :
      IsFinitelyPresentable.{u} ℱ ↔ PreservesFilteredColimits (coyoneda.obj (op ℱ))).2
      (preservesFilteredColimits_coyoneda_of_isFinitePresentation hJ ℱ)

/-- Companion to Lemma 18.27.12: for a fixed filtered diagram `\mathcal G_\lambda`, the canonical
comparison map
`colim_\lambda Hom_\mathcal O(\mathcal F, \mathcal G_\lambda) →
Hom_\mathcal O(\mathcal F, colim_\lambda \mathcal G_\lambda)` is bijective. -/
theorem homColimitComparison_bijective_of_isFinitePresentation
    (hJ : ∃ S : Set (Sheaf J (Type u)),
      CategoryTheory.GrothendieckTopology.IsQuasiCompactTestSet J S)
    (ℱ : SheafOfModules.{u} 𝒪) [ℱ.IsFinitePresentation]
    (𝒢 : Λ ⥤ SheafOfModules.{u} 𝒪)
    [HasColimit 𝒢] [HasColimit (𝒢 ⋙ coyoneda.obj (op ℱ))] :
    Function.Bijective (colimit.post 𝒢 (coyoneda.obj (op ℱ))) := sorry

end SheafOfModules
