import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Monoidal

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_17_22_1 (from Chap17) -/
open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

/-
Domain-style sampling for Lemma 17.22.1:
- primary domain: tensor/internal-Hom calculus in braided monoidal closed categories of
  `\mathcal O_X`-modules;
- inspected owner declarations:
  notation `A ⟶[C] B`,
  `CategoryTheory.MonoidalClosed.internalHomAdjunction₂`,
  `MonoidalCategory.tensorLeftTensor`,
  `CategoryTheory.ihom.adjunction`,
  `CategoryTheory.Adjunction.rightAdjointUniq`,
- owner abstraction: the canonical internal-Hom owner
  `MonoidalClosed.internalHomAdjunction₂`, whose objectwise surface is the notation
  `A ⟶[C] B`; the braided tensor-left comparison is only a bridge from the Stacks tensor order
  to that owner;
- primitive data: the ambient monoidal-closed structure and the modules `ℱ`, `𝒢`, `ℋ`;
- derived API: the textbook objectwise isomorphism
  `((ℱ ⊗ 𝒢) ⟶[ModX] ℋ) ≅ (ℱ ⟶[ModX] (𝒢 ⟶[ModX] ℋ))` and its companion naturality lemmas.

Source/core/bridge triage:
- `source-facing`: the textbook objectwise isomorphism
  `internalHomTensorIso ℱ 𝒢 ℋ`, together with its functoriality in `ℱ`, `𝒢`, and `ℋ`;
- `core/canonical`: notation `A ⟶[C] B` and `MonoidalClosed.internalHomAdjunction₂`;
- `bridge/view`: the braided tensor-left comparison built from `tensorLeftTensor` and
  `rightAdjointUniq`.

The public surface should therefore stay at the textbook object level and reuse the canonical
internal-Hom owner directly, while the functor-level right-adjoint-uniqueness comparison remains a
thin private bridge. -/
namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [BraidedCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
set_option quotPrecheck false in
local notation A " ⟶[ModX] " B:10 => ((ihom A).obj B)

private noncomputable def internalHomTensorNatIso
    (ℱ 𝒢 : ModX) :
    ihom (ℱ ⊗ 𝒢) ≅ ihom 𝒢 ⋙ ihom ℱ :=
  Adjunction.rightAdjointUniq
    (ihom.adjunction (ℱ ⊗ 𝒢))
    (((ihom.adjunction ℱ).comp (ihom.adjunction 𝒢)).ofNatIsoLeft
      (((MonoidalCategory.tensoringLeft (RingedSpace.Modules X)).mapIso (β_ ℱ 𝒢)) ≪≫
        MonoidalCategory.tensorLeftTensor 𝒢 ℱ).symm)

/-- Lemma 17.22.1: for `\mathcal O_X`-modules `ℱ`, `𝒢`, and `ℋ`, the internal Hom out of
`ℱ ⊗ 𝒢` is canonically isomorphic to the iterated internal Hom. On the theorem surface this is
attached directly to the canonical internal-Hom owner
`MonoidalClosed.internalHomAdjunction₂`. -/
noncomputable def internalHomTensorIso
    (ℱ 𝒢 ℋ : ModX) :
    ((ℱ ⊗ 𝒢) ⟶[ModX] ℋ) ≅ (ℱ ⟶[ModX] (𝒢 ⟶[ModX] ℋ)) :=
  (internalHomTensorNatIso ℱ 𝒢).app ℋ

private theorem internalHomTensorNatIso_natural_in_first_variable
    {ℱ ℱ' 𝒢 : ModX} (f : ℱ ⟶ ℱ') :
    MonoidalClosed.pre (f ⊗ₘ 𝟙 𝒢) ≫ (internalHomTensorNatIso ℱ 𝒢).hom =
      (internalHomTensorNatIso ℱ' 𝒢).hom ≫
        Functor.whiskerLeft (ihom 𝒢) (MonoidalClosed.pre f) := sorry

private theorem internalHomTensorNatIso_natural_in_second_variable
    {ℱ 𝒢 𝒢' : ModX} (g : 𝒢 ⟶ 𝒢') :
    MonoidalClosed.pre (𝟙 ℱ ⊗ₘ g) ≫ (internalHomTensorNatIso ℱ 𝒢).hom =
      (internalHomTensorNatIso ℱ 𝒢').hom ≫
        Functor.whiskerRight (MonoidalClosed.pre g) (ihom ℱ) := sorry

/-- Lemma 17.22.1 is contravariantly functorial in the first variable `ℱ`, objectwise at `ℋ`. -/
theorem internalHomTensorIso_natural_in_first_variable
    {ℱ ℱ' 𝒢 ℋ : ModX} (f : ℱ ⟶ ℱ') :
    (MonoidalClosed.pre (f ⊗ₘ 𝟙 𝒢)).app ℋ ≫
        (internalHomTensorIso ℱ 𝒢 ℋ).hom =
      (internalHomTensorIso ℱ' 𝒢 ℋ).hom ≫
        (MonoidalClosed.pre f).app (𝒢 ⟶[ModX] ℋ) := by
  simpa using
    NatTrans.congr_app (internalHomTensorNatIso_natural_in_first_variable f) ℋ

/-- Lemma 17.22.1 is contravariantly functorial in the second variable `𝒢`, objectwise at `ℋ`. -/
theorem internalHomTensorIso_natural_in_second_variable
    {ℱ 𝒢 𝒢' ℋ : ModX} (g : 𝒢 ⟶ 𝒢') :
    (MonoidalClosed.pre (𝟙 ℱ ⊗ₘ g)).app ℋ ≫
        (internalHomTensorIso ℱ 𝒢 ℋ).hom =
      (internalHomTensorIso ℱ 𝒢' ℋ).hom ≫
        (ihom ℱ).map ((MonoidalClosed.pre g).app ℋ) := by
  simpa using
    NatTrans.congr_app (internalHomTensorNatIso_natural_in_second_variable g) ℋ

/-- Lemma 17.22.1 is functorial in the third variable `ℋ`. -/
theorem internalHomTensorIso_natural_in_third_variable
    (ℱ 𝒢 : ModX) {ℋ ℋ' : ModX} (h : ℋ ⟶ ℋ') :
    (ihom (ℱ ⊗ 𝒢)).map h ≫ (internalHomTensorIso ℱ 𝒢 ℋ').hom =
      (internalHomTensorIso ℱ 𝒢 ℋ).hom ≫
        (ihom 𝒢 ⋙ ihom ℱ).map h :=
  (internalHomTensorNatIso ℱ 𝒢).hom.naturality h

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_22_2 (from Chap17) -/
open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.22.2:
- primary domain: left exactness of internal Hom for sheaves of modules on a ringed space;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `ShortComplex`,
  `ringedSiteModuleInternalHom_exact_in_source`,
  `ringedSiteModuleInternalHom_exact_in_target`;
- best owner abstraction:
  this item is not a new ringed-space owner; it is the opens-site specialization of the Chapter 18
  owner theorems for `ringedSiteModuleCategory`, with coefficient sheaf `X.sheaf`;
- primitive data:
  a short exact sequence `S : ShortComplex (RingedSpace.Modules X)` and a fixed module in the
  remaining internal-Hom variable;
- derived API:
  the two ringed-space exactness clauses obtained by specializing the generic ringed-site theorems.

Source/core/bridge triage:
- `source-facing`: the ringed-space wording of the two exactness statements for internal Hom;
- `core/canonical`: `ringedSiteModuleInternalHom_exact_in_source` and
  `ringedSiteModuleInternalHom_exact_in_target`;
- `bridge/view`: specialization along the opens Grothendieck topology
  `Opens.grothendieckTopology X` and the structure sheaf `X.sheaf`.

The previous local declarations duplicated the Chapter 18 owner theorems at the same mathematical
interface. This file should therefore be a direct recall/use bridge rather than maintain parallel
ringed-space theorem names. -/

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

/- Lemma 17.22.2 (1): for a short exact sequence
`0 ⟶ \mathcal F_2 ⟶ \mathcal F_1 ⟶ \mathcal F ⟶ 0` of `\mathcal O_X`-modules, the induced
sequence
`0 ⟶ \mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G) ⟶
\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F_1, \mathcal G) ⟶
\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F_2, \mathcal G)`
is exactly the opens-site specialization of the Chapter 18 owner theorem
`ringedSiteModuleInternalHom_exact_in_source`. -/
#check ringedSiteModuleInternalHom_exact_in_source (Opens.grothendieckTopology X) X.sheaf

/- Lemma 17.22.2 (2): for a short exact sequence
`0 ⟶ \mathcal G ⟶ \mathcal G_1 ⟶ \mathcal G_2 ⟶ 0` of `\mathcal O_X`-modules, the induced
sequence
`0 ⟶ \mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G) ⟶
\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G_1) ⟶
\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G_2)`
is exactly the opens-site specialization of the Chapter 18 owner theorem
`ringedSiteModuleInternalHom_exact_in_target`. -/
#check ringedSiteModuleInternalHom_exact_in_target (Opens.grothendieckTopology X) X.sheaf

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_22_3 (from Chap17) -/
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

/-! ### Lemma_17_22_4 (from Chap17) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.22.4:
- primary domain: internal Hom for sheaves of modules on a ringed space and its comparison with
  stalkwise linear maps;
- inspected owner declarations:
  notation `A ⟶[C] B`,
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `AlgebraicGeometry.RingedSpace.moduleStalkHom`,
  `AlgebraicGeometry.RingedSpace.tensorProductStalkIso`,
  `CategoryTheory.ihom.ev`,
  `CategoryTheory.MonoidalClosed.uncurry_id_eq_ev`;
- best owner abstraction:
  the source-facing comparison should be written on the theorem surface through the canonical
  internal-Hom owner notation `A ⟶[C] B`, with `RingedSpace.stalkModuleCat` supplying the stalk
  module owner and `ModuleCat` supplying the stalk internal Hom;
- primitive data:
  a ringed space `X`, sheaves `ℱ 𝒢 : (RingedSpace.Modules X)`, and a point `x : X`;
- derived API:
  the canonical comparison morphism from the stalk of `ℱ ⟶[ModX] 𝒢` to the internal Hom of the
  stalk modules, together with its finite-type and finite-presentation consequences.

Source/core/bridge triage:
- `source-facing`: the canonical comparison
  `(\mathcal H\!om_{\mathcal O_X}(\mathcal F,\mathcal G))_x →
    \mathcal H\!om_{\mathcal O_{X,x}}(\mathcal F_x,\mathcal G_x)`;
- `core/canonical`: `(RingedSpace.Modules X)`, `RingedSpace.stalkModuleCat`, `tensorProductStalkIso`, and
  `ihom`;
- `bridge/view`: the induced stalk morphism of the evaluation map, curried after transporting
  across the tensor-stalk isomorphism.
-/

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
local notation "StalkMod" x => ModuleCat (X.presheaf.stalk x)
set_option quotPrecheck false in
local notation A " ⟶[ModX] " B:10 => ((ihom A).obj B)
set_option quotPrecheck false in
local notation A " ⟶[StalkMod " x "] " B:10 => ((@ihom (StalkMod x) _ _ A _).obj B)

private abbrev tensorModel (ℱ 𝒢 : ModX) : ModX :=
  ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)) ⋙
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (moduleTensor ℱ 𝒢)

private theorem tensorModel_eq_tensorObj
    (ℱ 𝒢 : ModX) :
    tensorModel ℱ 𝒢 = (ℱ ⊗ 𝒢 : ModX) := by
  sorry

private noncomputable abbrev moduleTensorIsoTensorObj
    (ℱ 𝒢 : ModX) :
    moduleTensor ℱ 𝒢 ≅ (ℱ ⊗ 𝒢 : ModX) :=
  (asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
      (moduleTensor ℱ 𝒢))).symm ≪≫
    eqToIso (tensorModel_eq_tensorObj ℱ 𝒢)

/-- The canonical comparison from the stalk of the sheaf internal Hom to the internal Hom of the
stalk modules. -/
noncomputable def internalHomStalkComparison
    (ℱ 𝒢 : ModX) (x : X) :
    stalkModuleCat (ℱ ⟶[ModX] 𝒢) x ⟶
      ((stalkModuleCat ℱ x) ⟶[StalkMod x] (stalkModuleCat 𝒢 x)) :=
  MonoidalClosed.curry
    ((tensorProductStalkIso ℱ (ℱ ⟶[ModX] 𝒢) x).inv ≫
      moduleStalkHom x
        ((moduleTensorIsoTensorObj ℱ (ℱ ⟶[ModX] 𝒢)).hom ≫
          (ihom.ev ℱ).app 𝒢))

/-- Uncurrying `internalHomStalkComparison` recovers the stalkwise evaluation morphism transported
across the stalk tensor-product isomorphism. -/
theorem uncurry_internalHomStalkComparison
    (ℱ 𝒢 : ModX) (x : X) :
    MonoidalClosed.uncurry (internalHomStalkComparison ℱ 𝒢 x) =
      (tensorProductStalkIso ℱ (ℱ ⟶[ModX] 𝒢) x).inv ≫
        moduleStalkHom x
          ((moduleTensorIsoTensorObj ℱ (ℱ ⟶[ModX] 𝒢)).hom ≫
            (ihom.ev ℱ).app 𝒢) := by
  exact MonoidalClosed.uncurry_curry _

-- Proof sketch: represent a germ of a local section of the internal-Hom sheaf by a morphism on
-- some neighbourhood of `x` and evaluate it on stalk germs using
-- `internalHomStalkComparison`. If `ℱ` is of finite type, a local morphism with zero stalk map
-- kills finitely many local generators after shrinking, hence vanishes near `x`.
/-- Lemma 17.22.4, injective clause: if `\mathcal F` is of finite type, then the canonical
comparison
`(\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G))_x \to
\mathcal H\!\mathit{om}_{\mathcal O_{X, x}}(\mathcal F_x, \mathcal G_x)`
is injective. -/
theorem internalHomStalkComparison_injective_of_isFiniteType
    (ℱ 𝒢 : ModX) (x : X) [ℱ.IsFiniteType] :
    Function.Injective (internalHomStalkComparison ℱ 𝒢 x) := sorry

-- Proof sketch: choose a finite presentation of `ℱ` locally, apply Lemma `17.22.2` to the
-- induced left exact sequence of internal-Hom sheaves, and compare with the corresponding exact
-- sequence of stalk `Hom` modules. The finite-type injectivity clause handles the left term.
/-- Lemma 17.22.4, isomorphism clause: if `\mathcal F` is finitely presented, then the canonical
comparison
`(\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G))_x \to
\mathcal H\!\mathit{om}_{\mathcal O_{X, x}}(\mathcal F_x, \mathcal G_x)`
is an isomorphism. -/
theorem internalHomStalkComparison_isIso_of_isFinitePresentation
    (ℱ 𝒢 : ModX) (x : X) [ℱ.IsFinitePresentation] :
    IsIso (internalHomStalkComparison ℱ 𝒢 x) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_22_5 (from Chap17) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace.Hom

/- Domain-style sampling for Lemma 17.22.5:
- primary domain: pullback of internal-Hom sheaves along a morphism of ringed spaces;
- inspected owner declarations:
  `RingedSite.ofCommRingSheaf`,
  `RingedSite.Hom.pullbackInternalHomComparison`,
  `RingedSite.Hom.isIso_pullbackInternalHomComparison`,
  `AlgebraicGeometry.RingedSpace.Hom.IsFlat.pullback_exact`;
- best owner abstraction:
  the source-facing ringed-space comparison is a thin specialization of the ringed-site owner
  `RingedSite.Hom.pullbackInternalHomComparison`; the chapter-level public surface should remain
  the pullback owner `f^*` and the flatness owner `RingedSpace.Hom.IsFlat`;
- primitive data:
  a morphism `f : X ⟶ Y` and sheaves `ℱ 𝒢 : Y.Modules`;
- derived API:
  the ringed-space bridge `pullbackInternalHomComparison`, together with its flat/finitely
  presented isomorphism criterion obtained from the ringed-site owner theorem.

Source/core/bridge triage:
- `source-facing`: `pullbackInternalHomComparison`;
- `core/canonical`: `RingedSite.Hom.pullbackInternalHomComparison`,
  `RingedSite.Hom.isIso_pullbackInternalHomComparison`, `RingedSpace.Hom.IsFlat`, and the
  pullback owner `f^*`;
- `bridge/view`: the ringed-space specialization along the site of opens and
  `RingedSpace.Hom.toRingCatSheafHom`.
-/

variable {X Y : RingedSpace} (f : X ⟶ Y)
variable [MonoidalCategory Y.Modules] [MonoidalClosed Y.Modules]
variable [MonoidalCategory X.Modules] [MonoidalClosed X.Modules]
variable [(f^*).Monoidal]

private abbrev opensRingedSite (X : RingedSpace) : RingedSite :=
  RingedSite.ofCommRingSheaf (Opens.grothendieckTopology X) X.sheaf

private noncomputable abbrev opensRingedSiteHom (f : X ⟶ Y) :
    opensRingedSite X ⟶ opensRingedSite Y where
  base := Opens.map f.hom.base
  structureSheafMap := RingedSpace.Hom.toRingCatSheafHom f

private instance instIsFlatOpensRingedSiteHom [RingedSpace.Hom.IsFlat f] :
    RingedSite.Hom.IsFlat (opensRingedSiteHom f) where
  pullback_exact := by
    simpa [RingedSite.Hom.modulePullback, RingedSpace.Hom.pullback, opensRingedSiteHom] using
      (IsFlat.pullback_exact f)

/-- The canonical pullback-to-internal-Hom comparison morphism associated to a morphism of
ringed spaces. This is the ringed-space specialization of the ringed-site owner
`RingedSite.Hom.pullbackInternalHomComparison`. -/
noncomputable abbrev pullbackInternalHomComparison (ℱ 𝒢 : Y.Modules) :
    (f^*).obj ((ihom ℱ).obj 𝒢) ⟶
      (ihom ((f^*).obj ℱ)).obj ((f^*).obj 𝒢) :=
  RingedSite.Hom.pullbackInternalHomComparison (opensRingedSiteHom f) ℱ 𝒢

-- Proof sketch: transport the ringed-space morphism `f` to the ringed site of opens with its
-- structure sheaf. The Chapter 17 flatness bridge gives exactness of `f^*`, hence a
-- `RingedSite.Hom.IsFlat` instance on that ringed-site morphism. The result is then exactly the
-- Chapter 18 owner theorem specialized back to ringed spaces.
/-- Lemma 17.22.5: for a flat morphism of ringed spaces `f : (X, \mathcal O_X) ⟶
`(Y, \mathcal O_Y)` and an `\mathcal O_Y`-module `\mathcal F` of finite presentation, the
canonical map
`f^*\mathcal H\!\mathit{om}_{\mathcal O_Y}(\mathcal F, \mathcal G) ⟶
\mathcal H\!\mathit{om}_{\mathcal O_X}(f^*\mathcal F, f^*\mathcal G)`
is an isomorphism. -/
theorem isIso_pullbackInternalHomComparison
    (ℱ 𝒢 : Y.Modules) [ℱ.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    IsIso (pullbackInternalHomComparison f ℱ 𝒢) := by
  let X' : RingedSite := opensRingedSite X
  let Y' : RingedSite := opensRingedSite Y
  let g : X' ⟶ Y' := opensRingedSiteHom f
  let ℱ' : SheafOfModules Y'.structureSheaf := ℱ
  let 𝒢' : SheafOfModules Y'.structureSheaf := 𝒢
  have hg : IsIso (RingedSite.Hom.pullbackInternalHomComparison g ℱ' 𝒢') := by
    exact RingedSite.Hom.isIso_pullbackInternalHomComparison g ℱ' 𝒢'
  simpa [X', Y', g, ℱ', 𝒢', pullbackInternalHomComparison] using hg

end AlgebraicGeometry.RingedSpace.Hom

/-! ### Lemma_17_22_6 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

universe u

/- Domain-style sampling for Lemma 17.22.6:
- primary domain: internal Hom and coherence for sheaves of modules on a ringed space;
- inspected owner declarations:
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.IsCoherent`,
  `AlgebraicGeometry.RingedSpace.internalHomStalkComparison_isIso_of_isFinitePresentation`,
  `CategoryTheory.Limits.kernel`;
- best owner abstraction:
  the ambient owner is `RingedSpace.Modules X`, with `IsCoherent` as the canonical public target
  property;
- primitive data:
  a finitely presented source `ℱ : RingedSpace.Modules X` and a coherent target
  `𝒢 : RingedSpace.Modules X`;
- derived API:
  the local finite-kernel presentation of `((ihom ℱ).obj 𝒢).over U` and the resulting coherence
  statement for `(ihom ℱ).obj 𝒢`.

Source/core/bridge triage:
- `source-facing`: the local kernel presentation by finite biproducts of copies of `𝒢`;
- `core/canonical`: the owner category `RingedSpace.Modules X`, the predicate `IsCoherent`, and
  categorical kernels;
- `bridge/view`: the coherence theorem deduced from the local presentation.
-/

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
set_option quotPrecheck false in
local notation A " ⟶[ModX] " B:10 => ((ihom A).obj B)

-- Proof sketch: around each point, choose a local finite presentation of `ℱ` by finite free
-- `\mathcal O_U`-modules. Applying internal Hom into `𝒢|_U` turns that local presentation into a
-- left exact sequence whose first term identifies `\mathcal H\!om_{\mathcal O_U}(ℱ|_U, 𝒢|_U)` as
-- the kernel of a morphism between finite biproducts of copies of `𝒢|_U`.
/-- Lemma 17.22.6: if `\mathcal F` is finitely presented, then the internal-Hom sheaf
`\mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G)` is locally the kernel of a map
between finite direct sums of copies of `\mathcal G`, written here via the equivalent finite
biproduct presentation `∏ᶜ`. -/
theorem moduleInternalHom_locally_isKernel_of_finiteBiproductMap
    (ℱ 𝒢 : ModX) (x : X) [ℱ.IsFinitePresentation] :
    ∃ (U : Opens X) (_ : x ∈ U) (m n : ℕ)
      (φ : (∏ᶜ fun _ : Fin m ↦ 𝒢.over U) ⟶ (∏ᶜ fun _ : Fin n ↦ 𝒢.over U)),
      Nonempty ((ℱ ⟶[ModX] 𝒢).over U ≅ kernel φ) := sorry

-- Proof sketch: apply the local kernel presentation above. Finite biproducts of a coherent sheaf
-- are coherent, and Lemma `17.12.4` shows that kernels of morphisms between coherent sheaves are
-- coherent; coherence is local on the base, so the local kernel presentations glue.
/-- For a finitely presented source and coherent target, the internal-Hom sheaf is coherent. -/
theorem moduleInternalHom_isCoherent_of_isFinitePresentation
    (ℱ 𝒢 : ModX) [ℱ.IsFinitePresentation] [𝒢.IsCoherent] :
    (ℱ ⟶[ModX] 𝒢).IsCoherent := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_22_7 (from Chap17) -/
open CategoryTheory Limits MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u w

namespace SheafOfModules

/- Domain-style sampling for Lemma 17.22.7:
- primary domain: internal Hom in the closed monoidal category of sheaves of modules over a sheaf
  of rings, together with its interaction with filtered colimits;
- sampled owner declarations:
  `colimit.post`,
  `ihom`,
  `SheafOfModules.IsFinitePresentation`;
- best owner abstraction: the canonical comparison morphism is the generic categorical owner
  `colimit.post`, specialized here to the right adjoint `ihom ℱ`;
- primitive data: a ring-valued sheaf `𝒪`, a module sheaf `ℱ`, and a diagram `𝒢`;
- derived API: the specialized `colimit.post 𝒢 (ihom ℱ)` morphism and the finitely presented
  isomorphism theorem.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization in `AlgebraicGeometry.RingedSpace`;
- `core/canonical`: the owner-level declarations below in `SheafOfModules`;
- `bridge/view`: specialization along `𝒪 = (RingedSpace.ringCatSheaf X)`. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J RingCat.{u}}
variable {Λ : Type w} [SmallCategory Λ]
variable [MonoidalCategory (SheafOfModules 𝒪)] [MonoidalClosed (SheafOfModules 𝒪)]

-- Proof sketch: finite presentation is local on the ringed site, so after restricting to a cover
-- one may choose a finite free presentation of `ℱ`. Internal Hom from such a presentation is the
-- kernel of a morphism between finite direct sums, and filtered colimits commute with those finite
-- sums and preserve exactness, forcing the canonical comparison morphism to be an isomorphism.
/-- If `ℱ` is a finitely presented `\mathcal O`-module and `𝒢` is a filtered diagram of
`\mathcal O`-modules, then the canonical morphism
`colim_λ ℋom_𝒪(ℱ, 𝒢_λ) ⟶ ℋom_𝒪(ℱ, colim_λ 𝒢_λ)` is an isomorphism. -/
theorem isIso_internalHomColimitComparison_of_isFinitePresentation
    [IsFiltered Λ]
    (ℱ : SheafOfModules 𝒪) [ℱ.IsFinitePresentation]
    (𝒢 : Λ ⥤ SheafOfModules 𝒪)
    [HasColimit 𝒢] [HasColimit (𝒢 ⋙ ihom ℱ)] :
    IsIso (colimit.post 𝒢 (ihom ℱ)) := sorry

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {Λ : Type w} [SmallCategory Λ] [IsFiltered Λ]
    [MonoidalCategory (RingedSpace.Modules X)] [MonoidalClosed (RingedSpace.Modules X)]
variable (ℱ : RingedSpace.Modules X) [ℱ.IsFinitePresentation]
variable (𝒢 : Λ ⥤ RingedSpace.Modules X)
  [HasColimit 𝒢] [HasColimit (𝒢 ⋙ ihom ℱ)]

/- Lemma 17.22.7, source-facing bridge/view specialization: for a ringed space `X`, the
comparison morphism
`colim_\lambda \mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G_\lambda) ⟶
\mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F, colim_\lambda \mathcal G_\lambda)`
is covered exactly by
`SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation`
on `(RingedSpace.Modules X)`. -/
#check (SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation ℱ 𝒢 :
  IsIso (colimit.post 𝒢 (ihom ℱ)))

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_22_8 (from Chap17) -/
open CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry

noncomputable section

universe u w

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.22.8:
- primary domain: filtered colimits of represented Hom functors on the owner category
  `(RingedSpace.Modules X)`;
- sampled owner declarations:
  `colimit.post`,
  `coyoneda.obj`,
  `SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation`,
  `bijective_sheafColimitSectionComparison_of_cofinalFiniteQuasiCompactOverlapCoverings`;
- best owner abstraction: the source-facing theorem should be stated on `(RingedSpace.Modules X)`,
  with canonical comparison map `colimit.post ℱ (coyoneda.obj (op 𝒢))`;
- primitive data: a ringed space `X`, a finitely presented module `𝒢 : RingedSpace.Modules X`,
  and a filtered diagram `ℱ : Λ ⥤ RingedSpace.Modules X`;
- derived API: the internal-Hom comparison from Lemma `17.22.7` and the top-open sections
  comparison from Lemma `6.29.1`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma on `colim Hom_X(𝒢, ℱ_λ) → Hom_X(𝒢, colim ℱ_λ)`;
- `core/canonical`: `(RingedSpace.Modules X)`, `coyoneda.obj (op 𝒢)`, and `colimit.post`;
- `bridge/view`: the internal-Hom comparison from Lemma `17.22.7` and the top-open sections
  comparison from Lemma `6.29.1`. -/

variable {X : RingedSpace.{u}} {Λ : Type w} [SmallCategory Λ] [IsFiltered Λ]
local notation "JX" => Opens.grothendieckTopology X
local notation "ModX" => RingedSpace.Modules X

-- Proof sketch: identify `Hom_X(\mathcal G, -)` with global sections of the internal-Hom sheaf,
-- apply Lemma `17.22.7` to replace the internal Hom into `colim_\lambda \mathcal F_\lambda` by the
-- filtered colimit of the internal-Hom sheaves, and then apply Lemma `6.29.1` on the top open of
-- `X` using the cofinal finite-cover hypothesis.
/-- Lemma 17.22.8: if the top open of a ringed space `X` has a cofinal system of finite open
covers with quasi-compact pairwise intersections, then for a finitely presented
`\mathcal O_X`-module `\mathcal G` and a filtered diagram `\mathcal F_\lambda` of
`\mathcal O_X`-modules, the canonical map
`colim_\lambda Hom_X(\mathcal G, \mathcal F_\lambda) \to
Hom_X(\mathcal G, colim_\lambda \mathcal F_\lambda)` is bijective. -/
theorem homColimitComparison_bijective_of_isFinitePresentation
    (hX : HasCofinalFiniteQuasiCompactOverlapCoverings JX (⊤ : Opens X))
    (𝒢 : ModX)
    [𝒢.IsFinitePresentation]
    (ℱ : Λ ⥤ ModX)
    [HasColimit ℱ]
    [HasColimit (ℱ ⋙ coyoneda.obj (op 𝒢))] :
    Function.Bijective (colimit.post ℱ (coyoneda.obj (op 𝒢))) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Remark_17_22_9 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

local notation "JX" => Opens.grothendieckTopology twoClosedPointsSpace

/- Domain-style sampling for Remark 17.22.9:
- primary domain: filtered-colimit comparison morphisms for global sections of abelian sheaves on a
  topological space;
- sampled owner abstractions:
  `twoClosedPointsSpace`,
  `tailPushforwardIntegerSheafFunctor`,
  `sheafSections`,
  `colimit.post`,
  `preservesColimit_of_isIso_post`,
  `tailPushforwardIntegerSheaf_exists_global_sections_colimit`,
  `tailPushforwardColimit_global_sections_comparison_isIso`;
- best owner abstraction: the explicit comparison morphism
  `colimit.post tailPushforwardIntegerSheafFunctor
    ((sheafSections JX AddCommGrpCat).obj (op ⊤))`;
- primitive data: the imported witness space `twoClosedPointsSpace` and filtered diagram
  `tailPushforwardIntegerSheafFunctor`;
- derived API: the class-level statement
  `PreservesColimit tailPushforwardIntegerSheafFunctor
    ((sheafSections JX AddCommGrpCat).obj (op ⊤))`
  and its negation, which are bridge consequences of the comparison-map failure;
- layer triage:
  `source-facing`: the explicit map
    `colim Γ(X, j_{n,*}\underline{Z}) → Γ(X, colim j_{n,*}\underline{Z})`;
  `core/canonical`: `colimit.post`;
  `bridge/view`: the explicit Chapter 6 witness
    `twoClosedPointsSpace`, `tailPushforwardIntegerSheafFunctor`, together with the derived
    `PreservesColimit` reformulation.
-/

-- Proof sketch: Example `6.29.2` identifies the colimit of the global sections of the system
-- `j_{n,*}\underline{\mathbf Z}` on a quasi-compact space with an object of sections `M`, while
-- the global sections of the colimit sheaf are `M ⊞ M`; hence global sections need not preserve a
-- filtered colimit on a quasi-compact space.
/-- The two-closed-points space from Example 6.29.2 is quasi-compact. -/
theorem isCompact_univ_twoClosedPointsSpace :
    IsCompact (Set.univ : Set twoClosedPointsSpace) := by
  sorry

/-- Remark 17.22.9: on the Chapter 6 two-closed-points space, the canonical comparison map
`colim Γ(X, j_{n,*}\underline{Z}) → Γ(X, colim j_{n,*}\underline{Z})` is not an isomorphism. -/
theorem twoClosedPoints_globalSections_colimitComparison_not_isIso :
    ¬ IsIso
      (colimit.post tailPushforwardIntegerSheafFunctor
        ((sheafSections JX AddCommGrpCat).obj (op ⊤))) := by
  sorry

/-- Remark 17.22.9: equivalently, the same comparison map of global sections is not bijective. -/
theorem twoClosedPoints_globalSections_colimitComparison_not_bijective :
    ¬ Function.Bijective
      (colimit.post tailPushforwardIntegerSheafFunctor
        ((sheafSections JX AddCommGrpCat).obj (op ⊤))) := by
  intro hbij
  exact twoClosedPoints_globalSections_colimitComparison_not_isIso
    ((ConcreteCategory.isIso_iff_bijective _).2 hbij)

/-- Remark 17.22.9: the failure of the canonical comparison map implies that the global-sections
functor does not preserve this filtered colimit. -/
theorem twoClosedPoints_globalSections_not_preserves_filteredColimit :
    ¬ PreservesColimit tailPushforwardIntegerSheafFunctor
      ((sheafSections JX AddCommGrpCat).obj (op ⊤)) := by
  intro hpres
  let _ : PreservesColimit tailPushforwardIntegerSheafFunctor
      ((sheafSections JX AddCommGrpCat).obj (op ⊤)) := hpres
  exact twoClosedPoints_globalSections_colimitComparison_not_isIso inferInstance

/-- Remark 17.22.9: Example 6.29.2 gives a quasi-compact space for which the canonical comparison
map from the colimit of global sections of a filtered system of sheaves of abelian groups to the
global sections of the colimit sheaf is not an isomorphism. Thus some hypothesis beyond
quasi-compactness of `X` is necessary in Lemma 17.22.8. -/
theorem quasiCompact_does_not_force_globalSections_colimitComparison_isIso :
    ∃ X : TopCat.{0}, IsCompact (Set.univ : Set X) ∧
      ∃ 𝓕 : ℕ ⥤ X.Sheaf AddCommGrpCat.{0},
        ¬ IsIso
          (colimit.post 𝓕
            ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op ⊤))) := by
  refine ⟨twoClosedPointsSpace, isCompact_univ_twoClosedPointsSpace, tailPushforwardIntegerSheafFunctor,
    ?_⟩
  simpa using twoClosedPoints_globalSections_colimitComparison_not_isIso

/-- Remark 17.22.9: in particular, quasi-compactness does not force the global-sections functor to
preserve filtered colimits. -/
theorem quasiCompact_does_not_force_globalSections_preserve_filteredColimits :
    ∃ X : TopCat.{0}, IsCompact (Set.univ : Set X) ∧
      ∃ 𝓕 : ℕ ⥤ X.Sheaf AddCommGrpCat.{0},
        ¬ PreservesColimit 𝓕
          ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op ⊤)) := by
  refine ⟨twoClosedPointsSpace, isCompact_univ_twoClosedPointsSpace, tailPushforwardIntegerSheafFunctor,
    ?_⟩
  simpa using twoClosedPoints_globalSections_not_preserves_filteredColimit
