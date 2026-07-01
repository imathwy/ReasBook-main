import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import stacks_project.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory Opposite
open CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Limits

noncomputable section

universe u v

/-- The underlying `RingCat`-valued presheaf of a presheaf of commutative rings. -/
abbrev ringPresheaf {C : Type u} [Category.{v} C]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) : Cᵒᵖ ⥤ RingCat.{max u v} :=
  𝒪 ⋙ forget₂ CommRingCat RingCat

section PresheafFlat

variable {C : Type u} [Category.{v} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/- Domain-style sampling for Definition 18.28.1:
- primary domain: flatness of presheaves and sheaves of modules, expressed by exactness of the
  tensor-right endofunctor;
- sampled owner declarations:
  `tensorRight`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.IsFlat` from `Lemma_18_28_4`,
  `exactFunctor`;
- best owner abstraction: on the presheaf side, flatness should be owned by
  `PresheafOfModules.IsFlat`, mirroring the chapter's sheaf-side owner and taking exactness of
  `tensorRight ℱ` as primitive data;
- primitive data: a presheaf module `ℱ : PresheafOfModules (ringPresheaf 𝒪)`;
- derived API: flatness of ring morphisms and the unit instance.

Source/core/bridge triage:
- `source-facing`: Definition 18.28.1 defines flatness of presheaves of modules and flatness of
  morphisms of presheaves of rings;
- `core/canonical`: `PresheafOfModules (ringPresheaf 𝒪)`,
  `tensorRight ℱ`, and `exactFunctor`;
- `bridge/view`: the ring-map predicate `PresheafOfModules.IsFlatHom`, obtained by restricting
  scalars from the canonical presheaf-module owner.

The presheaf-side API should therefore be organized around `PresheafOfModules.IsFlat`, not a
parallel root-level wrapper. -/

namespace PresheafOfModules

/-- Definition 18.28.1 (1): a presheaf of `\mathcal O`-modules is flat when tensoring with it on
`PMod(\mathcal O)` is an exact endofunctor. -/
class IsFlat
    {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) : Prop where
  /-- Tensoring on the right by `ℱ` is exact on presheaves of `𝒪`-modules. -/
  exact_tensor :
    exactFunctor
      (PresheafOfModules (ringPresheaf 𝒪))
      (PresheafOfModules (ringPresheaf 𝒪))
      (tensorRight ℱ)

/-- Definition 18.28.1 (2): a morphism of presheaves of rings is flat when the target, viewed by
restriction of scalars as a presheaf of modules over the source, is flat. -/
def IsFlatHom
    {𝒪 𝒪' : Cᵒᵖ ⥤ CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') : Prop :=
  IsFlat
    ((PresheafOfModules.restrictScalars
        (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).obj
      (PresheafOfModules.unit (ringPresheaf 𝒪')))

-- Proof sketch: this is the defining restriction-of-scalars reformulation of `IsFlatHom`.
/-- Unfolding flatness of a morphism of presheaves of rings says that the target is flat as a
presheaf of modules over the source. -/
theorem isFlatHom_iff
    {𝒪 𝒪' : Cᵒᵖ ⥤ CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    IsFlatHom α ↔
      IsFlat
        ((PresheafOfModules.restrictScalars
            (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).obj
          (PresheafOfModules.unit (ringPresheaf 𝒪'))) := by
  rfl

-- Proof sketch: the structure presheaf is the tensor unit, so tensoring with it is naturally
-- isomorphic to the identity endofunctor of `PMod(𝒪)`, which is exact.
/-- The structure presheaf, viewed as a module over itself, is flat. -/
theorem unit_isFlat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    IsFlat (PresheafOfModules.unit (ringPresheaf 𝒪)) := sorry

/-- The structure presheaf carries its canonical flatness instance. -/
instance (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    IsFlat (PresheafOfModules.unit (ringPresheaf 𝒪)) :=
  unit_isFlat 𝒪

end PresheafOfModules

end PresheafFlat

/-- A sheaf of commutative rings viewed as a sheaf with values in `RingCat`. -/
abbrev ringSheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (𝒪 : Sheaf J CommRingCat.{max u v}) : Sheaf J RingCat.{max u v} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪

section PresheafSheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]

namespace PresheafOfModules

/-- The commutative-ring-valued sheafification of a presheaf of commutative rings. -/
abbrev commRingSheafification (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    Sheaf J CommRingCat.{max u v} :=
  (presheafToSheaf J CommRingCat.{max u v}).obj 𝒪

/-- The canonical ring map from `𝒪` to the underlying ring presheaf of `𝒪^#`. -/
abbrev sheafificationRingMap (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    ringPresheaf 𝒪 ⟶ (ringSheaf J (commRingSheafification J 𝒪)).obj :=
  show ringPresheaf 𝒪 ⟶ (ringSheaf J (commRingSheafification J 𝒪)).obj from
    Functor.whiskerRight
      (show 𝒪 ⟶ (commRingSheafification J 𝒪).obj from CategoryTheory.toSheafify J 𝒪)
      (forget₂ CommRingCat RingCat)

-- Proof sketch: the sheafification unit `𝒪 ⟶ 𝒪^#` is locally bijective for commutative rings, and
-- forgetting from commutative rings to rings preserves the local injectivity part.
/-- The canonical map from a commutative-ring presheaf to the underlying ring presheaf of its
sheafification is locally injective. -/
instance sheafificationRingMap_isLocallyInjective
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    Presheaf.IsLocallyInjective J (sheafificationRingMap J 𝒪) := sorry

-- Proof sketch: the sheafification unit `𝒪 ⟶ 𝒪^#` is locally bijective for commutative rings, and
-- forgetting from commutative rings to rings preserves the local surjectivity part.
/-- The canonical map from a commutative-ring presheaf to the underlying ring presheaf of its
sheafification is locally surjective. -/
instance sheafificationRingMap_isLocallySurjective
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    Presheaf.IsLocallySurjective J (sheafificationRingMap J 𝒪) := sorry

/-- The sheafification functor on presheaves of `\mathcal O`-modules along the canonical map
`\mathcal O \to \mathcal O^\#`. -/
abbrev moduleSheafification
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] :
    PresheafOfModules (ringPresheaf 𝒪) ⥤
      SheafOfModules (ringSheaf J (commRingSheafification J 𝒪)) :=
  PresheafOfModules.sheafification (sheafificationRingMap J 𝒪)

end PresheafOfModules

end PresheafSheafification

section SheafFlat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The sheaf tensor product of two sheaves of modules over a commutative sheaf of rings, defined
by sheafifying their presheaf tensor product. -/
noncomputable abbrev moduleTensor {𝒪 : Sheaf J CommRingCat.{max u v}}
    (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪) :
    ringedSiteModuleCategory J 𝒪 :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj)).obj
    (show PresheafOfModules (ringSheaf J 𝒪).obj from
      PresheafOfModules.Monoidal.tensorObj
        (show PresheafOfModules (ringSheaf J 𝒪).obj from ℱ.val)
        (show PresheafOfModules (ringSheaf J 𝒪).obj from 𝒢.val))

namespace SheafOfModules.RingedSite

/- Textbook notation for the tensor product of sheaves of `\mathcal O`-modules on a ringed
site. -/
scoped infixr:70 " ⊗ " => _root_.moduleTensor

end SheafOfModules.RingedSite

open scoped SheafOfModules.RingedSite

/-- The sheafification functor on presheaves of modules over a commutative sheaf of rings. -/
noncomputable def moduleSheafification (𝒪 : Sheaf J CommRingCat.{max u v}) :
    PresheafOfModules (ringSheaf J 𝒪).obj ⥤ ringedSiteModuleCategory J 𝒪 :=
  PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj)

/-- The morphism on sheaf tensor products induced by morphisms in each tensor factor. -/
noncomputable abbrev moduleTensorMap {𝒪 : Sheaf J CommRingCat.{max u v}}
    {ℱ₁ ℱ₂ 𝒢₁ 𝒢₂ : ringedSiteModuleCategory J 𝒪}
    (α : ℱ₁ ⟶ ℱ₂) (β : 𝒢₁ ⟶ 𝒢₂) :
    ℱ₁ ⊗ 𝒢₁ ⟶ ℱ₂ ⊗ 𝒢₂ :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj)).map
    (PresheafOfModules.Monoidal.tensorHom α.val β.val)

private abbrev moduleTensorTensorObjModel {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (SheafOfModules (ringSheaf J 𝒪))]
    (ℱ 𝒢 : SheafOfModules (ringSheaf J 𝒪)) :
    SheafOfModules (ringSheaf J 𝒪) :=
  ((SheafOfModules.forget (ringSheaf J 𝒪) ⋙
      PresheafOfModules.restrictScalars (𝟙 (ringSheaf J 𝒪).obj)) ⋙
    PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj)).obj (_root_.moduleTensor ℱ 𝒢)

private theorem moduleTensorTensorObjModel_eq_tensorObj
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (SheafOfModules (ringSheaf J 𝒪))]
    (ℱ 𝒢 : SheafOfModules (ringSheaf J 𝒪)) :
    moduleTensorTensorObjModel (J := J) ℱ 𝒢 =
      (MonoidalCategoryStruct.tensorObj ℱ 𝒢 : SheafOfModules (ringSheaf J 𝒪)) := by
  sorry

/-- The canonical bridge from the source-facing sheaf tensor product `moduleTensor` to the ambient
monoidal tensor object on sheaves of modules. -/
noncomputable abbrev moduleTensorIsoTensorObj
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (SheafOfModules (ringSheaf J 𝒪))]
    (ℱ 𝒢 : SheafOfModules (ringSheaf J 𝒪)) :
    _root_.moduleTensor ℱ 𝒢 ≅
      (MonoidalCategoryStruct.tensorObj ℱ 𝒢 : SheafOfModules (ringSheaf J 𝒪)) :=
  (asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J 𝒪).obj)).counit.app
      (_root_.moduleTensor ℱ 𝒢))).symm ≪≫
    eqToIso (moduleTensorTensorObjModel_eq_tensorObj (J := J) ℱ 𝒢)

-- Proof sketch: this is the identity law for `moduleTensorMap` with the fixed right factor.
/-- Tensoring sheaf morphisms on the right by a fixed module sends identities to identities. -/
theorem sheafModuleTensorRightFunctor_map_id {𝒪 : Sheaf J CommRingCat.{max u v}}
    (ℱ 𝒢 : ringedSiteModuleCategory J 𝒪) :
    moduleTensorMap (𝟙 ℱ) (𝟙 𝒢) =
      𝟙 (ℱ ⊗ 𝒢) := sorry

-- Proof sketch: this is the composition law for `moduleTensorMap` with the fixed right factor.
/-- Tensoring sheaf morphisms on the right by a fixed module sends compositions to
compositions. -/
theorem sheafModuleTensorRightFunctor_map_comp {𝒪 : Sheaf J CommRingCat.{max u v}}
    (𝒢 : ringedSiteModuleCategory J 𝒪)
    {ℱ₁ ℱ₂ ℱ₃ : ringedSiteModuleCategory J 𝒪}
    (φ : ℱ₁ ⟶ ℱ₂) (ψ : ℱ₂ ⟶ ℱ₃) :
    moduleTensorMap (φ ≫ ψ) (𝟙 𝒢) =
      moduleTensorMap φ (𝟙 𝒢) ≫
        moduleTensorMap ψ (𝟙 𝒢) := sorry

/-- The endofunctor on `Mod(𝒪)` given by tensoring on the right by a fixed sheaf of
`𝒪`-modules. -/
noncomputable def sheafModuleTensorRightFunctor {𝒪 : Sheaf J CommRingCat.{max u v}}
    (𝒢 : ringedSiteModuleCategory J 𝒪) :
    ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪 where
  obj ℱ := ℱ ⊗ 𝒢
  map φ := moduleTensorMap φ (𝟙 𝒢)
  map_id ℱ := sheafModuleTensorRightFunctor_map_id ℱ 𝒢
  map_comp φ ψ := sheafModuleTensorRightFunctor_map_comp 𝒢 φ ψ

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Definition 18.28.1 (3): for a site and a sheaf of rings `\mathcal O`, a sheaf of
`\mathcal O`-modules is flat when tensoring with it on `Mod(\mathcal O)` is an exact
endofunctor. -/
class IsFlat
    (𝒪 : Sheaf J CommRingCat.{max u v})
    (ℱ : ringedSiteModuleCategory J 𝒪) : Prop where
  /-- Tensoring on the right by `ℱ` is exact on sheaves of `𝒪`-modules. -/
  exact_tensor : exactFunctor _ _ (sheafModuleTensorRightFunctor ℱ)

variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- Definition 18.28.1 (4): a morphism of sheaves of rings on a site is flat when the target,
viewed by restriction of scalars as a sheaf of modules over the source, is flat. -/
def IsFlatHom
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') : Prop :=
  IsFlat 𝒪
    ((SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
      (SheafOfModules.unit (ringSheaf J 𝒪')))

/-- Unfolding flatness of a morphism of sheaves of rings says that the target is flat as a sheaf
of modules over the source. -/
theorem isFlatHom_iff
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    IsFlatHom α ↔
      IsFlat 𝒪
        ((SheafOfModules.restrictScalars
            ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
          (SheafOfModules.unit (ringSheaf J 𝒪'))) := by
  rfl

-- Proof sketch: the structure sheaf is the tensor unit, so tensoring with it is naturally
-- isomorphic to the identity endofunctor of `Mod(𝒪)`, which is exact.
/-- The structure sheaf, viewed as a module over itself, is flat. -/
theorem unit_isFlat
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    IsFlat 𝒪 (SheafOfModules.unit (ringSheaf J 𝒪) : ringedSiteModuleCategory J 𝒪) := sorry

/-- The structure sheaf carries its canonical flatness instance. -/
instance (𝒪 : Sheaf J CommRingCat.{max u v}) :
    IsFlat 𝒪 (SheafOfModules.unit (ringSheaf J 𝒪) : ringedSiteModuleCategory J 𝒪) :=
  unit_isFlat 𝒪

end SheafOfModules.RingedSite

end SheafFlat
