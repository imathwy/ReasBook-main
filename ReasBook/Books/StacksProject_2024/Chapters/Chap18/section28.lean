import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_28_1 (from Chap18) -/
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

/-! ### Lemma_18_28_2 (from Chap18) -/
open CategoryTheory MonoidalCategory Opposite Limits

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

-- Proof sketch: evaluate `tensorLeft ℱ` at each object `U`. The resulting functor on
-- `ModuleCat (𝒪.obj (op U))` is tensoring with the flat module `ℱ.obj (op U)`, so it preserves
-- finite limits by `Module.Flat.iff_preservesFiniteLimits_tensorLeft`. Since tensoring with `ℱ`
-- preserves all colimits by Lemma `18.27.7`, these objectwise left-exactness statements assemble
-- into the exact tensor-functor owner `PresheafOfModules.IsFlat`.
/-- Lemma 18.28.2: if each section module `\mathcal F(U)` is flat over `\mathcal O(U)`, then the
presheaf `\mathcal F` is flat. -/
theorem isFlat_of_flat_obj
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hflat : ∀ U : C, Module.Flat (𝒪.obj (op U)) (ℱ.obj (op U))) :
    IsFlat ℱ := sorry

end PresheafOfModules

/-! ### Lemma_18_28_3 (from Chap18) -/
open CategoryTheory Opposite MonoidalCategory Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

-- Proof sketch: flatness of `ℱ` means that tensoring with `ℱ` is an exact endofunctor on
-- presheaves of modules. Module sheafification is exact, and the tensor-sheafification
-- comparison identifies tensoring with `ℱ^#` over `𝒪^#` with sheafifying tensoring with `ℱ`;
-- therefore the sheafification `ℱ^#` is flat over the sheafified structure sheaf `𝒪^#`.
/-- Lemma 18.28.3: if a presheaf of `\mathcal O`-modules `\mathcal F` on a site is flat, then its
sheafification `\mathcal F^\#` is a flat `\mathcal O^\#`-module in the chapter's canonical
sheaf-level flatness owner. -/
theorem sheafification_isFlat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    [IsFlat ℱ] :
    SheafOfModules.RingedSite.IsFlat (commRingSheafification J 𝒪)
      ((moduleSheafification J 𝒪).obj ℱ) := sorry

/-- The sheafification of a flat presheaf carries its canonical flatness instance. -/
instance
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    [IsFlat ℱ] :
    SheafOfModules.RingedSite.IsFlat (commRingSheafification J 𝒪)
      ((moduleSheafification J 𝒪).obj ℱ) :=
  sheafification_isFlat J 𝒪 ℱ

end PresheafOfModules

/-! ### Lemma_18_28_4 (from Chap18) -/
open CategoryTheory Opposite Limits

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]

/- Domain-style sampling for Lemma 18.28.4:
- primary domain: sheafification of locally flat presheaves of modules, with the core
  sheafification machinery owned by the Chapter 18 flatness API for sheaves of modules;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFlat`,
  `PresheafOfModules.moduleSheafification`,
  `PresheafOfModules.sheafificationRingMap`,
  `sheafModuleTensorRightFunctor`,
  `exactFunctor`;
- best owner abstraction: the source-facing result should be stated directly in the chapter owner
  `SheafOfModules.RingedSite.IsFlat` for the sheafified module
  `((moduleSheafification J 𝒪).obj ℱ)` over `commRingSheafification J 𝒪`; exactness of tensoring
  is then derived API via the field `IsFlat.exact_tensor`;
- primitive data: a presheaf of commutative rings `𝒪`, a presheaf module
  `ℱ : PresheafOfModules (ringPresheaf 𝒪)`, and the local sectionwise flatness hypothesis;
- derived API: exactness of the sheaf tensor-right functor on
  `SheafOfModules (ringSheaf J (commRingSheafification J 𝒪))`.

Layer triage:
- `source-facing`: the local-flatness criterion for the sheafified module;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the exactness consequence expressed by `IsFlat.exact_tensor`.
-/

-- Proof sketch: use the local-flatness hypothesis to reduce injectivity of tensoring with
-- `\mathcal F^\#` to injectivity after passing to a covering on which the section modules of
-- `\mathcal F` are flat; then apply exactness of module sheafification and the local criterion
-- that a morphism of presheaves which is injective on a cover sheafifies to a monomorphism.
/-- Lemma 18.28.4: if every object of the site has a covering on which the section modules of a
presheaf `\mathcal F` are flat over the corresponding sections of `\mathcal O`, then the
associated sheaf `\mathcal F^\#` is flat over the sheafified structure sheaf `\mathcal O^\#`,
expressed in the chapter's canonical owner `SheafOfModules.RingedSite.IsFlat`. -/
theorem sheafification_isFlat_of_locally_flat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hlocal :
      ∀ U : C, ∃ R : Presieve U, Sieve.generate R ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Module.Flat (𝒪.obj (op V)) (ℱ.obj (op V))) :
    SheafOfModules.RingedSite.IsFlat
      (commRingSheafification J 𝒪) ((moduleSheafification J 𝒪).obj ℱ) := sorry

/-- Exactness companion to Lemma 18.28.4: the canonical flatness statement implies that
tensoring on the right by `\mathcal F^\#` is exact on sheaves of `\mathcal O^\#`-modules. -/
theorem sheafification_exact_tensor_of_locally_flat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hlocal :
      ∀ U : C, ∃ R : Presieve U, Sieve.generate R ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Module.Flat (𝒪.obj (op V)) (ℱ.obj (op V))) :
    exactFunctor
      (SheafOfModules (ringSheaf J (commRingSheafification J 𝒪)))
      (SheafOfModules (ringSheaf J (commRingSheafification J 𝒪)))
      (sheafModuleTensorRightFunctor ((moduleSheafification J 𝒪).obj ℱ)) :=
  (sheafification_isFlat_of_locally_flat J 𝒪 ℱ hlocal).exact_tensor

end PresheafOfModules

/-! ### Lemma_18_28_5 (from Chap18) -/
open CategoryTheory Limits Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

/- Domain-style sampling for Lemma 18.28.5:
- primary domain: closure of flat module objects under filtered colimits and coproducts in
  presheaf and sheaf module categories;
- sampled owner declarations:
  `Module.Flat`,
  `PresheafOfModules.IsFlat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.isFlat_colimit_of_isFiltered`;
- best owner abstraction: flatness is owned by the typeclasses
  `PresheafOfModules.IsFlat` and `SheafOfModules.RingedSite.IsFlat`, so stagewise flatness should
  be supplied by instances rather than explicit functions;
- primitive data: a filtered or discrete diagram of module objects;
- derived API: the colimit-closure lemmas below.

Source/core/bridge triage:
- `source-facing`: flatness is preserved by filtered colimits and direct sums;
- `core/canonical`: the flatness owner typeclasses on the ambient module categories;
- `bridge/view`: the colimit constructions computing the direct sums and filtered colimits.

This file should therefore keep the source-facing closure statements while reusing the canonical
instance-driven flatness owners already used upstream, rather than carrying parallel explicit
stagewise flatness data.
-/

-- Proof sketch: evaluate the filtered colimit presheaf at each object of `C`. The resulting
-- filtered colimit of flat modules is flat by the module-theoretic criterion from
-- Lemma `10.8.8`, and then Lemma `18.28.2` promotes these objectwise flatness statements back to
-- flatness of the colimit presheaf.
/-- Lemma 18.28.5 (1): a filtered colimit of flat presheaves of modules over a presheaf of
commutative rings is flat. -/
theorem isFlat_colimit_of_isFiltered {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ PresheafOfModules (ringPresheaf 𝒪))
    [∀ j, IsFlat (F.obj j)] :
    IsFlat (colimit F) := sorry

-- Proof sketch: a direct sum is the coproduct of the corresponding discrete diagram. Apply the
-- filtered-colimit argument objectwise to the discrete diagram, using that direct sums of flat
-- modules are flat, and conclude by Lemma `18.28.2`.
/-- Lemma 18.28.5 (2): a direct sum of flat presheaves of modules over a presheaf of commutative
rings is flat. -/
theorem isFlat_coproduct {I : Type u}
    (F : Discrete I ⥤ PresheafOfModules (ringPresheaf 𝒪))
    [∀ i, IsFlat (F.obj ⟨i⟩)] :
    IsFlat (colimit F) := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

open PresheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]

-- Proof sketch: pass to underlying presheaves, where filtered colimits are computed objectwise
-- and preserve flatness by part `(1)`. Then use the canonical ringed-site flatness owner
-- `IsFlat` for an arbitrary sheaf of commutative rings `𝒪`.
/-- Lemma 18.28.5 (3): a filtered colimit of flat sheaves of modules over a sheaf of
commutative rings `\mathcal O` on a site is flat. -/
theorem isFlat_colimit_of_isFiltered {K : Type u} [Category.{u} K] [IsFiltered K]
    {𝒪 : Sheaf J CommRingCat.{u}} (F : K ⥤ SheafOfModules (ringSheaf J 𝒪))
    [∀ k, IsFlat 𝒪 (F.obj k)] :
    IsFlat 𝒪 (colimit F) :=
  sorry

-- Proof sketch: a direct sum is the coproduct of a discrete diagram. Apply the sheaf filtered
-- colimit statement to that diagram, equivalently reason on underlying presheaves and use the
-- direct-sum preservation of flatness from part `(2)`.
/-- Lemma 18.28.5 (4): a direct sum of flat sheaves of modules over a sheaf of commutative rings
`\mathcal O` on a site is flat. -/
theorem isFlat_coproduct {I : Type u}
    {𝒪 : Sheaf J CommRingCat.{u}} (F : Discrete I ⥤ SheafOfModules (ringSheaf J 𝒪))
    [∀ i, IsFlat 𝒪 (F.obj ⟨i⟩)] :
    IsFlat 𝒪 (colimit F) :=
  sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_28_6 (from Chap18) -/
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Lemma 18.28.6:
- primary domain: flat sheaves of modules on a ringed site and their localized restrictions;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero_isFlat`,
  `PresheafOfModules.sheafification_isFlat`,
  `SheafOfModules.RingedSite.pullback_isFlat_of_isFlat`;
- best owner abstraction: the chapter owner `SheafOfModules.RingedSite.IsFlat`; the restriction
  `ℱ.over U` should be expressed by the same owner on `𝒪.over U`, not by a parallel exactness
  predicate on `tensorLeft`;
- primitive data: the sheaf of rings `𝒪`, the sheaf of modules `ℱ`, and the localized object
  `U : C`;
- derived API: flatness of the localized restriction `ℱ.over U`.

Source/core/bridge triage:
- `source-facing`: flatness of the restriction `ℱ|_U`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the restriction operation `ℱ ↦ ℱ.over U`. -/
-- Proof sketch: let `𝒢₁ ⟶ 𝒢₂ ⟶ 𝒢₃` be an exact short complex of `\mathcal O_U`-modules. Apply
-- extension by zero `j_{U!}`, which is exact by Lemma `18.19.3`, identify
-- `j_{U!} (𝒢ᵢ ⊗ ℱ|_U)` with `j_{U!} 𝒢ᵢ ⊗ ℱ` using Lemma `18.27.9`, use flatness of `ℱ`, and
-- then reflect exactness back to the localized site by Lemma `18.19.4`.
/-- Lemma 18.28.6: if `ℱ` is a flat `\mathcal O`-module on a ringed site
`(\mathcal C, \mathcal O)`, then for every object `U : \mathcal C` the restricted module
`ℱ|_U`, written `ℱ.over U`, is flat on the localized ringed site
`(\mathcal C/U, \mathcal O_U)`, expressed in the chapter's canonical owner
`SheafOfModules.RingedSite.IsFlat`. -/
theorem isFlat_over
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) (ℱ : SheafOfModules (ringSheaf J 𝒪))
    [IsFlat 𝒪 ℱ] :
    IsFlat (𝒪.over U) (ℱ.over U) := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_28_7 (from Chap18) -/
open CategoryTheory Opposite

noncomputable section

universe u

/-- The localized ring presheaf on the slice category `C/U`. -/
abbrev localizedRingPresheaf {C : Type u} [Category.{u} C]
    (𝒪 : Cᵒᵖ ⥤ RingCat.{u}) (U : C) :
    (Over U)ᵒᵖ ⥤ RingCat.{u} :=
  (Over.forget U).op ⋙ 𝒪

/-- Extension by zero from presheaves of modules over the localized ring presheaf on `C/U`. -/
abbrev presheafLocalizedExtensionByZero {C : Type u} [Category.{u} C]
    (𝒪 : Cᵒᵖ ⥤ RingCat.{u}) (U : C) :
    PresheafOfModules (localizedRingPresheaf 𝒪 U) ⥤ PresheafOfModules 𝒪 :=
  PresheafOfModules.pullback (𝟙 (localizedRingPresheaf 𝒪 U))

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]

/-- The localized structure module `\mathcal O_U` on the slice category `C/U`, regarded as a
module over the localized ring presheaf. -/
abbrev localizedStructureModule
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    PresheafOfModules (localizedRingPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat) U) :=
  PresheafOfModules.unit (localizedRingPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat) U)

/-- The presheaf `j_{U!}\mathcal O_U` obtained by extending the localized structure module by zero
from `C/U` back to `C`. -/
abbrev localizedStructureModuleExtensionByZero
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat) :=
  (presheafLocalizedExtensionByZero (𝒪 ⋙ forget₂ CommRingCat RingCat) U).obj
    (localizedStructureModule 𝒪 U)

-- Proof sketch: evaluate `j_{U!}\mathcal O_U` at an object `V`. By Remark `18.19.7` this section
-- module is the coproduct over all arrows `V ⟶ U` of copies of `\mathcal O(V)`, hence is a free,
-- in particular flat, `\mathcal O(V)`-module. Then apply Lemma `18.28.2`.
/-- Lemma 18.28.7 (1): for a presheaf of commutative rings `\mathcal O` on a category
`\mathcal C` and an object `U : \mathcal C`, the lower-shriek module `j_{U!}\mathcal O_U` is flat
as a presheaf of `\mathcal O`-modules. -/
theorem localizedStructureModuleExtensionByZero_isFlat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    IsFlat (localizedStructureModuleExtensionByZero 𝒪 U) := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

/-- The localized structure module `\mathcal O_U` on the slice site `(C/U, J.over U)`, extended
by zero to a sheaf of `\mathcal O`-modules on `(C, J)`. -/
abbrev localizedStructureModuleExtensionByZero
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) :
    SheafOfModules (ringSheaf J 𝒪) :=
  (SheafOfModules.pullback (𝟙 ((ringSheaf J 𝒪).over U))).obj
    (SheafOfModules.unit ((ringSheaf J 𝒪).over U))

-- Proof sketch: on the localized site, tensoring with `\mathcal O_U` is the identity functor.
-- Lemma `18.27.9` identifies tensoring with `j_{U!}\mathcal O_U` on `(C, J)` with extension by
-- zero `j_{U!}`, and Lemma `18.19.3` shows that extension by zero is exact. Hence tensoring with
-- `j_{U!}\mathcal O_U` is exact, i.e. `j_{U!}\mathcal O_U` is flat.
/-- Lemma 18.28.7 (2): if `(\mathcal C, J)` is a site and `\mathcal O` is a sheaf of
commutative rings on it, then the lower-shriek module `j_{U!}\mathcal O_U` is a flat sheaf of
`\mathcal O`-modules. -/
theorem localizedStructureModuleExtensionByZero_isFlat
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) :
    IsFlat 𝒪 (localizedStructureModuleExtensionByZero 𝒪 U) := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_28_8 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

-- Proof sketch: for each pair `(U, s)` with `U : C` and `s ∈ ℱ(U)`, the adjunction defining
-- `j_{U!}` gives a morphism `j_{U!}\mathcal O_U ⟶ ℱ` sending `1` to `s`. Taking the coproduct over
-- all such pairs yields a morphism whose components generate every section objectwise, hence an
-- epimorphism.
/-- Lemma 18.28.8 (1): any presheaf of `\mathcal O`-modules is the quotient of a direct sum of
lower-shriek modules `j_{U_i!}\mathcal O_{U_i}`. -/
theorem exists_epi_from_coproduct_localizedStructureModuleExtensionByZero
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) :
    ∃ (I : Type u) (U : I → C)
      (φ : (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ ℱ), Epi φ := sorry

-- Proof sketch: apply part `(1)` to obtain an epimorphism from a coproduct of the modules
-- `j_{U_i!}\mathcal O_{U_i}`. Each summand is flat by Lemma `18.28.7 (1)`, and the coproduct is
-- flat by Lemma `18.28.5 (2)`, giving a flat source surjecting onto `ℱ`.
/-- Lemma 18.28.8 (2): any presheaf of `\mathcal O`-modules is the quotient of a flat presheaf of
`\mathcal O`-modules. -/
theorem exists_epi_from_flat
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) :
    ∃ (𝒢 : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))
      (_h𝒢 : IsFlat 𝒢)
      (φ : 𝒢 ⟶ ℱ), Epi φ := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

-- Proof sketch: repeat the presheaf argument in the sheaf category, or apply the presheaf result
-- and then sheafify. For each local section over `U`, adjunction produces a map
-- `j_{U!}\mathcal O_U ⟶ ℱ`; the induced coproduct map is epimorphic.
/-- Lemma 18.28.8 (3): if `(\mathcal C, J)` is a site and `\mathcal O` is a sheaf of rings, then
any sheaf of `\mathcal O`-modules is the quotient of a direct sum of lower-shriek modules
`j_{U_i!}\mathcal O_{U_i}`. -/
theorem exists_epi_from_coproduct_localizedStructureModuleExtensionByZero
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (I : Type u) (U : I → C)
      (φ : (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ ℱ), Epi φ := sorry

-- Proof sketch: combine part `(3)` with Lemma `18.28.7 (2)` for flatness of each
-- `j_{U_i!}\mathcal O_{U_i}`, then use direct sums of flat sheaves to obtain a flat sheaf
-- surjecting onto `ℱ`.
/-- Lemma 18.28.8 (4): if `(\mathcal C, J)` is a site and `\mathcal O` is a sheaf of rings, then
any sheaf of `\mathcal O`-modules is the quotient of a flat sheaf of `\mathcal O`-modules. -/
theorem exists_epi_from_flat
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (𝒢 : SheafOfModules (ringSheaf J 𝒪))
      (_h𝒢 : IsFlat 𝒪 𝒢)
      (φ : 𝒢 ⟶ ℱ), Epi φ := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_28_9 (from Chap18) -/
open CategoryTheory MonoidalCategory Opposite

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Tensoring presheaves of modules on the right by a fixed module preserves zero morphisms. -/
instance tensorRight_preservesZeroMorphisms
    (𝒢 : PresheafOfModules (ringPresheaf 𝒪)) :
    (tensorRight 𝒢).PreservesZeroMorphisms := sorry

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
    (S.map (tensorRight 𝒢)).ShortExact := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/-- Tensoring sheaves of modules on the right by a fixed module preserves zero morphisms. -/
instance sheafModuleTensorRightFunctor_preservesZeroMorphisms
    (𝒢 : SheafOfModules (ringSheaf J 𝒪)) :
    (sheafModuleTensorRightFunctor 𝒢).PreservesZeroMorphisms := sorry

-- Proof sketch: argue exactly as in the presheaf case, replacing the presheaf tensor product by
-- the sheaf tensor product and using flatness of `S.X₃` as a sheaf of modules.
/-- Lemma 18.28.9 (2): if `(\mathcal C, J)` is a site, `0 ⟶ \mathcal F'' ⟶ \mathcal F' ⟶
\mathcal F ⟶ 0` is a short exact sequence of sheaves of `\mathcal O`-modules, and `\mathcal F`
is flat, then tensoring on the right by any sheaf `\mathcal G` preserves short exactness. -/
theorem shortExact_tensor_right_of_flat_quotient
    (𝒢 : SheafOfModules (ringSheaf J 𝒪))
    (S : ShortComplex (SheafOfModules (ringSheaf J 𝒪)))
    (hS : S.ShortExact)
    [IsFlat 𝒪 S.X₃] :
    (S.map (sheafModuleTensorRightFunctor 𝒢)).ShortExact := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_28_10 (from Chap18) -/
open CategoryTheory Opposite

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {S : ShortComplex (PresheafOfModules (ringPresheaf 𝒪))}

-- Proof sketch: if `S.X₁` is flat, apply Lemma `18.28.9` to see that tensoring `S` on the right
-- preserves short exactness, hence the exact tensor functor criterion gives flatness of `S.X₂`.
-- Conversely, if `S.X₂` is flat, use the exactness of tensoring with `S.X₂` and the snake-lemma
-- argument from the textbook to recover exactness after tensoring with `S.X₁`.
/-- Lemma 18.28.10: for a short exact sequence
`0 ⟶ \mathcal F_2 ⟶ \mathcal F_1 ⟶ \mathcal F_0 ⟶ 0` of presheaves of
`\mathcal O`-modules, if `\mathcal F_0` is flat then `\mathcal F_2` is flat if and only if
`\mathcal F_1` is flat. -/
theorem flat_iff_flat_of_shortExact
    (hS : S.ShortExact) [IsFlat S.X₃] :
    IsFlat S.X₁ ↔ IsFlat S.X₂ := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}
variable {S : ShortComplex (SheafOfModules (ringSheaf J 𝒪))}

-- Proof sketch: repeat the presheaf argument in `Mod(\mathcal O)`, using the sheaf version of
-- Lemma `18.28.9` to preserve short exactness under tensor product and the same snake-lemma
-- two-out-of-three argument for flatness.
/-- On a ringed site, if the right term of a short exact sequence of sheaves of
`\mathcal O`-modules is flat, then the left term is flat if and only if the middle term is flat. -/
theorem flat_iff_flat_of_shortExact
    (hS : S.ShortExact) [IsFlat 𝒪 S.X₃] :
    IsFlat 𝒪 S.X₁ ↔ IsFlat 𝒪 S.X₂ := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_28_11 (from Chap18) -/
open CategoryTheory MonoidalCategory Opposite

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- A right-augmented exact complex of presheaves of `\mathcal O`-modules
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`,
encoded by exactness at every displayed term and surjectivity of the augmentation. -/
structure RightAugmentedExact
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    (𝒬 : PresheafOfModules (ringPresheaf 𝒪))
    (q : ℱ 0 ⟶ 𝒬) : Prop where
  /-- Consecutive differentials in the resolution part compose to zero. -/
  d_comp_d : ∀ n : ℕ, d (n + 1) ≫ d n = 0
  /-- The last differential composes trivially with the augmentation. -/
  d_comp_q : d 0 ≫ q = 0
  /-- Exactness at every term `\mathcal F_n` with `n ≥ 1`. -/
  exact_succ :
      ∀ n : ℕ,
        (ShortComplex.mk (d (n + 1)) (d n) (d_comp_d n)).Exact
  /-- Exactness at `\mathcal F_0`. -/
  exact_zero :
      (ShortComplex.mk (d 0) q d_comp_q).Exact
  /-- Exactness at `\mathcal Q`, equivalently surjectivity of the augmentation. -/
  epi_q : Epi q

-- Proof sketch: split the augmented exact complex into the short exact sequences
-- `0 → im(d_{n+1}) → ℱ_n → im(d_n) → 0` and `0 → im(d_0) → ℱ_0 → 𝒬 → 0`. Apply Lemma
-- `18.28.9` to preserve each short exact sequence after tensoring with `𝒢`, and use Lemma
-- `18.28.10` inductively to show the successive images remain flat.
/-- Lemma 18.28.11 (1): if
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`
is an exact complex of flat presheaves of `\mathcal O`-modules, then tensoring on the right by
any presheaf `\mathcal G` again yields an exact right-augmented complex. -/
theorem rightAugmentedExact_tensor_right_of_flat
    (ℱ : ℕ → PresheafOfModules (ringPresheaf 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : PresheafOfModules (ringPresheaf 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    [IsFlat 𝒬]
    [∀ n : ℕ, IsFlat (ℱ n)] :
    RightAugmentedExact
      (fun n ↦ (tensorRight 𝒢).obj (ℱ n))
      (fun n ↦ (tensorRight 𝒢).map (d n))
      ((tensorRight 𝒢).obj 𝒬)
      ((tensorRight 𝒢).map q) := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

/-- A right-augmented exact complex of sheaves of `\mathcal O`-modules on a ringed site
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`,
encoded by exactness at every displayed term and surjectivity of the augmentation. -/
structure RightAugmentedExact
    (ℱ : ℕ → SheafOfModules (ringSheaf J 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    (𝒬 : SheafOfModules (ringSheaf J 𝒪))
    (q : ℱ 0 ⟶ 𝒬) : Prop where
  /-- Consecutive differentials in the resolution part compose to zero. -/
  d_comp_d : ∀ n : ℕ, d (n + 1) ≫ d n = 0
  /-- The last differential composes trivially with the augmentation. -/
  d_comp_q : d 0 ≫ q = 0
  /-- Exactness at every term `\mathcal F_n` with `n ≥ 1`. -/
  exact_succ :
      ∀ n : ℕ,
        (ShortComplex.mk (d (n + 1)) (d n) (d_comp_d n)).Exact
  /-- Exactness at `\mathcal F_0`. -/
  exact_zero :
      (ShortComplex.mk (d 0) q d_comp_q).Exact
  /-- Exactness at `\mathcal Q`, equivalently surjectivity of the augmentation. -/
  epi_q : Epi q

-- Proof sketch: repeat the presheaf argument in `Mod(\mathcal O)`, using the sheaf version of
-- Lemma `18.28.9` on each short exact subsequence and Lemma `18.28.10` to propagate flatness of
-- successive images through the augmented resolution.
/-- Lemma 18.28.11 (2): if `(\mathcal C, J)` is a site and
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`
is an exact complex of flat sheaves of `\mathcal O`-modules, then tensoring on the right by any
sheaf `\mathcal G` again yields an exact right-augmented complex in `\mathrm{Mod}(\mathcal O)`. -/
theorem rightAugmentedExact_tensor_right_of_flat
    (ℱ : ℕ → SheafOfModules (ringSheaf J 𝒪))
    (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
    {𝒬 𝒢 : SheafOfModules (ringSheaf J 𝒪)}
    (q : ℱ 0 ⟶ 𝒬)
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    [IsFlat 𝒪 𝒬]
    [∀ n : ℕ, IsFlat 𝒪 (ℱ n)] :
    RightAugmentedExact
      (fun n ↦ (sheafModuleTensorRightFunctor 𝒢).obj (ℱ n))
      (fun n ↦ (sheafModuleTensorRightFunctor 𝒢).map (d n))
      ((sheafModuleTensorRightFunctor 𝒢).obj 𝒬)
      ((sheafModuleTensorRightFunctor 𝒢).map q) := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_28_12 (from Chap18) -/
open CategoryTheory
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

variable {C : Type u} [Category.{u} C]
variable {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules.RingedSite
variable {𝒪 : Sheaf J CommRingCat.{u}}

-- Proof sketch: flatness is owned by the exact tensor functor
-- `SheafOfModules.RingedSite.IsFlat`. Tensoring with `𝒢 ⊗ 𝓕` is the composite of
-- tensoring first with `𝓕` and then with `𝒢`, so exactness follows from exactness of the two
-- flat tensor functors and stability of exactness under composition.
/-- Lemma 18.28.12: for a ringed site `(\mathcal C, \mathcal O)`, if `\mathcal G` and
`\mathcal F` are flat `\mathcal O`-modules, then their tensor product
`\mathcal G \otimes_\mathcal O \mathcal F`, formalized here as `𝒢 ⊗ 𝓕`, is again a flat
`\mathcal O`-module. -/
theorem isFlat_tensor
    (𝒢 𝓕 : SheafOfModules (ringSheaf J 𝒪))
    [IsFlat 𝒪 𝒢] [IsFlat 𝒪 𝓕] :
    IsFlat 𝒪 (𝒢 ⊗ 𝓕) := by
  sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_28_13 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

/-- The underlying `RingCat`-valued structure map attached to a morphism of sheaves of
commutative rings on a fixed site. -/
abbrev ringedSiteStructureMap
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {𝒪₁ 𝒪₂ : Sheaf J CommRingCat.{max u v}}
    (α : 𝒪₁ ⟶ 𝒪₂) :
    ringSheaf J 𝒪₁ ⟶
      ((𝟭 C).sheafPushforwardContinuous RingCat.{max u v} J J).obj (ringSheaf J 𝒪₂) :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map α

/-
Domain-style sampling for Lemma 18.28.13:
- primary domain: change of rings for module sheaves on a ringed site and preservation of
  flatness under extension of scalars;
- sampled owner declarations:
  `ringSheaf`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.pullback`,
  `ringedSiteStructureMap`;
- best owner abstraction: the ambient owner is the flatness class
  `SheafOfModules.RingedSite.IsFlat`, and same-site extension of scalars is the canonical
  `SheafOfModules.pullback` applied to the public same-site bridge
  `ringedSiteStructureMap`;
- primitive data: a morphism `α : 𝒪₁ ⟶ 𝒪₂` of commutative structure sheaves and a module
  `𝒢 : SheafOfModules (ringSheaf J 𝒪₁)` with flatness instance;
- bridge/view owner: `ringedSiteStructureMap α`, which packages the identity-site transport
  needed by `SheafOfModules.pullback`.

Source/core/bridge triage:
- `source-facing`: extension of scalars along a morphism of structure sheaves on a fixed site;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`, `ringSheaf`, and
  `SheafOfModules.pullback`;
- `bridge/view`: the underlying `RingCat`-valued same-site structure map
  `ringedSiteStructureMap α`.

This file should therefore reuse `IsFlat` and `SheafOfModules.pullback` directly, with the
same-site transport expressed through the public bridge owner `ringedSiteStructureMap`, rather
than through an inaccessible local wrapper.
-/

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪₁ 𝒪₂ : Sheaf J CommRingCat.{max u v}}
variable (α : 𝒪₁ ⟶ 𝒪₂)
variable [(PresheafOfModules.pushforward (ringedSiteStructureMap α).hom).IsRightAdjoint]
variable [(SheafOfModules.pushforward (ringedSiteStructureMap α)).IsRightAdjoint]

-- Proof sketch: the source-facing change-of-rings datum is the morphism
-- `α : 𝒪₁ ⟶ 𝒪₂` of commutative structure sheaves. The corresponding extension of scalars is the
-- canonical same-site pullback along the induced `RingCat`-valued structure map
-- `ringedSiteStructureMap α`, and flatness is expressed through the chapter owner
-- `SheafOfModules.RingedSite.IsFlat`.
/-- Lemma 18.28.13: for a morphism of sheaves of commutative rings
`\mathcal O_1 \to \mathcal O_2` on a site, if `\mathcal G` is a flat
`\mathcal O_1`-module, then the extension of scalars
`\mathcal G \otimes_{\mathcal O_1} \mathcal O_2`, canonically realized as the same-site
change-of-rings pullback, is a flat `\mathcal O_2`-module. -/
theorem pullback_isFlat
    (𝒢 : SheafOfModules (ringSheaf J 𝒪₁))
    [IsFlat 𝒪₁ 𝒢] :
    IsFlat 𝒪₂ ((SheafOfModules.pullback (ringedSiteStructureMap α)).obj 𝒢) := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_28_14 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]

private abbrev finiteIndex (n : ℕ) : Type u :=
  ULift.{u} (Fin n)

private abbrev localizedModuleCategory
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) (U : C) :=
  ringedSiteModuleCategory (J.over U) (𝒪.over U)

private abbrev iteratedLocalizedModuleCategory
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) {U : C} (V : Over U) :=
  ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)

private abbrev localizedFiniteFreeModule
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) (U : C) (n : ℕ) :
    localizedModuleCategory J 𝒪 U :=
  SheafOfModules.free (finiteIndex n)

private abbrev iteratedLocalizedFiniteFreeModule
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) {U : C} (V : Over U) (n : ℕ) :
    iteratedLocalizedModuleCategory J 𝒪 V :=
  SheafOfModules.free (finiteIndex n)

private abbrev iteratedRestriction
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) {U : C} (V : Over U) :
    localizedModuleCategory J 𝒪 U ⥤ iteratedLocalizedModuleCategory J 𝒪 V :=
  SheafOfModules.pushforward (𝟙 (((ringSheaf J 𝒪).over U).over V))

private def localFiniteFreeFactorization
    (ℱ : ringedSiteModuleCategory J 𝒪) {U : C} {m n : ℕ}
    (relation : localizedFiniteFreeModule J 𝒪 U m ⟶ localizedFiniteFreeModule J 𝒪 U n)
    (s : localizedFiniteFreeModule J 𝒪 U n ⟶ ℱ.over U) : Prop :=
  let Free := localizedFiniteFreeModule J 𝒪 U
  ∃ (I : Type u) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
    ∀ i : I,
      let restriction := iteratedRestriction J 𝒪 (Ui i)
      let Free' := iteratedLocalizedFiniteFreeModule J 𝒪 (Ui i)
      ∃ (l : ℕ)
        (B : restriction.obj (Free n) ⟶ Free' l)
        (t : Free' l ⟶ (ℱ.over U).over (Ui i)),
        restriction.map s = B ≫ t ∧
          restriction.map relation ≫ B = 0

/- Domain-style sampling for Lemma 18.28.14:
- primary domain: flat sheaves of modules on a ringed site, tested by localized finite-free
  factorization criteria;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.free`,
  `SheafOfModules.over`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pushforwardOver`;
- best owner abstraction: the ambient module object should live in the chapter-level owner
  `ringedSiteModuleCategory J 𝒪`, while localization is expressed through the canonical
  restriction objects `ℱ ↦ ℱ.over U`, `((ℱ.over U).over V)`, and the canonical localization
  functor to iterated slice sites;
- primitive data: a module `ℱ : ringedSiteModuleCategory J 𝒪`, finite free modules on localized
  sites, and the further-localization functor from `(C/U, \mathcal O_U)` to
  `((C/U)/V, \mathcal O_V)`;
- derived API: the uniform local finite-free factorization predicate and its source-facing
  one-relation / finite-presentation specializations.

Source/core/bridge triage:
- `source-facing`: the two local factorization predicates and their equivalence with flatness;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`,
  `SheafOfModules.RingedSite.IsFlat`, `SheafOfModules.free`,
  `SheafOfModules.over`, `SheafOfModules.pushforward`, and
  `SheafOfModules.pushforwardOver`;
- `bridge/view`: the further-localization functor from `ℱ.over U` to `((ℱ.over U).over V)` and
  the uniform factorization predicate `localFiniteFreeFactorization`.

This file should therefore reuse the upstream owner `ringedSiteModuleCategory` from
`Lemma_18_19_2`, with localized finite free modules and iterated restrictions expressed through a
thin internal layer over the chapter's canonical `over` / `pushforward` surface rather than
repeating the raw sheaf expressions in every public statement.
-/

/-- The single-relation local factorization criterion for flatness on a ringed site. -/
def flatSingleRelationFactorization
    (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  ∀ (U : C) (n : ℕ),
    let Free := localizedFiniteFreeModule J 𝒪 U
    ∀ (f : Free 1 ⟶ Free n) (s : Free n ⟶ ℱ.over U) (_ : f ≫ s = 0),
      localFiniteFreeFactorization ℱ f s

/-- The finite-presentation local factorization criterion for flatness on a ringed site. -/
def flatMatrixFactorization
    (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  ∀ (U : C) (m n : ℕ),
    let Free := localizedFiniteFreeModule J 𝒪 U
    ∀ (A : Free m ⟶ Free n) (s : Free n ⟶ ℱ.over U) (_ : A ≫ s = 0),
      localFiniteFreeFactorization ℱ A s

-- Proof sketch: `(1) → (2)` is the standard local syzygy criterion obtained by applying
-- flatness to the ideal generated by one relation. `(2) → (3)` is an induction on the number of
-- columns of the presentation matrix. `(3) → (1)` is the finite-presentation criterion for
-- injectivity after tensoring, using that sections of `ℱ` are filtered colimits of finitely
-- presented modules and then applying the local factorization through finite free modules.
/-- Lemma 18.28.14: for a ringed site `(\mathcal C, \mathcal O)` and an `\mathcal O`-module
`\mathcal F`, flatness of `\mathcal F` is equivalent to the local finite-relation factorization
criterion for one relation and to its finite-presentation version for arbitrary maps
`\mathcal O_U^{\oplus m} \to \mathcal O_U^{\oplus n}`. -/
theorem isFlat_tfae_factorizationCriteria
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    List.TFAE [
      IsFlat 𝒪 ℱ,
      flatSingleRelationFactorization ℱ,
      flatMatrixFactorization ℱ
    ] := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_28_15 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{u}}

/-- Restriction of scalars along `α`, written as the pushforward functor for the identity functor
on the underlying site. -/
abbrev restrictionAlong (α : 𝒪' ⟶ 𝒪) :
    SheafOfModules (ringSheaf J 𝒪) ⥤ SheafOfModules (ringSheaf J 𝒪') :=
  SheafOfModules.pushforward (ringedSiteStructureMap α)

/-- A square-zero reduction datum consists of a kernel ideal sheaf
`\mathcal I \hookrightarrow \mathcal O'`, a quotient presentation
`\mathcal F' \twoheadrightarrow \mathcal F`, and the sectionwise square-zero condition on
`\mathcal I`. Here `restrictionAlong α` is the same-site restriction-of-scalars functor attached
to `\alpha : \mathcal O' \to \mathcal O`. -/
structure IsSquareZeroReduction
    (α : 𝒪' ⟶ 𝒪)
    (𝓘 : SheafOfModules (ringSheaf J 𝒪'))
    (ι : 𝓘 ⟶ SheafOfModules.unit (ringSheaf J 𝒪'))
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (tensorTo : moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ) ⟶ ℱ')
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ) : Prop where
  /-- The ideal sheaf maps trivially to the quotient structure sheaf `\mathcal O`. -/
  ideal_comp :
    ι ≫ SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap α) = 0
  /-- The ideal sheaf is included as a submodule of `\mathcal O'`. -/
  ideal_mono : Mono ι
  /-- The sequence `\mathcal I \to \mathcal O' \to \mathcal O` is exact. -/
  ideal_exact :
    (ShortComplex.mk ι
      (SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap α))
      ideal_comp).Exact
  /-- The map `\mathcal O' \to \mathcal O` is an epimorphism of sheaves of modules. -/
  ideal_epi : Epi (SheafOfModules.unitToPushforwardObjUnit (ringedSiteStructureMap α))
  /-- Sectionwise, the kernel ideal squares to zero. -/
  square_zero :
    ∀ U : Cᵒᵖ, ∀ x y : 𝓘.val.obj U,
      ((show ↑((ringSheaf J 𝒪').obj.obj U) from ι.val.app U x) *
        (show ↑((ringSheaf J 𝒪').obj.obj U) from ι.val.app U y)) = 0
  /-- The tensor-action map and quotient map compose to zero. -/
  quot_comp : tensorTo ≫ quot = 0
  /-- The sequence `\mathcal I \otimes_{\mathcal O} \mathcal F \to \mathcal F' \to \mathcal F`
  is exact in the categorical formulation used in this file. -/
  quot_exact : (ShortComplex.mk tensorTo quot quot_comp).Exact
  /-- The quotient map `\mathcal F' \to \mathcal F` is an epimorphism. -/
  quot_epi : Epi quot

-- Proof sketch: for the forward implication, use Lemma `18.28.13` to descend flatness along the
-- quotient map `\mathcal O' \twoheadrightarrow \mathcal O`, and apply Lemma `18.28.9` to the
-- exact sequence defining `\mathcal F`. Conversely, test flatness of `\mathcal F'` on a monic
-- map, pass to the quotient exact sequence from `IsSquareZeroReduction`, and use flatness of
-- `\mathcal F` together with the assumed monomorphism of `tensorTo` to recover injectivity after
-- tensoring.
/-- Lemma 18.28.15: let `(\mathcal C, J)` be a site, let `\alpha : \mathcal O' \to \mathcal O` be
a surjection of sheaves of rings with square-zero kernel ideal sheaf `\mathcal I`, let
`\mathcal F'` be an `\mathcal O'`-module, and let `\mathcal F = \mathcal F'/\mathcal I\mathcal
F'`. In the categorical formulation used here, the quotient data are encoded by
`IsSquareZeroReduction α 𝓘 ι ℱ' ℱ tensorTo quot`, and the map `tensorTo` is the textbook map
`\mathcal I \otimes_{\mathcal O} \mathcal F \to \mathcal F'` after viewing `\mathcal F` as an
`\mathcal O'`-module by restriction of scalars. Then `\mathcal F'` is flat over `\mathcal O'` if
and only if `\mathcal F` is flat over `\mathcal O` and `tensorTo` is injective. -/
theorem isFlat_iff_isFlat_reduction_and_mono_tensor_of_squareZeroReduction
    (α : 𝒪' ⟶ 𝒪) [Epi α]
    (𝓘 : SheafOfModules (ringSheaf J 𝒪'))
    (ι : 𝓘 ⟶ SheafOfModules.unit (ringSheaf J 𝒪'))
    (ℱ' : SheafOfModules (ringSheaf J 𝒪'))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (tensorTo : moduleTensor 𝓘 (restrictionAlong α |>.obj ℱ) ⟶ ℱ')
    (quot : ℱ' ⟶ (restrictionAlong α).obj ℱ)
    (hsetup : IsSquareZeroReduction α 𝓘 ι ℱ' ℱ tensorTo quot) :
    IsFlat 𝒪' ℱ' ↔
      IsFlat 𝒪 ℱ ∧ Mono tensorTo := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_28_16 (from Chap18) -/
open CategoryTheory Opposite
open SheafOfModules

noncomputable section

universe u

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 18.28.16:
- primary domain: same-site change of rings for sheaves of modules, with flatness owned by
  `SheafOfModules.RingedSite.IsFlatHom` and the canonical base-change morphism owned by the
  pullback/pushforward adjunction for `ringedSiteStructureMap α`;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFlatHom`,
  `ringedSiteStructureMap`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `SheafOfModules.unitToPushforwardObjUnit`,
  `Ideal.quotientMap`,
  `CategoryTheory.Subobject.arrow`;
- best owner abstraction: the ideal-sheaf side should be organized around the intrinsic owner
  `I : Subobject (SheafOfModules.unit (ringSheaf J 𝒪))`, with its sectionwise ideals derived from
  `I.arrow`, while the conclusion should remain the sheaf-level `IsIso` statement for the
  adjunction unit at `ℱ`;
- primitive data: a morphism `α : 𝒪 ⟶ 𝒪'`, an ideal sheaf
  `I : Subobject (SheafOfModules.unit (ringSheaf J 𝒪))`, and an `\mathcal O`-module `ℱ`;
- derived API: the ideal of sections cut out by `I` on each object, the sectionwise quotient-map
  hypothesis, and the sectionwise annihilation-by-a-power predicate.

Source/core/bridge triage:
- `source-facing`: the textbook base-change map
  `id ⊗ 1 : \mathcal F \to \mathcal F \otimes_{\mathcal O} \mathcal O'`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlatHom α`,
  `SheafOfModules.pullbackPushforwardAdjunction (ringedSiteStructureMap α)`, and the structure
  sheaf owner `SheafOfModules.unit (ringSheaf J 𝒪)` together with its subobjects;
- `bridge/view`: the sectionwise ideal `idealSectionIdeal I U`, derived from the subobject owner
  `I`, together with the induced quotient maps modulo that ideal.
-/

variable {C : Type u} [Category.{u} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {𝒪 𝒪' : Sheaf J CommRingCat.{u}}

/-- The ideal of sections over `U` cut out by an ideal sheaf
`I : \operatorname{Sub}(\mathcal O)`. -/
def idealSectionIdeal
    (I : Subobject (SheafOfModules.unit (ringSheaf J 𝒪)))
    (U : Cᵒᵖ) : Ideal ((ringSheaf J 𝒪).obj.obj U) :=
  { carrier := Set.range fun s : (I : SheafOfModules (ringSheaf J 𝒪)).val.obj U ↦
      (Hom.val I.arrow).app U s
    zero_mem' := ⟨0, by simpa using ((Hom.val I.arrow).app U).hom.map_zero⟩
    add_mem' := by
      rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
      exact ⟨x + y, by simpa using ((Hom.val I.arrow).app U).hom.map_add x y⟩
    smul_mem' := by
      rintro r _ ⟨x, rfl⟩
      exact ⟨r • x, by simpa using ((Hom.val I.arrow).app U).hom.map_smul r x⟩ }

/-- An `\mathcal O`-module is annihilated by `\mathcal I^n` when, on every object of the site,
the `n`th power of the ideal of sections cut out by `I` acts trivially on the corresponding
module of sections. -/
abbrev IsAnnihilatedByIdealSheafPower
    (I : Subobject (SheafOfModules.unit (ringSheaf J 𝒪)))
    (n : ℕ) (ℱ : SheafOfModules (ringSheaf J 𝒪)) : Prop :=
  ∀ U : Cᵒᵖ, idealSectionIdeal I U ^ n ≤
    Module.annihilator ((ringSheaf J 𝒪).obj.obj U) (ℱ.val.obj U)

-- Proof sketch: evaluate the sheaf-level base-change unit at each object `U`. The flatness
-- hypothesis is expressed by the chapter owner `IsFlatHom α`; the quotient and annihilation
-- assumptions are stated objectwise using the derived section ideals from `I`. Apply the module
-- statement from Lemma `15.90.2` to each section ring map `(α.hom.app U).hom`, then reassemble
-- these objectwise isomorphisms into the sheaf-level adjunction unit.
/-- Lemma 18.28.16: let `\mathcal C` be a site, let `\mathcal O \to \mathcal O'` be a flat
homomorphism of sheaves of rings, and let `\mathcal I \subset \mathcal O` be an ideal sheaf,
formalized by a subobject `I : \operatorname{Sub}(\mathcal O)`, such that
`\mathcal O/\mathcal I \to \mathcal O'/\mathcal I \mathcal O'` is an isomorphism. If an
`\mathcal O`-module `\mathcal F` is annihilated by `\mathcal I^n` for some `n ≥ 0`, then the
canonical base-change morphism
`id ⊗ 1 : \mathcal F \to \mathcal F \otimes_{\mathcal O} \mathcal O'`, formalized here as the
unit of the pullback/pushforward adjunction for `ringedSiteStructureMap α`, is an isomorphism. -/
theorem tensorBaseChangeUnit_isIso_of_isFlatHom_of_quotientMap_bijective_of_annihilated
    (α : 𝒪 ⟶ 𝒪')
    (hflat : IsFlatHom α)
    (I : Subobject (SheafOfModules.unit (ringSheaf J 𝒪)))
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (hquot : ∀ U : Cᵒᵖ,
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map ((α.hom.app U).hom) (idealSectionIdeal I U))
          ((α.hom.app U).hom)
          Ideal.le_comap_map))
    (hpow : ∃ n : ℕ, IsAnnihilatedByIdealSheafPower I n ℱ) :
    IsIso ((SheafOfModules.pullbackPushforwardAdjunction (ringedSiteStructureMap α)).unit.app ℱ) :=
  sorry

end SheafOfModules.RingedSite
