import Mathlib
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The presheaf category underlying `\mathcal O_X`-modules on a ringed space. -/
private abbrev PresheafModules (X : RingedSpace.{u}) :=
  PresheafOfModules.{u} X.ringCatSheaf.obj

variable {X Y : RingedSpace.{u}}

/- Domain-style sampling for Lemma 17.21.3:
- primary domain: pullback of module sheaves on ringed spaces and the comparison maps for tensor,
  exterior, and symmetric algebra sheaf constructions;
- sampled owner declarations:
  `RingedSpace.Hom.pullback`,
  `RingedSpace.Hom.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `PresheafOfModules.sheafificationAdjunction`;
- best owner abstraction: the source-facing content is an isomorphism in `X.Modules`
  obtained from the canonical pullback/pushforward adjunction, while the pushforward comparison
  morphism is auxiliary implementation data;
- primitive data: the objectwise algebra presheaf and the induced morphism into the pushforward of
  the pulled-back algebra sheaf;
- derived API: the three pullback comparison isomorphisms.

Source/core/bridge triage:
- `source-facing`: the three isomorphisms asserting that pullback commutes with tensor, exterior,
  and symmetric algebra sheaves;
- `core/canonical`: `f^*`, `f _*`, and `SheafOfModules.pullbackPushforwardAdjunction`;
- `bridge/view`: the auxiliary pushforward-side comparison morphisms constructed before applying
  the adjunction.

The public API should therefore expose only the `≅` statements as the owner declarations and keep
the raw comparison morphisms private.
-/

/-- The objectwise tensor algebra module on an open set of a ringed space. -/
private abbrev tensorAlgebraPresheafObj
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    ModuleCat (X.presheaf.obj U) :=
  ModuleCat.of (X.presheaf.obj U)
    (TensorAlgebra (X.presheaf.obj U) (ℱ.val.obj U))

/-- The linear map on sections induced by restriction for the tensor algebra presheaf. -/
private def tensorAlgebraRestrictionLinear
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    let _ :
        Algebra (X.presheaf.obj U) (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
      Algebra.compHom
        (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
        (X.presheaf.map i).hom
    ℱ.val.obj U →ₗ[X.presheaf.obj U] TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V) := by
  let _ :
      Algebra (X.presheaf.obj U) (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  refine
    { toFun := fun m ↦
        TensorAlgebra.ι (X.presheaf.obj V)
          (show ℱ.val.obj V from (ℱ.val.map i).hom m)
      map_add' := ?_
      map_smul' := ?_ }
  · sorry
  · sorry

/-- The restriction map for the tensor algebra presheaf. -/
private noncomputable def tensorAlgebraPresheafMap
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    tensorAlgebraPresheafObj ℱ U ⟶
      (ModuleCat.restrictScalars (X.presheaf.map i).hom).obj
        (tensorAlgebraPresheafObj ℱ V) := by
  let _ :
      Algebra (X.presheaf.obj U) (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  exact
    (show tensorAlgebraPresheafObj ℱ U ⟶
        ModuleCat.of (X.presheaf.obj U) (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) from
      ModuleCat.ofHom
        ((TensorAlgebra.lift (X.presheaf.obj U)
          (tensorAlgebraRestrictionLinear ℱ i)).toLinearMap))

/-- The tensor algebra restriction maps satisfy the identity axiom of a presheaf of modules. -/
private theorem tensorAlgebraPresheaf_map_id
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    tensorAlgebraPresheafMap ℱ (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (tensorAlgebraPresheafObj ℱ U) := sorry

/-- The tensor algebra restriction maps satisfy the composition axiom of a presheaf of modules. -/
private theorem tensorAlgebraPresheaf_map_comp
    (ℱ : X.Modules) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    tensorAlgebraPresheafMap ℱ (i ≫ j) =
      tensorAlgebraPresheafMap ℱ i ≫
        (ModuleCat.restrictScalars _).map (tensorAlgebraPresheafMap ℱ j) ≫
          (ModuleCat.restrictScalarsComp' (X.presheaf.map i).hom
            (X.presheaf.map j).hom
            (X.presheaf.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom <| X.presheaf.map_comp i j)).inv.app
            (tensorAlgebraPresheafObj ℱ W) := sorry

/-- The presheaf of tensor algebras associated to an `\mathcal O_X`-module. -/
private noncomputable def tensorAlgebraPresheaf
    (ℱ : X.Modules) : PresheafModules X where
  obj := tensorAlgebraPresheafObj ℱ
  map := tensorAlgebraPresheafMap ℱ
  map_id := tensorAlgebraPresheaf_map_id ℱ
  map_comp := tensorAlgebraPresheaf_map_comp ℱ

/-- The tensor algebra sheaf associated to an `\mathcal O_X`-module. -/
noncomputable abbrev moduleTensorAlgebra
    (ℱ : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (tensorAlgebraPresheaf ℱ)

/-- The objectwise symmetric algebra module on an open set of a ringed space. -/
private abbrev symmetricAlgebraPresheafObj
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    ModuleCat (X.presheaf.obj U) :=
  ModuleCat.of (X.presheaf.obj U)
    (SymmetricAlgebra (X.presheaf.obj U) (ℱ.val.obj U))

/-- The linear map on sections induced by restriction for the symmetric algebra presheaf. -/
private def symmetricAlgebraRestrictionLinear
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    let _ :
        Algebra (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
      Algebra.compHom
        (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
        (X.presheaf.map i).hom
    ℱ.val.obj U →ₗ[X.presheaf.obj U] SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V) := by
  let _ :
      Algebra (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  refine
    { toFun := fun m ↦
        SymmetricAlgebra.ι (X.presheaf.obj V) (ℱ.val.obj V)
          (show ℱ.val.obj V from (ℱ.val.map i).hom m)
      map_add' := ?_
      map_smul' := ?_ }
  · sorry
  · sorry

/-- The restriction map for the symmetric algebra presheaf. -/
private noncomputable def symmetricAlgebraPresheafMap
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    symmetricAlgebraPresheafObj ℱ U ⟶
      (ModuleCat.restrictScalars (X.presheaf.map i).hom).obj
        (symmetricAlgebraPresheafObj ℱ V) := by
  let _ :
      Algebra (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  exact
    (show symmetricAlgebraPresheafObj ℱ U ⟶
        ModuleCat.of (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) from
      ModuleCat.ofHom
        ((SymmetricAlgebra.lift (symmetricAlgebraRestrictionLinear ℱ i)).toLinearMap))

/-- The symmetric algebra restriction maps satisfy the identity axiom of a presheaf of modules. -/
private theorem symmetricAlgebraPresheaf_map_id
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    symmetricAlgebraPresheafMap ℱ (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (symmetricAlgebraPresheafObj ℱ U) := sorry

/-- The symmetric algebra restriction maps satisfy the composition axiom of a presheaf of
modules. -/
private theorem symmetricAlgebraPresheaf_map_comp
    (ℱ : X.Modules) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    symmetricAlgebraPresheafMap ℱ (i ≫ j) =
      symmetricAlgebraPresheafMap ℱ i ≫
        (ModuleCat.restrictScalars _).map (symmetricAlgebraPresheafMap ℱ j) ≫
          (ModuleCat.restrictScalarsComp' (X.presheaf.map i).hom
            (X.presheaf.map j).hom
            (X.presheaf.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom <| X.presheaf.map_comp i j)).inv.app
            (symmetricAlgebraPresheafObj ℱ W) := sorry

/-- The presheaf of symmetric algebras associated to an `\mathcal O_X`-module. -/
private noncomputable def symmetricAlgebraPresheaf
    (ℱ : X.Modules) : PresheafModules X where
  obj := symmetricAlgebraPresheafObj ℱ
  map := symmetricAlgebraPresheafMap ℱ
  map_id := symmetricAlgebraPresheaf_map_id ℱ
  map_comp := symmetricAlgebraPresheaf_map_comp ℱ

/-- The symmetric algebra sheaf associated to an `\mathcal O_X`-module. -/
noncomputable abbrev moduleSymmetricAlgebra
    (ℱ : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (symmetricAlgebraPresheaf ℱ)

/-- The objectwise exterior algebra module on an open set of a ringed space. -/
private abbrev exteriorAlgebraPresheafObj
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    ModuleCat (X.presheaf.obj U) :=
  ModuleCat.of (X.presheaf.obj U)
    (ExteriorAlgebra (X.presheaf.obj U) (ℱ.val.obj U))

/-- The linear map on sections induced by restriction for the exterior algebra presheaf. -/
private def exteriorAlgebraRestrictionLinear
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    let _ :
        Algebra (X.presheaf.obj U) (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
      Algebra.compHom
        (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
        (X.presheaf.map i).hom
    ℱ.val.obj U →ₗ[X.presheaf.obj U] ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V) := by
  let _ :
      Algebra (X.presheaf.obj U) (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  refine
    { toFun := fun m ↦
        ExteriorAlgebra.ι (X.presheaf.obj V)
          (show ℱ.val.obj V from (ℱ.val.map i).hom m)
      map_add' := ?_
      map_smul' := ?_ }
  · sorry
  · sorry

/-- The exterior restriction map squares to zero on generators. -/
private theorem exteriorAlgebraRestrictionLinear_sq_zero
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ∀ m : ℱ.val.obj U,
      exteriorAlgebraRestrictionLinear ℱ i m *
        exteriorAlgebraRestrictionLinear ℱ i m = 0 := sorry

/-- The restriction map for the exterior algebra presheaf. -/
private noncomputable def exteriorAlgebraPresheafMap
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    exteriorAlgebraPresheafObj ℱ U ⟶
      (ModuleCat.restrictScalars (X.presheaf.map i).hom).obj
        (exteriorAlgebraPresheafObj ℱ V) := by
  let _ :
      Algebra (X.presheaf.obj U) (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  exact
    (show exteriorAlgebraPresheafObj ℱ U ⟶
        ModuleCat.of (X.presheaf.obj U) (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) from
      ModuleCat.ofHom
        ((ExteriorAlgebra.lift (X.presheaf.obj U)
          ⟨exteriorAlgebraRestrictionLinear ℱ i,
            exteriorAlgebraRestrictionLinear_sq_zero ℱ i⟩).toLinearMap))

/-- The exterior algebra restriction maps satisfy the identity axiom of a presheaf of modules. -/
private theorem exteriorAlgebraPresheaf_map_id
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    exteriorAlgebraPresheafMap ℱ (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (exteriorAlgebraPresheafObj ℱ U) := sorry

/-- The exterior algebra restriction maps satisfy the composition axiom of a presheaf of
modules. -/
private theorem exteriorAlgebraPresheaf_map_comp
    (ℱ : X.Modules) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    exteriorAlgebraPresheafMap ℱ (i ≫ j) =
      exteriorAlgebraPresheafMap ℱ i ≫
        (ModuleCat.restrictScalars _).map (exteriorAlgebraPresheafMap ℱ j) ≫
          (ModuleCat.restrictScalarsComp' (X.presheaf.map i).hom
            (X.presheaf.map j).hom
            (X.presheaf.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom <| X.presheaf.map_comp i j)).inv.app
            (exteriorAlgebraPresheafObj ℱ W) := sorry

/-- The presheaf `U ↦ \bigwedge_{\mathcal O_X(U)} \mathcal F(U)` whose sheafification is the
exterior algebra sheaf `Λ(ℱ)`. This is the bridge/view owner used to construct morphisms on
`Λ(ℱ)` by sheafifying natural transformations on sections. -/
noncomputable def exteriorAlgebraPresheaf
    (ℱ : X.Modules) : PresheafModules X where
  obj := exteriorAlgebraPresheafObj ℱ
  map := exteriorAlgebraPresheafMap ℱ
  map_id := exteriorAlgebraPresheaf_map_id ℱ
  map_comp := exteriorAlgebraPresheaf_map_comp ℱ

/-- The exterior algebra sheaf associated to an `\mathcal O_X`-module. -/
noncomputable abbrev moduleExteriorAlgebra
    (ℱ : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (exteriorAlgebraPresheaf ℱ)

end AlgebraicGeometry.RingedSpace

scoped[AlgebraicGeometry] notation3:max "T(" ℱ ")" =>
  AlgebraicGeometry.RingedSpace.moduleTensorAlgebra ℱ
scoped[AlgebraicGeometry] notation3:max "Λ(" ℱ ")" =>
  AlgebraicGeometry.RingedSpace.moduleExteriorAlgebra ℱ
scoped[AlgebraicGeometry] notation3:max "Symm(" ℱ ")" =>
  AlgebraicGeometry.RingedSpace.moduleSymmetricAlgebra ℱ

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

private abbrev preimageOpen (f : X ⟶ Y) (U : (Opens Y)ᵒᵖ) : (Opens X)ᵒᵖ :=
  op ((Opens.map f.hom.base).obj U.unop)

private abbrev preimageRingHom (f : X ⟶ Y) (U : (Opens Y)ᵒᵖ) :
    Y.presheaf.obj U →+* X.presheaf.obj (preimageOpen f U) :=
  let f' := f.hom
  (f'.c.app U).hom

private abbrev pullbackUnit (f : X ⟶ Y) (ℱ : Y.Modules) :
    ℱ ⟶ (f _*).obj ((f^*).obj ℱ) :=
  (SheafOfModules.pullbackPushforwardAdjunction
    (toRingCatSheafHom f)).unit.app ℱ

private def tensorAlgebraPushforwardGeneratorLinear
    (f : X ⟶ Y) (ℱ : Y.Modules) (U : (Opens Y)ᵒᵖ) :
    let _ :
        Algebra (Y.presheaf.obj U)
          (TensorAlgebra (X.presheaf.obj (preimageOpen f U))
            (((f^*).obj ℱ).val.obj (preimageOpen f U))) :=
      Algebra.compHom
        (TensorAlgebra (X.presheaf.obj (preimageOpen f U))
          (((f^*).obj ℱ).val.obj (preimageOpen f U)))
        (preimageRingHom f U)
    ℱ.val.obj U →ₗ[Y.presheaf.obj U]
      TensorAlgebra (X.presheaf.obj (preimageOpen f U))
        (((f^*).obj ℱ).val.obj (preimageOpen f U)) := by
  let _ :
      Algebra (Y.presheaf.obj U)
        (TensorAlgebra (X.presheaf.obj (preimageOpen f U))
          (((f^*).obj ℱ).val.obj (preimageOpen f U))) :=
    Algebra.compHom
      (TensorAlgebra (X.presheaf.obj (preimageOpen f U))
        (((f^*).obj ℱ).val.obj (preimageOpen f U)))
      (preimageRingHom f U)
  refine
    { toFun := fun m ↦
        TensorAlgebra.ι (X.presheaf.obj (preimageOpen f U))
          (show ((f^*).obj ℱ).val.obj (preimageOpen f U) from
            (pullbackUnit f ℱ).val.app U m)
      map_add' := ?_
      map_smul' := ?_ }
  · sorry
  · sorry

private noncomputable def tensorAlgebraPresheafPushforwardHom
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    tensorAlgebraPresheaf ℱ ⟶
      (PresheafOfModules.pushforward (toRingCatSheafHom f).hom).obj
        (tensorAlgebraPresheaf ((f^*).obj ℱ)) where
  app U := by
    let _ :
        Algebra (Y.presheaf.obj U)
          (TensorAlgebra (X.presheaf.obj (preimageOpen f U))
            (((f^*).obj ℱ).val.obj (preimageOpen f U))) :=
      Algebra.compHom
        (TensorAlgebra (X.presheaf.obj (preimageOpen f U))
          (((f^*).obj ℱ).val.obj (preimageOpen f U)))
        (preimageRingHom f U)
    exact
      (show tensorAlgebraPresheafObj ℱ U ⟶
          (ModuleCat.restrictScalars (preimageRingHom f U)).obj
            (tensorAlgebraPresheafObj ((f^*).obj ℱ) (preimageOpen f U)) from
        ModuleCat.ofHom
          ((TensorAlgebra.lift (Y.presheaf.obj U)
            (tensorAlgebraPushforwardGeneratorLinear f ℱ U)).toLinearMap))
  naturality {U V} i := by
    sorry

private noncomputable def tensorAlgebraPresheafToPushforwardModuleTensorAlgebra
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    tensorAlgebraPresheaf ℱ ⟶
      ((f _*).obj (moduleTensorAlgebra ((f^*).obj ℱ))).val :=
  tensorAlgebraPresheafPushforwardHom f ℱ ≫
    (PresheafOfModules.pushforward (toRingCatSheafHom f).hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (tensorAlgebraPresheaf ((f^*).obj ℱ)))

private noncomputable def tensorAlgebraToPushforwardModuleTensorAlgebra
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    moduleTensorAlgebra ℱ ⟶ (f _*).obj (moduleTensorAlgebra ((f^*).obj ℱ)) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).symm
    (tensorAlgebraPresheafToPushforwardModuleTensorAlgebra f ℱ)

private def symmetricAlgebraPushforwardGeneratorLinear
    (f : X ⟶ Y) (ℱ : Y.Modules) (U : (Opens Y)ᵒᵖ) :
    let _ :
        Algebra (Y.presheaf.obj U)
          (SymmetricAlgebra (X.presheaf.obj (preimageOpen f U))
            (((f^*).obj ℱ).val.obj (preimageOpen f U))) :=
      Algebra.compHom
        (SymmetricAlgebra (X.presheaf.obj (preimageOpen f U))
          (((f^*).obj ℱ).val.obj (preimageOpen f U)))
        (preimageRingHom f U)
    ℱ.val.obj U →ₗ[Y.presheaf.obj U]
      SymmetricAlgebra (X.presheaf.obj (preimageOpen f U))
        (((f^*).obj ℱ).val.obj (preimageOpen f U)) := by
  let _ :
      Algebra (Y.presheaf.obj U)
        (SymmetricAlgebra (X.presheaf.obj (preimageOpen f U))
          (((f^*).obj ℱ).val.obj (preimageOpen f U))) :=
    Algebra.compHom
      (SymmetricAlgebra (X.presheaf.obj (preimageOpen f U))
        (((f^*).obj ℱ).val.obj (preimageOpen f U)))
      (preimageRingHom f U)
  refine
    { toFun := fun m ↦
        SymmetricAlgebra.ι
          (X.presheaf.obj (preimageOpen f U))
          (((f^*).obj ℱ).val.obj (preimageOpen f U))
          (show ((f^*).obj ℱ).val.obj (preimageOpen f U) from
            (pullbackUnit f ℱ).val.app U m)
      map_add' := ?_
      map_smul' := ?_ }
  · sorry
  · sorry

private noncomputable def symmetricAlgebraPresheafPushforwardHom
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    symmetricAlgebraPresheaf ℱ ⟶
      (PresheafOfModules.pushforward (toRingCatSheafHom f).hom).obj
        (symmetricAlgebraPresheaf ((f^*).obj ℱ)) where
  app U := by
    let _ :
        Algebra (Y.presheaf.obj U)
          (SymmetricAlgebra (X.presheaf.obj (preimageOpen f U))
            (((f^*).obj ℱ).val.obj (preimageOpen f U))) :=
      Algebra.compHom
        (SymmetricAlgebra (X.presheaf.obj (preimageOpen f U))
          (((f^*).obj ℱ).val.obj (preimageOpen f U)))
        (preimageRingHom f U)
    exact
      (show symmetricAlgebraPresheafObj ℱ U ⟶
          (ModuleCat.restrictScalars (preimageRingHom f U)).obj
            (symmetricAlgebraPresheafObj ((f^*).obj ℱ) (preimageOpen f U)) from
        ModuleCat.ofHom
          ((SymmetricAlgebra.lift
            (symmetricAlgebraPushforwardGeneratorLinear f ℱ U)).toLinearMap))
  naturality {U V} i := by
    sorry

private noncomputable def symmetricAlgebraPresheafToPushforwardModuleSymmetricAlgebra
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    symmetricAlgebraPresheaf ℱ ⟶
      ((f _*).obj (moduleSymmetricAlgebra ((f^*).obj ℱ))).val :=
  symmetricAlgebraPresheafPushforwardHom f ℱ ≫
    (PresheafOfModules.pushforward (toRingCatSheafHom f).hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (symmetricAlgebraPresheaf ((f^*).obj ℱ)))

private noncomputable def symmetricAlgebraToPushforwardModuleSymmetricAlgebra
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    moduleSymmetricAlgebra ℱ ⟶
      (f _*).obj (moduleSymmetricAlgebra ((f^*).obj ℱ)) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).symm
    (symmetricAlgebraPresheafToPushforwardModuleSymmetricAlgebra f ℱ)

private def exteriorAlgebraPushforwardGeneratorLinear
    (f : X ⟶ Y) (ℱ : Y.Modules) (U : (Opens Y)ᵒᵖ) :
    let _ :
        Algebra (Y.presheaf.obj U)
          (ExteriorAlgebra (X.presheaf.obj (preimageOpen f U))
            (((f^*).obj ℱ).val.obj (preimageOpen f U))) :=
      Algebra.compHom
        (ExteriorAlgebra (X.presheaf.obj (preimageOpen f U))
          (((f^*).obj ℱ).val.obj (preimageOpen f U)))
        (preimageRingHom f U)
    ℱ.val.obj U →ₗ[Y.presheaf.obj U]
      ExteriorAlgebra (X.presheaf.obj (preimageOpen f U))
        (((f^*).obj ℱ).val.obj (preimageOpen f U)) := by
  let _ :
      Algebra (Y.presheaf.obj U)
        (ExteriorAlgebra (X.presheaf.obj (preimageOpen f U))
          (((f^*).obj ℱ).val.obj (preimageOpen f U))) :=
    Algebra.compHom
      (ExteriorAlgebra (X.presheaf.obj (preimageOpen f U))
        (((f^*).obj ℱ).val.obj (preimageOpen f U)))
      (preimageRingHom f U)
  refine
    { toFun := fun m ↦
        ExteriorAlgebra.ι (X.presheaf.obj (preimageOpen f U))
          (show ((f^*).obj ℱ).val.obj (preimageOpen f U) from
            (pullbackUnit f ℱ).val.app U m)
      map_add' := ?_
      map_smul' := ?_ }
  · sorry
  · sorry

private theorem exteriorAlgebraPushforwardGeneratorLinear_sq_zero
    (f : X ⟶ Y) (ℱ : Y.Modules) (U : (Opens Y)ᵒᵖ) :
    ∀ m : ℱ.val.obj U,
      exteriorAlgebraPushforwardGeneratorLinear f ℱ U m *
        exteriorAlgebraPushforwardGeneratorLinear f ℱ U m = 0 := sorry

private noncomputable def exteriorAlgebraPresheafPushforwardHom
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    exteriorAlgebraPresheaf ℱ ⟶
      (PresheafOfModules.pushforward (toRingCatSheafHom f).hom).obj
        (exteriorAlgebraPresheaf ((f^*).obj ℱ)) where
  app U := by
    let _ :
        Algebra (Y.presheaf.obj U)
          (ExteriorAlgebra (X.presheaf.obj (preimageOpen f U))
            (((f^*).obj ℱ).val.obj (preimageOpen f U))) :=
      Algebra.compHom
        (ExteriorAlgebra (X.presheaf.obj (preimageOpen f U))
          (((f^*).obj ℱ).val.obj (preimageOpen f U)))
        (preimageRingHom f U)
    exact
      (show exteriorAlgebraPresheafObj ℱ U ⟶
          (ModuleCat.restrictScalars (preimageRingHom f U)).obj
            (exteriorAlgebraPresheafObj ((f^*).obj ℱ) (preimageOpen f U)) from
        ModuleCat.ofHom
          ((ExteriorAlgebra.lift (Y.presheaf.obj U)
            ⟨exteriorAlgebraPushforwardGeneratorLinear f ℱ U,
              exteriorAlgebraPushforwardGeneratorLinear_sq_zero f ℱ U⟩).toLinearMap))
  naturality {U V} i := by
    sorry

private noncomputable def exteriorAlgebraPresheafToPushforwardModuleExteriorAlgebra
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    exteriorAlgebraPresheaf ℱ ⟶
      ((f _*).obj (moduleExteriorAlgebra ((f^*).obj ℱ))).val :=
  exteriorAlgebraPresheafPushforwardHom f ℱ ≫
    (PresheafOfModules.pushforward (toRingCatSheafHom f).hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (exteriorAlgebraPresheaf ((f^*).obj ℱ)))

private noncomputable def exteriorAlgebraToPushforwardModuleExteriorAlgebra
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    moduleExteriorAlgebra ℱ ⟶
      (f _*).obj (moduleExteriorAlgebra ((f^*).obj ℱ)) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).symm
    (exteriorAlgebraPresheafToPushforwardModuleExteriorAlgebra f ℱ)

-- Proof sketch: form the tensor algebra presheaf objectwise, note that pullback is built from
-- inverse image and extension of scalars, and compare both sides using the universal property of
-- the tensor algebra after passing through sheafification.
/-- The auxiliary comparison morphism underlying `pullback_moduleTensorAlgebra`. -/
private noncomputable def pullback_moduleTensorAlgebra_hom
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    ((f^*).obj (moduleTensorAlgebra ℱ)) ⟶ moduleTensorAlgebra ((f^*).obj ℱ) :=
  ((SheafOfModules.pullbackPushforwardAdjunction
      (toRingCatSheafHom f)).homEquiv _ _).symm
    (tensorAlgebraToPushforwardModuleTensorAlgebra f ℱ)

private theorem pullback_moduleTensorAlgebra_hom_isIso
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    IsIso (pullback_moduleTensorAlgebra_hom f ℱ) := by
  sorry

/-- Lemma 17.21.3 (1): pullback commutes with the tensor algebra of a sheaf of modules. -/
noncomputable abbrev pullback_moduleTensorAlgebra
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    ((f^*).obj T(ℱ)) ≅ T((f^*).obj ℱ) := by
  letI := pullback_moduleTensorAlgebra_hom_isIso f ℱ
  exact asIso (pullback_moduleTensorAlgebra_hom f ℱ)

-- Proof sketch: define exterior algebras by sheafifying the objectwise exterior algebra
-- presheaf; the pullback comparison is induced from the tensor algebra comparison and the
-- compatibility of pullback with the alternating quotient relations.
/-- The auxiliary comparison morphism underlying `pullback_moduleExteriorAlgebra`. -/
private noncomputable def pullback_moduleExteriorAlgebra_hom
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    ((f^*).obj (moduleExteriorAlgebra ℱ)) ⟶ moduleExteriorAlgebra ((f^*).obj ℱ) :=
  ((SheafOfModules.pullbackPushforwardAdjunction
      (toRingCatSheafHom f)).homEquiv _ _).symm
    (exteriorAlgebraToPushforwardModuleExteriorAlgebra f ℱ)

private theorem pullback_moduleExteriorAlgebra_hom_isIso
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    IsIso (pullback_moduleExteriorAlgebra_hom f ℱ) := by
  sorry

/-- Lemma 17.21.3 (2): pullback commutes with the exterior algebra of a sheaf of modules. -/
noncomputable abbrev pullback_moduleExteriorAlgebra
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    ((f^*).obj Λ(ℱ)) ≅ Λ((f^*).obj ℱ) := by
  letI := pullback_moduleExteriorAlgebra_hom_isIso f ℱ
  exact asIso (pullback_moduleExteriorAlgebra_hom f ℱ)

-- Proof sketch: define symmetric algebras by sheafifying the objectwise symmetric algebra
-- presheaf; then pullback preserves the tensor algebra and the commutator quotient, giving the
-- canonical comparison isomorphism.
/-- The auxiliary comparison morphism underlying `pullback_moduleSymmetricAlgebra`. -/
private noncomputable def pullback_moduleSymmetricAlgebra_hom
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    ((f^*).obj (moduleSymmetricAlgebra ℱ)) ⟶ moduleSymmetricAlgebra ((f^*).obj ℱ) :=
  ((SheafOfModules.pullbackPushforwardAdjunction
      (toRingCatSheafHom f)).homEquiv _ _).symm
    (symmetricAlgebraToPushforwardModuleSymmetricAlgebra f ℱ)

private theorem pullback_moduleSymmetricAlgebra_hom_isIso
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    IsIso (pullback_moduleSymmetricAlgebra_hom f ℱ) := by
  sorry

/-- Lemma 17.21.3 (3): pullback commutes with the symmetric algebra of a sheaf of modules. -/
noncomputable abbrev pullback_moduleSymmetricAlgebra
    (f : X ⟶ Y) (ℱ : Y.Modules) :
    ((f^*).obj Symm(ℱ)) ≅ Symm((f^*).obj ℱ) := by
  letI := pullback_moduleSymmetricAlgebra_hom_isIso f ℱ
  exact asIso (pullback_moduleSymmetricAlgebra_hom f ℱ)

end AlgebraicGeometry.RingedSpace
