import Mathlib
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Stalk

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_17_21_3 (from Chap17) -/
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

/-! ### Lemma_17_21_4 (from Chap17) -/
open CategoryTheory
open AlgebraicGeometry
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.21.4:
- primary domain: symmetric and exterior power exact sequences of `\mathcal O_X`-modules on a
  ringed space;
- inspected owner declarations:
  `symmetricPowerMap`,
  `exteriorPowerMap`,
  `symmetricPowerLeftTensorMap`,
  `exteriorPowerLeftTensorMap`,
  `ShortComplex.ShortExact`,
  `symmetric_power_exact_of_exact`,
  `exterior_power_exact_of_exact`;
- best owner abstraction:
  the source-facing owner is a short complex in `RingedSpace.Modules X` built from the canonical
  sheaf owners `Symm[n]` and `Λ^[n]` together with their canonical sheaf-level comparison maps
  from `Lemma_17_21_1`; the module-theoretic exactness theorems from Chapter 10 are only the
  proof bridge;
- primitive-vs-derived split:
  primitive data are a short complex `S : ShortComplex ModX` and a degree `n : ℕ`;
  derived API consists of the sheaf-level power-operation maps already owned by
  `Lemma_17_21_1`, and the resulting short exact sequences.

Source/core/bridge triage:
- `source-facing`: the two exact sequences of sheaves
  `S.X₁ ⊗ Symm[n] S.X₂ ⟶ Symm[n + 1] S.X₂ ⟶ Symm[n + 1] S.X₃ ⟶ 0`
  and
  `S.X₁ ⊗ Λ^[n] S.X₂ ⟶ Λ^[n + 1] S.X₂ ⟶ Λ^[n + 1] S.X₃ ⟶ 0`;
- `core/canonical`: `Symm[n]`, `Λ^[n]`, `symmetricPowerMap`, `exteriorPowerMap`,
  `symmetricPowerLeftTensorMap`, `exteriorPowerLeftTensorMap`, and
  `ShortComplex.ShortExact`;
- `bridge/view`: the reduction to the module-valued exactness owners
  `symmetric_power_exact_of_exact` and `exterior_power_exact_of_exact`. -/

-- Proof sketch: the sectionwise composite is the canonical module-theoretic composite
-- `M₂ ⊗ Sym^n(M₁) → Sym^(n + 1)(M₁) → Sym^(n + 1)(M)` associated to `S.f(U)` and `S.g(U)`, which
-- vanishes by exactness in Chapter 10 after sheafifying.
/-- The canonical short complex
`S.X₁ ⊗ Symm[n] S.X₂ ⟶ Symm[n + 1] S.X₂ ⟶ Symm[n + 1] S.X₃`
attached to a short complex `S` of `\mathcal O_X`-modules. -/
noncomputable def symmetricPowerSequence
    (S : ShortComplex ModX) (n : ℕ) :
    ShortComplex ModX :=
  ShortComplex.mk
    (symmetricPowerLeftTensorMap n S.f)
    (symmetricPowerMap (n + 1) S.g)
    (by sorry)

-- Proof sketch: the sectionwise composite is the canonical module-theoretic composite
-- `M₂ ⊗ ⋀^n(M₁) → ⋀^(n + 1)(M₁) → ⋀^(n + 1)(M)` associated to `S.f(U)` and `S.g(U)`, which
-- vanishes by exactness in Chapter 10 after sheafifying.
/-- The canonical short complex
`S.X₁ ⊗ Λ^[n] S.X₂ ⟶ Λ^[n + 1] S.X₂ ⟶ Λ^[n + 1] S.X₃`
attached to a short complex `S` of `\mathcal O_X`-modules. -/
noncomputable def exteriorPowerSequence
    (S : ShortComplex ModX) (n : ℕ) :
    ShortComplex ModX :=
  ShortComplex.mk
    (exteriorPowerLeftTensorMap n S.f)
    (exteriorPowerMap (n + 1) S.g)
    (by sorry)

section

variable {S : ShortComplex ModX}

-- Proof sketch: after passing to the stalk at each point, the sequence identifies with the
-- module-theoretic symmetric-power exact sequence from Lemma `10.13.2`; exactness of sheaves of
-- modules is detected stalkwise.
/-- Lemma 17.21.4 (1), stated in degree `n + 1`: for a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of `\mathcal O_X`-modules, the canonical sequence
`S.X₁ ⊗ Symm[n] S.X₂ ⟶ Symm[n + 1] S.X₂ ⟶ Symm[n + 1] S.X₃ ⟶ 0`
is short exact in `RingedSpace.Modules X`. -/
theorem symmetricPowerSequence_shortExact
    (hS : S.ShortExact) (n : ℕ) :
    (symmetricPowerSequence S n).ShortExact := by
  sorry

-- Proof sketch: the same stalkwise reduction identifies the exterior-power sequence with the
-- module-theoretic exact sequence from Lemma `10.13.2`.
/-- Lemma 17.21.4 (2), stated in degree `n + 1`: for a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of `\mathcal O_X`-modules, the canonical sequence
`S.X₁ ⊗ Λ^[n] S.X₂ ⟶ Λ^[n + 1] S.X₂ ⟶ Λ^[n + 1] S.X₃ ⟶ 0`
is short exact in `RingedSpace.Modules X`. -/
theorem exteriorPowerSequence_shortExact
    (hS : S.ShortExact) (n : ℕ) :
    (exteriorPowerSequence S n).ShortExact := by
  sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_21_5 (from Chap17) -/
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.21.5:
- primary domain: tensor, exterior, and symmetric power operations on `\mathcal O_X`-modules on
  a ringed space, together with stability of local generation, finite type, finite presentation,
  coherence, quasi-coherence, and local freeness;
- inspected owner declarations:
  `tensorPowerSheaf`,
  `T^[n] ℱ`,
  `SheafOfModules.LocalGeneratorsData`,
  `moduleTensor_nonempty_localGeneratorsData`,
  `SheafOfModules.RingedSite.isFiniteType_ringedSiteModuleTensor`,
  `SheafOfModules.RingedSite.isQuasicoherent_ringedSiteModuleTensor`,
  `SheafOfModules.RingedSite.isFinitePresentation_ringedSiteModuleTensor`,
  `SheafOfModules.RingedSite.isLocallyFree_ringedSiteModuleTensor`,
  `symmetricPowerSequence_shortExact`,
  `exteriorPowerSequence_shortExact`;
- best owner abstraction:
  the source-facing power owners are the recursive tensor powers `T^[n] ℱ` together with the
  Chapter 17 owners `Λ^[n] ℱ` and `Symm[n] ℱ`; for local generation on ringed spaces the
  source-facing owner remains `Nonempty ℱ.LocalGeneratorsData`, while the other property clauses
  reuse the canonical owner predicates already attached to `X.Modules`;
- primitive data:
  a module sheaf `ℱ : ModX` and a degree `n : ℕ`;
- derived API:
  closure of local generation by sections, finite type, finite presentation, coherence,
  quasi-coherence, and local freeness under those power operations.

Source/core/bridge triage:
- `source-facing`: the three power operations and the Stacks assertions that they preserve the
  standard local finiteness and freeness properties;
- `core/canonical`: the owner category `X.Modules`, the recursive owner `tensorPowerSheaf`
  presented on the theorem surface as `T^[n] ℱ`, the sheaf power owners `Λ^[n]` and `Symm[n]`,
  the Chapter 17 owner `Nonempty ℱ.LocalGeneratorsData` for local generation, and the remaining
  Chapter 17/18 property owners on sheaves of modules;
- `bridge/view`: the local-generation proofs pass through Lemma `17.16.6`'s tensor-product bridge,
  which internally uses the Chapter 18 ringed-site class, and the exterior/symmetric clauses use
  the canonical quotient and exact-sequence bridges from Lemma `17.21.4`.
-/

section LocallyGeneratedBySections

variable (ℱ : ModX) (n : ℕ)

-- Proof sketch: argue by induction on `n`; the base case is the structure sheaf, and the
-- successor step applies Lemma `17.16.6 (1)` at the Chapter 17 owner
-- `Nonempty _.LocalGeneratorsData` to `ℱ ⊗ T^n(ℱ)`.
/-- Lemma 17.21.5 (1): if `\mathcal F` is locally generated by sections, then each tensor power
`\mathrm{T}^n(\mathcal F)` is locally generated by sections. -/
theorem tensorPowerSheaf_nonempty_localGeneratorsData
    (hℱ : Nonempty ℱ.LocalGeneratorsData) :
    Nonempty (T^[n] ℱ).LocalGeneratorsData := sorry

-- Proof sketch: `\bigwedge^n(\mathcal F)` is a quotient of `\mathrm{T}^n(\mathcal F)`, so local
-- generators descend from the tensor power at the same Chapter 17 owner layer.
/-- Lemma 17.21.5 (2): if `\mathcal F` is locally generated by sections, then each exterior power
`\bigwedge^n(\mathcal F)` is locally generated by sections. -/
theorem exteriorPowerSheaf_nonempty_localGeneratorsData
    (hℱ : Nonempty ℱ.LocalGeneratorsData) :
    Nonempty (Λ^[n] ℱ).LocalGeneratorsData := sorry

-- Proof sketch: `\operatorname{Sym}^n(\mathcal F)` is a quotient of `\mathrm{T}^n(\mathcal F)`,
-- so local generators descend from the tensor power at the same Chapter 17 owner layer.
/-- Lemma 17.21.5 (3): if `\mathcal F` is locally generated by sections, then each symmetric power
`\operatorname{Sym}^n(\mathcal F)` is locally generated by sections. -/
theorem symmetricPowerSheaf_nonempty_localGeneratorsData
    (hℱ : Nonempty ℱ.LocalGeneratorsData) :
    Nonempty (Symm[n] ℱ).LocalGeneratorsData := sorry

end LocallyGeneratedBySections

section FiniteType

variable (ℱ : ModX) (n : ℕ) [ℱ.IsFiniteType]

-- Proof sketch: induct on `n`; the base case is the unit sheaf, and the successor step applies
-- Lemma `17.16.6 (2)` to `ℱ ⊗ T^n(\mathcal F)`.
/-- Lemma 17.21.5 (4): if `\mathcal F` is of finite type, then each tensor power
`\mathrm{T}^n(\mathcal F)` is of finite type. -/
theorem tensorPowerSheaf_isFiniteType :
    (T^[n] ℱ).IsFiniteType := sorry

-- Proof sketch: exterior powers are quotients of tensor powers, and finite type descends to such
-- quotients.
/-- Lemma 17.21.5 (5): if `\mathcal F` is of finite type, then each exterior power
`\bigwedge^n(\mathcal F)` is of finite type. -/
theorem exteriorPowerSheaf_isFiniteType :
    (Λ^[n] ℱ).IsFiniteType := sorry

-- Proof sketch: symmetric powers are quotients of tensor powers, and finite type descends to such
-- quotients.
/-- Lemma 17.21.5 (6): if `\mathcal F` is of finite type, then each symmetric power
`\operatorname{Sym}^n(\mathcal F)` is of finite type. -/
theorem symmetricPowerSheaf_isFiniteType :
    (Symm[n] ℱ).IsFiniteType := sorry

end FiniteType

section FinitePresentation

variable (ℱ : ModX) (n : ℕ) [ℱ.IsFinitePresentation]

-- Proof sketch: induct on `n`; the base case is the unit sheaf, and the successor step applies
-- Lemma `17.16.6 (4)` to `ℱ ⊗ T^n(\mathcal F)`.
/-- Lemma 17.21.5 (7): if `\mathcal F` is of finite presentation, then each tensor power
`\mathrm{T}^n(\mathcal F)` is of finite presentation. -/
theorem tensorPowerSheaf_isFinitePresentation :
    (T^[n] ℱ).IsFinitePresentation := sorry

-- Proof sketch: Lemma `17.21.4` gives the standard presentation of exterior powers as quotients
-- of tensor powers, and finite presentation descends through that exact sequence.
/-- Lemma 17.21.5 (8): if `\mathcal F` is of finite presentation, then each exterior power
`\bigwedge^n(\mathcal F)` is of finite presentation. -/
theorem exteriorPowerSheaf_isFinitePresentation :
    (Λ^[n] ℱ).IsFinitePresentation := sorry

-- Proof sketch: Lemma `17.21.4` gives the standard presentation of symmetric powers as quotients
-- of tensor powers, and finite presentation descends through that exact sequence.
/-- Lemma 17.21.5 (9): if `\mathcal F` is of finite presentation, then each symmetric power
`\operatorname{Sym}^n(\mathcal F)` is of finite presentation. -/
theorem symmetricPowerSheaf_isFinitePresentation :
    (Symm[n] ℱ).IsFinitePresentation := sorry

end FinitePresentation

section Coherent

variable (ℱ : ModX) (n : ℕ) [ℱ.IsCoherent]

-- Proof sketch: for `n > 0`, induct on `n`; the first positive tensor power is `ℱ`, and the
-- successor step applies Lemma `17.16.6 (6)` to the coherent sheaves `ℱ` and `T^n(\mathcal F)`.
/-- Lemma 17.21.5 (10): if `\mathcal F` is coherent, then for `n > 0` the tensor power
`\mathrm{T}^n(\mathcal F)` is coherent. -/
theorem tensorPowerSheaf_isCoherent_of_pos
    (hn : 0 < n) :
    (T^[n] ℱ).IsCoherent := sorry

-- Proof sketch: use the exterior-power exact sequence from Lemma `17.21.4`, together with the
-- coherence of positive tensor powers and closure of coherent sheaves under cokernels.
/-- Lemma 17.21.5 (11): if `\mathcal F` is coherent, then for `n > 0` the exterior power
`\bigwedge^n(\mathcal F)` is coherent. -/
theorem exteriorPowerSheaf_isCoherent_of_pos
    (hn : 0 < n) :
    (Λ^[n] ℱ).IsCoherent := sorry

-- Proof sketch: use the symmetric-power exact sequence from Lemma `17.21.4`, together with the
-- coherence of positive tensor powers and closure of coherent sheaves under cokernels.
/-- Lemma 17.21.5 (12): if `\mathcal F` is coherent, then for `n > 0` the symmetric power
`\operatorname{Sym}^n(\mathcal F)` is coherent. -/
theorem symmetricPowerSheaf_isCoherent_of_pos
    (hn : 0 < n) :
    (Symm[n] ℱ).IsCoherent := sorry

end Coherent

section Quasicoherent

variable (ℱ : ModX) (n : ℕ) [ℱ.IsQuasicoherent]

-- Proof sketch: induct on `n`; the base case is the unit sheaf, and the successor step applies
-- Lemma `17.16.6 (3)` to `ℱ ⊗ T^n(\mathcal F)`.
/-- Lemma 17.21.5 (13): if `\mathcal F` is quasi-coherent, then each tensor power
`\mathrm{T}^n(\mathcal F)` is quasi-coherent. -/
theorem tensorPowerSheaf_isQuasicoherent :
    (T^[n] ℱ).IsQuasicoherent := sorry

-- Proof sketch: exterior powers are obtained from tensor powers by quotienting by the alternating
-- relations, and quasi-coherence is preserved under that construction.
/-- Lemma 17.21.5 (14): if `\mathcal F` is quasi-coherent, then each exterior power
`\bigwedge^n(\mathcal F)` is quasi-coherent. -/
theorem exteriorPowerSheaf_isQuasicoherent :
    (Λ^[n] ℱ).IsQuasicoherent := sorry

-- Proof sketch: symmetric powers are obtained from tensor powers by quotienting by the symmetric
-- relations, and quasi-coherence is preserved under that construction.
/-- Lemma 17.21.5 (15): if `\mathcal F` is quasi-coherent, then each symmetric power
`\operatorname{Sym}^n(\mathcal F)` is quasi-coherent. -/
theorem symmetricPowerSheaf_isQuasicoherent :
    (Symm[n] ℱ).IsQuasicoherent := sorry

end Quasicoherent

section LocallyFree

variable (ℱ : ModX) (n : ℕ) [ℱ.IsLocallyFree]

-- Proof sketch: induct on `n`; the base case is the locally free unit sheaf, and the successor
-- step applies Lemma `17.16.6 (7)` to `ℱ ⊗ T^n(\mathcal F)`.
/-- Lemma 17.21.5 (16): if `\mathcal F` is locally free, then each tensor power
`\mathrm{T}^n(\mathcal F)` is locally free. -/
theorem tensorPowerSheaf_isLocallyFree :
    (T^[n] ℱ).IsLocallyFree := sorry

-- Proof sketch: on a neighbourhood where `\mathcal F` is free, the exterior power of that free
-- module sheaf is again free, so the local trivializations descend to `\bigwedge^n(\mathcal F)`.
/-- Lemma 17.21.5 (17): if `\mathcal F` is locally free, then each exterior power
`\bigwedge^n(\mathcal F)` is locally free. -/
theorem exteriorPowerSheaf_isLocallyFree :
    (Λ^[n] ℱ).IsLocallyFree := sorry

-- Proof sketch: on a neighbourhood where `\mathcal F` is free, the symmetric power of that free
-- module sheaf is again free, so the local trivializations descend to `\operatorname{Sym}^n(\mathcal F)`.
/-- Lemma 17.21.5 (18): if `\mathcal F` is locally free, then each symmetric power
`\operatorname{Sym}^n(\mathcal F)` is locally free. -/
theorem symmetricPowerSheaf_isLocallyFree :
    (Symm[n] ℱ).IsLocallyFree := sorry

end LocallyFree

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_21_6 (from Chap17) -/
open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.21.6:
- primary domain: tensor, exterior, and symmetric algebra sheaves of `\mathcal O_X`-modules, and
  stability of quasi-coherence and local freeness under those algebra constructions;
- inspected owner declarations:
  `T(ℱ)`, `Λ(ℱ)`, `Symm(ℱ)` from `Lemma_17_21_3`,
  `tensorPowerSheaf_isQuasicoherent`,
  `exteriorPowerSheaf_isQuasicoherent`,
  `symmetricPowerSheaf_isQuasicoherent`,
  `tensorPowerSheaf_isLocallyFree`,
  `exteriorPowerSheaf_isLocallyFree`,
  `symmetricPowerSheaf_isLocallyFree` from `Lemma_17_21_5`,
  `ringedSpaceModule_isQuasicoherent_of_isLocallyFree`;
- best owner abstraction: the public owners are the already-defined algebra sheaves `T(ℱ)`, `Λ(ℱ)`,
  and `Symm(ℱ)` in `X.Modules`, while `IsQuasicoherent` and `IsLocallyFree` are the derived owner
  predicates that should be attached directly to those objects;
- primitive data: a module sheaf `ℱ : ModX`;
- derived API: the six closure instances below.

Source/core/bridge triage:
- `source-facing`: the six Stacks assertions that tensor, exterior, and symmetric algebra sheaves
  of a quasi-coherent or locally free module sheaf retain the same property;
- `core/canonical`: the owner objects `T(ℱ)`, `Λ(ℱ)`, `Symm(ℱ)` together with the predicates
  `( _ ).IsQuasicoherent` and `( _ ).IsLocallyFree` on `X.Modules`;
- `bridge/view`: proofs may use the power-sheaf closure results from `Lemma_17_21_5`, but the
  public surface should be owner-level instances on the algebra sheaves themselves, not parallel
  non-instance wrapper theorems.
-/ 

section Quasicoherent

variable (ℱ : ModX) [ℱ.IsQuasicoherent]

-- Proof sketch: quasi-coherence is checked locally on affine opens. On such a neighborhood,
-- `ℱ` comes from a module of sections, and the tensor algebra sheaf is the associated sheaf of
-- the ordinary tensor algebra of that module, so it remains quasi-coherent.
/-- Lemma 17.21.6 (1): if `\mathcal F` is quasi-coherent, then its tensor algebra
`\mathrm{T}(\mathcal F)` is quasi-coherent. -/
instance moduleTensorAlgebra_isQuasicoherent :
    (T(ℱ)).IsQuasicoherent := sorry

-- Proof sketch: after restricting to an affine open where `ℱ` is represented by a module `M`,
-- the sheaf `Λ(ℱ)` is the associated sheaf of the exterior algebra `Λ(M)`, hence is
-- quasi-coherent on that neighborhood.
/-- Lemma 17.21.6 (2): if `\mathcal F` is quasi-coherent, then its exterior algebra
`\bigwedge(\mathcal F)` is quasi-coherent. -/
instance moduleExteriorAlgebra_isQuasicoherent :
    (Λ(ℱ)).IsQuasicoherent := sorry

-- Proof sketch: on an affine neighborhood where `ℱ` comes from a module of sections, `Symm(ℱ)`
-- is the sheaf associated to the ordinary symmetric algebra of that module, which is again a
-- quasi-coherent module sheaf.
/-- Lemma 17.21.6 (3): if `\mathcal F` is quasi-coherent, then its symmetric algebra
`\operatorname{Sym}(\mathcal F)` is quasi-coherent. -/
instance moduleSymmetricAlgebra_isQuasicoherent :
    (Symm(ℱ)).IsQuasicoherent := sorry

end Quasicoherent

section LocallyFree

variable (ℱ : ModX) [ℱ.IsLocallyFree]

-- Proof sketch: once `ℱ` is free on an open neighbourhood, the proof of Lemma `17.21.5` shows
-- that the same neighbourhood makes every tensor power `T^n(ℱ)` free, so their direct sum
-- realizes the tensor algebra as locally free.
/-- Lemma 17.21.6 (4): if `\mathcal F` is locally free, then its tensor algebra
`\mathrm{T}(\mathcal F)` is locally free. -/
instance moduleTensorAlgebra_isLocallyFree :
    (T(ℱ)).IsLocallyFree := sorry

-- Proof sketch: on any neighbourhood where `ℱ` is free, all exterior powers `\bigwedge^n(ℱ)` are
-- free by the argument of Lemma `17.21.5`; summing these compatible local trivializations gives a
-- local trivialization of the exterior algebra itself.
/-- Lemma 17.21.6 (5): if `\mathcal F` is locally free, then its exterior algebra
`\bigwedge(\mathcal F)` is locally free. -/
instance moduleExteriorAlgebra_isLocallyFree :
    (Λ(ℱ)).IsLocallyFree := sorry

-- Proof sketch: on a neighbourhood where `ℱ` is free, all symmetric powers
-- `\operatorname{Sym}^n(ℱ)` are free by Lemma `17.21.5`, and their direct sum therefore gives a
-- free local model for the symmetric algebra.
/-- Lemma 17.21.6 (6): if `\mathcal F` is locally free, then its symmetric algebra
`\operatorname{Sym}(\mathcal F)` is locally free. -/
instance moduleSymmetricAlgebra_isLocallyFree :
    (Symm(ℱ)).IsLocallyFree := sorry

end LocallyFree

end AlgebraicGeometry.RingedSpace
