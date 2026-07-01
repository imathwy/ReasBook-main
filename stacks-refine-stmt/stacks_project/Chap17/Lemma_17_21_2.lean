import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import stacks_project.Chap17.Lemma_17_17_2
import stacks_project.Chap17.Lemma_17_21_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-
Domain-style sampling for Lemma 17.21.2:
- primary domain: algebra constructions on sheaves of modules over a ringed space and their
  behavior on stalks;
- inspected owner declarations:
  `RingedSpace.stalkModuleCat`,
  `moduleTensorAlgebra`,
  `moduleSymmetricAlgebra`,
  `moduleExteriorAlgebra`,
  `tensorProductStalkIso`;
- best owner abstraction: the source-facing content is a stalkwise comparison for the sheaf-side
  owners `T(ℱ)`, `Symm(ℱ)`, and `Λ(ℱ)`, with the stalk itself expressed through the existing
  bundled owner `RingedSpace.stalkModuleCat`;
- primitive data: a module sheaf `ℱ : X.Modules` and a point `x : X`;
- derived API: the three canonical stalk isomorphisms into the corresponding algebra objects
  formed from `RingedSpace.stalkModuleCat ℱ x`.

Source/core/bridge triage:
- `source-facing`: the three canonical stalk isomorphisms from the source text;
- `core/canonical`: `RingedSpace.stalkModuleCat` and the sheaf-side owners
  `moduleTensorAlgebra`, `moduleSymmetricAlgebra`, `moduleExteriorAlgebra`;
- `bridge/view`: the explicit presheaf-level filtered-colimit comparisons used internally to
  define the public stalk isomorphisms.

This file should therefore reuse `RingedSpace.stalkModuleCat` directly and expose the canonical
stalk comparisons themselves as the public API, rather than `Nonempty` wrappers around them.
-/

/-- The presheaf category underlying `\mathcal O_X`-modules on a ringed space. -/
private abbrev PresheafModules (X : RingedSpace.{u}) :=
  PresheafOfModules.{u} X.ringCatSheaf.obj

private abbrev stalkRing (x : X) :=
  X.presheaf.stalk x

private abbrev stalkRingGerm (U : Opens X) (x : X) (hx : x ∈ U) :=
  X.presheaf.germ U x hx

private def stalkGermLinear (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    ℱ.val.obj (op U) →ₛₗ[(stalkRingGerm U x hx).hom] ↑(stalkModuleCat ℱ x) where
  toFun := fun s ↦ (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) s
  map_add' := by
    intro s t
    simpa using (TopCat.Presheaf.germ ℱ.val.presheaf U x hx).hom.map_add s t
  map_smul' := by
    intro r s
    simpa using (PresheafOfModules.germ_smul ℱ.val x U hx r s)

/-- The objectwise tensor algebra module on an open set of a ringed space. -/
private abbrev tensorAlgebraPresheafObj (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
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
private noncomputable def tensorAlgebraPresheaf (ℱ : X.Modules) : PresheafModules X where
  obj := tensorAlgebraPresheafObj ℱ
  map := tensorAlgebraPresheafMap ℱ
  map_id := tensorAlgebraPresheaf_map_id ℱ
  map_comp := tensorAlgebraPresheaf_map_comp ℱ

/-- The objectwise symmetric algebra module on an open set of a ringed space. -/
private abbrev symmetricAlgebraPresheafObj (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
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
private noncomputable def symmetricAlgebraPresheaf (ℱ : X.Modules) : PresheafModules X where
  obj := symmetricAlgebraPresheafObj ℱ
  map := symmetricAlgebraPresheafMap ℱ
  map_id := symmetricAlgebraPresheaf_map_id ℱ
  map_comp := symmetricAlgebraPresheaf_map_comp ℱ

private abbrev stalkTensorAlgebra (ℱ : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x)
    (TensorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x))

private abbrev stalkSymmetricAlgebra (ℱ : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x)
    (SymmetricAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x))

private abbrev stalkExteriorAlgebra (ℱ : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x)
    (ExteriorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x))

private def tensorAlgebraGermLinear (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    let _ :
        Algebra (X.presheaf.obj (op U))
          (TensorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    ℱ.val.obj (op U) →ₗ[X.presheaf.obj (op U)]
      TensorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  let _ :
      Algebra (X.presheaf.obj (op U))
        (TensorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
    Algebra.compHom _ (stalkRingGerm U x hx).hom
  refine
    { toFun := fun m ↦
        TensorAlgebra.ι (X.presheaf.stalk x)
          ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)
      map_add' := ?_
      map_smul' := ?_ }
  · intro m n
    have h :
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) (m + n) =
          (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m +
            (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) n := by
      simpa using (TopCat.Presheaf.germ ℱ.val.presheaf U x hx).hom.map_add m n
    rw [h]
    simpa using (TensorAlgebra.ι (X.presheaf.stalk x)).map_add
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) n)
  · intro r m
    have h :
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) (r • m) =
          (stalkRingGerm U x hx) r • (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m := by
      simpa using PresheafOfModules.germ_smul ℱ.val x U hx r m
    rw [h]
    simpa using (TensorAlgebra.ι (X.presheaf.stalk x)).map_smul
      ((stalkRingGerm U x hx) r)
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)

private def symmetricAlgebraGermLinear (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    let _ :
        Algebra (X.presheaf.obj (op U))
          (SymmetricAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    ℱ.val.obj (op U) →ₗ[X.presheaf.obj (op U)]
      SymmetricAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  let _ :
      Algebra (X.presheaf.obj (op U))
        (SymmetricAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
    Algebra.compHom _ (stalkRingGerm U x hx).hom
  refine
    { toFun := fun m ↦
        SymmetricAlgebra.ι (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)
          ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)
      map_add' := ?_
      map_smul' := ?_ }
  · intro m n
    have h :
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) (m + n) =
          (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m +
            (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) n := by
      simpa using (TopCat.Presheaf.germ ℱ.val.presheaf U x hx).hom.map_add m n
    rw [h]
    simpa using (SymmetricAlgebra.ι (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)).map_add
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) n)
  · intro r m
    have h :
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) (r • m) =
          (stalkRingGerm U x hx) r • (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m := by
      simpa using PresheafOfModules.germ_smul ℱ.val x U hx r m
    rw [h]
    simpa using (SymmetricAlgebra.ι (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)).map_smul
      ((stalkRingGerm U x hx) r)
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)

private def exteriorAlgebraGermLinear (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    let _ :
        Algebra (X.presheaf.obj (op U))
          (ExteriorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    ℱ.val.obj (op U) →ₗ[X.presheaf.obj (op U)]
      ExteriorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  let _ :
      Algebra (X.presheaf.obj (op U))
        (ExteriorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
    Algebra.compHom _ (stalkRingGerm U x hx).hom
  refine
    { toFun := fun m ↦
        ExteriorAlgebra.ι (X.presheaf.stalk x)
          ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)
      map_add' := ?_
      map_smul' := ?_ }
  · intro m n
    have h :
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) (m + n) =
          (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m +
            (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) n := by
      simpa using (TopCat.Presheaf.germ ℱ.val.presheaf U x hx).hom.map_add m n
    rw [h]
    simpa using (ExteriorAlgebra.ι (X.presheaf.stalk x)).map_add
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) n)
  · intro r m
    have h :
        (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) (r • m) =
          (stalkRingGerm U x hx) r • (TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m := by
      simpa using PresheafOfModules.germ_smul ℱ.val x U hx r m
    rw [h]
    simpa using (ExteriorAlgebra.ι (X.presheaf.stalk x)).map_smul
      ((stalkRingGerm U x hx) r)
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m)

private theorem exteriorAlgebraGermLinear_sq_zero (ℱ : X.Modules) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    ∀ m : ℱ.val.obj (op U),
      exteriorAlgebraGermLinear ℱ x U hx m *
        exteriorAlgebraGermLinear ℱ x U hx m = 0 := by
  intro m
  simpa [exteriorAlgebraGermLinear] using
    (ExteriorAlgebra.ι_sq_zero
      ((TopCat.Presheaf.germ ℱ.val.presheaf U x hx) m))

private noncomputable def tensorAlgebraGermHom (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    (tensorAlgebraPresheaf ℱ).presheaf.obj (op U) ⟶ AddCommGrpCat.of ↑(stalkTensorAlgebra ℱ x) :=
  by
    let _ :
        Algebra (X.presheaf.obj (op U))
          (TensorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    exact AddCommGrpCat.ofHom <|
      (((TensorAlgebra.lift (X.presheaf.obj (op U))
        (tensorAlgebraGermLinear ℱ x U hx)).toLinearMap).toAddMonoidHom)

private noncomputable def symmetricAlgebraGermHom (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    (symmetricAlgebraPresheaf ℱ).presheaf.obj (op U) ⟶ AddCommGrpCat.of ↑(stalkSymmetricAlgebra ℱ x) :=
  by
    let _ :
        Algebra (X.presheaf.obj (op U))
          (SymmetricAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    exact AddCommGrpCat.ofHom <|
      (((SymmetricAlgebra.lift (symmetricAlgebraGermLinear ℱ x U hx)).toLinearMap).toAddMonoidHom)

private noncomputable def exteriorAlgebraGermHom (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    (exteriorAlgebraPresheaf ℱ).presheaf.obj (op U) ⟶ AddCommGrpCat.of ↑(stalkExteriorAlgebra ℱ x) :=
  by
    let _ :
        Algebra (X.presheaf.obj (op U))
          (ExteriorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    let e :
        ExteriorAlgebra (X.presheaf.obj (op U)) (ℱ.val.obj (op U)) →ₐ[X.presheaf.obj (op U)]
          ExteriorAlgebra (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) :=
      (ExteriorAlgebra.lift (X.presheaf.obj (op U)))
        ⟨exteriorAlgebraGermLinear ℱ x U hx, exteriorAlgebraGermLinear_sq_zero ℱ x U hx⟩
    exact AddCommGrpCat.ofHom <|
      (e.toLinearMap.toAddMonoidHom)

private noncomputable def tensorAlgebraNhdsGermHom
    (ℱ : X.Modules) (x : X) (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙ (tensorAlgebraPresheaf ℱ).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkTensorAlgebra ℱ x) := by
  exact show (((OpenNhds.inclusion x).op ⋙ (tensorAlgebraPresheaf ℱ).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkTensorAlgebra ℱ x) from
    tensorAlgebraGermHom ℱ x (Opposite.unop U).1 (Opposite.unop U).2

private noncomputable def symmetricAlgebraNhdsGermHom
    (ℱ : X.Modules) (x : X) (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙ (symmetricAlgebraPresheaf ℱ).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkSymmetricAlgebra ℱ x) := by
  exact show (((OpenNhds.inclusion x).op ⋙ (symmetricAlgebraPresheaf ℱ).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkSymmetricAlgebra ℱ x) from
    symmetricAlgebraGermHom ℱ x (Opposite.unop U).1 (Opposite.unop U).2

private noncomputable def exteriorAlgebraNhdsGermHom
    (ℱ : X.Modules) (x : X) (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙ (exteriorAlgebraPresheaf ℱ).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkExteriorAlgebra ℱ x) := by
  exact show (((OpenNhds.inclusion x).op ⋙ (exteriorAlgebraPresheaf ℱ).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkExteriorAlgebra ℱ x) from
    exteriorAlgebraGermHom ℱ x (Opposite.unop U).1 (Opposite.unop U).2

private theorem tensorAlgebraNhdsGermHom_naturality
    (ℱ : X.Modules) (x : X) {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙ (tensorAlgebraPresheaf ℱ).presheaf).map i) ≫
        tensorAlgebraNhdsGermHom ℱ x V =
      tensorAlgebraNhdsGermHom ℱ x U := sorry

private theorem symmetricAlgebraNhdsGermHom_naturality
    (ℱ : X.Modules) (x : X) {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙ (symmetricAlgebraPresheaf ℱ).presheaf).map i) ≫
        symmetricAlgebraNhdsGermHom ℱ x V =
      symmetricAlgebraNhdsGermHom ℱ x U := sorry

private theorem exteriorAlgebraNhdsGermHom_naturality
    (ℱ : X.Modules) (x : X) {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙ (exteriorAlgebraPresheaf ℱ).presheaf).map i) ≫
        exteriorAlgebraNhdsGermHom ℱ x V =
      exteriorAlgebraNhdsGermHom ℱ x U := sorry

private def presheafTensorAlgebraStalkComparison (ℱ : X.Modules) (x : X) :
    TopCat.Presheaf.stalk (tensorAlgebraPresheaf ℱ).presheaf x ⟶
      AddCommGrpCat.of ↑(stalkTensorAlgebra ℱ x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (tensorAlgebraPresheaf ℱ).presheaf) <|
    Cocone.mk _ <|
      { app := fun U ↦ tensorAlgebraNhdsGermHom ℱ x U
        naturality := by
          intro U V i
          exact tensorAlgebraNhdsGermHom_naturality ℱ x i }

private def presheafSymmetricAlgebraStalkComparison (ℱ : X.Modules) (x : X) :
    TopCat.Presheaf.stalk (symmetricAlgebraPresheaf ℱ).presheaf x ⟶
      AddCommGrpCat.of ↑(stalkSymmetricAlgebra ℱ x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (symmetricAlgebraPresheaf ℱ).presheaf) <|
    Cocone.mk _ <|
      { app := fun U ↦ symmetricAlgebraNhdsGermHom ℱ x U
        naturality := by
          intro U V i
          exact symmetricAlgebraNhdsGermHom_naturality ℱ x i }

private def presheafExteriorAlgebraStalkComparison (ℱ : X.Modules) (x : X) :
    TopCat.Presheaf.stalk (exteriorAlgebraPresheaf ℱ).presheaf x ⟶
      AddCommGrpCat.of ↑(stalkExteriorAlgebra ℱ x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (exteriorAlgebraPresheaf ℱ).presheaf) <|
    Cocone.mk _ <|
      { app := fun U ↦ exteriorAlgebraNhdsGermHom ℱ x U
        naturality := by
          intro U V i
          exact exteriorAlgebraNhdsGermHom_naturality ℱ x i }

-- Proof sketch: the unit map from the tensor-algebra presheaf to its sheafification becomes an
-- isomorphism on stalks; composing its inverse with the explicit filtered-colimit map from the
-- stalk of the presheaf tensor algebra to the tensor algebra on the stalk module yields the
-- canonical `\mathcal O_{X,x}`-linear comparison.
private noncomputable def tensorAlgebraStalkComparison_hom (ℱ : X.Modules) (x : X) :
    stalkModuleCat (T(ℱ)) x ⟶ stalkTensorAlgebra ℱ x := by
  letI : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    (inferInstance : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  letI :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    (inferInstance :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u})
  let η :
      TopCat.Presheaf.stalk (tensorAlgebraPresheaf ℱ).presheaf x ⟶
        TopCat.Presheaf.stalk (T(ℱ)).val.presheaf x :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (tensorAlgebraPresheaf ℱ).presheaf)
  haveI : IsIso η := by
    simpa [moduleTensorAlgebra, tensorAlgebraPresheaf] using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (tensorAlgebraPresheaf ℱ).presheaf)
  let comparison :
      TopCat.Presheaf.stalk (T(ℱ)).val.presheaf x ⟶ AddCommGrpCat.of ↑(stalkTensorAlgebra ℱ x) :=
    inv η ≫ presheafTensorAlgebraStalkComparison ℱ x
  exact ModuleCat.ofHom
    { toFun := comparison
      map_add' := by
        intro m n
        simpa [comparison] using comparison.hom.map_add m n
      map_smul' := by
        intro r m
        sorry }

private theorem tensorAlgebraStalkComparison_hom_isIso (ℱ : X.Modules) (x : X) :
    IsIso (tensorAlgebraStalkComparison_hom ℱ x) := sorry

-- Proof sketch: the same sheafification-on-stalks argument identifies the stalk of the symmetric
-- algebra sheaf with the stalk of the presheaf of symmetric algebras, and the latter maps
-- canonically to the symmetric algebra of the stalk module.
private noncomputable def symmetricAlgebraStalkComparison_hom (ℱ : X.Modules) (x : X) :
    stalkModuleCat (Symm(ℱ)) x ⟶ stalkSymmetricAlgebra ℱ x := by
  letI : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    (inferInstance : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  letI :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    (inferInstance :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u})
  let η :
      TopCat.Presheaf.stalk (symmetricAlgebraPresheaf ℱ).presheaf x ⟶
        TopCat.Presheaf.stalk (Symm(ℱ)).val.presheaf x :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (symmetricAlgebraPresheaf ℱ).presheaf)
  haveI : IsIso η := by
    simpa [moduleSymmetricAlgebra, symmetricAlgebraPresheaf] using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (symmetricAlgebraPresheaf ℱ).presheaf)
  let comparison :
      TopCat.Presheaf.stalk (Symm(ℱ)).val.presheaf x ⟶
        AddCommGrpCat.of ↑(stalkSymmetricAlgebra ℱ x) :=
    inv η ≫ presheafSymmetricAlgebraStalkComparison ℱ x
  exact ModuleCat.ofHom
    { toFun := comparison
      map_add' := by
        intro m n
        simpa [comparison] using comparison.hom.map_add m n
      map_smul' := by
        intro r m
        sorry }

private theorem symmetricAlgebraStalkComparison_hom_isIso (ℱ : X.Modules) (x : X) :
    IsIso (symmetricAlgebraStalkComparison_hom ℱ x) := sorry

-- Proof sketch: use the same sheafification-on-stalks argument for the exterior-algebra sheaf and
-- then compare the presheaf stalk with the exterior algebra generated by the stalk module.
private noncomputable def exteriorAlgebraStalkComparison_hom (ℱ : X.Modules) (x : X) :
    stalkModuleCat (Λ(ℱ)) x ⟶ stalkExteriorAlgebra ℱ x := by
  letI : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    (inferInstance : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  letI :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    (inferInstance :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u})
  let η :
      TopCat.Presheaf.stalk (exteriorAlgebraPresheaf ℱ).presheaf x ⟶
        TopCat.Presheaf.stalk (Λ(ℱ)).val.presheaf x :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (exteriorAlgebraPresheaf ℱ).presheaf)
  haveI : IsIso η := by
    simpa [moduleExteriorAlgebra, exteriorAlgebraPresheaf] using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (exteriorAlgebraPresheaf ℱ).presheaf)
  let comparison :
      TopCat.Presheaf.stalk (Λ(ℱ)).val.presheaf x ⟶ AddCommGrpCat.of ↑(stalkExteriorAlgebra ℱ x) :=
    inv η ≫ presheafExteriorAlgebraStalkComparison ℱ x
  exact ModuleCat.ofHom
    { toFun := comparison
      map_add' := by
        intro m n
        simpa [comparison] using comparison.hom.map_add m n
      map_smul' := by
        intro r m
        sorry }

private theorem exteriorAlgebraStalkComparison_hom_isIso (ℱ : X.Modules) (x : X) :
    IsIso (exteriorAlgebraStalkComparison_hom ℱ x) := sorry

-- Proof sketch: after constructing the comparison morphism and proving it is an isomorphism, take
-- its associated categorical isomorphism.
/-- Lemma 17.21.2 (1): the stalk of the tensor algebra sheaf of `\mathcal F` at `x` is canonically
isomorphic to the tensor algebra of the stalk `\mathcal F_x` over `\mathcal O_{X, x}`. -/
noncomputable opaque tensorAlgebraStalkIso (ℱ : X.Modules) (x : X) :
    stalkModuleCat (T(ℱ)) x ≅
      ModuleCat.of (X.presheaf.stalk x)
        (TensorAlgebra (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x)) :=
  by
    letI := tensorAlgebraStalkComparison_hom_isIso ℱ x
    exact asIso (tensorAlgebraStalkComparison_hom ℱ x)

-- Proof sketch: compose the symmetric-algebra comparison morphism with its `IsIso` witness.
/-- Lemma 17.21.2 (2): the stalk of the symmetric algebra sheaf of `\mathcal F` at `x` is
canonically isomorphic to the symmetric algebra of the stalk `\mathcal F_x` over
`\mathcal O_{X, x}`. -/
noncomputable opaque symmetricAlgebraStalkIso (ℱ : X.Modules) (x : X) :
    stalkModuleCat (Symm(ℱ)) x ≅
      ModuleCat.of (X.presheaf.stalk x)
        (SymmetricAlgebra (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x)) :=
  by
    letI := symmetricAlgebraStalkComparison_hom_isIso ℱ x
    exact asIso (symmetricAlgebraStalkComparison_hom ℱ x)

-- Proof sketch: compose the exterior-algebra comparison morphism with its `IsIso` witness.
/-- Lemma 17.21.2 (3): the stalk of the exterior algebra sheaf of `\mathcal F` at `x` is
canonically isomorphic to the exterior algebra of the stalk `\mathcal F_x` over
`\mathcal O_{X, x}`. -/
noncomputable opaque exteriorAlgebraStalkIso (ℱ : X.Modules) (x : X) :
    stalkModuleCat (Λ(ℱ)) x ≅
      ModuleCat.of (X.presheaf.stalk x)
        (ExteriorAlgebra (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x)) :=
  by
    letI := exteriorAlgebraStalkComparison_hom_isIso ℱ x
    exact asIso (exteriorAlgebraStalkComparison_hom ℱ x)

end AlgebraicGeometry.RingedSpace
