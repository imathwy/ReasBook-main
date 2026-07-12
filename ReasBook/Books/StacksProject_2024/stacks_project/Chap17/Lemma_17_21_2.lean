import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import StacksProject_2024.Chap10.Lemma_10_13_5
import StacksProject_2024.Chap17.AlgebraSheafConstructions
import StacksProject_2024.Chap17.Lemma_17_3_2
import StacksProject_2024.Chap18.Lemma_18_36_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-
Domain-style sampling for Lemma 17.21.2:
- primary domain: algebra constructions on sheaves of modules over a ringed space and their
  behavior on stalks;
- inspected owner declarations:
  `RingedSpace.stalkModuleCat`,
  `moduleTensorAlgebra`,
  `moduleSymmetricAlgebra`,
  `moduleExteriorAlgebra`,
  `tensorAlgebraPresheaf`,
  `symmetricAlgebraPresheaf`,
  `exteriorAlgebraPresheaf`,
  `tensorProductStalkIso`;
- best owner abstraction: the source-facing content is a stalkwise comparison for the sheaf-side
  owners `T(ℱ)`, `Symm(ℱ)`, and `Λ(ℱ)`, with the stalk itself expressed through the existing
  bundled owner `RingedSpace.stalkModuleCat`, and with the bridge presheaves reused directly from
  `Lemma_17_21_3`;
- primitive data: a module sheaf `ℱ : X.Modules` and a point `x : X`;
- derived API: the three canonical stalk isomorphisms into the corresponding algebra objects
  formed from `RingedSpace.stalkModuleCat ℱ x`.

Source/core/bridge triage:
- `source-facing`: the three canonical stalk isomorphisms from the source text;
- `core/canonical`: `RingedSpace.stalkModuleCat` and the sheaf-side owners
  `moduleTensorAlgebra`, `moduleSymmetricAlgebra`, `moduleExteriorAlgebra`;
- `bridge/view`: the explicit presheaf-level filtered-colimit comparisons used internally to
  define the public stalk isomorphisms.

This file should therefore reuse `RingedSpace.stalkModuleCat` and the algebra-presheaf owners from
`Lemma_17_21_3` directly, and expose the canonical stalk comparisons themselves as the public API,
rather than `Nonempty` wrappers around them.
-/

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

private abbrev stalkTensorAlgebra (ℱ : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x)
    (TensorAlgebra (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x))

private abbrev stalkSymmetricAlgebra (ℱ : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x)
    (SymmetricAlgebra (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x))

private abbrev stalkExteriorAlgebra (ℱ : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x)
    (ExteriorAlgebra (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x))

private def tensorAlgebraGermLinear (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    let _ :
        Algebra (X.presheaf.obj (op U))
          (TensorAlgebra (stalkRing x) ↑(stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    ℱ.val.obj (op U) →ₗ[X.presheaf.obj (op U)]
      TensorAlgebra (stalkRing x) ↑(stalkModuleCat ℱ x) := by
  let _ :
      Algebra (X.presheaf.obj (op U))
        (TensorAlgebra (stalkRing x) ↑(stalkModuleCat ℱ x)) :=
    Algebra.compHom _ (stalkRingGerm U x hx).hom
  refine
    { toFun := fun m ↦
        TensorAlgebra.ι (stalkRing x) (stalkGermLinear ℱ x U hx m)
      map_add' := ?_
      map_smul' := ?_ }
  · intro m n
    rw [show stalkGermLinear ℱ x U hx (m + n) =
        stalkGermLinear ℱ x U hx m + stalkGermLinear ℱ x U hx n by
      simpa using (stalkGermLinear ℱ x U hx).map_add m n]
    simpa using
      (TensorAlgebra.ι (stalkRing x)).map_add
        (stalkGermLinear ℱ x U hx m)
        (stalkGermLinear ℱ x U hx n)
  · intro r m
    rw [show stalkGermLinear ℱ x U hx (r • m) =
        (stalkRingGerm U x hx) r • stalkGermLinear ℱ x U hx m by
      simpa using (stalkGermLinear ℱ x U hx).map_smulₛₗ r m]
    simpa using
      (TensorAlgebra.ι (stalkRing x)).map_smul
        ((stalkRingGerm U x hx) r)
        (stalkGermLinear ℱ x U hx m)

private def symmetricAlgebraGermLinear (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    let _ :
        Algebra (X.presheaf.obj (op U))
          (SymmetricAlgebra (stalkRing x) ↑(stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    ℱ.val.obj (op U) →ₗ[X.presheaf.obj (op U)]
      SymmetricAlgebra (stalkRing x) ↑(stalkModuleCat ℱ x) := by
  let _ :
      Algebra (X.presheaf.obj (op U))
        (SymmetricAlgebra (stalkRing x) ↑(stalkModuleCat ℱ x)) :=
    Algebra.compHom _ (stalkRingGerm U x hx).hom
  refine
    { toFun := fun m ↦
        SymmetricAlgebra.ι (stalkRing x) ↑(stalkModuleCat ℱ x)
          (stalkGermLinear ℱ x U hx m)
      map_add' := ?_
      map_smul' := ?_ }
  · intro m n
    rw [show stalkGermLinear ℱ x U hx (m + n) =
        stalkGermLinear ℱ x U hx m + stalkGermLinear ℱ x U hx n by
      simpa using (stalkGermLinear ℱ x U hx).map_add m n]
    simpa using
      (SymmetricAlgebra.ι (stalkRing x) ↑(stalkModuleCat ℱ x)).map_add
        (stalkGermLinear ℱ x U hx m)
        (stalkGermLinear ℱ x U hx n)
  · intro r m
    rw [show stalkGermLinear ℱ x U hx (r • m) =
        (stalkRingGerm U x hx) r • stalkGermLinear ℱ x U hx m by
      simpa using (stalkGermLinear ℱ x U hx).map_smulₛₗ r m]
    simpa using
      (SymmetricAlgebra.ι (stalkRing x) ↑(stalkModuleCat ℱ x)).map_smul
        ((stalkRingGerm U x hx) r)
        (stalkGermLinear ℱ x U hx m)

private def exteriorAlgebraGermLinear (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    let _ :
        Algebra (X.presheaf.obj (op U))
          (ExteriorAlgebra (stalkRing x) ↑(stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    ℱ.val.obj (op U) →ₗ[X.presheaf.obj (op U)]
      ExteriorAlgebra (stalkRing x) ↑(stalkModuleCat ℱ x) := by
  let _ :
      Algebra (X.presheaf.obj (op U))
        (ExteriorAlgebra (stalkRing x) ↑(stalkModuleCat ℱ x)) :=
    Algebra.compHom _ (stalkRingGerm U x hx).hom
  refine
    { toFun := fun m ↦
        ExteriorAlgebra.ι (stalkRing x) (stalkGermLinear ℱ x U hx m)
      map_add' := ?_
      map_smul' := ?_ }
  · intro m n
    rw [show stalkGermLinear ℱ x U hx (m + n) =
        stalkGermLinear ℱ x U hx m + stalkGermLinear ℱ x U hx n by
      simpa using (stalkGermLinear ℱ x U hx).map_add m n]
    simpa using
      (ExteriorAlgebra.ι (stalkRing x)).map_add
        (stalkGermLinear ℱ x U hx m)
        (stalkGermLinear ℱ x U hx n)
  · intro r m
    rw [show stalkGermLinear ℱ x U hx (r • m) =
        (stalkRingGerm U x hx) r • stalkGermLinear ℱ x U hx m by
      simpa using (stalkGermLinear ℱ x U hx).map_smulₛₗ r m]
    simpa using
      (ExteriorAlgebra.ι (stalkRing x)).map_smul
        ((stalkRingGerm U x hx) r)
        (stalkGermLinear ℱ x U hx m)

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem exteriorAlgebraGermLinear_sq_zero (ℱ : X.Modules) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    ∀ m : ℱ.val.obj (op U),
      exteriorAlgebraGermLinear ℱ x U hx m *
        exteriorAlgebraGermLinear ℱ x U hx m = 0 := by
  intro m
  simpa [exteriorAlgebraGermLinear] using
    (ExteriorAlgebra.ι_sq_zero (stalkGermLinear ℱ x U hx m))

private noncomputable def tensorAlgebraGermHom (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    (tensorAlgebraPresheaf ℱ).presheaf.obj (op U) ⟶ AddCommGrpCat.of ↑(stalkTensorAlgebra ℱ x) :=
  by
    let _ :
        Algebra (X.presheaf.obj (op U))
          (TensorAlgebra (stalkRing x) ↑(stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    exact AddCommGrpCat.ofHom <|
      (((TensorAlgebra.lift (X.presheaf.obj (op U))
        (tensorAlgebraGermLinear ℱ x U hx)).toLinearMap).toAddMonoidHom)

private noncomputable def symmetricAlgebraGermHom (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    (symmetricAlgebraPresheaf ℱ).presheaf.obj (op U) ⟶ AddCommGrpCat.of ↑(stalkSymmetricAlgebra ℱ x) :=
  by
    let _ :
        Algebra (X.presheaf.obj (op U))
          (SymmetricAlgebra (stalkRing x) ↑(stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    exact AddCommGrpCat.ofHom <|
      (((SymmetricAlgebra.lift (symmetricAlgebraGermLinear ℱ x U hx)).toLinearMap).toAddMonoidHom)

private noncomputable def exteriorAlgebraGermHom (ℱ : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U) :
    (exteriorAlgebraPresheaf ℱ).presheaf.obj (op U) ⟶ AddCommGrpCat.of ↑(stalkExteriorAlgebra ℱ x) :=
  by
    let _ :
        Algebra (X.presheaf.obj (op U))
          (ExteriorAlgebra (stalkRing x) ↑(stalkModuleCat ℱ x)) :=
      Algebra.compHom _ (stalkRingGerm U x hx).hom
    let e :
        ExteriorAlgebra (X.presheaf.obj (op U)) (ℱ.val.obj (op U)) →ₐ[X.presheaf.obj (op U)]
          ExteriorAlgebra (stalkRing x) ↑(stalkModuleCat ℱ x) :=
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

/-- Helper for Lemma 17.21.2: the tensor-algebra stalk target is definitionally the tensor algebra
on the stalk module. -/
private theorem stalkTensorAlgebra_val
    (ℱ : X.Modules) (x : X) :
    ↑(stalkTensorAlgebra ℱ x) =
      TensorAlgebra (X.presheaf.stalk x) ↑(stalkModuleCat ℱ x) := rfl

/-- Helper for Lemma 17.21.2: forgetting the commutative-ring structure commutes with taking the
ordinary stalk at `x`. -/
private noncomputable abbrev commRingStalkToRingStalkIso
    (x : X) :
    (forget₂ CommRingCat RingCat).obj (TopCat.Presheaf.stalk X.presheaf x) ≅
      (RingedSpace.ringCatSheaf X).presheaf.stalk x :=
  CategoryTheory.preservesColimitIso (forget₂ CommRingCat RingCat)
    ((OpenNhds.inclusion x).op ⋙ X.presheaf)

/-- Helper for Lemma 17.21.2: the ordinary stalk of a presheaf of modules carries its canonical
`\mathcal O_{X, x}`-module structure. -/
private noncomputable instance presheafStalkModule
    (P : PresheafOfModules X.ringCatSheaf.obj) (x : X) :
    Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk P.presheaf x) :=
  by
    -- Proof comment: first use the built-in module structure over the `RingCat` stalk of the
    -- forgotten structure sheaf, then transport scalars back along the canonical stalk ring iso.
    letI : Module ((RingedSpace.ringCatSheaf X).presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk P.presheaf x) := by
      infer_instance
    let e := (commRingStalkToRingStalkIso (X := X) x).ringCatIsoToRingEquiv
    exact Module.compHom ↑(TopCat.Presheaf.stalk P.presheaf x) e.toRingHom

/-- Helper for Lemma 17.21.2: a morphism of module presheaves induces the corresponding map on
ordinary stalks, viewed with the explicit source and target stalk objects. -/
private noncomputable def presheafStalkMap
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (x : X) (φ : P ⟶ Q) :
    TopCat.Presheaf.stalk P.presheaf x ⟶ TopCat.Presheaf.stalk Q.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ)

/-- Helper for Lemma 17.21.2: the ordinary stalk map induced by a morphism of module presheaves
is linear over `\mathcal O_{X, x}`. -/
private theorem presheafStalkMap_map_smul
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (x : X) (φ : P ⟶ Q)
    (r : X.presheaf.stalk x) (m : ↑(TopCat.Presheaf.stalk P.presheaf x)) :
    presheafStalkMap (X := X) x φ (r • m) =
      r • presheafStalkMap (X := X) x φ m := by
  obtain ⟨U, hxU, rU, hrU⟩ := TopCat.Presheaf.germ_exist X.presheaf x r
  obtain ⟨V, hxV, mV, hmV⟩ := TopCat.Presheaf.germ_exist P.presheaf x m
  let W : Opens X := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  let rW : X.presheaf.obj (op W) := X.presheaf.map iWU.op rU
  let mW : P.obj (op W) := P.map iWV.op mV
  have hrW : r = X.presheaf.germ W x hxW rW := by
    -- Proof comment: rewrite the scalar germ on the common refinement `W = U ∩ V`.
    calc
      r = X.presheaf.germ U x hxU rU := hrU.symm
      _ = X.presheaf.germ W x hxW rW := by
        rw [show rW = X.presheaf.map iWU.op rU by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply X.presheaf iWU x hxW rU
  have hmW : m = TopCat.Presheaf.germ P.presheaf W x hxW mW := by
    -- Proof comment: rewrite the module germ on the same common refinement.
    calc
      m = TopCat.Presheaf.germ P.presheaf V x hxV mV := hmV.symm
      _ = TopCat.Presheaf.germ P.presheaf W x hxW mW := by
        rw [show mW = P.map iWV.op mV by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply P.presheaf iWV x hxW mV
  rw [hrW, hmW]
  -- Proof comment: compare both sides on the common representative and use germwise
  -- compatibility of `φ` with scalar multiplication.
  calc
    presheafStalkMap (X := X) x φ
        (X.presheaf.germ W x hxW rW • TopCat.Presheaf.germ P.presheaf W x hxW mW) =
      presheafStalkMap (X := X) x φ
        (TopCat.Presheaf.germ P.presheaf W x hxW (rW • mW)) := by
          exact congrArg (presheafStalkMap (X := X) x φ)
            (PresheafOfModules.germ_smul P x W hxW rW mW).symm
    _ =
      TopCat.Presheaf.germ Q.presheaf W x hxW ((φ.app (op W)) (rW • mW)) := by
        simpa [presheafStalkMap] using
          (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
            ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ) (rW • mW))
    _ =
      TopCat.Presheaf.germ Q.presheaf W x hxW (rW • (φ.app (op W)) mW) := by
        simpa using (φ.app (op W)).hom.map_smul rW mW
    _ =
      X.presheaf.germ W x hxW rW •
        TopCat.Presheaf.germ Q.presheaf W x hxW ((φ.app (op W)) mW) := by
          exact PresheafOfModules.germ_smul Q x W hxW rW ((φ.app (op W)) mW)
    _ =
      X.presheaf.germ W x hxW rW •
        presheafStalkMap (X := X) x φ
          (TopCat.Presheaf.germ P.presheaf W x hxW mW) := by
            simpa [presheafStalkMap] using
              (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
                ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ) mW).symm

/-- Helper for Lemma 17.21.2: a morphism of module presheaves induces a morphism of the
corresponding stalk modules over `\mathcal O_{X, x}`. -/
private noncomputable def presheafStalkHom
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (x : X) (φ : P ⟶ Q) :
    ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk P.presheaf x) ⟶
      ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk Q.presheaf x) :=
  ModuleCat.ofHom
    { toFun := presheafStalkMap (X := X) x φ
      map_add' := by
        intro m n
        exact (presheafStalkMap (X := X) x φ).hom.map_add m n
      map_smul' := by
        intro r m
        simpa using presheafStalkMap_map_smul (X := X) x φ r m }

/-- Helper for Lemma 17.21.2: the stalk map of the sheafification unit is bijective on the
underlying additive groups. -/
private theorem sheafificationUnitStalkMap_bijective
    (P : PresheafOfModules X.ringCatSheaf.obj) (x : X) :
    Function.Bijective
      (presheafStalkMap (X := X) x
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)) := by
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
  have hη :
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map η =
        CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf := by
    -- Proof comment: forgetting the module sheafification unit gives the additive unit.
    simpa [η] using
      (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
        (𝟙 X.ringCatSheaf.obj) P)
  have hη_iso :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map η)) := by
    -- Proof comment: the additive sheafification unit is an isomorphism on stalks.
    rw [hη]
    simpa using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P.presheaf)
  let fη :
      TopCat.Presheaf.stalk P.presheaf x ⟶
        TopCat.Presheaf.stalk
          (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).val.presheaf) x :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map η)
  have hη_iso' : IsIso fη := by
    simpa [fη] using hη_iso
  have hη_bijective :
      Function.Bijective (ConcreteCategory.hom fη) :=
    (CategoryTheory.isIso_iff_bijective fη).1 hη_iso'
  simpa [presheafStalkMap, η, fη] using hη_bijective

/-- Helper for Lemma 17.21.2: the stalk of a sheafified module presheaf identifies with the stalk
of the underlying module presheaf. -/
private noncomputable def presheafSheafificationStalkIso
    (P : PresheafOfModules X.ringCatSheaf.obj) (x : X) :
    stalkModuleCat ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) x ≅
      ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk P.presheaf x) :=
  by
    let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
    let f :
        ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk P.presheaf x) ⟶
          stalkModuleCat ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) x :=
      presheafStalkHom (X := X) x η
    have hf_bijective : Function.Bijective f.hom := by
      -- Proof comment: the linear map is the sheafification-unit stalk map with the explicit
      -- module structure packaged around the same underlying function.
      simpa [f, presheafStalkHom] using
        sheafificationUnitStalkMap_bijective (X := X) P x
    -- Proof comment: convert the bijective linear map into a linear equivalence, then package it
    -- as the requested categorical isomorphism in the reverse direction.
    exact (LinearEquiv.ofBijective f.hom hf_bijective).toModuleIso.symm

/-- Helper for Lemma 17.21.2: the tensor-algebra presheaf stalk is canonically the tensor algebra
of the stalk module. -/
private noncomputable def tensorAlgebraPresheafStalkIso
    (ℱ : X.Modules) (x : X) :
    ModuleCat.of (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (tensorAlgebraPresheaf ℱ).presheaf x) ≅
      stalkTensorAlgebra ℱ x :=
  -- TODO: express the tensor-algebra presheaf stalk as the filtered colimit of neighborhood
  -- tensor algebras and compare it with `TensorAlgebra` of the module stalk via preserved
  -- colimits; this is blocked on the missing sheafification-stalk adapter above.
  sorry

/-- Helper for Lemma 17.21.2: the symmetric-algebra presheaf stalk is canonically the symmetric
algebra of the stalk module. -/
private noncomputable def symmetricAlgebraPresheafStalkIso
    (ℱ : X.Modules) (x : X) :
    ModuleCat.of (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (symmetricAlgebraPresheaf ℱ).presheaf x) ≅
      stalkSymmetricAlgebra ℱ x :=
  -- TODO: follow the tensor-algebra route with `SymmetricAlgebra.functor`; the unresolved input is
  -- still the module-valued sheafification-stalk comparison needed to stay in one stalk spelling.
  sorry

/-- Helper for Lemma 17.21.2: the exterior-algebra presheaf stalk is canonically the exterior
algebra of the stalk module. -/
private noncomputable def exteriorAlgebraPresheafStalkIso
    (ℱ : X.Modules) (x : X) :
    ModuleCat.of (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (exteriorAlgebraPresheaf ℱ).presheaf x) ≅
      stalkExteriorAlgebra ℱ x :=
  -- TODO: repeat the preserved-colimit comparison for `ExteriorAlgebra`, using
  -- `exteriorAlgebraGermLinear_sq_zero` on generators once the ordinary sheafification-stalk
  -- bridge is available.
  sorry

-- Route correction: keep the final comparison morphisms expressed as the composition of the
-- sheafification-stalk adapter with the presheaf-stalk algebra comparison, so the remaining gap is
-- isolated to the dedicated bridge isomorphisms above.
private noncomputable def tensorAlgebraStalkComparison_hom (ℱ : X.Modules) (x : X) :
    stalkModuleCat (T(ℱ)) x ⟶ stalkTensorAlgebra ℱ x :=
  (presheafSheafificationStalkIso (P := tensorAlgebraPresheaf ℱ) x).hom ≫
    (tensorAlgebraPresheafStalkIso ℱ x).hom

private theorem tensorAlgebraStalkComparison_hom_isIso (ℱ : X.Modules) (x : X) :
    IsIso (tensorAlgebraStalkComparison_hom ℱ x) := by
  -- Proof comment: the comparison morphism is a composite of two explicit isomorphisms.
  dsimp [tensorAlgebraStalkComparison_hom]
  infer_instance

private noncomputable def symmetricAlgebraStalkComparison_hom (ℱ : X.Modules) (x : X) :
    stalkModuleCat (Symm(ℱ)) x ⟶ stalkSymmetricAlgebra ℱ x :=
  (presheafSheafificationStalkIso (P := symmetricAlgebraPresheaf ℱ) x).hom ≫
    (symmetricAlgebraPresheafStalkIso ℱ x).hom

private theorem symmetricAlgebraStalkComparison_hom_isIso (ℱ : X.Modules) (x : X) :
    IsIso (symmetricAlgebraStalkComparison_hom ℱ x) := by
  -- Proof comment: the symmetric comparison is again a composite of the two bridge isomorphisms.
  dsimp [symmetricAlgebraStalkComparison_hom]
  infer_instance

private noncomputable def exteriorAlgebraStalkComparison_hom (ℱ : X.Modules) (x : X) :
    stalkModuleCat (Λ(ℱ)) x ⟶ stalkExteriorAlgebra ℱ x :=
  (presheafSheafificationStalkIso (P := exteriorAlgebraPresheaf ℱ) x).hom ≫
    (exteriorAlgebraPresheafStalkIso ℱ x).hom

private theorem exteriorAlgebraStalkComparison_hom_isIso (ℱ : X.Modules) (x : X) :
    IsIso (exteriorAlgebraStalkComparison_hom ℱ x) := by
  -- Proof comment: the exterior comparison is a composite of the same two abstract bridge steps.
  dsimp [exteriorAlgebraStalkComparison_hom]
  infer_instance

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
