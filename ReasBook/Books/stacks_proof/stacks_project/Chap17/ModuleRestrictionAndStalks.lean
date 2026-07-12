import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Lattice
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice
open AlgebraicGeometry
open Opposite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X

noncomputable abbrev moduleRestrictionMap
    {ℱ 𝒢 : ModX}
    (U : Opens X) (φ : ℱ ⟶ 𝒢) :
    ℱ.over U ⟶ 𝒢.over U :=
  (SheafOfModules.pushforward (𝟙 (Sheaf.over (RingedSpace.ringCatSheaf X) U))).map φ

scoped[ModuleRestriction] notation:max φ " |_ " U => RingedSpace.moduleRestrictionMap U φ

noncomputable abbrev moduleStalkMap
    {ℱ 𝒢 : ModX}
    (x : X) (φ : ℱ ⟶ 𝒢) :
    TopCat.Presheaf.stalk ℱ.val.presheaf x ⟶ TopCat.Presheaf.stalk 𝒢.val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val)

private theorem moduleStalkMap_map_add
    (x : X) {ℱ 𝒢 : ModX} (φ : ℱ ⟶ 𝒢)
    (m n : ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x)) :
    RingedSpace.moduleStalkMap x φ (m + n) =
      RingedSpace.moduleStalkMap x φ m + RingedSpace.moduleStalkMap x φ n := by
  simpa using (RingedSpace.moduleStalkMap x φ).hom.map_add m n

theorem moduleStalkMap_germ
    {ℱ 𝒢 : ModX} (x : X) (φ : ℱ ⟶ 𝒢)
    (U : Opens X) (hx : x ∈ U) (s : ℱ.val.obj (op U)) :
    RingedSpace.moduleStalkMap x φ (TopCat.Presheaf.germ ℱ.val.presheaf U x hx s) =
      TopCat.Presheaf.germ 𝒢.val.presheaf U x hx ((φ.val.app (op U)) s) := by
  simpa [RingedSpace.moduleStalkMap] using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
      ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val) s)

private theorem moduleStalkMap_map_smul
    (x : X) {ℱ 𝒢 : ModX} (φ : ℱ ⟶ 𝒢)
    (r : X.presheaf.stalk x)
    (m : ↑(RingedSpace.stalkModuleCat ℱ x)) :
    RingedSpace.moduleStalkMap x φ (r • m) =
      r • RingedSpace.moduleStalkMap x φ m := by
  obtain ⟨U, hxU, rU, hrU⟩ := TopCat.Presheaf.germ_exist X.presheaf x r
  obtain ⟨V, hxV, mV, hmV⟩ := TopCat.Presheaf.germ_exist ℱ.val.presheaf x m
  let W : Opens X := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  let rW : X.presheaf.obj (op W) := X.presheaf.map iWU.op rU
  let mW : ℱ.val.obj (op W) := ℱ.val.map iWV.op mV
  have hrW : r = X.presheaf.germ W x hxW rW := by
    -- Rewrite the scalar germ on the common refinement `W = U ∩ V`.
    calc
      r = X.presheaf.germ U x hxU rU := hrU.symm
      _ = X.presheaf.germ W x hxW rW := by
        rw [show rW = X.presheaf.map iWU.op rU by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply X.presheaf iWU x hxW rU
  have hmW : m = TopCat.Presheaf.germ ℱ.val.presheaf W x hxW mW := by
    -- Rewrite the module germ on the same common refinement.
    calc
      m = TopCat.Presheaf.germ ℱ.val.presheaf V x hxV mV := hmV.symm
      _ = TopCat.Presheaf.germ ℱ.val.presheaf W x hxW mW := by
        rw [show mW = ℱ.val.map iWV.op mV by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply ℱ.val.presheaf iWV x hxW mV
  rw [hrW, hmW]
  -- Evaluate both sides on the common representative and use germwise compatibility with scalar
  -- multiplication.
  calc
    RingedSpace.moduleStalkMap x φ
        (X.presheaf.germ W x hxW rW •
          TopCat.Presheaf.germ ℱ.val.presheaf W x hxW mW) =
      RingedSpace.moduleStalkMap x φ
        (TopCat.Presheaf.germ ℱ.val.presheaf W x hxW (rW • mW)) := by
          exact congrArg (RingedSpace.moduleStalkMap x φ)
            (PresheafOfModules.germ_smul ℱ.val x W hxW rW mW).symm
    _ =
      TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW
        ((φ.val.app (op W)) (rW • mW)) := by
          rw [RingedSpace.moduleStalkMap_germ x φ W hxW (rW • mW)]
    _ =
      TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW
        (rW • (φ.val.app (op W)) mW) := by
          simpa using (φ.val.app (op W)).hom.map_smul rW mW
    _ =
      X.presheaf.germ W x hxW rW •
        TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW ((φ.val.app (op W)) mW) := by
          exact PresheafOfModules.germ_smul 𝒢.val x W hxW rW ((φ.val.app (op W)) mW)
    _ =
      X.presheaf.germ W x hxW rW •
        RingedSpace.moduleStalkMap x φ
          (TopCat.Presheaf.germ ℱ.val.presheaf W x hxW mW) := by
            rw [RingedSpace.moduleStalkMap_germ x φ W hxW mW]

noncomputable def moduleStalkHom
    (x : X) {ℱ 𝒢 : ModX} (φ : ℱ ⟶ 𝒢) :
    RingedSpace.stalkModuleCat ℱ x ⟶ RingedSpace.stalkModuleCat 𝒢 x :=
  ModuleCat.ofHom
    { toFun := RingedSpace.moduleStalkMap x φ
      map_add' := RingedSpace.moduleStalkMap_map_add x φ
      map_smul' := by
        intro r m
        simpa using RingedSpace.moduleStalkMap_map_smul x φ r m }

noncomputable def stalkModuleFunctor (x : X) :
    ModX ⥤ ModuleCat (X.presheaf.stalk x) where
  obj ℱ := RingedSpace.stalkModuleCat ℱ x
  map φ := RingedSpace.moduleStalkHom x φ
  map_id ℱ := by
    -- Reduce equality of module morphisms to equality on stalk elements.
    apply ModuleCat.hom_ext
    ext m
    change RingedSpace.moduleStalkMap x (𝟙 ℱ) m = m
    change
      (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map
              (𝟙 ℱ.val)))) m = m
    rw [(PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map_id]
    have hid :
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (𝟙
            ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).obj ℱ.val))) =
          𝟙 _ := by
      exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_id _
    rw [hid]
    rfl
  map_comp φ ψ := by
    -- Compare the two morphisms pointwise and use functoriality of the stalk functor.
    apply ModuleCat.hom_ext
    ext m
    change RingedSpace.moduleStalkMap x (φ ≫ ψ) m =
      RingedSpace.moduleStalkMap x ψ (RingedSpace.moduleStalkMap x φ m)
    change
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map
            (φ ≫ ψ).val))) m =
      (ConcreteCategory.hom
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
              ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val)) ≫
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
              ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map ψ.val)))) m
    calc
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map
            (φ ≫ ψ).val))) m =
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val) ≫
            ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map ψ.val)))) m := by
              rfl
      _ =
        (ConcreteCategory.hom
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
              ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map φ.val)) ≫
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
              ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map ψ.val)))) m := by
                simp

instance stalkModuleFunctor_preservesZeroMorphisms (x : X) :
    (stalkModuleFunctor x).PreservesZeroMorphisms where
  map_zero {ℱ 𝒢} := by
    apply ModuleCat.hom_ext_iff.mpr
    apply LinearMap.ext
    intro m
    change RingedSpace.moduleStalkMap x (0 : ℱ ⟶ 𝒢) m = 0
    change
      (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map
              (0 : ℱ.val ⟶ 𝒢.val)))) m = 0
    rw [(PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).map_zero]
    have hzero :
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (0 :
            ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).obj ℱ.val) ⟶
              ((PresheafOfModules.toPresheaf (RingedSpace.ringCatSheaf X).obj).obj 𝒢.val))) = 0 := by
      exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_zero _ _
    rw [hzero]
    rfl

private noncomputable abbrev unitStalkAddIso (x : X) :
    TopCat.Presheaf.stalk (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf x ≅
      (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat).obj
        (X.presheaf.stalk x) := by
  change TopCat.Presheaf.stalk
      (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat) x ≅ _
  exact
    (preservesColimitIso
      (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat)
      ((OpenNhds.inclusion x).op ⋙ X.presheaf)).symm

/-- Helper for ModuleRestrictionAndStalks: the additive comparison from the stalk of the unit
module to the underlying additive group of the ring stalk sends a germ to the corresponding ring
germ. -/
private theorem unitStalkAddIso_hom_germ
    (x : X) (U : Opens X) (hx : x ∈ U)
    (s : (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.obj (op U)) :
    (show ↑(X.presheaf.stalk x) from
        (RingedSpace.unitStalkAddIso x).hom
          (TopCat.Presheaf.germ
            (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf U x hx s)) =
      X.presheaf.germ U x hx (show X.presheaf.obj (op U) from s) := by
  -- Route correction: normalize `unitStalkAddIso` to the canonical preserved-colimit comparison,
  -- then evaluate that comparison on the explicit neighborhood stage `op ⟨U, hx⟩`.
  let j : (OpenNhds x)ᵒᵖ := op ⟨U, hx⟩
  have hι := congrArg
    (fun f ↦ f (show X.presheaf.obj (op U) from s))
    (ι_preservesColimitIso_inv
      (forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat)
      ((OpenNhds.inclusion x).op ⋙ X.presheaf) j)
  simpa [RingedSpace.unitStalkAddIso, j, CategoryTheory.types_comp_apply] using hι

private theorem unitStalkLinearEquiv_map_smul (x : X)
    (r : X.presheaf.stalk x)
    (m : ↑(RingedSpace.stalkModuleCat (SheafOfModules.unit (RingedSpace.ringCatSheaf X)) x)) :
    (show ↑(X.presheaf.stalk x) from (RingedSpace.unitStalkAddIso x).hom (r • m)) =
      r • (show ↑(X.presheaf.stalk x) from (RingedSpace.unitStalkAddIso x).hom m) := by
  obtain ⟨U, hxU, rU, hrU⟩ := TopCat.Presheaf.germ_exist X.presheaf x r
  obtain ⟨V, hxV, mV, hmV⟩ := TopCat.Presheaf.germ_exist
    (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf x m
  let W : Opens X := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  let rW : X.presheaf.obj (op W) := X.presheaf.map iWU.op rU
  let mW :
      (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.obj (op W) :=
    (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.map iWV.op mV
  have hrW : r = X.presheaf.germ W x hxW rW := by
    -- Represent the scalar germ on the common refinement `W = U ∩ V`.
    calc
      r = X.presheaf.germ U x hxU rU := hrU.symm
      _ = X.presheaf.germ W x hxW rW := by
        rw [show rW = X.presheaf.map iWU.op rU by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply X.presheaf iWU x hxW rU
  have hmW :
      m =
        TopCat.Presheaf.germ
          (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf W x hxW mW := by
    -- Represent the unit-module germ on the same common refinement.
    calc
      m =
          TopCat.Presheaf.germ
            (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf V x hxV mV :=
        hmV.symm
      _ =
          TopCat.Presheaf.germ
            (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf W x hxW mW := by
          rw [show mW =
            (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.map iWV.op mV by rfl]
          symm
          exact TopCat.Presheaf.germ_res_apply
            (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf iWV x hxW mV
  rw [hrW, hmW]
  -- Push the unit-sheaf germwise scalar-multiplication identity through the additive comparison.
  calc
    (show ↑(X.presheaf.stalk x) from
      (RingedSpace.unitStalkAddIso x).hom
        (X.presheaf.germ W x hxW rW •
          TopCat.Presheaf.germ
            (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf W x hxW mW)) =
      (show ↑(X.presheaf.stalk x) from
        (RingedSpace.unitStalkAddIso x).hom
          (TopCat.Presheaf.germ
            (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf W x hxW
            (rW • mW))) := by
          exact congrArg ((RingedSpace.unitStalkAddIso x).hom)
            (PresheafOfModules.germ_smul
              (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val x W hxW rW mW).symm
    _ = X.presheaf.germ W x hxW (show X.presheaf.obj (op W) from rW • mW) := by
      exact RingedSpace.unitStalkAddIso_hom_germ x W hxW (rW • mW)
    _ = X.presheaf.germ W x hxW rW •
        X.presheaf.germ W x hxW (show X.presheaf.obj (op W) from mW) := by
          change
            (X.presheaf.germ W x hxW).hom (rW * (show X.presheaf.obj (op W) from mW)) =
              (X.presheaf.germ W x hxW).hom rW *
                (X.presheaf.germ W x hxW).hom (show X.presheaf.obj (op W) from mW)
          exact (X.presheaf.germ W x hxW).hom.map_mul rW (show X.presheaf.obj (op W) from mW)
    _ = X.presheaf.germ W x hxW rW •
        (show ↑(X.presheaf.stalk x) from
          (RingedSpace.unitStalkAddIso x).hom
            (TopCat.Presheaf.germ
              (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf W x hxW mW)) := by
          rw [RingedSpace.unitStalkAddIso_hom_germ x W hxW mW]

noncomputable def unitStalkLinearEquiv (x : X) :
    ↑(RingedSpace.stalkModuleCat (SheafOfModules.unit (RingedSpace.ringCatSheaf X)) x) ≃ₗ[X.presheaf.stalk x]
      ↑(X.presheaf.stalk x) where
  toFun := (RingedSpace.unitStalkAddIso x).hom
  invFun := (RingedSpace.unitStalkAddIso x).inv
  left_inv m := (RingedSpace.unitStalkAddIso x).hom_inv_id_apply m
  right_inv r := (RingedSpace.unitStalkAddIso x).inv_hom_id_apply r
  map_add' m n := by
    simpa using ((RingedSpace.unitStalkAddIso x).hom.hom.map_add m n)
  map_smul' := RingedSpace.unitStalkLinearEquiv_map_smul x

noncomputable def unitStalkLinearMap (x : X) :
    RingedSpace.stalkModuleCat (SheafOfModules.unit (RingedSpace.ringCatSheaf X)) x ⟶
      ModuleCat.of (X.presheaf.stalk x) ↑(X.presheaf.stalk x) :=
  ModuleCat.ofHom (RingedSpace.unitStalkLinearEquiv x).toLinearMap

end RingedSpace

namespace RingedSpace

variable {X : RingedSpace.{u}} {U : Opens X}

attribute [local instance] CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback

private instance opensOrderTop : OrderTop (Opens X) :=
  (inferInstance : CompleteLattice (Opens X)).toOrderTop

private instance opensHasFiniteLimits : HasFiniteLimits (Opens X) :=
  hasFiniteLimits_of_semilatticeInf_orderTop

private instance hasFiniteProducts_over :
    HasFiniteProducts (Over U) := by
  let _ : HasPullbacks (Opens X) := by infer_instance
  let _ : HasBinaryProducts (Over U) := inferInstance
  exact hasFiniteProducts_of_has_binary_and_terminal

noncomputable abbrev moduleOverRestrictionMap
    {ℱ 𝒢 : SheafOfModules (Sheaf.over (RingedSpace.ringCatSheaf X) U)}
    (V : Over U) (φ : ℱ ⟶ 𝒢) :
    ℱ.over V ⟶ 𝒢.over V :=
  show
      (SheafOfModules.pushforward
        (𝟙 (Sheaf.over (Sheaf.over (RingedSpace.ringCatSheaf X) U) V))).obj ℱ ⟶
        (SheafOfModules.pushforward
          (𝟙 (Sheaf.over (Sheaf.over (RingedSpace.ringCatSheaf X) U) V))).obj 𝒢 from
    (SheafOfModules.pushforward
      (𝟙 (Sheaf.over (Sheaf.over (RingedSpace.ringCatSheaf X) U) V))).map φ

scoped[ModuleRestriction] notation:max φ " |_ " V => RingedSpace.moduleOverRestrictionMap V φ

end RingedSpace

end AlgebraicGeometry

namespace SheafOfModules

variable {X : RingedSpace.{u}}

private theorem unit_obj_eq_ring_obj (U : Opens X) :
    (((SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.obj (op U) :
        Type u)) =
      X.presheaf.obj (op U) := by
  -- The unit module sheaf is definitionally the structure sheaf viewed as a module over itself.
  rfl

abbrev unitSectionToRingSection (U : Opens X) :
    (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.obj (op U) →
      X.presheaf.obj (op U) :=
  Eq.mp (unit_obj_eq_ring_obj U)

theorem unitStalkLinearMap_germ
    (x : X) (U : Opens X) (hx : x ∈ U)
    (s : (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.obj (op U)) :
    RingedSpace.unitStalkLinearMap x
        (TopCat.Presheaf.germ (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf U x hx s) =
      X.presheaf.germ U x hx (unitSectionToRingSection U s) := by
  -- Unfold the linear map to the underlying additive comparison and apply the germ computation.
  simpa [RingedSpace.unitStalkLinearMap, RingedSpace.unitStalkLinearEquiv] using
    RingedSpace.unitStalkAddIso_hom_germ x U hx s

end SheafOfModules

namespace AlgebraicGeometry

namespace RingedSpace

variable {X : RingedSpace.{u}}

/-- ModuleRestrictionAndStalks: on a ringed space, a morphism of `\mathcal O_X`-modules restricts
to every open subset, induces a morphism on stalk modules, and the stalk of the unit module is
canonically identified with the stalk ring. -/
noncomputable def moduleRestrictionAndStalks
    (x : X) (U : Opens X) {ℱ 𝒢 : RingedSpace.Modules X} (φ : ℱ ⟶ 𝒢) :
    (ℱ.over U ⟶ 𝒢.over U) ×
      (RingedSpace.stalkModuleCat ℱ x ⟶ RingedSpace.stalkModuleCat 𝒢 x) ×
      (↑(RingedSpace.stalkModuleCat
          (SheafOfModules.unit (RingedSpace.ringCatSheaf X)) x) ≃ₗ[X.presheaf.stalk x]
        ↑(X.presheaf.stalk x)) :=
  (RingedSpace.moduleRestrictionMap U φ,
    RingedSpace.moduleStalkHom x φ,
    RingedSpace.unitStalkLinearEquiv x)

end RingedSpace

end AlgebraicGeometry
