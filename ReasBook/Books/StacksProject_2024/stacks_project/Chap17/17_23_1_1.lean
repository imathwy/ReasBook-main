import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_23_1
import StacksProject_2024.Chap17.Lemma_17_14_5.FreeSections
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.Chap17.SheafOfModulesTensorUnit

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open Opposite
open TopCat
open TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

/- Domain-style sampling for 17.23.1.1:
- primary domain: annihilator sheaves of `\mathcal O_X`-modules and their stalkwise action;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `AlgebraicGeometry.RingedSpace.unitStalkLinearMap`,
  `SheafOfModules.annihilator`,
  `SheafOfModules.annihilatorι`;
- best owner abstraction:
  the source-facing annihilator sheaf should reuse `SheafOfModules.annihilator`, while the stalk
  module should be expressed through `AlgebraicGeometry.RingedSpace.stalkModuleCat`, the
  structure-sheaf stalk should be reached through the owner bridge
  `AlgebraicGeometry.RingedSpace.unitStalkLinearMap`; the stalk-side source item should therefore
  be expressed through the canonical comparison map `annihilatorStalkToRing ℱ x` induced by
  `SheafOfModules.annihilatorι`;
- primitive data:
  a module sheaf `ℱ` and a point `x`;
- derived API:
  stalk-element and germwise membership statements obtained from the stalk-ideal inclusion.

Source/core/bridge triage:
- `source-facing`: the stalk-ideal inclusion
  `(Ann_{\mathcal O_X}(\mathcal F))_x \subset Ann_{\mathcal O_{X, x}}(\mathcal F_x)`;
- `core/canonical`: `SheafOfModules.annihilator`, `RingedSpace.stalkModuleCat`, and
  `RingedSpace.unitStalkLinearMap`;
- `bridge/view`: `SheafOfModules.annihilatorStalkToRing`,
  `SheafOfModules.annihilatorSectionImage`,
  `SheafOfModules.unitStalkLinearMap_germ`, and the elementwise/germwise membership lemmas, which
  turn the stalk-ideal inclusion into local-section statements. -/

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (SheafOfModules.{u} (RingedSpace.ringCatSheaf X))]
variable [MonoidalClosed (SheafOfModules.{u} (RingedSpace.ringCatSheaf X))]

local notation "ModX" => SheafOfModules (RingedSpace.ringCatSheaf X)
local notation "𝒪X" => SheafOfModules.unit (RingedSpace.ringCatSheaf X)

open scoped AnnihilatorSheaf

/- The canonical stalk comparison induced by the annihilator inclusion lands in the stalk ring
through the unit-module identification. -/
noncomputable abbrev annihilatorStalkToRing (ℱ : ModX) (x : X) :
    RingedSpace.stalkModuleCat (Ann(ℱ)) x ⟶
      ModuleCat.of (X.presheaf.stalk x) ↑(X.presheaf.stalk x) :=
  RingedSpace.moduleStalkHom x (annihilatorι ℱ) ≫ RingedSpace.unitStalkLinearMap x

/-- The ideal of the stalk ring `\mathcal O_{X, x}` cut out by the stalk of the annihilator sheaf
of `\mathcal F`. -/
noncomputable def annihilatorStalkIdeal (ℱ : ModX) (x : X) : Ideal (X.presheaf.stalk x) :=
  LinearMap.range (annihilatorStalkToRing ℱ x).hom

/-- Helper for 17.23.1.1: `unitHomEquiv` on the slice over `U` is computed by evaluating the
underlying morphism at the terminal object `U → U`. -/
private theorem unitHomEquiv_apply_terminal
    {U : Opens X} (M : SheafOfModules (X.ringCatSheaf.over U))
    (f : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M) :
    (M.unitHomEquiv f).1 (op (Over.mk (𝟙 U))) =
      (f.val.app (op (Over.mk (𝟙 U))))
        (show ((SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj
            (op (Over.mk (𝟙 U)))) from (1 : X.presheaf.obj (op U))) := by
  -- Proof comment: `unitHomEquiv` on the slice is definitionally evaluation on the terminal
  -- object lying over `U`.
  rfl

/-- Helper for 17.23.1.1: a section of the internal-Hom sheaf on `U` is the same as a section of
the restricted internal-Hom sheaf over the slice on `U`. -/
private noncomputable def internalHomObjEquivOverSections
    (ℱ 𝒢 : ModX) (U : Opens X) :
    ((ihom ℱ).obj 𝒢).val.obj (op U) ≃ (((ihom ℱ).obj 𝒢).over U).sections := by
  -- Proof comment: recover a slice section by evaluating the restricted sheaf on the terminal
  -- object of `Over U`.
  simpa using (RingedSpace.over_sections_equiv_evaluation (((ihom ℱ).obj 𝒢).over U)).symm

/-- Helper for 17.23.1.1: a section of the restricted internal-Hom sheaf corresponds to a unit
morphism on the slice over `U`. -/
private noncomputable def internalHomOverSectionsEquivUnitHom
    (ℱ 𝒢 : ModX) (U : Opens X) :
    (((ihom ℱ).obj 𝒢).over U).sections ≃
      (SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ (((ihom ℱ).obj 𝒢).over U)) :=
  ((((ihom ℱ).obj 𝒢).over U).unitHomEquiv).symm

/-- Helper for 17.23.1.1: a morphism from the tensor unit to the restricted internal-Hom sheaf
over `U` is the same as a local morphism `ℱ|_U ⟶ 𝒢|_U`. -/
private noncomputable def internalHomUnitHomEquivOverHom
    (ℱ 𝒢 : ModX) (U : Opens X) :
    (SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ (((ihom ℱ).obj 𝒢).over U)) ≃
      (ℱ.over U ⟶ 𝒢.over U) :=
  -- Proof comment: on the slice over `U`, the closed structure identifies maps from the unit
  -- object into the internal Hom with ordinary local module morphisms.
  ((((ihom (ℱ.over U)).obj (𝒢.over U)).unitHomEquiv).symm)

/-- Helper for 17.23.1.1: a value of the internal-Hom sheaf on `U` is the same thing as a local
module morphism `ℱ|_U ⟶ 𝒢|_U`. -/
private noncomputable def internalHomSectionEquivOverHom
    (ℱ 𝒢 : ModX) (U : Opens X) :
    (((ihom ℱ).obj 𝒢).val.obj (op U)) ≃ (ℱ.over U ⟶ 𝒢.over U) :=
  -- Proof comment: evaluate the restricted internal-Hom sheaf at the terminal object, interpret
  -- the resulting section as a unit morphism on the slice, and then uncurry it to a local map.
  (internalHomObjEquivOverSections ℱ 𝒢 U).trans
    ((internalHomOverSectionsEquivUnitHom ℱ 𝒢 U).trans
      (internalHomUnitHomEquivOverHom ℱ 𝒢 U))

/-- Helper for 17.23.1.1: evaluating the sectionwise component of the canonical self-action map
on a local ring section is ordinary scalar multiplication on `\mathcal F(U)`. -/
private theorem selfInternalHomUnitMap_app_apply
    (ℱ : ModX) (U : Opens X) (a : X.presheaf.obj (op U)) (m : ℱ.val.obj (op U)) :
    ((((internalHomSectionEquivOverHom ℱ ℱ U)
        (ModuleCat.Hom.hom ((Hom.val (selfInternalHomUnitMap ℱ)).app (op U)) a)).val.app
      (op (Over.mk (𝟙 U)))) m) =
      unitSectionToRingSection U a • m := by
  -- Proof comment: transport the component of `selfInternalHomUnitMap` on `U` to the
  -- corresponding local endomorphism of `ℱ|_U`, then evaluate it on the terminal slice object.
  simpa [internalHomSectionEquivOverHom, internalHomObjEquivOverSections,
    internalHomOverSectionsEquivUnitHom, internalHomUnitHomEquivOverHom,
    RingedSpace.over_sections_equiv_evaluation, unitHomEquiv_apply_terminal,
    SheafOfModules.selfInternalHomUnitMap, MonoidalClosed.id, unitSectionToRingSection]

/-- Helper for 17.23.1.1: a local section of the annihilator sheaf acts by zero on every section
of `\mathcal F` over the same open set. -/
theorem annihilatorSectionImage_smul_eq_zero
    (ℱ : ModX) (U : Opens X) (s : (Ann(ℱ)).val.obj (op U)) (m : ℱ.val.obj (op U)) :
    annihilatorSectionImage ℱ U s • m = 0 := by
  have hzero : annihilatorι ℱ ≫ selfInternalHomUnitMap ℱ = 0 :=
    kernel.condition (selfInternalHomUnitMap ℱ)
  -- Proof comment: evaluate the kernel condition on `U` to see that the chosen annihilator
  -- section is sent to the zero endomorphism of `ℱ(U)`.
  have hval :
      (Hom.val (annihilatorι ℱ ≫ selfInternalHomUnitMap ℱ)) = 0 := by
    exact congrArg Hom.val hzero
  have hcomp :
      ((Hom.val (annihilatorι ℱ)).app (op U)) ≫
          ((Hom.val (selfInternalHomUnitMap ℱ)).app (op U)) = 0 := by
    change (Hom.val (annihilatorι ℱ ≫ selfInternalHomUnitMap ℱ)).app (op U) = 0
    simpa using congrArg (fun α => α.app (op U)) hval
  have hsection_zero :
      internalHomSectionEquivOverHom ℱ ℱ U
          (ModuleCat.Hom.hom ((Hom.val (selfInternalHomUnitMap ℱ)).app (op U))
            (((Hom.val (annihilatorι ℱ)).app (op U)) s)) = 0 := by
    -- Proof comment: the component of the self-action map vanishes on the annihilator section,
    -- and transporting through the canonical equivalence preserves that zero endomorphism.
    have hsection_zero_raw :
        ModuleCat.Hom.hom
            (((Hom.val (annihilatorι ℱ)).app (op U)) ≫
              ((Hom.val (selfInternalHomUnitMap ℱ)).app (op U))) s = 0 := by
      exact congrArg
        (fun g : (Ann(ℱ)).val.obj (op U) ⟶ ((ihom ℱ).obj ℱ).val.obj (op U) =>
          ModuleCat.Hom.hom g s)
        hcomp
    exact congrArg (internalHomSectionEquivOverHom ℱ ℱ U) <| by
      simpa using hsection_zero_raw
  have happly :
      ModuleCat.Hom.hom
          (((internalHomSectionEquivOverHom ℱ ℱ U)
              (ModuleCat.Hom.hom ((Hom.val (selfInternalHomUnitMap ℱ)).app (op U))
                (((Hom.val (annihilatorι ℱ)).app (op U)) s))).val.app
            (op (Over.mk (𝟙 U)))) m = 0 := by
    -- Proof comment: evaluate the vanishing local endomorphism on the terminal slice object and
    -- then on the chosen section `m`.
    simpa using congrArg
      (fun g : ℱ.over U ⟶ ℱ.over U =>
        ModuleCat.Hom.hom (g.val.app (op (Over.mk (𝟙 U)))) m)
      hsection_zero
  -- Route correction: rewrite the component of `selfInternalHomUnitMap` through the dedicated
  -- self-action evaluation lemma before identifying the resulting scalar with
  -- `annihilatorSectionImage`.
  rw [selfInternalHomUnitMap_app_apply] at happly
  simpa [annihilatorSectionImage] using happly

/-- Helper for 17.23.1.1: the canonical stalk comparison sends a germ of an annihilator section
to the germ of its image in the structure sheaf. -/
theorem annihilatorStalkToRing_germ
    (ℱ : ModX) (x : X) (U : Opens X) (hx : x ∈ U) (s : (Ann(ℱ)).val.obj (op U)) :
    annihilatorStalkToRing ℱ x (TopCat.Presheaf.germ (Ann(ℱ)).val.presheaf U x hx s) =
      X.presheaf.germ U x hx (annihilatorSectionImage ℱ U s) := by
  have hmap :
      RingedSpace.moduleStalkHom x (annihilatorι ℱ)
          (TopCat.Presheaf.germ (Ann(ℱ)).val.presheaf U x hx s) =
        TopCat.Presheaf.germ (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf U x
          hx ((annihilatorι ℱ).val.app (op U) s) := by
    -- Proof comment: rewrite the stalk image of the annihilator inclusion through the germ API.
    simpa [RingedSpace.moduleStalkHom] using
      (RingedSpace.moduleStalkMap_germ x (annihilatorι ℱ) U hx s)
  -- Proof comment: once the stalk map lands in the unit sheaf, identify it with the
  -- corresponding ring germ.
  change
    RingedSpace.unitStalkLinearMap x
        (RingedSpace.moduleStalkHom x (annihilatorι ℱ)
          (TopCat.Presheaf.germ (Ann(ℱ)).val.presheaf U x hx s)) =
      X.presheaf.germ U x hx (annihilatorSectionImage ℱ U s)
  rw [hmap, unitStalkLinearMap_germ]

/-- Helper for 17.23.1.1: the image of a stalk element of the annihilator sheaf acts trivially on
every stalk element of `\mathcal F`. -/
theorem annihilatorStalkImage_smul_eq_zero
    (ℱ : ModX) (x : X)
    (t : RingedSpace.stalkModuleCat (Ann(ℱ)) x) (m : RingedSpace.stalkModuleCat ℱ x) :
    annihilatorStalkToRing ℱ x t • m = 0 := by
  obtain ⟨U, hxU, s, hs⟩ := TopCat.Presheaf.germ_exist (Ann(ℱ)).val.presheaf x t
  obtain ⟨V, hxV, n, hn⟩ := TopCat.Presheaf.germ_exist ℱ.val.presheaf x m
  let W : Opens X := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let sW : (Ann(ℱ)).val.obj (op W) := (Ann(ℱ)).val.map (homOfLE inf_le_left).op s
  let nW : ℱ.val.obj (op W) := ℱ.val.map (homOfLE inf_le_right).op n
  have htW :
      t = TopCat.Presheaf.germ (Ann(ℱ)).val.presheaf W x hxW sW := by
    calc
      t = TopCat.Presheaf.germ (Ann(ℱ)).val.presheaf U x hxU s := hs.symm
      _ = TopCat.Presheaf.germ (Ann(ℱ)).val.presheaf W x hxW sW := by
        rw [show sW = (Ann(ℱ)).val.map (homOfLE inf_le_left).op s by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply (Ann(ℱ)).val.presheaf (homOfLE inf_le_left) x hxW s
  have hmW :
      m = TopCat.Presheaf.germ ℱ.val.presheaf W x hxW nW := by
    calc
      m = TopCat.Presheaf.germ ℱ.val.presheaf V x hxV n := hn.symm
      _ = TopCat.Presheaf.germ ℱ.val.presheaf W x hxW nW := by
        rw [show nW = ℱ.val.map (homOfLE inf_le_right).op n by rfl]
        symm
        exact TopCat.Presheaf.germ_res_apply ℱ.val.presheaf (homOfLE inf_le_right) x hxW n
  have hsection_zero :
      annihilatorSectionImage ℱ W sW • nW = 0 := by
    -- Proof comment: this is the sectionwise annihilation statement, transported to the common
    -- refinement where both representatives live.
    exact annihilatorSectionImage_smul_eq_zero ℱ W sW nW
  -- Proof comment: represent both stalk elements over the common refinement and then rewrite the
  -- stalk scalar action as the germ of the already-vanishing sectionwise scalar action.
  rw [htW, hmW, annihilatorStalkToRing_germ ℱ x W hxW sW]
  calc
    X.presheaf.germ W x hxW (annihilatorSectionImage ℱ W sW) •
        TopCat.Presheaf.germ ℱ.val.presheaf W x hxW nW =
      TopCat.Presheaf.germ ℱ.val.presheaf W x hxW (annihilatorSectionImage ℱ W sW • nW) := by
        symm
        simpa using
          (PresheafOfModules.germ_smul ℱ.val x W hxW (annihilatorSectionImage ℱ W sW) nW)
    _ = TopCat.Presheaf.germ ℱ.val.presheaf W x hxW 0 := by
        exact congrArg (TopCat.Presheaf.germ ℱ.val.presheaf W x hxW) hsection_zero
    _ = 0 := by
        exact (TopCat.Presheaf.germ ℱ.val.presheaf W x hxW).hom.map_zero

-- Proof sketch: first pass from the stalk of `Ann(ℱ)` to the stalk of the unit
-- `\mathcal O_X`-module via `RingedSpace.moduleStalkHom x (annihilatorι ℱ)`, then identify that
-- stalk with `\mathcal O_{X,x}` through `RingedSpace.unitStalkLinearMap x`. Because sections of
-- `Ann(ℱ)` lie in the kernel of the action map, the resulting stalk scalar acts by zero on
-- every element of `ℱ_x`, hence lies in `Module.annihilator (\mathcal O_{X,x}) (ℱ_x)`.
/-- Companion bridge: the canonical image of a stalk element of
`\operatorname{Ann}_{\mathcal O_X}(\mathcal F)` in `\mathcal O_{X, x}` lies in the annihilator
ideal of the stalk `\mathcal F_x`. -/
theorem stalk_annihilatorImage_mem_stalk_annihilator
    (ℱ : ModX) (x : X)
    (t : RingedSpace.stalkModuleCat (Ann(ℱ)) x) :
    annihilatorStalkToRing ℱ x t ∈
      Module.annihilator (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  -- Proof comment: membership in the module annihilator ideal is exactly the statement that the
  -- corresponding stalk scalar kills every element of `\mathcal F_x`.
  rw [Module.mem_annihilator]
  intro m
  exact annihilatorStalkImage_smul_eq_zero ℱ x t m

/-- 17.23.1.1: the ideal of the stalk ring `\mathcal O_{X, x}` cut out by the stalk of the
annihilator sheaf `\operatorname{Ann}_{\mathcal O_X}(\mathcal F)` is contained in the annihilator
ideal of the stalk module `\mathcal F_x`. This is the stalkwise inclusion
`(\operatorname{Ann}_{\mathcal O_X}(\mathcal F))_x \subset
\operatorname{Ann}_{\mathcal O_{X, x}}(\mathcal F_x)`. -/
theorem annihilatorStalkIdeal_le_module_annihilator (ℱ : ModX) (x : X) :
    annihilatorStalkIdeal ℱ x ≤
      Module.annihilator (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  rintro _ ⟨t, rfl⟩
  exact stalk_annihilatorImage_mem_stalk_annihilator ℱ x t

/-- Companion bridge: if `s` is a local section of the annihilator sheaf near `x`, then its germ
in `\mathcal O_{X, x}` lies in the annihilator ideal of the stalk `\mathcal F_x`. -/
theorem germ_annihilator_mem_stalk_annihilator (ℱ : ModX) (x : X)
    (U : Opens X) (hx : x ∈ U) (s : (Ann(ℱ)).val.obj (op U)) :
    X.presheaf.germ U x hx (annihilatorSectionImage ℱ U s) ∈
      Module.annihilator (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  have hmap :
      RingedSpace.moduleStalkHom x (annihilatorι ℱ)
          (TopCat.Presheaf.germ (Ann(ℱ)).val.presheaf U x hx s) =
        TopCat.Presheaf.germ (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf U x
          hx ((annihilatorι ℱ).val.app (op U) s) := by
    simpa [RingedSpace.moduleStalkHom] using
      (RingedSpace.moduleStalkMap_germ x (annihilatorι ℱ) U hx s)
  have hmem :=
    stalk_annihilatorImage_mem_stalk_annihilator ℱ x
      (TopCat.Presheaf.germ (Ann(ℱ)).val.presheaf U x hx s)
  have hgerm :
      annihilatorStalkToRing ℱ x
          (TopCat.Presheaf.germ (Ann(ℱ)).val.presheaf U x hx s) =
        X.presheaf.germ U x hx (annihilatorSectionImage ℱ U s) := by
    change
      RingedSpace.unitStalkLinearMap x
          (RingedSpace.moduleStalkHom x (annihilatorι ℱ)
            (TopCat.Presheaf.germ (Ann(ℱ)).val.presheaf U x hx s)) =
        X.presheaf.germ U x hx (annihilatorSectionImage ℱ U s)
    rw [hmap, unitStalkLinearMap_germ]
  have hmem' :
      annihilatorStalkToRing ℱ x
          (TopCat.Presheaf.germ (Ann(ℱ)).val.presheaf U x hx s) ∈
        Module.annihilator (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
    simpa [annihilatorStalkToRing] using hmem
  exact hgerm ▸ hmem'

end SheafOfModules
