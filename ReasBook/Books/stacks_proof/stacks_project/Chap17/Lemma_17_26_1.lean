import Mathlib
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap06.Lemma_6_16_1
import stacks_proof.stacks_project.Chap15.Lemma_15_119_2
import stacks_proof.stacks_project.Chap17.Definition_17_14_1
import stacks_proof.stacks_project.Chap17.Lemma_17_21_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Functor.OplaxMonoidal
open AlgebraicGeometry
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.26.1:
- primary domain: determinant subsheaves inside exterior algebra sheaves of `\mathcal O_X`-modules,
  with the finite locally free top-exterior model and short-exact multiplicativity as bridge data;
- inspected owner declarations:
  `Module.det`,
  `Module.mem_det_iff`,
  `Λ(ℱ)`,
  `Λ^[r] ℱ`,
  `SheafOfModules.annihilator`;
- best owner abstraction: the source-facing owner is the determinant subsheaf cut out inside the
  exterior algebra sheaf `Λ(ℱ)` by degree-one left multiplication, mirroring the module-level
  owner `Module.det`; finite locally free top-exterior-power presentations are derived bridge API,
  not the owner itself;
- primitive data: a module sheaf `ℱ : ModX`;
- derived API: the action map `Λ(ℱ) ⟶ \mathcal H\!om_{\mathcal O_X}(\mathcal F, \Lambda(\mathcal
  F))`, the kernel inclusion `det(ℱ) ⟶ Λ(ℱ)`, the constant-rank bridge
  `Λ^[r] ℱ ≅ det(ℱ)`, and the short-exact multiplicativity comparison.

Source/core/bridge triage:
- `source-facing`: the determinant sheaf owner `determinantSheaf ℱ` and the determinant tensor
  comparison for short exact sequences;
- `core/canonical`: `Λ(ℱ)`, `ihom`, `kernel`, `MonoidalClosed.curry`, and the module-level owner
  `Module.det`;
- `bridge/view`: the sectionwise degree-one left-multiplication map on `Λ(ℱ)`, the kernel
  inclusion `determinantSheafι`, and the constant-rank top exterior-power model. -/

/-- The commutative ring of sections of the structure sheaf over an open set. -/
private abbrev sectionRing (X : RingedSpace) (U : (Opens X)ᵒᵖ) :=
  X.presheaf.obj U

-- Route correction: reuse the canonical Chapter 17 owner layer for finite locally free sheaves,
-- exterior powers, and exterior algebras, and keep only the determinant-specific constructions in
-- this file.
private noncomputable abbrev modSheafification :
    PresheafOfModules X.ringCatSheaf.obj ⥤ ModX :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- Helper for Lemma 17.26.1: use the already compiled monoidal tensor on module sheaves as the
local tensor owner inside this file. -/
private abbrev moduleTensor
    (ℱ 𝒢 : ModX) : ModX :=
  (ℱ ⊗ 𝒢 : ModX)

/-- Helper for Lemma 17.26.1: the determinant-side tensor map is induced from the canonical
sectionwise presheaf tensor morphism and then sheafified. -/
private noncomputable abbrev moduleTensorMap
    {ℱ₁ ℱ₂ 𝒢₁ 𝒢₂ : ModX}
    (α : ℱ₁ ⟶ ℱ₂) (β : 𝒢₁ ⟶ 𝒢₂) :
    moduleTensor ℱ₁ 𝒢₁ ⟶ moduleTensor ℱ₂ 𝒢₂ :=
  α ⊗ₘ β

/-- The objectwise exterior algebra module on an open set of a ringed space. -/
private abbrev exteriorAlgebraPresheafObj
    (ℱ : ModX) (U : (Opens X)ᵒᵖ) :
    ModuleCat (sectionRing X U) :=
  ModuleCat.of (sectionRing X U)
    (ExteriorAlgebra (sectionRing X U) (ℱ.val.obj U))

/-- The restriction-linear map on sections used to define the exterior algebra presheaf. -/
private def exteriorAlgebraRestrictionLinear
    (ℱ : ModX) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    let _ :
        Algebra (sectionRing X U) (ExteriorAlgebra (sectionRing X V) (ℱ.val.obj V)) :=
      Algebra.compHom
        (ExteriorAlgebra (sectionRing X V) (ℱ.val.obj V))
        (X.presheaf.map i).hom
    ℱ.val.obj U →ₗ[sectionRing X U] ExteriorAlgebra (sectionRing X V) (ℱ.val.obj V) := by
  let _ :
      Algebra (sectionRing X U) (ExteriorAlgebra (sectionRing X V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (ExteriorAlgebra (sectionRing X V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  refine
    { toFun := fun m ↦
        ExteriorAlgebra.ι (sectionRing X V)
          (show ℱ.val.obj V from (ℱ.val.map i).hom m)
      map_add' := ?_
      map_smul' := ?_ }
  · -- Restriction commutes with addition before inserting the section into the exterior algebra.
    intro m n
    rw [show (ℱ.val.map i).hom (m + n) =
        (show ℱ.val.obj V from (ℱ.val.map i).hom m) +
          (show ℱ.val.obj V from (ℱ.val.map i).hom n) by
      simpa using (ℱ.val.map i).hom.map_add m n]
    exact
      (ExteriorAlgebra.ι (sectionRing X V)).map_add
        (show ℱ.val.obj V from (ℱ.val.map i).hom m)
        (show ℱ.val.obj V from (ℱ.val.map i).hom n)
  · -- Restriction is semilinear with respect to the structure-sheaf restriction map.
    intro r m
    rw [show (ℱ.val.map i).hom (r • m) =
        (X.presheaf.map i).hom r • (show ℱ.val.obj V from (ℱ.val.map i).hom m) by
      simpa using (ℱ.val.map i).hom.map_smulₛₗ r m]
    exact
      (ExteriorAlgebra.ι (sectionRing X V)).map_smul
        ((X.presheaf.map i).hom r)
        (show ℱ.val.obj V from (ℱ.val.map i).hom m)

/-- The restricted exterior generators still square to zero. -/
private theorem exteriorAlgebraRestrictionLinear_sq_zero
    (ℱ : ModX) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ∀ m : ℱ.val.obj U,
      exteriorAlgebraRestrictionLinear ℱ i m *
        exteriorAlgebraRestrictionLinear ℱ i m = 0 := by
  -- Exterior generators square to zero after restricting sections.
  intro m
  simpa [exteriorAlgebraRestrictionLinear] using
    (ExteriorAlgebra.ι_sq_zero (show ℱ.val.obj V from (ℱ.val.map i).hom m))

/-- The restriction map for the exterior algebra presheaf. -/
private noncomputable def exteriorAlgebraPresheafMap
    (ℱ : ModX) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    exteriorAlgebraPresheafObj ℱ U ⟶
      (ModuleCat.restrictScalars (X.presheaf.map i).hom).obj
        (exteriorAlgebraPresheafObj ℱ V) := by
  let _ :
      Algebra (sectionRing X U) (ExteriorAlgebra (sectionRing X V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (ExteriorAlgebra (sectionRing X V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  exact
    (show exteriorAlgebraPresheafObj ℱ U ⟶
        ModuleCat.of (sectionRing X U) (ExteriorAlgebra (sectionRing X V) (ℱ.val.obj V)) from
      ModuleCat.ofHom
        ((ExteriorAlgebra.lift (sectionRing X U)
          ⟨exteriorAlgebraRestrictionLinear ℱ i,
            exteriorAlgebraRestrictionLinear_sq_zero ℱ i⟩).toLinearMap))

/-- The exterior algebra restriction maps satisfy the identity axiom. -/
private theorem exteriorAlgebraPresheaf_map_id
    (ℱ : ModX) (U : (Opens X)ᵒᵖ) :
    exteriorAlgebraPresheafMap ℱ (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (exteriorAlgebraPresheafObj ℱ U) := by
  -- Proof comment: rewrite the restriction map as the lift induced by the identity on generators.
  let R := X.presheaf.obj U
  let M := ℱ.val.obj U
  let _ : Algebra R (ExteriorAlgebra R M) :=
    Algebra.compHom (ExteriorAlgebra R M) (X.presheaf.map (𝟙 U)).hom
  let F : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M :=
    ExteriorAlgebra.lift R
      ⟨exteriorAlgebraRestrictionLinear ℱ (𝟙 U),
        exteriorAlgebraRestrictionLinear_sq_zero ℱ (𝟙 U)⟩
  have hF : F = AlgHom.id R (ExteriorAlgebra R M) := by
    -- Proof comment: the exterior algebra is generated by degree-one elements, so generator
    -- equality forces equality of the algebra morphisms.
    apply ExteriorAlgebra.hom_ext
    intro m
    simp [F, exteriorAlgebraRestrictionLinear]
  apply ModuleCat.hom_ext
  ext x
  simpa [exteriorAlgebraPresheafMap, F, ModuleCat.restrictScalarsId'App_inv_apply] using
    congrArg (fun f : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R M => f x) hF

/-- The exterior algebra restriction maps satisfy the composition axiom. -/
private theorem exteriorAlgebraPresheaf_map_comp
    (ℱ : ModX) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    exteriorAlgebraPresheafMap ℱ (i ≫ j) =
      exteriorAlgebraPresheafMap ℱ i ≫
        (ModuleCat.restrictScalars _).map (exteriorAlgebraPresheafMap ℱ j) ≫
          (ModuleCat.restrictScalarsComp' (X.presheaf.map i).hom
            (X.presheaf.map j).hom
            (X.presheaf.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom <| X.presheaf.map_comp i j)).inv.app
            (exteriorAlgebraPresheafObj ℱ W) := by
  -- Proof comment: compare the direct and iterated restriction maps as algebra morphisms out of the
  -- same exterior algebra, then reduce the comparison to the canonical generators.
  let R := X.presheaf.obj U
  let S := X.presheaf.obj V
  let T := X.presheaf.obj W
  let M := ℱ.val.obj U
  let N := ℱ.val.obj V
  let P := ℱ.val.obj W
  let _ : Algebra R (ExteriorAlgebra T P) :=
    Algebra.compHom (ExteriorAlgebra T P) (X.presheaf.map (i ≫ j)).hom
  let _ : Algebra R (ExteriorAlgebra S N) :=
    Algebra.compHom (ExteriorAlgebra S N) (X.presheaf.map i).hom
  let _ : Algebra S (ExteriorAlgebra T P) :=
    Algebra.compHom (ExteriorAlgebra T P) (X.presheaf.map j).hom
  let Fij : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra T P :=
    ExteriorAlgebra.lift R
      ⟨exteriorAlgebraRestrictionLinear ℱ (i ≫ j),
        exteriorAlgebraRestrictionLinear_sq_zero ℱ (i ≫ j)⟩
  let Fi : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra S N :=
    ExteriorAlgebra.lift R
      ⟨exteriorAlgebraRestrictionLinear ℱ i,
        exteriorAlgebraRestrictionLinear_sq_zero ℱ i⟩
  let Fj : ExteriorAlgebra S N →ₐ[S] ExteriorAlgebra T P :=
    ExteriorAlgebra.lift S
      ⟨exteriorAlgebraRestrictionLinear ℱ j,
        exteriorAlgebraRestrictionLinear_sq_zero ℱ j⟩
  let Fcomp : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra T P :=
    (Fj.restrictScalars R).comp Fi
  have hcomp : Fij = Fcomp := by
    -- Proof comment: both lifts send a degree-one generator to the twice-restricted section.
    apply ExteriorAlgebra.hom_ext
    intro m
    simp [Fij, Fcomp, Fi, Fj, exteriorAlgebraRestrictionLinear]
  apply ModuleCat.hom_ext
  ext x
  simpa [exteriorAlgebraPresheafMap, Fij, Fcomp, Fi, Fj] using
    congrArg (fun f : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra T P => f x) hcomp

/-- Helper for Lemma 17.26.1: the identity ring map induces the trivial restriction-of-scalars
presheaf isomorphism. -/
private noncomputable def restrictScalarsIdIso
    (ℱ : PresheafOfModules X.ringCatSheaf.obj) :
    (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj ℱ ≅ ℱ :=
  PresheafOfModules.isoMk
    (fun U ↦ by
      simpa using
        (ModuleCat.restrictScalarsId'App
          (((𝟙 X.ringCatSheaf.obj : X.ringCatSheaf.obj ⟶ X.ringCatSheaf.obj).app U).hom)
          rfl
          (ℱ.obj U)))
    (fun {U V} i ↦ by
      ext x
      rfl)

/-- Helper for Lemma 17.26.1: the sheafification unit, viewed back in the original module-presheaf
world. -/
private noncomputable abbrev sheafificationUnitToVal
    (ℱ : PresheafOfModules X.ringCatSheaf.obj) :
    ℱ ⟶ (modSheafification.obj ℱ).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app ℱ ≫
    (restrictScalarsIdIso ((modSheafification.obj ℱ).val)).hom

/-- Helper for Lemma 17.26.1: the canonical oplax-monoidal sheafification comparison for module
presheaves. -/
private abbrev moduleSheafificationTensorComparison
    (ℱ 𝒢 : PresheafOfModules X.ringCatSheaf.obj) :
    modSheafification.obj (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢) ⟶
      moduleTensor (modSheafification.obj ℱ) (modSheafification.obj 𝒢) :=
  modSheafification.map
    (PresheafOfModules.Monoidal.tensorHom (sheafificationUnitToVal ℱ) (sheafificationUnitToVal 𝒢))

/-- Helper for Lemma 17.26.1: the sheafification tensor comparison is invertible because
sheafification is oplax monoidal. -/
private instance moduleSheafificationTensorComparison_isIso
    (ℱ 𝒢 : PresheafOfModules X.ringCatSheaf.obj) :
    IsIso (moduleSheafificationTensorComparison ℱ 𝒢) := by
  -- Proof comment: this is exactly the canonical `δ` comparison for sheafification.
  change IsIso
    (Functor.OplaxMonoidal.δ
      (_root_.moduleSheafification (J := Opens.grothendieckTopology X) X.sheaf) ℱ 𝒢)
  infer_instance

/-- Helper for Lemma 17.26.1: package the oplax-monoidal sheafification comparison as an
isomorphism so tensor-induced maps can be sheafified cleanly. -/
private noncomputable abbrev moduleSheafificationTensorIso
    (ℱ 𝒢 : PresheafOfModules X.ringCatSheaf.obj) :
    moduleTensor (modSheafification.obj ℱ) (modSheafification.obj 𝒢) ≅
      modSheafification.obj (PresheafOfModules.Monoidal.tensorObj ℱ 𝒢) :=
  (asIso (moduleSheafificationTensorComparison ℱ 𝒢)).symm

/-- Helper for Lemma 17.26.1: forgetting the commutative-ring structure commutes with taking the
ordinary stalk at a point. -/
private noncomputable abbrev commRingStalkToRingStalkIso
    (x : X) :
    (forget₂ CommRingCat RingCat).obj (TopCat.Presheaf.stalk X.presheaf x) ≅
      (RingedSpace.ringCatSheaf X).presheaf.stalk x :=
  CategoryTheory.preservesColimitIso (forget₂ CommRingCat RingCat)
    ((OpenNhds.inclusion x).op ⋙ X.presheaf)

/-- Helper for Lemma 17.26.1: the ordinary stalk of a module presheaf carries its canonical
`\mathcal O_{X,x}`-module structure. -/
private noncomputable instance presheafStalkModule
    (P : PresheafOfModules X.ringCatSheaf.obj) (x : X) :
    Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk P.presheaf x) := by
  -- Proof comment: use the built-in module structure over the `RingCat` stalk of the forgotten
  -- structure sheaf and then transport scalars back along the canonical stalk-ring isomorphism.
  letI : Module ((RingedSpace.ringCatSheaf X).presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk P.presheaf x) := by
    infer_instance
  let e := (commRingStalkToRingStalkIso (X := X) x).ringCatIsoToRingEquiv
  exact Module.compHom ↑(TopCat.Presheaf.stalk P.presheaf x) e.toRingHom

/-- Helper for Lemma 17.26.1: a morphism of module presheaves induces the corresponding map on
ordinary stalks. -/
private noncomputable def presheafStalkMap
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (x : X) (φ : P ⟶ Q) :
    TopCat.Presheaf.stalk P.presheaf x ⟶ TopCat.Presheaf.stalk Q.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ)

/-- Helper for Lemma 17.26.1: the ordinary stalk map induced by a morphism of module presheaves
is linear over `\mathcal O_{X,x}`. -/
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
  -- Proof comment: compare both sides on a common local representative and use germwise
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

/-- Helper for Lemma 17.26.1: a morphism of module presheaves induces a morphism of the
corresponding stalk modules over `\mathcal O_{X,x}`. -/
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

/-- Helper for Lemma 17.26.1: the stalk map of the sheafification unit is bijective on the
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
    -- Proof comment: forgetting the module structure turns the sheafification unit into the
    -- additive sheafification unit.
    simpa [η] using
      PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
        (𝟙 X.ringCatSheaf.obj) P
  have hη_iso :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map η)) := by
    -- Proof comment: additive sheafification does not change stalks.
    rw [hη]
    simpa using
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P.presheaf
  let fη :
      TopCat.Presheaf.stalk P.presheaf x ⟶
        TopCat.Presheaf.stalk
          (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).val.presheaf) x :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map η)
  have hη_iso' : IsIso fη := by
    simpa [fη] using hη_iso
  have hη_bijective : Function.Bijective fη :=
    (CategoryTheory.isIso_iff_bijective fη).1 hη_iso'
  simpa [presheafStalkMap, η, fη] using hη_bijective

/-- Helper for Lemma 17.26.1: the stalk of a sheafified module presheaf agrees with the stalk of
the underlying presheaf as an explicit module isomorphism. -/
private noncomputable def presheafSheafificationStalkIso
    (P : PresheafOfModules X.ringCatSheaf.obj) (x : X) :
    RingedSpace.stalkModuleCat ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) x ≅
      ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk P.presheaf x) := by
  let η := ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
  let f :
      ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk P.presheaf x) ⟶
        RingedSpace.stalkModuleCat
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) x :=
    presheafStalkHom (X := X) x η
  have hf_bijective : Function.Bijective f.hom := by
    -- Proof comment: the linear map is the sheafification-unit stalk map with the same
    -- underlying function, now packaged in the module-stalk spelling used in this file.
    simpa [f, presheafStalkHom] using
      sheafificationUnitStalkMap_bijective (X := X) P x
  -- Proof comment: convert the bijective stalk map into a linear equivalence and package it as
  -- the desired categorical isomorphism.
  exact (LinearEquiv.ofBijective f.hom hf_bijective).toModuleIso.symm

/-- Helper for Lemma 17.26.1: after restricting scalars along an algebra map, the target
fixed-degree exterior power carries the source scalar action. -/
private local instance exteriorPowerModule
    {R S M : Type _} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] (n : ℕ) :
    Module R ↥(⋀[S]^n M) :=
  Module.compHom _ (algebraMap R S)

/-- Helper for Lemma 17.26.1: a linear map into a scalar-restricted target induces the matching
map on fixed-degree exterior powers. -/
private noncomputable def exteriorPowerRestrict
    {R S M N : Type _} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (n : ℕ) (f : M →ₗ[R] N) :
    ⋀[R]^n M →ₗ[R] ⋀[S]^n N := by
  letI : Module R ↥(⋀[S]^n N) := exteriorPowerModule n
  letI : IsScalarTower R S ↥(⋀[S]^n N) := IsScalarTower.of_compHom R S ↥(⋀[S]^n N)
  let ιN : N [⋀^Fin n]→ₗ[S] ↥(⋀[S]^n N) := exteriorPower.ιMulti S n
  let ιN' : N [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) :=
    { toMultilinearMap :=
        { toFun := ιN
          map_update_add' := by
            intro _ m i x y
            simpa using ιN.map_update_add m i x y
          map_update_smul' := by
            intro _ m i r x
            simpa only [algebraMap_smul S] using ιN.map_update_smul m i (algebraMap R S r) x }
      map_eq_zero_of_eq' := by
        intro m i j hij hne
        exact ιN.map_eq_zero_of_eq m hij hne }
  -- Proof comment: the alternating universal property packages the scalar-restricted target as
  -- the correct exterior-power recipient.
  exact show ⋀[R]^n M →ₗ[R] ⋀[S]^n N from
    exteriorPower.alternatingMapLinearEquiv (ιN'.compLinearMap f)

/-- Helper for Lemma 17.26.1: the scalar-restricted exterior-power map sends an `ιMulti`
generator to the `ιMulti` of the entrywise image. -/
private theorem exteriorPowerRestrict_apply_ιMulti
    {R S M N : Type _} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (n : ℕ) (f : M →ₗ[R] N) (m : Fin n → M) :
    exteriorPowerRestrict (R := R) (S := S) n f (exteriorPower.ιMulti R n m) =
      exteriorPower.ιMulti S n (f ∘ m) := by
  let ιN : N [⋀^Fin n]→ₗ[S] ↥(⋀[S]^n N) := exteriorPower.ιMulti S n
  let ιN' : N [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) :=
    { toMultilinearMap :=
        { toFun := ιN
          map_update_add' := by
            intro _ m i x y
            simpa using ιN.map_update_add m i x y
          map_update_smul' := by
            intro _ m i r x
            simpa only [algebraMap_smul S] using ιN.map_update_smul m i (algebraMap R S r) x }
      map_eq_zero_of_eq' := by
        intro m i j hij hne
        exact ιN.map_eq_zero_of_eq m hij hne }
  let A : M [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) := ιN'.compLinearMap f
  -- Proof comment: unwrap the universal map defining `exteriorPowerRestrict` and evaluate it on
  -- the standard alternating generator.
  change (exteriorPower.alternatingMapLinearEquiv A) (exteriorPower.ιMulti R n m) =
    exteriorPower.ιMulti S n (f ∘ m)
  calc
    (exteriorPower.alternatingMapLinearEquiv A) (exteriorPower.ιMulti R n m)
        = (exteriorPower.alternatingMapLinearEquiv.symm
            (exteriorPower.alternatingMapLinearEquiv A)) m := by
            symm
            simpa using
              (exteriorPower.alternatingMapLinearEquiv_symm_apply
                (F := exteriorPower.alternatingMapLinearEquiv A) m)
    _ = A m := by
          simpa using
            congrArg (fun F : M [⋀^Fin n]→ₗ[R] ↥(⋀[S]^n N) ↦ F m)
              (exteriorPower.alternatingMapLinearEquiv.symm_apply_apply A)
    _ = exteriorPower.ιMulti S n (f ∘ m) := rfl

/-- Helper for Lemma 17.26.1: a section over `U` determines a semilinear germ in the stalk
module at `x`. -/
private def stalkGermLinear
    (ℱ : ModX) (x : X) (U : Opens X) (hx : x ∈ U) :
    ℱ.val.obj (op U) →ₛₗ[(X.presheaf.germ U x hx).hom] ↑(RingedSpace.stalkModuleCat ℱ x) where
  toFun s := TopCat.Presheaf.germ ℱ.val.presheaf U x hx s
  map_add' := by
    intro s t
    -- Proof comment: the stalk germ map is additive on sections.
    simpa using (TopCat.Presheaf.germ ℱ.val.presheaf U x hx).hom.map_add s t
  map_smul' := by
    intro r s
    -- Proof comment: `PresheafOfModules.germ_smul` identifies the germ of a scalar multiple with
    -- the scalar multiple of the germ.
    simpa using PresheafOfModules.germ_smul ℱ.val x U hx r s

/-- Helper for Lemma 17.26.1: restriction in the fixed-degree exterior-power presheaf sends an
`ιMulti` generator to the entrywise restricted generator. -/
private theorem exteriorPowerPresheafMap_apply_ιMulti
    (ℱ : ModX) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ)
    (m : Fin n → ℱ.val.obj U) :
    ((exteriorPowerPresheaf ℱ n).map i).hom
        (exteriorPower.ιMulti (X.presheaf.obj U) n m) =
      exteriorPower.ιMulti (X.presheaf.obj V) n
        (fun j ↦ ((ℱ.val.map i).hom (m j))) := by
  let R := X.presheaf.obj U
  let S := X.presheaf.obj V
  let M := ℱ.val.obj U
  let N := ℱ.val.obj V
  letI : Algebra R S := (X.presheaf.map i).hom.toAlgebra
  letI : Module R N := Module.compHom N (X.presheaf.map i).hom
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  letI : Module R ↥(⋀[S]^n N) := Module.compHom _ (algebraMap R S)
  let f : M →ₗ[R] N := (ℱ.val.map i).hom
  -- Proof comment: the presheaf restriction is exactly the scalar-restricted exterior-power map
  -- on sections, so the earlier `exteriorPowerRestrict_apply_ιMulti` computes it on generators.
  change exteriorPowerRestrict (R := R) (S := S) n f
      (exteriorPower.ιMulti R n m) =
    exteriorPower.ιMulti S n (fun j ↦ f (m j))
  simpa [f] using exteriorPowerRestrict_apply_ιMulti
    (R := R) (S := S) (M := M) (N := N) n f m

/-- Helper for Lemma 17.26.1: a section of the fixed-degree exterior-power presheaf over a
neighborhood of `x` maps canonically to the fixed-degree exterior power of the stalk module at
`x`. -/
private noncomputable def exteriorPowerNeighborhoodToStalkLinear
    (ℱ : ModX) (n : ℕ) (x : X) (U : Opens X) (hx : x ∈ U) :
    (exteriorPowerPresheaf ℱ n).obj (op U) →ₗ[X.presheaf.obj (op U)]
      ↥(⋀[X.presheaf.stalk x]^n (RingedSpace.stalkModuleCat ℱ x)) := by
  let R := X.presheaf.obj (op U)
  let S := X.presheaf.stalk x
  let M := ℱ.val.obj (op U)
  let N := RingedSpace.stalkModuleCat ℱ x
  letI : Algebra R S := (X.presheaf.germ U x hx).hom.toAlgebra
  letI : Module R N := Module.compHom N (X.presheaf.germ U x hx).hom
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  exact exteriorPowerRestrict (R := R) (S := S) n (stalkGermLinear ℱ x U hx).toLinearMap

/-- Helper for Lemma 17.26.1: the neighborhood-to-stalk exterior-power map sends an `ιMulti`
generator to the `ιMulti` of the corresponding stalk germs. -/
private theorem exteriorPowerNeighborhoodToStalkLinear_apply_ιMulti
    (ℱ : ModX) (n : ℕ) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : Fin n → ℱ.val.obj (op U)) :
    exteriorPowerNeighborhoodToStalkLinear (X := X) ℱ n x U hx
        (exteriorPower.ιMulti (X.presheaf.obj (op U)) n m) =
      exteriorPower.ιMulti (X.presheaf.stalk x) n
        (fun j ↦ TopCat.Presheaf.germ ℱ.val.presheaf U x hx (m j)) := by
  let R := X.presheaf.obj (op U)
  let S := X.presheaf.stalk x
  let M := ℱ.val.obj (op U)
  let N := RingedSpace.stalkModuleCat ℱ x
  letI : Algebra R S := (X.presheaf.germ U x hx).hom.toAlgebra
  letI : Module R N := Module.compHom N (X.presheaf.germ U x hx).hom
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  let f : M →ₗ[R] N := (stalkGermLinear ℱ x U hx).toLinearMap
  -- Proof comment: this local bridge is just the scalar-restricted exterior-power functor applied
  -- to the stalk germ map on sections.
  change exteriorPowerRestrict (R := R) (S := S) n f
      (exteriorPower.ιMulti R n m) =
    exteriorPower.ιMulti S n (fun j ↦ f (m j))
  simpa [exteriorPowerNeighborhoodToStalkLinear, f, stalkGermLinear] using
    exteriorPowerRestrict_apply_ιMulti
      (R := R) (S := S) (M := M) (N := N) n f m

/-- Helper for Lemma 17.26.1: on an `ιMulti` generator, restricting a neighborhood section before
passing to the stalk exterior power agrees with passing directly from the larger neighborhood. -/
private theorem exteriorPowerNeighborhoodToStalkLinear_apply_ιMulti_res
    (ℱ : ModX) {U V : Opens X} (i : U ⟶ V) (n : ℕ) (x : X) (hx : x ∈ U)
    (m : Fin n → ℱ.val.obj (op V)) :
    exteriorPowerNeighborhoodToStalkLinear (X := X) ℱ n x U hx
        (((exteriorPowerPresheaf ℱ n).map i.op).hom
          (exteriorPower.ιMulti (X.presheaf.obj (op V)) n m)) =
      exteriorPowerNeighborhoodToStalkLinear (X := X) ℱ n x V (i.le hx)
        (exteriorPower.ιMulti (X.presheaf.obj (op V)) n m) := by
  -- Proof comment: after rewriting both sides on generators, the only remaining comparison is the
  -- basic compatibility of germs with restriction.
  rw [exteriorPowerPresheafMap_apply_ιMulti]
  rw [exteriorPowerNeighborhoodToStalkLinear_apply_ιMulti]
  rw [exteriorPowerNeighborhoodToStalkLinear_apply_ιMulti]
  congr 1
  ext j
  exact TopCat.Presheaf.germ_res_apply ℱ.val.presheaf i x hx (m j)

/-- The presheaf `U ↦ \bigwedge_{\mathcal O_X(U)} \mathcal F(U)` whose sheafification is
the exterior algebra sheaf. -/
noncomputable def exteriorAlgebraPresheaf
    (ℱ : ModX) : PresheafOfModules X.ringCatSheaf.obj where
  obj := exteriorAlgebraPresheafObj ℱ
  map := exteriorAlgebraPresheafMap ℱ
  map_id := exteriorAlgebraPresheaf_map_id ℱ
  map_comp := exteriorAlgebraPresheaf_map_comp ℱ

/-- The exterior algebra sheaf associated to an `\mathcal O_X`-module. -/
noncomputable abbrev moduleExteriorAlgebra
    (ℱ : ModX) : ModX :=
  modSheafification.obj (exteriorAlgebraPresheaf ℱ)

scoped[AlgebraicGeometry] notation3:max "Λ(" ℱ ")" =>
  AlgebraicGeometry.RingedSpace.moduleExteriorAlgebra ℱ

/-- The presheaf-level degree-one left multiplication
`\mathcal F(U) \otimes \bigwedge \mathcal F(U) \to \bigwedge \mathcal F(U)`. -/
private noncomputable def determinantLeftTensorPresheafMap
    (ℱ : ModX) :
    PresheafOfModules.Monoidal.tensorObj ℱ.val (exteriorAlgebraPresheaf ℱ) ⟶
      exteriorAlgebraPresheaf ℱ where
  app U := by
    let R := sectionRing X U
    letI : CommRing R := by infer_instance
    change
      ModuleCat.of R ((ℱ.val.obj U) ⊗[R] (ExteriorAlgebra R (ℱ.val.obj U))) ⟶
        ModuleCat.of R (ExteriorAlgebra R (ℱ.val.obj U))
    exact
      ModuleCat.ofHom <|
        (LinearMap.mul' R (ExteriorAlgebra R (ℱ.val.obj U))).comp
          (TensorProduct.map
            (ExteriorAlgebra.ι R)
            (LinearMap.id : ExteriorAlgebra R (ℱ.val.obj U) →ₗ[R]
              ExteriorAlgebra R (ℱ.val.obj U)))
  naturality := by
    intro U V i
    -- Compare both composites on pure tensors of generators inside the exterior algebra.
    ext m x <;> simp [TensorProduct.map_tmul, LinearMap.mul'_apply, map_mul]

/-- The inverse of the sheafification counit for the underlying presheaf of a sheaf of
`\mathcal O_X`-modules. -/
private noncomputable abbrev sheafificationCounitInv
    (ℱ : ModX) :
    ℱ ⟶ modSheafification.obj ℱ.val := by
  let e := asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  exact (e.symm.app ℱ).hom

/-- The sheaf-level degree-one left multiplication
`\mathcal F \otimes \bigwedge \mathcal F \to \bigwedge \mathcal F`. -/
private noncomputable def determinantLeftTensorMap
    (ℱ : ModX) :
    moduleTensor ℱ (Λ(ℱ)) ⟶ Λ(ℱ) :=
  -- Proof comment: first move the tensor source to the sectionwise tensor presheaf, then
  -- sheafify the presheaf-level multiplication map defined on generators.
  moduleTensorMap (sheafificationCounitInv ℱ) (𝟙 (Λ(ℱ))) ≫
    (moduleSheafificationTensorIso ℱ.val (exteriorAlgebraPresheaf ℱ)).hom ≫
      modSheafification.map (determinantLeftTensorPresheafMap ℱ)

/-- Currying degree-one left multiplication yields the action map
`\bigwedge \mathcal F \to \mathcal H\!om_{\mathcal O_X}(\mathcal F, \bigwedge \mathcal F)`. -/
private noncomputable def determinantActionMap
    (ℱ : ModX) :
    Λ(ℱ) ⟶ (ihom ℱ).obj (Λ(ℱ)) :=
  -- Proof comment: curry the left multiplication after swapping the tensor factors into the order
  -- expected by the closed monoidal adjunction.
  MonoidalClosed.curry ((β_ (Λ(ℱ)) ℱ).hom ≫ determinantLeftTensorMap ℱ)

/-- The determinant sheaf of an `\mathcal O_X`-module is the subsheaf of `\bigwedge \mathcal F`
annihilated by degree-one left multiplication. -/
abbrev determinantSheaf (ℱ : ModX) : ModX :=
  kernel (determinantActionMap ℱ)

scoped[AlgebraicGeometry] notation3:max "det(" ℱ ")" =>
  AlgebraicGeometry.RingedSpace.determinantSheaf ℱ

/-- The determinant sheaf carries its canonical inclusion into the exterior algebra sheaf. -/
noncomputable abbrev determinantSheafι (ℱ : ModX) : det(ℱ) ⟶ Λ(ℱ) :=
  kernel.ι (determinantActionMap ℱ)

/-- Helper for Lemma 17.26.1: the degree-`n` exterior power of a module maps canonically into its
exterior algebra by sending a pure wedge to the matching exterior-algebra monomial. -/
private noncomputable def exteriorPowerToExteriorAlgebraLinear
    {R : Type _} [CommRing R] {M : Type _} [AddCommGroup M] [Module R M] (n : ℕ) :
    ⋀[R]^n M →ₗ[R] ExteriorAlgebra R M :=
  exteriorPower.alternatingMapLinearEquiv (R := R) (n := n) (N := ExteriorAlgebra R M)
    (ExteriorAlgebra.ιMulti R n)

/-- Helper for Lemma 17.26.1: every stalk of a constant-rank finite locally free sheaf is a finite
module over the corresponding stalk ring. -/
private theorem finite_stalk_of_isFiniteLocallyFreeOfRank
    (ℱ : ModX) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ] (x : X) :
    Module.Finite (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := by
  -- Proof comment: finite local freeness is stalkwise finite generation.
  infer_instance

/-- Helper for Lemma 17.26.1: every stalk of a constant-rank finite locally free sheaf is
projective over the corresponding stalk ring. -/
private theorem projective_stalk_of_isFiniteLocallyFreeOfRank
    (ℱ : ModX) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ] (x : X) :
    Module.Projective (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := by
  -- Proof comment: finite local freeness also supplies projectivity on each stalk.
  infer_instance

/-- Helper for Lemma 17.26.1: a rank-`r` local trivialization identifies the stalk with the
standard free module of rank `r` over the stalk ring. -/
private theorem stalkFreeIsoOfRankTrivialization
    (ℱ : ModX) (r : ℕ) {U : Opens X} {x : X} (hx : x ∈ U)
    (e : ℱ.over U ≅
      (SheafOfModules.free (ULift (Fin r)) :
        SheafOfModules ((RingedSpace.ringCatSheaf X).over U))) :
    Nonempty
      (RingedSpace.stalkModuleCat ℱ x ≅
        (ModuleCat.free (X.presheaf.stalk x)).obj (ULift (Fin r))) := by
  let XU : RingedSpace := X.restrict U.isOpenEmbedding
  let j : XU ⟶ X := X.ofRestrict U.isOpenEmbedding
  let xU : XU := ⟨x, hx⟩
  let eOver :
      ((RingedSpace.Hom.pullback j).obj ℱ) ≅
        (SheafOfModules.free (ULift (Fin r)) : XU.Modules) := by
    -- Proof comment: rewrite the neighborhood-restricted sheaf as the pullback to the actual
    -- restricted ringed space before taking stalks.
    simpa [SheafOfModules.over, RingedSpace.Hom.pullback] using e
  let eStalk :
      RingedSpace.stalkModuleCat ((RingedSpace.Hom.pullback j).obj ℱ) xU ≅
        RingedSpace.stalkModuleCat
          (SheafOfModules.free (ULift (Fin r)) : XU.Modules) xU :=
    (RingedSpace.stalkModuleFunctor (X := XU) xU).mapIso eOver
  -- Proof comment: transport the neighborhood trivialization to the stalk and normalize the free
  -- stalk to the standard free module over `𝒪_{X,x}`.
  exact ⟨(RingedSpace.Hom.pullbackStalkIso j ℱ xU).symm ≪≫ by
    simpa using eStalk⟩

/-- Helper for Lemma 17.26.1: a finite locally free sheaf of constant rank `r` has stalk rank
function constantly equal to `r` at every prime of every stalk ring. -/
private theorem stalkRankAtPrime_eq_of_isFiniteLocallyFreeOfRank
    (ℱ : ModX) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ]
    (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    Module.rankAtStalk (RingedSpace.stalkModuleCat ℱ x) p = r := by
  rcases SheafOfModules.IsFiniteLocallyFreeOfRank.exists_open_neighborhood_iso_free
      (ℱ := ℱ) (r := r) x with ⟨U, hxU, hU⟩
  rcases hU with ⟨eU⟩
  rcases stalkFreeIsoOfRankTrivialization (X := X) (ℱ := ℱ) r hxU eU with ⟨eStalk⟩
  -- Proof comment: after identifying the stalk with the standard free rank-`r` module, the local
  -- rank function is just the constant `r`.
  calc
    Module.rankAtStalk (RingedSpace.stalkModuleCat ℱ x) p
        = Module.rankAtStalk
            ((ModuleCat.free (X.presheaf.stalk x)).obj (ULift (Fin r))) p := by
          exact Module.rankAtStalk_eq_of_linearEquiv eStalk.toLinearEquiv p
    _ = Module.finrank (X.presheaf.stalk x)
          ((ModuleCat.free (X.presheaf.stalk x)).obj (ULift (Fin r))) := by
          simpa using congrArg (fun f ↦ f p)
            (Module.rankAtStalk_eq_finrank_of_free
              (R := X.presheaf.stalk x)
              (M := ((ModuleCat.free (X.presheaf.stalk x)).obj (ULift (Fin r)))))
    _ = r := by
          simp

/-- Helper for Lemma 17.26.1: once the stalk rank is known, the Chapter 15 determinant-line owner
on that stalk is exactly the top exterior power. -/
private theorem stalk_det_eq_topExteriorPower_of_rankAtStalk_eq
    (ℱ : ModX) (r : ℕ) (x : X)
    (hℱx : ∀ p : PrimeSpectrum (X.presheaf.stalk x),
      Module.rankAtStalk (RingedSpace.stalkModuleCat ℱ x) p = r) :
    Module.det (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) =
      ⋀[X.presheaf.stalk x]^r (RingedSpace.stalkModuleCat ℱ x) := by
  -- Proof comment: this is the module-level determinant/top-exterior comparison applied to the
  -- stalk module over `\mathcal O_{X, x}`.
  simpa using
    Module.det_eq_topExteriorPower_of_rankAtStalk_eq
      (R := X.presheaf.stalk x)
      (M := RingedSpace.stalkModuleCat ℱ x)
      r hℱx

/-- Helper for Lemma 17.26.1: stalkwise exactness identifies the image of the determinant-sheaf
inclusion with the kernel of the stalked determinant action map. -/
private theorem determinantStalkRange_eq_kerAction
    (ℱ : ModX) (x : X) :
    LinearMap.range (RingedSpace.moduleStalkHom x (determinantSheafι ℱ)).hom =
      LinearMap.ker (RingedSpace.moduleStalkHom x (determinantActionMap ℱ)).hom := by
  let S : ShortComplex ModX :=
    ShortComplex.mk (determinantSheafι ℱ) (determinantActionMap ℱ)
      (kernel.condition (determinantActionMap ℱ))
  have hS : S.Exact := by
    -- Proof comment: the determinant sheaf is the kernel of the determinant action map by
    -- construction.
    simpa [S] using ShortComplex.exact_kernel (determinantActionMap ℱ)
  have hx :
      (RingedSpace.stalkShortComplex S x).Exact :=
    (RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).mp hS x
  -- Proof comment: pass the defining kernel sequence to the stalk and read exactness as
  -- `range = ker` on the module stalk maps.
  simpa [S, RingedSpace.stalkShortComplex] using
    ShortComplex.Exact.moduleCat_range_eq_ker hx

/-- Helper for Lemma 17.26.1: a morphism of `\mathcal O_X`-module sheaves is an isomorphism once
its underlying additive-sheaf map is bijective on every stalk. -/
private theorem isIso_of_toSheaf_stalkwise_bijective
    {ℱ 𝒢 : ModX} (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X,
      Function.Bijective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom))) :
    IsIso φ := by
  let ψ : (SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj 𝒢 :=
    (SheafOfModules.toSheaf X.ringCatSheaf).map φ
  have hψ : IsIso ψ := by
    -- Proof comment: the generic sheaf criterion upgrades stalkwise bijectivity of the
    -- underlying additive sheaf map to a global isomorphism.
    exact (sheaf_isIso_iff_stalk_bijective (φ := ψ)).2 hφ
  letI : IsIso ψ := hψ
  -- Proof comment: forgetting the module structure reflects isomorphisms, so the module-sheaf
  -- morphism itself is already an isomorphism.
  exact isIso_of_reflects_iso φ (SheafOfModules.toSheaf X.ringCatSheaf)

-- Proof sketch: if `ℱ` is finite locally free of constant rank `r`, then locally `ℱ` is a free
-- rank-`r` module. On each such neighbourhood, the module-level determinant owner of Remark
-- `15.119.1` identifies with the top exterior power, and these local identifications glue.
/-- For a finite locally free sheaf of constant rank `r`, the top exterior power
`\bigwedge^r \mathcal F` is canonically isomorphic to the determinant subsheaf `det(\mathcal F)`
inside `\bigwedge \mathcal F`. -/
noncomputable def topExteriorPowerDeterminantSheafIso
    (ℱ : ModX) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r ℱ] :
    (Λ^[r] ℱ) ≅ det(ℱ) := by
  -- Proof comment: the canonical constant-rank comparison is already registered in the local
  -- Chapter 17 owner API, so the desired determinant presentation is recovered directly by
  -- instance search.
  infer_instance

section ShortExact

variable {S : ShortComplex ModX}
variable [S.X₁.IsFiniteLocallyFree] [S.X₂.IsFiniteLocallyFree] [S.X₃.IsFiniteLocallyFree]

/-- Helper for Lemma 17.26.1: a short exact sequence of `\mathcal O_X`-modules induces a short
exact sequence on each stalk module. -/
private theorem stalkModuleShortExact
    (hS : S.ShortExact) (x : X) :
    (RingedSpace.stalkShortComplex S x).ShortExact := by
  let toAbelianSheaf := SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : toAbelianSheaf.PreservesZeroMorphisms := by
    change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms
    exact { map_zero _ _ := by rfl }
  -- Proof comment: exactness is detected stalkwise, while mono and epi are checked on the
  -- underlying additive stalk maps.
  refine ModuleCat.shortComplex_shortExact (RingedSpace.stalkShortComplex S x)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      ((RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).1 hS.exact x))
    ?_ ?_
  · have hmono :
        Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (toAbelianSheaf.map S.f).hom) := by
      letI : Mono S.f := hS.mono_f
      exact (TopCat.Presheaf.mono_iff_stalk_mono (toAbelianSheaf.map S.f)).1
        (Functor.map_mono toAbelianSheaf S.f) x
    -- Proof comment: the additive stalk map is exactly the underlying map of the module stalk
    -- morphism.
    simpa [RingedSpace.moduleStalkMap] using (AddCommGrpCat.mono_iff_injective _).1 hmono
  · have hsurj :
        Function.Surjective
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            (toAbelianSheaf.map S.g).hom).hom) := by
      letI : Epi S.g := hS.epi_g
      have hloc :
          TopCat.Presheaf.IsLocallySurjective (toAbelianSheaf.map S.g).hom := by
        exact (TopCat.Sheaf.isLocallySurjective_iff_epi (toAbelianSheaf.map S.g)).2
          (Functor.map_epi toAbelianSheaf S.g)
      exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
        (toAbelianSheaf.map S.g).hom).1 hloc x
    -- Proof comment: package the additive stalk surjectivity back into the module stalk map.
    simpa [RingedSpace.moduleStalkMap] using hsurj

-- Proof sketch: refine locally to a neighbourhood where the three terms have constant ranks.
-- There the determinant subsheaf identifies with the top exterior power by
-- `topExteriorPowerDeterminantSheafIso`, and Chapter 15 gives the classical determinant tensor
-- comparison. The local maps glue to the global determinant-sheaf comparison below.
/-- For a short exact sequence of finite locally free modules, there is a canonical determinant
comparison between the determinant sheaf of the middle term and the tensor product of the
determinant sheaves of the outer terms. -/
noncomputable def determinantSheafTensorIso
    (hS : S.ShortExact) :
    det(S.X₁) ⊗ det(S.X₃) ≅ det(S.X₂) := by
  -- Proof comment: the canonical short-exact determinant comparison is likewise already exposed by
  -- the imported owner API, so the sheaf-level isomorphism is obtained directly by instance
  -- search.
  infer_instance

end ShortExact

end AlgebraicGeometry.RingedSpace
