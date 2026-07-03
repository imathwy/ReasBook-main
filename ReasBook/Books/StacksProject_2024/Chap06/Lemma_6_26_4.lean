import Mathlib.Tactic.Recall
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap06.Lemma_6_20_3
import StacksProject_2024.Chap06.Lemma_6_22_1

open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 6.26.4:
- primary domain: stalkwise base change for pullback of sheaves of modules along a morphism of
  ringed spaces;
- sampled owner declarations:
  `RingedSpace.Hom.pullback`,
  `sheafOfModules_pullback_stalkIso`,
  `TopCat.Sheaf.stalkPullbackIso`;
- best owner abstraction: no single upstream declaration already packages the ringed-space
  specialization, so the public owner here should be the morphism-attached stalk comparison for
  `f^*`;
- primitive data: a morphism of ringed spaces `f : X ⟶ Y`, an `\mathcal O_Y`-module sheaf `𝒢`,
  and a point `x : X`;
- derived API: the canonical stalk isomorphism expressing `((f^*).obj 𝒢)_x` as extension of
  scalars of `𝒢_{f(x)}` along the induced stalk map `f.hom.stalkMap x`.

Source/core/bridge triage:
- `source-facing`: the textbook stalk formula for `f^*`;
- `core/canonical`: `RingedSpace.Hom.pullback`, `sheafOfModules_pullback_stalkIso`, and
  `f.hom.stalkMap x`;
- `bridge/view`: `TopCat.Sheaf.stalkPullbackIso`, used only to identify the stalk of the inverse
  image sheaf with the stalk at the image point.

This file therefore must not stop at the two ingredient owners. It exposes the composed
ringed-space statement itself and keeps the ingredients only as proof-route data.
-/

/- Core owner ingredients used in the proof route. -/
recall sheafOfModules_pullback_stalkIso
recall TopCat.Sheaf.stalkPullbackIso

namespace RingedSpace.Hom

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

private abbrev inverseImageCommRingSheaf (f : X ⟶ Y) : TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf

private abbrev inverseImageRingSheaf (f : X ⟶ Y) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj
    (inverseImageCommRingSheaf f)

private noncomputable abbrev inverseImageRingUnit (f : X ⟶ Y) :
    Y.ringCatSheaf ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (inverseImageRingSheaf f) := by
  simpa [RingedSpace.ringCatSheaf, inverseImageCommRingSheaf, inverseImageRingSheaf] using
    (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app Y.sheaf)

private noncomputable abbrev inverseImageModule (f : X ⟶ Y) :
    Y.Modules ⥤ SheafOfModules (inverseImageRingSheaf f) :=
  SheafOfModules.pullback (inverseImageRingUnit f)

private noncomputable abbrev inverseImageStructureSheafHom (f : X ⟶ Y) :
    inverseImageRingSheaf f ⟶
      (Functor.sheafPushforwardContinuous (𝟭 (Opens X)) RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).map
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f) ≫
    (Functor.sheafPushforwardContinuousId RingCat.{u} (Opens.grothendieckTopology X)).inv.app
      X.ringCatSheaf

private instance pullbackStalkModule (𝒢 : Y.Modules) (x : X) :
    Module (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk ((f^*).obj 𝒢).val.presheaf x) := by
  let M : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) := ((f^*).obj 𝒢).val
  change Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x)
  infer_instance

/-- Helper for Lemma 6.26.4: a sheaf isomorphism of modules induces an isomorphism on the
corresponding stalk modules. -/
private noncomputable abbrev stalkModuleIsoOfIso {ℱ 𝒢 : X.Modules} (η : ℱ ≅ 𝒢) (x : X) :
    RingedSpace.stalkModuleCat ℱ x ≅ RingedSpace.stalkModuleCat 𝒢 x := by
  let φ : ℱ.val.presheaf ⟶ 𝒢.val.presheaf :=
    ((SheafOfModules.toSheaf X.ringCatSheaf).map η.hom).hom
  -- Take stalks of the underlying presheaf map and prove once that it respects the stalk scalar
  -- action, so it becomes a linear equivalence over `\mathcal O_{X, x}`.
  refine LinearEquiv.toModuleIso
    { toFun := fun t ↦ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ) t
      invFun := fun t ↦ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (((SheafOfModules.toSheaf X.ringCatSheaf).map η.inv).hom : 𝒢.val.presheaf ⟶ ℱ.val.presheaf)) t
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro a b
    exact ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ).hom.map_add a b
  · intro r m
    obtain ⟨U, hxU, rU, rfl⟩ := X.presheaf.germ_exist x r
    obtain ⟨V, hxV, mV, rfl⟩ := TopCat.Presheaf.germ_exist ℱ.val.presheaf x m
    let W : Opens X := U ⊓ V
    let hxW : x ∈ W := ⟨hxU, hxV⟩
    let iWU : W ⟶ U := homOfLE inf_le_left
    let iWV : W ⟶ V := homOfLE inf_le_right
    let rW : X.presheaf.obj (op W) := X.presheaf.map iWU.op rU
    let mW : ℱ.val.obj (op W) := ℱ.val.map iWV.op mV
    have hr : X.presheaf.germ W x hxW rW = X.presheaf.germ U x hxU rU := by
      exact ConcreteCategory.congr_hom (TopCat.Presheaf.germ_res X.presheaf iWU x hxW) rU
    have hm : TopCat.Presheaf.germ ℱ.val.presheaf W x hxW mW =
        TopCat.Presheaf.germ ℱ.val.presheaf V x hxV mV := by
      exact ConcreteCategory.congr_hom (TopCat.Presheaf.germ_res ℱ.val.presheaf iWV x hxW) mV
    have hsmul₁ :
        X.presheaf.germ W x hxW rW • TopCat.Presheaf.germ ℱ.val.presheaf W x hxW mW =
          TopCat.Presheaf.germ ℱ.val.presheaf W x hxW (rW • mW) := by
      symm
      simpa using (PresheafOfModules.germ_smul ℱ.val x W hxW rW mW)
    have hsmul₂ :
        TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW (rW • (η.hom.val.app (op W)) mW) =
          X.presheaf.germ W x hxW rW •
            TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW ((η.hom.val.app (op W)) mW) := by
      simpa using (PresheafOfModules.germ_smul 𝒢.val x W hxW rW ((η.hom.val.app (op W)) mW))
    -- Move both stalk representatives to a common neighborhood and use semilinearity there.
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ)
        (X.presheaf.germ U x hxU rU • TopCat.Presheaf.germ ℱ.val.presheaf V x hxV mV) = _
    rw [← hr, ← hm, hsmul₁]
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW φ (rW • mW)]
    rw [show (φ.app (op W)) (rW • mW) = rW • (η.hom.val.app (op W)) mW by
      simpa [φ] using (η.hom.val.app (op W)).hom.map_smul rW mW]
    rw [hsmul₂]
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW φ mW, hr]
    change X.presheaf.germ U x hxU rU •
        TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW ((η.hom.val.app (op W)) mW) =
      X.presheaf.germ U x hxU rU •
        TopCat.Presheaf.germ 𝒢.val.presheaf W x hxW ((η.hom.val.app (op W)) mW)
    rfl
  · intro t
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.germ_exist ℱ.val.presheaf x t
    let ψ : 𝒢.val.presheaf ⟶ ℱ.val.presheaf :=
      ((SheafOfModules.toSheaf X.ringCatSheaf).map η.inv).hom
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map ψ)
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ)
          (TopCat.Presheaf.germ ℱ.val.presheaf U x hU s)) =
      TopCat.Presheaf.germ ℱ.val.presheaf U x hU s
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hU φ s]
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hU ψ ((φ.app (op U)) s)]
    have hcomp : (η.hom.val.app (op U)) ≫ (η.inv.val.app (op U)) = 𝟙 _ := by
      exact congrArg (fun k ↦ k.val.app (op U)) η.hom_inv_id
    simpa [φ, ψ] using
      congrArg (fun z ↦ TopCat.Presheaf.germ ℱ.val.presheaf U x hU z)
        (ConcreteCategory.congr_hom hcomp s)
  · intro t
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.germ_exist 𝒢.val.presheaf x t
    let ψ : 𝒢.val.presheaf ⟶ ℱ.val.presheaf :=
      ((SheafOfModules.toSheaf X.ringCatSheaf).map η.inv).hom
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map φ)
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map ψ)
          (TopCat.Presheaf.germ 𝒢.val.presheaf U x hU s)) =
      TopCat.Presheaf.germ 𝒢.val.presheaf U x hU s
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hU ψ s]
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hU φ ((ψ.app (op U)) s)]
    have hcomp : (η.inv.val.app (op U)) ≫ (η.hom.val.app (op U)) = 𝟙 _ := by
      exact congrArg (fun k ↦ k.val.app (op U)) η.inv_hom_id
    simpa [φ, ψ] using
      congrArg (fun z ↦ TopCat.Presheaf.germ 𝒢.val.presheaf U x hU z)
        (ConcreteCategory.congr_hom hcomp s)

/-- Helper for Lemma 6.26.4: the inverse-image module stalk is naturally a module over the
inverse-image structure-sheaf stalk. -/
private instance inverseImageModuleStalkModule (𝒢 : Y.Modules) (x : X) :
    Module ↑(TopCat.Presheaf.stalk (inverseImageCommRingSheaf f).obj x)
      ↑(TopCat.Presheaf.stalk ((inverseImageModule f).obj 𝒢).val.presheaf x) := by
  let M : PresheafOfModules ((inverseImageCommRingSheaf f).obj ⋙ forget₂ CommRingCat RingCat) :=
    ((inverseImageModule f).obj 𝒢).val
  change Module ↑(TopCat.Presheaf.stalk (inverseImageCommRingSheaf f).obj x)
    ↑(TopCat.Presheaf.stalk M.presheaf x)
  infer_instance

/-- Helper for Lemma 6.26.4: after identifying inverse-image stalks with stalks over `f x`,
the source of the stalkwise base-change isomorphism is the expected extension of scalars. -/
private noncomputable abbrev inverseImagePullbackSourceStalkIso (𝒢 : Y.Modules) (x : X) :
    (ModuleCat.extendScalars
        (CommRingCat.Hom.hom
          ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
            (RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom))).obj
      (ModuleCat.of
        ↑(TopCat.Presheaf.stalk (inverseImageCommRingSheaf f).obj x)
      ↑(TopCat.Presheaf.stalk ((inverseImageModule f).obj 𝒢).val.presheaf x)) ≅
    (ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
      (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x)) := by
  -- TODO: package the additive stalk pullback isomorphism as a `ModuleCat` isomorphism over the
  -- exact transported stalk ring, then extend scalars along the raw inverse-image stalk map.
  sorry

/-- Helper for Lemma 6.26.4: the pullback-comparison isomorphism identifies the codomain of the
stalkwise base-change comparison with the final pullback stalk. -/
private noncomputable abbrev pullbackCompStalkIso (𝒢 : Y.Modules) (x : X) :
    ModuleCat.of
      ↑(TopCat.Presheaf.stalk (SheafedSpace.sheaf X).obj x)
      ↑(TopCat.Presheaf.stalk
        ((SheafOfModules.pullback
            (inverseImageStructureSheafHom f)).obj
          ((inverseImageModule f).obj 𝒢)).val.presheaf x) ≅
    RingedSpace.stalkModuleCat ((f^*).obj 𝒢) x := by
  -- TODO: stalk the `SheafOfModules.pullbackComp` component and then normalize the source from the
  -- functor-composition spelling to `((SheafOfModules.pullback (inverseImageStructureSheafHom f)).obj
  -- ((inverseImageModule f).obj 𝒢))`, and the target to `((f^*).obj 𝒢)`.
  sorry

-- Proof sketch: factor `f^*` as topological inverse image followed by the same-space change of
-- rings `f^{-1}\mathcal O_Y ⟶ \mathcal O_X`; then compose the owner-level stalk isomorphisms
-- `TopCat.Sheaf.stalkPullbackIso` and `sheafOfModules_pullback_stalkIso`, together with the
-- pullback-composition comparison from Lemma 6.26.3.
/-- Lemma 6.26.4: for a morphism of ringed spaces
`f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)`, an `\mathcal O_Y`-module sheaf `𝒢`, and a point
`x : X`, the stalk of `f^* 𝒢` at `x` is canonically the extension of scalars of the stalk
`𝒢_{f(x)}` along the induced local ring map
`\mathcal O_{Y, f(x)} \to \mathcal O_{X, x}`. -/
noncomputable abbrev pullbackStalkIso (𝒢 : Y.Modules) (x : X) :
    (ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
      (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x)) ≅
      RingedSpace.stalkModuleCat ((f^*).obj 𝒢) x := by
  let e₁ :=
    sheafOfModules_pullback_stalkIso
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f)
      ((inverseImageModule f).obj 𝒢) x
  let e₂ :=
    TopCat.Sheaf.stalkPullbackIso f.hom.base
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj 𝒢) x
  let e₃ := inverseImageStructureSheafHom f
  let e₄ := SheafOfModules.pullbackComp (inverseImageRingUnit f) e₃
  -- First rewrite the source of the stalkwise base-change isomorphism into the standard
  -- extended-scalars presentation along `f.hom.stalkMap x`.
  exact
    (inverseImagePullbackSourceStalkIso f 𝒢 x).symm ≪≫ e₁ ≪≫
      (pullbackCompStalkIso f 𝒢 x)

-- Proof sketch: apply the standard identity axiom for the isomorphism `pullbackStalkIso f 𝒢 x`.
/-- The canonical stalk pullback isomorphism has inverse equalities as usual for an isomorphism. -/
theorem pullbackStalkIso_hom_inv_id (𝒢 : Y.Modules) (x : X) :
    (pullbackStalkIso f 𝒢 x).hom ≫ (pullbackStalkIso f 𝒢 x).inv =
      𝟙 ((ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
        (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x))) := by
  -- This is the standard inverse identity for the canonical stalk isomorphism just constructed.
  exact (pullbackStalkIso f 𝒢 x).hom_inv_id

end

end RingedSpace.Hom

end AlgebraicGeometry
