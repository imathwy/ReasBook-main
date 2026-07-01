import Mathlib.Tactic.Recall
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap06.Lemma_6_20_3
import stacks_project.Chap06.Lemma_6_22_1

open CategoryTheory TopologicalSpace
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
  sorry

-- Proof sketch: apply the standard identity axiom for the isomorphism `pullbackStalkIso f 𝒢 x`.
/-- The canonical stalk pullback isomorphism has inverse equalities as usual for an isomorphism. -/
theorem pullbackStalkIso_hom_inv_id (𝒢 : Y.Modules) (x : X) :
    (pullbackStalkIso f 𝒢 x).hom ≫ (pullbackStalkIso f 𝒢 x).inv =
      𝟙 ((ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
        (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x))) := sorry

end

end RingedSpace.Hom

end AlgebraicGeometry
