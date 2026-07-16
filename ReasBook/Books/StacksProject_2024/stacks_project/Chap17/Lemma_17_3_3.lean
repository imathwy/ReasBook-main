import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_8_1
import StacksProject_2024.stacks_project.Chap06.Definition_6_10_1
import StacksProject_2024.stacks_project.Chap06.Lemma_6_21_5
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped TopCat AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.3.3:
- primary domain: adjunctions and exactness properties of pullback and pushforward functors on
  sheaves of modules and abelian sheaves over ringed spaces;
- inspected owner declarations:
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `Functor.sheafPullback`,
  `Functor.sheafPullbackConstruction.preservesFiniteLimits`,
  `Adjunction.rightAdjoint_preservesLimits`,
  `Adjunction.leftAdjoint_preservesColimits`,
  `leftExactFunctor`, `rightExactFunctor`, `exactFunctor_iff`;
- best owner abstraction: `SheafOfModules.pullbackPushforwardAdjunction` for module sheaves, and
  for the abelian-sheaf clause the site-level inverse-image owner
  `(Opens.map f.hom.base).sheafPullback AddCommGrpCat _ _` attached to the underlying continuous
  map, viewed through the canonical exactness predicate `exactFunctor`;
- primitive data: the ringed-space morphism `f`, packaged upstream as
  `RingedSpace.Hom.toRingCatSheafHom f`, together with the underlying continuous map
  `f.hom.base` for the abelian-sheaf clause;
- derived API: preservation of limits and colimits, left/right exactness, and exactness. -/

/- Source/core/bridge triage for Lemma 17.3.3:
- `source-facing`: the Stacks assertions that `f_*` is left exact, `f^*` is right exact, and the
  inverse-image functor on abelian sheaves attached to a morphism of ringed spaces is exact;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction` together with the owner
  predicates `leftExactFunctor`, `rightExactFunctor`, and `exactFunctor`, plus the canonical
  site-level pullback owner for `Opens.map f.hom.base`;
- `bridge/view`: the ringed-space specializations for module sheaves and the abelian-sheaf
  specialization along the underlying continuous map `f.hom.base`. -/

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

local notation "OX" => (RingedSpace.ringCatSheaf X)
local notation "OY" => (RingedSpace.ringCatSheaf Y)

/- Lemma 17.3.3: for a morphism of ringed spaces
`f : (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)`, the pushforward functor on module sheaves
commutes with all limits. -/
#synth PreservesLimits (f _*)

/- The direct image functor `f_*` on `\mathcal O_X`-modules is left exact. -/
#check
  (show leftExactFunctor (Mod(OX)) (Mod(OY)) (f _*) from
    by
      simpa [leftExactFunctor_iff] using
        (inferInstance : PreservesFiniteLimits (f _*)))

/- The pullback of `\mathcal O_Y`-modules along a morphism of ringed spaces commutes with all
colimits. -/
#synth PreservesColimits (f^*)

/- The inverse-image module functor `f^*` is right exact. -/
#check
  (show rightExactFunctor (Mod(OY)) (Mod(OX)) (f^*) from
    by
      simpa [rightExactFunctor_iff] using
        (inferInstance : PreservesFiniteColimits (f^*)))

/-- The inverse-image functor on abelian sheaves along the underlying continuous map of a morphism
of ringed spaces is exact. This is the abelian-sheaf clause of Lemma 17.3.3, stated at the
ringed-space bridge layer and derived from the canonical site-level pullback owner. -/
theorem ringedSpaceAbelianSheafPullback_exact :
    exactFunctor (Ab((Y : TopCat))) (Ab((X : TopCat))) ((f.hom.base)⁻¹) := by
  let G := Opens.map f.hom.base
  let JY := Opens.grothendieckTopology (Y : TopCat)
  let JX := Opens.grothendieckTopology (X : TopCat)
  change exactFunctor (Sheaf JY AddCommGrpCat) (Sheaf JX AddCommGrpCat)
    (G.sheafPullback AddCommGrpCat JY JX)
  let _ : HasSheafify JY AddCommGrpCat := inferInstance
  let _ : HasSheafify JX AddCommGrpCat := inferInstance
  let _ : RepresentablyFlat G := inferInstance
  let _ : PreservesFiniteLimits
      (G.op.lan :
        ((Opens (Y : TopCat))ᵒᵖ ⥤ AddCommGrpCat) ⥤
          ((Opens (X : TopCat))ᵒᵖ ⥤ AddCommGrpCat)) := by
    infer_instance
  let _ : PreservesFiniteLimits (G.sheafPullback AddCommGrpCat JY JX) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits G AddCommGrpCat JY JX
  let _ : PreservesFiniteColimits (G.sheafPullback AddCommGrpCat JY JX) := by
    let _ : (G.sheafPullback AddCommGrpCat JY JX).IsLeftAdjoint :=
      (G.sheafAdjunctionContinuous AddCommGrpCat JY JX).isLeftAdjoint
    infer_instance
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
