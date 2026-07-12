import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules

universe u

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
variable (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable [HasWeakSheafify JC RingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf JD RingCat.{u})

/- Domain-style sampling for Lemma 18.12.2:
- primary domain: inverse image / pullback of sheaves of modules along a morphism of topoi
  presented by a continuous functor;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `Definition_18_13_1`'s direct recall of `SheafOfModules.pullback`;
- best owner abstraction: the canonical pullback owner `SheafOfModules.pullback`;
- primitive data: a morphism of sheaves of rings, here the unit
  `((F.sheafAdjunctionContinuous RingCat JD JC).unit.app 𝒪) : 𝒪 ⟶ f_* f^{-1} 𝒪`;
- derived API: the specialization of `pullback` to that unit map.

Source/core/bridge triage:
- `source-facing`: the inverse-image functor on `𝒪`-modules for the morphism of topoi defined by
  `F`;
- `core/canonical`: `SheafOfModules.pullback`;
- `bridge/view`: the specialization along the adjunction unit map above.

This file should therefore recall the owner declaration directly and keep the unit-map
specialization only as a thin companion. -/

/- Lemma 18.12.2, owner form: the inverse image of sheaves of modules is the canonical pullback
functor `SheafOfModules.pullback`. -/
recall SheafOfModules.pullback

/- Lemma 18.12.2: for a morphism of topoi presented by a continuous functor `F : D ⥤ C`, the
inverse image of a sheaf of `𝒪`-modules on `D` is obtained by specializing `pullback` to the unit
map `𝒪 ⟶ f_* f^{-1} 𝒪`. -/
#check
  (pullback ((F.sheafAdjunctionContinuous RingCat JD JC).unit.app 𝒪) :
    SheafOfModules 𝒪 ⥤ _)
