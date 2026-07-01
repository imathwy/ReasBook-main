import Mathlib

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CategoricalPullback
open CategoricalPullback.CatCommSqOver

universe u

noncomputable section

section

variable {C D Cp Dp : Type u}
variable [CommRing C] [CommRing D] [CommRing Cp] [CommRing Dp]

/- Domain-style sampling for 15.6.3.1:
- primary domain: categorical base change for module categories over a commuting square of
  commutative rings;
- sampled owner declarations:
  `ModuleCat.extendScalarsComp`,
  `CategoricalPullback.CatCommSqOver`,
  `CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback`,
  `CategoricalPullback.iso`;
- best owner abstraction: the chapter owner should be the canonical module-category base-change
  square in `CatCommSqOver`, with the induced pullback functor derived from that owner and the
  comparison isomorphism read directly from its `iso` field;
- primitive data: the four ring maps `Dp → D`, `Dp → Cp`, `D → C`, `Cp → C` and the
  commutativity witness `f.comp p = g.comp q`;
- derived API: the induced functor to the categorical pullback, together with the owner field
  `(moduleCatBaseChangeSquare f g p q hcomm).iso`.

Source/core/bridge triage:
- `source-facing`: `moduleCatBaseChangeSquare`;
- `core/canonical`: `CatCommSqOver`;
- `bridge/view`: `moduleCatBaseChangeToCategoricalPullback`. -/

/-- The categorical base-change square of extension-of-scalars functors attached to a commuting
square of commutative rings. -/
noncomputable def moduleCatBaseChangeSquare
    (f : D →+* C) (g : Cp →+* C) (p : Dp →+* D) (q : Dp →+* Cp)
    (hcomm : f.comp p = g.comp q) :
    CatCommSqOver (ModuleCat.extendScalars f) (ModuleCat.extendScalars g) (ModuleCat Dp) where
  fst := ModuleCat.extendScalars p
  snd := ModuleCat.extendScalars q
  iso := (ModuleCat.extendScalarsComp p f).symm ≪≫
    eqToIso (congrArg (fun u ↦ ModuleCat.extendScalars u) hcomm) ≪≫
    ModuleCat.extendScalarsComp q g

/-- The canonical functor `Mod_Dp → Mod_D ×_[Mod_C] Mod_Cp` attached to a commuting square of
commutative rings. -/
noncomputable def moduleCatBaseChangeToCategoricalPullback
    (f : D →+* C) (g : Cp →+* C) (p : Dp →+* D) (q : Dp →+* Cp)
    (hcomm : f.comp p = g.comp q) :
    ModuleCat Dp ⥤ CategoricalPullback (ModuleCat.extendScalars f) (ModuleCat.extendScalars g) :=
  (toFunctorToCategoricalPullback
    (ModuleCat.extendScalars f) (ModuleCat.extendScalars g) (ModuleCat Dp)).obj
    (moduleCatBaseChangeSquare f g p q hcomm)

end
