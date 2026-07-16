import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap15.«15_6_3_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CategoricalPullback

universe u

section

variable {C D Cp Dp : Type u}
variable [CommRing C] [CommRing D] [CommRing Cp] [CommRing Dp]
variable (f : D →+* C) (g : Cp →+* C) (p : Dp →+* D) (q : Dp →+* Cp)

/- Domain-style sampling for 15.7.1.1:
- primary domain: categorical base change for module categories over a commuting square of
  commutative rings;
- sampled owner abstractions:
  `ModuleCat.extendScalarsComp`,
  `moduleCatBaseChangeSquare`,
  `moduleCatBaseChangeToCategoricalPullback`,
  `CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback`;
- best owner abstraction: the chapter owner `moduleCatBaseChangeSquare`;
- primitive data: the commuting square of ring maps `Dp → D`, `Dp → Cp`, `D → C`, `Cp → C`,
  given by `p`, `q`, `f`, `g`, and a proof `f.comp p = g.comp q`;
- derived API: the induced functor `moduleCatBaseChangeToCategoricalPullback`, and the
  comparison isomorphism read directly as `(moduleCatBaseChangeSquare f g p q hcomm).iso`.

Source/core/bridge triage:
- `source-facing`: `moduleCatBaseChangeSquare`;
- `core/canonical`: `CatCommSqOver`;
- `bridge/view`: `moduleCatBaseChangeToCategoricalPullback`. -/

/- 15.7.1.1: for a commuting square of commutative rings `Dp → D`, `Dp → Cp`, `D → C`, and
`Cp → C`, the categorical base-change square of extension-of-scalars functors is the specialization
of the chapter owner `moduleCatBaseChangeSquare`. -/
recall moduleCatBaseChangeSquare

variable (hcomm : f.comp p = g.comp q)

/- Specialized square for the ring maps `p`, `q`, `f`, `g`. -/
#check (moduleCatBaseChangeSquare f g p q hcomm)

/- The induced functor
`Mod_{Dp} → Mod_D ×_[Mod_C] Mod_{Cp}` is the corresponding owner-derived pullback functor. -/
recall moduleCatBaseChangeToCategoricalPullback

/- Companion specialization to the same commuting square. -/
#check (moduleCatBaseChangeToCategoricalPullback f g p q hcomm)

/- The canonical base-change comparison between the two iterated extension-of-scalars functors is
the `iso` field of the owner square. -/
#check ((moduleCatBaseChangeSquare f g p q hcomm).iso :
  ModuleCat.extendScalars p ⋙ ModuleCat.extendScalars f ≅
    ModuleCat.extendScalars q ⋙ ModuleCat.extendScalars g)

variable (L : ModuleCat Dp)

/- The structural isomorphism on an object of the specialized pullback functor is definitionally
the component of that canonical comparison. -/
#check (((moduleCatBaseChangeToCategoricalPullback f g p q hcomm).obj L).iso :
  (ModuleCat.extendScalars f).obj ((ModuleCat.extendScalars p).obj L) ≅
    (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars q).obj L))

end
