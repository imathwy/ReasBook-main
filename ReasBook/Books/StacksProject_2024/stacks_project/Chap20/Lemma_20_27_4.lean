import Mathlib.Tactic.Recall
import StacksProject_2024.Chap18.Definition_18_13_1
import StacksProject_2024.Chap20.Lemma_20_27_1

open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

universe u

variable {X Y : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.27.4:
- primary domain: derived pullback of module sheaves on a ringed space, viewed as derived
  extension of scalars from the inverse-image structure sheaf on `Y` to the structure sheaf on
  `X`;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `AlgebraicGeometry.RingedSpace.modulePullbackToDerived`,
  `AlgebraicGeometry.RingedSpace.modulePullbackToDerived_hasLeftDerivedFunctor`,
  `CategoryTheory.Functor.totalLeftDerivedCounit`;
- best owner abstraction:
  `source-facing`: the identification of `L(f)^*` as the left derived functor of the Chapter 18
    pullback owner `f^*`;
  `core/canonical`: `SheafOfModules.pullback`, `modulePullbackToDerived`, and the total-left-
    derived-functor witness attached to `totalLeftDerivedCounit`;
  `bridge/view`: the ringed-space notations `f^*` and `L(f)^*`.

Source/core/bridge triage:
- `source-facing`: Lemma `20.27.4` identifies `L(f)^*` as the left derived functor of the
  Chapter 18 pullback `f^*`;
- `core/canonical`: `modulePullbackToDerived`, `modulePullbackToDerived_hasLeftDerivedFunctor`,
  and `Functor.totalLeftDerivedCounit`;
- `bridge/view`: the underived/derived pullback notations `f^*` and `L(f)^*`.

Accordingly, this file should recall the Chapter 18 owner for module pullback and expose the
canonical `IsLeftDerivedFunctor` witness for `L(f)^*` through the generic
`totalLeftDerivedCounit`, rather than keeping the chapter-local counit wrapper on the theorem
surface. -/

/- Definition 18.13.1, specialized to ringed spaces: the pullback functor on module sheaves is
the canonical owner `SheafOfModules.pullback`, namely the extension-of-scalars functor from the
inverse-image module sheaf to the structure sheaf on `X`. -/
recall SheafOfModules.pullback

/- Lemma 20.27.1: the homotopy-category pullback functor built from `f^*` has an everywhere
defined total left derived functor. -/
recall modulePullbackToDerived_hasLeftDerivedFunctor

/- The generic total-left-derived owner provides the canonical counit exhibiting `L(f)^*` as that
left derived functor. -/
recall Functor.totalLeftDerivedCounit

section

variable (f : X ⟶ Y)
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [(f^*).Additive]

/-- Lemma 20.27.4: the derived pullback `L(f)^*` is the left derived functor of the Chapter 18
pullback `f^*`, expressed through the canonical homotopy-category source functor
`modulePullbackToDerived f` and the generic total-left-derived counit. -/
@[stacks 08DE]
instance modulePullbackDerived_isLeftDerivedFunctor :
    (L(f)^*).IsLeftDerivedFunctor
      ((modulePullbackToDerived f).totalLeftDerivedCounit DerivedCategory.Qh (ModuleQis Y))
      (ModuleQis Y) := by
  simpa [modulePullbackDerived] using
    (inferInstance :
      Functor.IsLeftDerivedFunctor
        ((modulePullbackToDerived f).totalLeftDerived DerivedCategory.Qh (ModuleQis Y))
        ((modulePullbackToDerived f).totalLeftDerivedCounit DerivedCategory.Qh (ModuleQis Y))
        (ModuleQis Y))

end

end

end AlgebraicGeometry.RingedSpace
