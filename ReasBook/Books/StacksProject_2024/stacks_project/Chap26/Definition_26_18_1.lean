import Mathlib
import Mathlib.Tactic.Recall

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (X S S' : Scheme.{u})
variable [X.Over S]
variable (f : S' ⟶ S)
variable (R : Type u) [CommRing R]

-- Semantic recall: the source-facing notion "scheme over `S`" is the canonical mathlib/project
-- owner `Scheme.Over S`, and Chapter 26 base change downstream is organized through the slice
-- pullback functor `Over.pullback f`.
/- Source/core/bridge triage:
- `source-facing`: a scheme over `S` and its base change along `f : S' ⟶ S`.
- `core/canonical`: `Scheme.Over S`, `Scheme.asOver`, and `Over.pullback f`.
- `bridge/view`: `Scheme.canonicallyOverPullback`, `Over.pullback_obj_hom`, and the two
  `Scheme.asOver_pullback_*` lemmas below identifying the scheme-level pullback presentation with
  the slice-category base-change owner. -/
/- Definition 26.18.1: a scheme over `S` is an object of `Scheme.Over S`,
with structure morphism recovered by `Scheme.asOver`; base change along
`f : S' ⟶ S` is the pullback scheme `pullback (X ↘ S) f`, whose induced
structure over `S'` is supplied by `Scheme.canonicallyOverPullback`. In the
repository's canonical `Over`-language, this same base change object is
`(Over.pullback f).obj (Scheme.asOver X S)`. Over a ring `R`, this means over
`Spec (CommRingCat.of R)`. -/
recall AlgebraicGeometry.Scheme.Over
recall AlgebraicGeometry.Scheme.asOver
recall CategoryTheory.Over.pullback
#check pullback (X ↘ S) f
recall AlgebraicGeometry.Scheme.canonicallyOverPullback
recall CategoryTheory.Over.pullback_obj_hom
#check (inferInstance : (pullback (X ↘ S) f).Over S')
#check Spec (CommRingCat.of R)

namespace Scheme

/-- Definition 26.18.1, bridge to the canonical slice-category owner: the base change scheme
`pullback (X ↘ S) f` over `S'` is exactly the object obtained by applying `Over.pullback f` to the
scheme-over-`S` object `X.asOver`. -/
@[simp] theorem asOver_pullback
    {X S S' : Scheme.{u}} [X.Over S] (f : S' ⟶ S) :
    Scheme.asOver (pullback (X ↘ S) f) S' = (Over.pullback f).obj (Scheme.asOver X S) := rfl

/-- Definition 26.18.1, source-facing structure-morphism formula for the base changed scheme. -/
@[simp] theorem asOver_pullback_hom
    {X S S' : Scheme.{u}} [X.Over S] (f : S' ⟶ S) :
    (Scheme.asOver (pullback (X ↘ S) f) S').hom = pullback.snd (X ↘ S) f := rfl

end Scheme

end AlgebraicGeometry
