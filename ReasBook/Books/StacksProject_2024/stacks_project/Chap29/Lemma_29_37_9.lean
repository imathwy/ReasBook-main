import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Pullbacks

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` surfaced the canonical scheme-module pullback
`AlgebraicGeometry.Scheme.Modules.pullback`. Local Chapter 29 uses `pullback.snd f g` for
the base-changed morphism and `pullback.fst f g` for the projection to `X`.

The intended local owner is `RelativelyAmple` from Definition 29.37.1, but the current
read-only item environment cannot dependency-close that owner: direct elaboration of
`Definition_29_37_1.lean` fails in the upstream Chapter 28/17 ampleness import path. This file
therefore records the source lemma as a labeled recall block and checks the dependency-closed
base-change and module-pullback surfaces. The Stacks tag evidence is consistent with tag `0893`.
-/

/- Lemma 29.37.9 (Stacks tag `0893`): let `f : X ⟶ S` be a morphism of schemes, let `L` be
an invertible `𝒪_X`-module, and let `g : S' ⟶ S` be any morphism. If `L` is `f`-ample, then
the pulled-back module `(pullback.fst f g)^* L` on `X ×_S S'` is `pullback.snd f g`-ample.

When the Chapter 28/29 ampleness owners are dependency-closed, the intended source-facing
statement is the theorem skeleton with hypothesis `RelativelyAmple f L` and conclusion
`RelativelyAmple (pullback.snd f g)
  ((Scheme.Modules.pullback (pullback.fst f g)).obj L)`.
-/
#check fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ QuasiCompact f
#check fun {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) ↦
  pullback.snd f g
#check fun {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : X.Modules) ↦
  (Scheme.Modules.pullback (pullback.fst f g)).obj L

end AlgebraicGeometry
