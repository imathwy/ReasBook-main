import StacksProject_2024.Chap29.Definition_29_15_1
import StacksProject_2024.Chap29.Lemma_29_37_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
`lean_leansearch` surfaced general scheme-morphism base-change owners such as
`quasiCompact_isStableUnderBaseChange`, but no canonical quasi-projective stability theorem.
Local Chapter 29 uses the source-facing owner `QuasiProjective` from `Definition_29_40_1`, and
records a base change of `f : X ⟶ S` along `g : S' ⟶ S` as `pullback.snd f g`. The proof source
is expected to combine finite-type base change (Lemma 29.15.4) with relative-ampleness base
change (Lemma 29.37.9).

The current read-only item environment cannot import `Definition_29_40_1`: its relative-ampleness
owner path rebuilds upstream Chapter 17 files before this target is elaborated, and that import
path fails outside this item. This file therefore records the source lemma as a labeled recall
block and checks the dependency-closed base-change surfaces instead of introducing a fake
replacement for `QuasiProjective`. The Stacks tag evidence is consistent with tag `0B3G`. -/

/- Lemma 29.40.2 (Stacks tag `0B3G`): a base change of a quasi-projective morphism is
quasi-projective.

When `Definition_29_40_1` is dependency-closed, the intended source-facing statement is:
`theorem QuasiProjective.pullback_snd {X S S' : Scheme} {f : X ⟶ S}
  (h : QuasiProjective f) (g : S' ⟶ S) : QuasiProjective (pullback.snd f g)`.
-/
#check fun {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) ↦
  pullback.snd f g
#check fun {X S : Scheme.{u}} (f : X ⟶ S) ↦
  AlgebraicGeometry.Scheme.Hom.FiniteType f
#check fun {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : X.Modules) ↦
  (Scheme.Modules.pullback (pullback.fst f g)).obj L

end AlgebraicGeometry
