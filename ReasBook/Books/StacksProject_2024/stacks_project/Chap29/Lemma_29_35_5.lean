import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_35_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the ring-level base-change owner `RingHom.IsStableUnderBaseChange`
  and the unramified base-change instance `Algebra.Unramified.baseChange`;
- local Chapter 29 precedent `Lemma_29_14_6.lean` records the scheme-side base-change owner on the
  canonical pullback projection `pullback.snd f g`;
- the source-facing owners for this section are the local classes `Unramified` and `GUnramified`
  from `Lemma_29_35_9.lean`, so this item is stated directly for those owners on
  `pullback.snd f g`.
-/

section

variable {X S S' : Scheme.{u}}

/-- Lemma 29.35.5 (1): the base change of an unramified morphism is unramified. -/
@[stacks 02GA]
theorem unramified_pullback_snd (f : X ⟶ S) [Unramified f] (g : S' ⟶ S) :
    Unramified (pullback.snd f g) := sorry

/-- Lemma 29.35.5 (2): the base change of a G-unramified morphism is G-unramified. -/
@[stacks 02GA]
theorem gUnramified_pullback_snd (f : X ⟶ S) [GUnramified f] (g : S' ⟶ S) :
    GUnramified (pullback.snd f g) := sorry

end

end AlgebraicGeometry
