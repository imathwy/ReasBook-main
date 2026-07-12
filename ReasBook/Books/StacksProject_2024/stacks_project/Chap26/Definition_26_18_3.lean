import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced the canonical owner
-- `MorphismProperty.IsStableUnderBaseChange`. Its slice-level specializations
-- `MorphismProperty.baseChange_obj` and `MorphismProperty.overPullbackMap`, built from the slice
-- pullback functor `Over.pullback`, are the corresponding object-over-base and morphism-over-base
-- views used in Chapter 26.
/- Source/core/bridge triage:
- `source-facing`: preservation of a property of schemes over a base, and of morphisms over a
  base, under arbitrary base change.
- `core/canonical`: `Over.pullback` is the base-change construction on schemes over a base, and
  `IsStableUnderBaseChange` is the canonical preservation owner for morphism properties.
- `bridge/view`: `baseChange_obj` and `overPullbackMap` are the slice-category specializations used
  to read this owner for objects and morphisms over a fixed base. -/

/- Definition 26.18.3 (1): for a property `P` of schemes over a base, saying that `P` is
preserved under arbitrary base change is the canonical requirement that the underlying morphism
property of the structure map be stable under base change; the resulting object-over-base
specialization is `baseChange_obj`. -/
recall MorphismProperty.IsStableUnderBaseChange

/- Definition 26.18.3 (2): for a property `P` of morphisms of schemes over a base, the base change
of a morphism over `S` along `S' ⟶ S` is expressed by the slice pullback functor
`Over.pullback`. The corresponding source-facing bridge theorems are
`MorphismProperty.baseChange_obj` for objects over a base and `MorphismProperty.overPullbackMap`
for morphisms over a base. -/
recall Over.pullback
recall MorphismProperty.baseChange_obj
recall MorphismProperty.overPullbackMap

namespace CategoryTheory.MorphismProperty

/-- Definition 26.18.3 (1), source-facing bridge: the canonical owner
`P.IsStableUnderBaseChange` is equivalent to preservation of the structure morphism of every
scheme over `S` after base change along any `S' ⟶ S`. -/
theorem isStableUnderBaseChange_iff_forall_baseChange_obj
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    P.IsStableUnderBaseChange ↔
      ∀ ⦃S S' : Scheme.{u}⦄ (f : S' ⟶ S) (X : Over S),
        P X.hom → P ((Over.pullback f).obj X).hom := by
  constructor
  · intro _ S S' f X hX
    exact baseChange_obj f X hX
  · intro h
    refine IsStableUnderBaseChange.of_forall_exists_isPullback ?_
    intro X Y Z f g _ hg
    haveI : HasPullback g f := hasPullback_symmetry f g
    refine ⟨pullback g f, pullback.snd g f, pullback.fst g f, ?_, ?_⟩
    · exact (IsPullback.of_hasPullback g f).flip
    · simpa using h f (Over.mk g) hg

end CategoryTheory.MorphismProperty
