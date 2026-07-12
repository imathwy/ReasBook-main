import Mathlib.Tactic.Recall
import StacksProject_2024.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical base-change instance
  `AlgebraicGeometry.instLocallyOfFinitePresentationSndScheme`;
- local Chapter 29 precedent records the source phrase “of finite presentation” through
  `AlgebraicGeometry.Scheme.Hom.FinitePresentation`, so only the second clause remains a
  source-facing project theorem on that owner.
-/

/- Lemma 29.21.4 (1): the base change of a morphism which is locally of finite presentation is
locally of finite presentation. This is exactly the canonical mathlib pullback-stability instance
for `LocallyOfFinitePresentation`. -/
recall AlgebraicGeometry.instLocallyOfFinitePresentationSndScheme

namespace AlgebraicGeometry.Scheme.Hom

section

variable {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

/-- A finite-presentation morphism remains of finite presentation after pullback. -/
theorem FinitePresentation.pullback_snd (hf : FinitePresentation f) :
    FinitePresentation (pullback.snd f g) := by
  letI : FinitePresentation f := hf
  exact
    { toLocallyOfFinitePresentation := inferInstance
      toQuasiCompact := inferInstance
      toQuasiSeparated := inferInstance }

/-- Lemma 29.21.4 (2): the base change of a morphism of finite presentation is of finite
presentation. -/
@[stacks 01TS]
theorem finitePresentation_pullback_snd (hf : FinitePresentation f) :
    FinitePresentation (pullback.snd f g) := by
  exact FinitePresentation.pullback_snd f g hf

/-- Any base change of a finite-presentation morphism is of finite presentation. -/
@[stacks 01TS, instance]
instance instFinitePresentationPullbackSndOfFinitePresentation [FinitePresentation f] :
    FinitePresentation (pullback.snd f g) :=
  finitePresentation_pullback_snd f g inferInstance

end

end AlgebraicGeometry.Scheme.Hom
