import Mathlib
import StacksProject_2024.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall note: `lean_leansearch` recalled the scheme-morphism owners
-- `AlgebraicGeometry.Surjective`, `AlgebraicGeometry.IsSmooth`, and the base-change projection
-- `AlgebraicGeometry.Surjective.instSndScheme`, so the source statement is recorded directly as an
-- existence theorem for a smooth surjective cover whose pullback immersion is regular.

/-- A cover whose pullback along `i` is a regular immersion. -/
class RegularImmersionPullbackCover
    {X Z X' : Scheme.{u}} (i : Z ⟶ X) (f : X' ⟶ X) : Prop where
  surjective : Surjective f
  smooth : Smooth f
  isRegularImmersion : IsRegularImmersion (pullback.snd i f)

/-- The pullback morphism of a `RegularImmersionPullbackCover` is a regular immersion. -/
instance instIsRegularImmersionPullbackSndRegularImmersionPullbackCover
    {X Z X' : Scheme.{u}} {i : Z ⟶ X} {f : X' ⟶ X}
    [h : RegularImmersionPullbackCover i f] :
    IsRegularImmersion (pullback.snd i f) := h.isRegularImmersion

/-- Lemma 31.21.11: if `i : Z ⟶ X` is a Koszul-regular closed immersion, then there exists a
surjective smooth morphism `f : X' ⟶ X` such that the base change
`pullback.snd i f : pullback i f ⟶ X'` is a regular immersion. -/
@[stacks 0692]
theorem exists_smooth_surjective_regularImmersion_pullback
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsKoszulRegularClosedImmersion i] :
    ∃ (X' : Scheme.{u}) (f : X' ⟶ X), RegularImmersionPullbackCover i f := sorry

end AlgebraicGeometry
