import StacksProject_2024.Chap28.Definition_28_26_1
-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: the Chapter 28 owner for ampleness is `Scheme.Modules.IsAmple`, while pullback
of scheme modules is owned canonically by `i^*`. The local `Invertible` owner from
Definition 28.26.1 is a source-facing bridge to the canonical tensor-equivalence owner, so this
file only publicizes the minimal scheme-level pullback instance needed for the closed-immersion
ampleness statement. -/

variable {X Y Z : Scheme.{u}}
variable [MonoidalCategory X.Modules] [MonoidalCategory Y.Modules] [MonoidalCategory Z.Modules]

/-- Pullback of an invertible `\mathcal O_Y`-module along a morphism of schemes is again
invertible. -/
instance pullback_invertible
    (f : X ⟶ Y) (L : Y.Modules) [hL : Invertible L] :
    Invertible ((f^*).obj L) where
  isEquivalence_tensorRight := by
    sorry

namespace IsAmple

/-- If `L` is ample, then its restriction along a closed immersion is ample. -/
@[stacks 01PU]
theorem pullback_of_isClosedImmersion
    {i : Z ⟶ X} [IsClosedImmersion i]
    {L : X.Modules} [Invertible L] (hA : IsAmple L)
    : IsAmple ((i^*).obj L) :=
  sorry

end IsAmple

/-- Restriction along a closed immersion preserves ampleness. -/
instance instIsAmple_pullback_of_isClosedImmersion
    (i : Z ⟶ X) [IsClosedImmersion i] (L : X.Modules) [Invertible L] [hA : IsAmple L] :
    IsAmple ((i^*).obj L) :=
  hA.pullback_of_isClosedImmersion

end AlgebraicGeometry.Scheme.Modules
