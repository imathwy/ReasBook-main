import StacksProject_2024.Chap29.Definition_29_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

-- Semantic recall: `AlgebraicGeometry.universallyInjective_isStableUnderComposition` is the
-- canonical composition-stability owner, and `Radicial` is the source-facing source-layer owner.
-- The lemma below is the thin bridge back to the source formulation.

/-- Lemma 29.10.5: the composition of two radicial morphisms of schemes is radicial. -/
@[stacks 02V1, instance]
theorem radicial_comp_of_radicial [Radicial f] [Radicial g] :
    Radicial (f ≫ g) :=
  radicial_of_universallyInjective (f ≫ g)

end

end AlgebraicGeometry
