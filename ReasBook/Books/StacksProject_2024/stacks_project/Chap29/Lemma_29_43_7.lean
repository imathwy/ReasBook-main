import StacksProject_2024.Chap29.Definition_29_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
`Definition_29_43_1` already provides the source-facing owner `HProjective` on the chapter's
canonical projective-bundle surface. This file therefore states the composition lemma directly for
that owner, rather than leaving the item only as a recall of the generic
`MorphismProperty.IsStableUnderComposition` interface. The source tag is `01WE`. -/

section

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Lemma 29.43.7: a composition of H-projective morphisms is H-projective. -/
@[stacks 01WE, instance]
theorem hProjective_comp [HProjective f] [HProjective g] :
    HProjective (f ≫ g) := sorry

end

end AlgebraicGeometry
