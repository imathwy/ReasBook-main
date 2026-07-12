import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 29.21.5: any open immersion is locally of finite presentation. This is a pure canonical
recall of mathlib's existing instance/theorem
`AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion`. -/
@[stacks 01TR]
theorem locallyOfFinitePresentation_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    LocallyOfFinitePresentation f := by
  exact AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion

end AlgebraicGeometry
