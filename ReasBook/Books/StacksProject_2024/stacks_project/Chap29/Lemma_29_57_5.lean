import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_57_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

-- Semantic recall: `lean_leansearch` pointed to the canonical base-change projection
-- `pullback.snd`; local Section 29.57 precedent already fixes the owner
-- `Scheme.Hom.degreesOfFibresBoundedBy`, so this item is stated directly for that predicate.

/-- Lemma 29.57.5: if `n` bounds the degrees of the fibres of `f`, then for any morphism
`g : Y' ⟶ Y` the same `n` bounds the degrees of the fibres of the base change
`pullback.snd f g : Y' ×[Y] X ⟶ Y'`. -/
@[stacks 03J7]
theorem degreesOfFibresBoundedBy_baseChange
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) {n : ℕ}
    (h : degreesOfFibresBoundedBy f n) :
    degreesOfFibresBoundedBy (pullback.snd f g) n := sorry

/-- Any base change of a morphism with universally bounded fibres again has universally bounded
fibres. -/
theorem universallyBoundedFibres_baseChange
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : universallyBoundedFibres f) :
    universallyBoundedFibres (pullback.snd f g) := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, degreesOfFibresBoundedBy_baseChange f g hn⟩

end Scheme.Hom
end AlgebraicGeometry
