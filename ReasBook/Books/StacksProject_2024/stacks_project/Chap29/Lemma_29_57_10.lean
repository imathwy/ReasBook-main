import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_57_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-fibre API
-- `Scheme.Hom.fiber` / `Scheme.Hom.fiberToSpecResidueField`; local Section 29.57 precedent
-- already fixes the owner predicates `degreesOfFibresBoundedBy` and `universallyBoundedFibres`.
-- This item is therefore stated as descent of those fibre-degree bounds along a surjective flat
-- morphism in a commutative triangle.

/-- Lemma 29.57.10: in a commutative triangle `f ≫ h = g`, if `g` has fibres of degree at most
`n` and `f` is surjective and flat, then `h` also has fibres of degree at most `n`. -/
@[stacks 03JB]
theorem degreesOfFibresBoundedBy_of_comp_of_flat_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ Z) [Flat f] [Surjective f]
    {n : ℕ} (hcomm : f ≫ h = g) (hg : degreesOfFibresBoundedBy g n) :
    degreesOfFibresBoundedBy h n := sorry

/-- Universal boundedness descends along a commutative triangle with a flat surjective left edge. -/
@[stacks 03JB]
theorem universallyBoundedFibres_of_comp_of_flat_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ Z) [Flat f] [Surjective f]
    (hcomm : f ≫ h = g) (hg : universallyBoundedFibres g) :
    universallyBoundedFibres h := sorry

end Scheme.Hom
end AlgebraicGeometry
