import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_57_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

-- Semantic recall: the dedicated `lean_leansearch` tool is unavailable in this environment.
-- Local Section 29.57 precedent in `Definition_29_57_1.lean` already fixes the canonical owner
-- `Scheme.Hom.degreesOfFibresBoundedBy`, so this item is stated as its composition rule.

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {n m : ℕ}

/-- Lemma 29.57.4: if `n` bounds the degrees of the fibres of `f` and `m` bounds the degrees of
the fibres of `g`, then `n * m` bounds the degrees of the fibres of `f ≫ g`. -/
theorem degreesOfFibresBoundedBy_comp
    (hf : degreesOfFibresBoundedBy f n) (hg : degreesOfFibresBoundedBy g m) :
    degreesOfFibresBoundedBy (f ≫ g) (n * m) := sorry

end Scheme.Hom
end AlgebraicGeometry
