import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_30_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners `Smooth`
-- and `IsImmersion`; local Chapter 29 precedent records commutative triangles with an explicit
-- equality such as `hcomm : i ≫ f = p`, and Chapter 31 records regular immersions as
-- `IsRegularImmersion`.

/-- Lemma 31.22.10: in a commutative triangle `Y -i-> X -f-> S` and `Y -p-> S`,
if `p` is syntomic, `f` is smooth, and `i` is an immersion, then `i` is a regular immersion. -/
@[stacks 067T]
theorem isRegularImmersion_of_syntomic_of_smooth_of_isImmersion
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (p : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] (hcomm : i ≫ f = p) (hp : Syntomic p) (hf : Smooth f) :
    IsRegularImmersion i := sorry

end AlgebraicGeometry
