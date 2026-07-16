import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_22_10

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced mathlib's canonical scheme-morphism owner
-- `IsSmooth`; local Stacks files use the project-facing abbreviation `Smooth`, and Lemma
-- 31.22.10 fixes the same commutative-triangle shape with `IsRegularImmersion`.

/-- Lemma 31.22.11: in a commutative triangle `Y -i-> X -f-> S` and `Y -p-> S`,
if `p` and `f` are smooth and `i` is an immersion, then `i` is a regular immersion. -/
@[stacks 067U]
theorem isRegularImmersion_of_smooth_of_smooth_of_isImmersion
    {Y X S : Scheme.{u}} (i : Y ⟶ X) (p : Y ⟶ S) (f : X ⟶ S)
    [IsImmersion i] (hcomm : i ≫ f = p) (hp : Smooth p) (hf : Smooth f) :
    IsRegularImmersion i := sorry

end AlgebraicGeometry
