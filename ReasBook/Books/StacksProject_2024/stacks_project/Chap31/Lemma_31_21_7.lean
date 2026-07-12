import Mathlib
import StacksProject_2024.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall note: the source item records composition stability for the chapter-local
-- immersion-regularity owners from `Definition_31_21_1`, so the public API keeps those owners and
-- exposes composition through labeled source-facing theorems. We avoid global composition
-- instances here because they make instance search range over arbitrary composites.

section

variable {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)

/-- Lemma 31.21.7 (1): the composite of two regular immersions of schemes is a regular immersion. -/
@[stacks 067Q]
theorem isRegularImmersion_comp
    [IsRegularImmersion i] [IsRegularImmersion j] :
    IsRegularImmersion (i ≫ j) := sorry

/-- Lemma 31.21.7 (2): the composite of two Koszul-regular immersions of schemes is a
Koszul-regular immersion. -/
@[stacks 067Q]
theorem isKoszulRegularImmersion_comp
    [IsKoszulRegularImmersion i] [IsKoszulRegularImmersion j] :
    IsKoszulRegularImmersion (i ≫ j) := sorry

/-- Lemma 31.21.7 (3): the composite of two `H_1`-regular immersions of schemes is an
`H_1`-regular immersion. -/
@[stacks 067Q]
theorem isH1RegularImmersion_comp
    [IsH1RegularImmersion i] [IsH1RegularImmersion j] :
    IsH1RegularImmersion (i ≫ j) := sorry

/-- Lemma 31.21.7 (4): the composite of an `H_1`-regular immersion with a quasi-regular immersion
is a quasi-regular immersion. -/
@[stacks 067Q]
theorem isQuasiRegularImmersion_comp_of_isH1RegularImmersion
    [IsH1RegularImmersion i] [IsQuasiRegularImmersion j] :
    IsQuasiRegularImmersion (i ≫ j) := sorry

end

end AlgebraicGeometry
