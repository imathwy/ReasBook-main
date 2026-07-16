import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced only the ambient `IsImmersion` API, while local
-- Chapter 31 precedent fixes the owner predicates as the classes from `Definition_31_21_1`.

/-- Lemma 31.21.2 (1): a regular immersion of schemes is Koszul-regular. -/
@[stacks 063K]
theorem isKoszulRegularImmersion_of_isRegularImmersion
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsRegularImmersion i] :
    IsKoszulRegularImmersion i := sorry

/-- Lemma 31.21.2 (2): a Koszul-regular immersion of schemes is `H_1`-regular. -/
@[stacks 063K]
theorem isH1RegularImmersion_of_isKoszulRegularImmersion
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsKoszulRegularImmersion i] :
    IsH1RegularImmersion i := sorry

/-- Lemma 31.21.2 (3): an `H_1`-regular immersion of schemes is quasi-regular. -/
@[stacks 063K]
theorem isQuasiRegularImmersion_of_isH1RegularImmersion
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsH1RegularImmersion i] :
    IsQuasiRegularImmersion i := sorry

end AlgebraicGeometry
