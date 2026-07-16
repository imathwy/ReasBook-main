import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_20_2
import StacksProject_2024.stacks_project.Chap31.Lemma_31_20_1

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "𝒪X" => SheafOfModules.unit (RingedSpace.ringCatSheaf X)

section

variable (I : Subobject 𝒪X)

-- Semantic recall: the owner predicates for regular, Koszul-regular, `H_1`-regular, and
-- quasi-regular ideal sheaves are the chapter-local definitions in `Definition_31_20_2`, and
-- Lemma `31.20.1` provides the sequence-level implication chain reused here.

/-- Lemma 31.20.3 (1): for a ringed space, a regular sheaf of ideals is Koszul-regular. -/
@[stacks 063E]
theorem regularIdealSheaf_isKoszulRegularIdealSheaf (hI : IsRegularIdealSheaf I) :
    IsKoszulRegularIdealSheaf I := sorry

/-- Lemma 31.20.3 (2): for a ringed space, a Koszul-regular sheaf of ideals is `H_1`-regular. -/
@[stacks 063E]
theorem koszulRegularIdealSheaf_isH1RegularIdealSheaf (hI : IsKoszulRegularIdealSheaf I) :
    IsH1RegularIdealSheaf I := sorry

/-- Lemma 31.20.3 (3): for a ringed space, an `H_1`-regular sheaf of ideals is quasi-regular. -/
@[stacks 063E]
theorem h1RegularIdealSheaf_isQuasiRegularIdealSheaf (hI : IsH1RegularIdealSheaf I) :
    IsQuasiRegularIdealSheaf I := sorry

end

end AlgebraicGeometry.RingedSpace
