import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_20_8
import StacksProject_2024.stacks_project.Chap31.Lemma_31_21_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` only surfaced the ambient `IsImmersion` and
-- `IsLocallyNoetherian` API; local Chapter 31 precedent fixes the four regularity predicates
-- as the classes from `Definition_31_21_1`, with `List.TFAE` used for the analogous ideal-sheaf
-- equivalence in `Lemma_31_20_8`.

/-- Lemma 31.21.3: for an immersion into a locally Noetherian scheme, regular,
Koszul-regular, `H_1`-regular, and quasi-regular are equivalent. -/
@[stacks 063L]
theorem immersionRegularity_tfae
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] [IsLocallyNoetherian X] :
    List.TFAE
      [ IsRegularImmersion i
      , IsKoszulRegularImmersion i
      , IsH1RegularImmersion i
      , IsQuasiRegularImmersion i
      ] := sorry

end AlgebraicGeometry
