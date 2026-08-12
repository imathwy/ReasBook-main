import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_1_1
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_1_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- Corollary 1-1-10: For any set `X`, the canonical generators of `FreeGroup X` form a basis of
the free group on `X`. -/
theorem free_group_on_has_basis (X : Type u) :
    IsFreeGroupBasis (Set.range (FreeGroup.of : X → FreeGroup X)) :=
  (FreeGroupBasis.ofFreeGroup X).isFreeGroupBasis_range
