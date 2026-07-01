import Mathlib
import stacks_project.Chap10.Situation_10_102_1
import stacks_project.Chap10.Lemma_10_102_3
import stacks_project.Chap10.Definition_10_102_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open LinearMap

variable {R : Type u} [CommRing R]
variable {e : ℕ}

namespace FiniteFreeComplex

variable (C : _root_.FiniteFreeComplex R e)

private abbrev adjacentLeftIndex (i : Fin (e - 1)) : Fin e :=
  ⟨i.1, by omega⟩

private abbrev adjacentRightIndex (i : Fin (e - 1)) : Fin e :=
  ⟨i.1 + 1, by omega⟩

private abbrev adjacentMiddleIndex (i : Fin (e - 1)) : Fin (e + 1) :=
  ⟨i.1 + 1, by omega⟩

-- Proof sketch: identify the complex with a split exact sum of two-term identity complexes. In
-- that model each differential is a projection onto a free summand of rank equal to the relevant
-- alternating sum, adjacent projection ranks add to the rank of the middle term, and the maximal
-- minors include a unit so the associated ideal is the unit ideal.
/-- Lemma 10.102.6: if the bounded finite free complex is isomorphic to a direct sum of trivial
two-term complexes, then each differential has the expected alternating rank formula, adjacent
differential ranks add to the rank of the middle term, and each ideal `I(φ_i)` is the unit ideal.
-/
theorem exteriorRank_diffAt_eq_alternatingRankFormula_of_isDirectSumOfTrivialComplexes
    (hC : IsDirectSumOfTrivialComplexes C.toChainComplex)
    (i : Fin e) :
    (exteriorRank (C.diffAt i) : ℤ) = C.alternatingRank i := sorry

/-- In the direct-sum-of-trivial-complexes situation, adjacent differential ranks add up to the
rank of the middle term. The index `i` corresponds to the consecutive differentials
`C_{i + 2} → C_{i + 1} → C_i`. -/
theorem adjacent_differential_exteriorRank_add_eq
    (hC : IsDirectSumOfTrivialComplexes C.toChainComplex)
    (i : Fin (e - 1)) :
    exteriorRank (C.diffAt (adjacentLeftIndex i)) +
        exteriorRank (C.diffAt (adjacentRightIndex i)) =
      C.rank (adjacentMiddleIndex i) := sorry

/-- In the direct-sum-of-trivial-complexes situation, the rank-minor ideal of every differential
is the unit ideal. -/
theorem rankMinorIdeal_diffAt_eq_top_of_isDirectSumOfTrivialComplexes
    (hC : IsDirectSumOfTrivialComplexes C.toChainComplex)
    (i : Fin e) :
    I(C.diffAt i) = ⊤ := sorry

end FiniteFreeComplex

end
