module

public import Topology_Munkres_2000.Book.Example_24_2.LexIco

public section

open Prod.Lex

universe u

/-- Example 24.2: If `X` is well ordered, then the dictionary-ordered product
`X ×ₗ Set.Ico (0 : ℝ) 1` is a linear continuum. -/
instance instLinearContinuumLexIco {X : Type u} [LinearOrder X] [WellFoundedLT X] :
    LinearContinuum (X ×ₗ Set.Ico (0 : ℝ) 1) := by
  -- Combine the explicit least-upper-bound construction with inferred density.
  refine { leastUpperBoundProperty := ?_ }
  exact LeastUpperBoundProperty.of_exists_isLUB exists_isLUB_lexIco
