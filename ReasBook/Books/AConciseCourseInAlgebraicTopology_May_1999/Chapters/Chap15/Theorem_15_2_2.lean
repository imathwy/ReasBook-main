import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_3_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Definition_15_2_1

noncomputable section

open CategoryTheory
open Topology
open scoped CellularChainComplex

universe u

-- `Definition_15_2_1` owns the Chapter 15 skeletal pair, chain group, and boundary surface.
-- This file packages that imported source-facing API into the chain-complex comparison theorem.

/-- The Chapter 15 cellular differentials compose to zero, so the imported degreewise groups
`axiomaticCellularChainGroup X H n` package into a chain complex. -/
private theorem axiomaticCellularChainComplex_sq
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (n : ℕ) :
    axiomaticCellularBoundary X H (n + 1) ≫ axiomaticCellularBoundary X H n = 0 := sorry

/-- The Chapter 15 axiomatic chain complex `C_*(X)`, whose degree-`n` term is
`H_n(X^n, X^{n-1})` and whose differential is `axiomaticCellularBoundary X H n`. -/
def axiomaticCellularChainComplex
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of
    (fun n ↦ axiomaticCellularChainGroup X H n)
    (fun n ↦ axiomaticCellularBoundary X H n)
    (axiomaticCellularChainComplex_sq X H)

/-- The differential of `axiomaticCellularChainComplex X H` in degree `n` is the Chapter 15
cellular boundary `axiomaticCellularBoundary X H n`. -/
theorem axiomaticCellularChainComplex_d
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (n : ℕ) :
    (axiomaticCellularChainComplex X H).d (n + 1) n = axiomaticCellularBoundary X H n := by
  exact
    ChainComplex.of_d
      (fun n ↦ axiomaticCellularChainGroup X H n)
      (fun n ↦ axiomaticCellularBoundary X H n)
      (axiomaticCellularChainComplex_sq X H)
      n

/-- Theorem 15.2.2. For a CW complex `X` and a pair homology theory `H` with coefficient group
`π`, there are Chapter 13 cellular differential data on `X` and an explicit comparison morphism
from the axiomatically defined chain complex `C_*(X)` to the corresponding cellular chain complex
`C_*(X; π)`, and that comparison is an isomorphism. -/
theorem exists_cellularChainComplexWithCoefficientsIso
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    {π : Type} [AddCommGroup π] (H : PairHomologyTheory π) :
    ∃ data : CellularDifferentialFamily X,
      ∃ comparison : axiomaticCellularChainComplex X H ⟶ C_*(X, data, π),
        IsIso comparison := by
  sorry
