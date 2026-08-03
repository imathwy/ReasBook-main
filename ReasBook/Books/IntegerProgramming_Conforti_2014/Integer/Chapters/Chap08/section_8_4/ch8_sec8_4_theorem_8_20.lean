import Integer.Chapters.Chap08.section_8_4.ch8_sec8_4_theorem_8_19

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain-style sampling for this refine pass:
-- * primary domain: finite cutting-stock optimization and fixed-parameter algorithmic complexity
-- * sampled owner declarations: Chapter 8.2 Example 8.15's `cutting_patterns` and Chapter 8.4
--   Example 8.15's `gilmore_gomory_feasible_set` and `gilmore_gomory_objective`, plus Chapter 8.4
--   Theorem 8.19's `cutting_stock_usage` bridge and `cutting_stock_usage.IsOptimal`, together with
--   the Chapter 9 algorithm owners `IntegralFeasibilityAlgorithm` and `ShortestVectorAlgorithm`
-- * source-facing layer: the cutting-stock input data `(w, W, b)` with the standard well-formedness
--   assumptions `0 < w_i` and `w_i ≤ W`
-- * core/canonical owner: Example 8.15's Gilmore-Gomory feasible-set and objective API
-- * bridge/view: the derived size parameter `largestEntry` used in the running-time statement
-- * primitive data: widths, stock width, demands, and the well-formedness assumptions
-- * derived API: feasible pattern type, usage vectors, optimality certificates,
--   and the running-time bound attached to a solver

section Theorem820

variable {m : ℕ}

/-- A cutting-stock input consists of the item widths `w`, the stock width `W`, and the demands
`b`, together with the standard well-formedness assumptions used in Theorem 8.19. -/
structure CuttingStockProblem (m : ℕ) where
  width : Fin m → ℕ
  stockWidth : ℕ
  demand : Fin m → ℕ
  width_pos : ∀ i, 0 < width i
  width_le_stockWidth : ∀ i, width i ≤ stockWidth

namespace CuttingStockProblem

/-- The largest entry in the natural cutting-stock formulation attached to `problem`. -/
def largestEntry (problem : CuttingStockProblem m) : ℕ :=
  max problem.stockWidth <|
    max (Finset.univ.sup fun i ↦ problem.width i) (Finset.univ.sup fun i ↦ problem.demand i)

/-- The type of optimal cutting-stock usage vectors for `problem`. -/
abbrev OptimalUsage (problem : CuttingStockProblem m) :=
  {x : cutting_stock_usage problem.width problem.stockWidth // x.IsOptimal problem.demand}

/-- A well-formed cutting-stock input has an optimal usage certificate by Theorem 8.19. -/
theorem exists_optimalUsage
    (problem : CuttingStockProblem m) :
    Nonempty problem.OptimalUsage := by
  obtain ⟨x, hx, _⟩ :=
    exists_optimal_cutting_stock_solution_with_log_pattern_bound
      problem.width problem.stockWidth problem.demand problem.width_pos problem.width_le_stockWidth
  exact ⟨⟨x, hx⟩⟩

end CuttingStockProblem

/-- The discrete logarithmic factor in the running-time bound, modeled on the largest input entry.
-/
def cutting_stock_log_factor (a : ℕ) : ℕ :=
  Nat.log2 (a + 1) + 1

/-- A running-time function has the Chapter 8.4 complexity bound when it is bounded by
`log a · 2^{O(m)}` with `a = problem.largestEntry`, uniformly over all cutting-stock inputs with
`m` item types. -/
def HasLogEntryExponentialRunningTime
    (runningTime : CuttingStockProblem m → ℕ) : Prop :=
  ∃ C c : ℕ, ∀ problem : CuttingStockProblem m,
    runningTime problem ≤
      cutting_stock_log_factor problem.largestEntry * (C * 2 ^ (c * m))

/-- An algorithm for the cutting-stock problem returns an optimal usage vector for every
well-formed input and satisfies the claimed `log a · 2^{O(m)}` running-time bound. -/
structure CuttingStockAlgorithm (m : ℕ) where
  solve : (problem : CuttingStockProblem m) → problem.OptimalUsage
  runningTime : CuttingStockProblem m → ℕ
  runningTime_bound :
    HasLogEntryExponentialRunningTime runningTime

/-- A cutting-stock algorithm coerces to its solver map. -/
instance cuttingStockAlgorithmCoeFun (m : ℕ) :
    CoeFun (CuttingStockAlgorithm m)
      (fun _ ↦
        (problem : CuttingStockProblem m) → problem.OptimalUsage) where
  coe algorithm := algorithm.solve

namespace CuttingStockAlgorithm

/-- The optimal usage vector returned by `algorithm` on `problem`. -/
abbrev output
    {m : ℕ}
    (algorithm : CuttingStockAlgorithm m)
    (problem : CuttingStockProblem m) :
    cutting_stock_usage problem.width problem.stockWidth :=
  (algorithm problem).1

/-- The output of a cutting-stock algorithm is optimal for the input demand vector. -/
theorem output_spec
    {m : ℕ}
    (algorithm : CuttingStockAlgorithm m)
    (problem : CuttingStockProblem m) :
    (algorithm.output problem).IsOptimal problem.demand :=
  (algorithm problem).2

/-- A cutting-stock algorithm satisfies its explicit `log a · 2^{O(m)}` running-time bound. -/
theorem runningTime_le
    {m : ℕ}
    (algorithm : CuttingStockAlgorithm m) :
    ∃ C c : ℕ, ∀ problem : CuttingStockProblem m,
      algorithm.runningTime problem ≤
        cutting_stock_log_factor problem.largestEntry * (C * 2 ^ (c * m)) :=
  algorithm.runningTime_bound

end CuttingStockAlgorithm

/-- Theorem 8.20. There exists an algorithm that computes an optimal solution to the cutting-stock
problem whose running time is `log a · 2^{O(m)}`, where `a` is the largest entry in the natural
cutting-stock input formulation. -/
theorem cutting_stock_has_log_entry_exponential_time_algorithm
    (m : ℕ) :
    Nonempty (CuttingStockAlgorithm m) := sorry

end Theorem820
