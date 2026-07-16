import Mathlib
import DifferentialForms_Cartan_1970.cartan.VII.section29.«0002_Theorem_4»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

-- Semantic recall note: the `lean_leansearch` MCP tool was unavailable in this environment, so
-- this item is a bridge/view consequence of the section owner declaration
-- `IsHigherOrderHolomorphicOdeSolution` and the stronger existence-uniqueness theorem in
-- Theorem 4.

/-- Problem VII.3-extra-1: for a holomorphic `k`th-order scalar differential equation
`y^(k) = F (x, y, y', ..., y^(k - 1))` whose right-hand side is analytic at the prescribed
initial jet `(a, y₀)`, there exists a local holomorphic solution with that initial jet. -/
theorem exists_local_holomorphic_solution_of_higher_order_ode
    {k : ℕ} (hk : 0 < k) {F : ℂ × (Fin k → ℂ) → ℂ} {a : ℂ} {y₀ : Fin k → ℂ}
    (hF : AnalyticAt ℂ F (a, y₀)) :
    ∃ φ : ℂ → ℂ, IsHigherOrderHolomorphicOdeSolution k F a y₀ (φ : Germ (𝓝 a) ℂ) := by
  rcases exists_eventuallyEq_unique_solution_of_higher_order_holomorphic_ode hk hF with
    ⟨φ, hφ, _⟩
  exact ⟨φ, hφ⟩
