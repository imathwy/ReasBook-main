import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_25_38 (from Items/Chap25) -/
open MeasureTheory ProbabilityTheory Topology
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

-- Proof sketch: stop the Brownian motion at an increasing exhaustion of relatively compact open
-- subsets of `G`, apply the harmonic-martingale characterization from the preceding Brownian Itô
-- results to `u (W_t)`, use optional stopping for the localized martingales, and pass to the exit
-- time by continuity and dominated convergence.
/-- Theorem 25.38 (1): if `u` solves the Dirichlet problem on `G` with boundary value `f`, then for
every `x ∈ G` the value `u x` is the Brownian exit expectation `E_x[f(W_{τ_{Gᶜ}})]`; equivalently,
it is the integral of `f` against the Brownian harmonic measure on `frontier G`, defined from a
frontier-valued exit map agreeing with the stopped Brownian path whenever the exit time is
finite. -/
theorem dirichlet_solution_eq_exit_expectation
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess) (G : Set State)
    (exitValue : Ω → frontier G) (hExitMeas : Measurable exitValue)
    {f : frontier G → ℝ} {u : State → ℝ}
    (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)
    (hExit :
      ∀ ω : Ω, hittingAfter W Gᶜ 0 ω < ⊤ →
        (exitValue ω : State) = stoppedValue W (hittingAfter W Gᶜ 0) ω)
    (hG : IsOpen G) (hGcpt : IsCompact (closure G))
    (hu : SolvesDirichletProblem G f u) :
    ∀ ⦃x : State⦄ (hx : x ∈ G),
      u x =
        ∫ ω, f (exitValue ω) ∂(P x : Measure Ω) := sorry

/-- Theorem 25.38 (1), harmonic-measure formulation: the Brownian exit expectation from
`dirichlet_solution_eq_exit_expectation` can be rewritten as the integral of `f` against the
canonical harmonic measure on `frontier G`. -/
theorem dirichlet_solution_eq_harmonicMeasure_integral
    (P : State → ProbabilityMeasure Ω) (W : VectorProcess) (G : Set State)
    (exitValue : Ω → frontier G) (hExitMeas : Measurable exitValue)
    {f : frontier G → ℝ} {u : State → ℝ}
    (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)
    (hExit :
      ∀ ω : Ω, hittingAfter W Gᶜ 0 ω < ⊤ →
        (exitValue ω : State) = stoppedValue W (hittingAfter W Gᶜ 0) ω)
    (hG : IsOpen G) (hGcpt : IsCompact (closure G))
    (hu : SolvesDirichletProblem G f u) :
    ∀ ⦃x : State⦄ (hx : x ∈ G),
      u x =
        ∫ y, f y ∂
          (harmonicMeasure P G exitValue hExitMeas ⟨x, hx⟩ : Measure (frontier G)) := by
  intro x hx
  have hfrontier_compact : IsCompact (frontier G) :=
    IsCompact.of_isClosed_subset hGcpt isClosed_frontier frontier_subset_closure
  have hcont_u : Continuous (fun y : frontier G ↦ u y) :=
    continuousOn_iff_continuous_restrict.mp
      (hu.continuousOn_closure.mono frontier_subset_closure)
  have hcont_f : Continuous f := by
    refine hcont_u.congr ?_
    intro y
    exact hu.boundary_eq y
  have hf :
      AEStronglyMeasurable f
        (harmonicMeasure P G exitValue hExitMeas ⟨x, hx⟩ : Measure (frontier G)) := by
    letI : CompactSpace (frontier G) := isCompact_iff_compactSpace.mp hfrontier_compact
    exact hcont_f.aestronglyMeasurable_of_compactSpace
  calc
    u x = ∫ ω, f (exitValue ω) ∂(P x : Measure Ω) :=
      dirichlet_solution_eq_exit_expectation P W G exitValue hExitMeas hW hExit hG hGcpt hu hx
    _ =
        ∫ y, f y ∂
          (harmonicMeasure P G exitValue hExitMeas ⟨x, hx⟩ : Measure (frontier G)) := by
      symm
      exact integral_harmonicMeasure P G exitValue hExitMeas ⟨x, hx⟩ hf

-- Proof sketch: apply part (1) to both solutions, using the harmonic-measure reformulation above.
-- On `G` the harmonic-measure representation gives the same value because the boundary datum is
-- the same, and on `frontier G` the two
-- solutions already agree with `f`; together with `closure G = G ∪ frontier G` for open `G`, this
-- yields equality on `closure G`.
/-- Theorem 25.38 (2): the Dirichlet problem on `G` with boundary value `f` has at most one
solution; any two solutions agree on `closure G`. -/
theorem dirichlet_problem_solution_unique
    (G : Set State) {f : frontier G → ℝ} {u v : State → ℝ}
    (hG : IsOpen G) (hGcpt : IsCompact (closure G))
    (hu : SolvesDirichletProblem G f u)
    (hv : SolvesDirichletProblem G f v) :
    Set.EqOn u v (closure G) := sorry

end ProbabilityTheory
