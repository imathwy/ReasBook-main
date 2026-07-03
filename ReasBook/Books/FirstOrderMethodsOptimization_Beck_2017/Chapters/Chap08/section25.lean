import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_8_25 (from Chap08) -/
open scoped BigOperators

universe u v

section

variable {Source : Type u} {Link : Type v}
variable [Fintype Source] [DecidableEq Source] [DecidableEq Link]

/- Definition 8.25 is `source-facing`: the textbook introduces a finite-source, finite-link
network utility maximization problem. Domain sampling against earlier Chapter 8 items shows that
the canonical owner for the optimization statement itself is mathlib's `IsMaxOn`; the genuinely
new local objects are the total-utility objective and the feasible rate set cut out by the
capacity and box constraints. The link-user sets `S(ℓ)` are derivable from the primitive
per-source route data `linksUsedBySource`, so they are not packaged as a second public owner. -/

/-- The total utility of a source-rate vector `x`, obtained by summing the utilities
`u_s (x_s)` over all sources. -/
def network_utility_objective (u : Source → ℝ → ℝ) : (Source → ℝ) → ℝ :=
  fun x ↦ ∑ s : Source, u s (x s)

-- Proof sketch: unfold `network_utility_objective`; it is definitionally the finite sum of the
-- source utilities evaluated at the corresponding coordinates of `x`.
/-- Evaluating `network_utility_objective u` at `x` gives the finite sum
`∑ s, u s (x s)`. -/
@[simp] theorem network_utility_objective_apply
    (u : Source → ℝ → ℝ) (x : Source → ℝ) :
    network_utility_objective u x = ∑ s : Source, u s (x s) := by
  -- Unfolding the objective exposes exactly the textbook sum of source utilities.
  rfl

/-- The total load induced on a link `ℓ` by the source-rate vector `x`, obtained by summing the
rates of the sources whose routes use `ℓ`. -/
def network_link_load
    (linksUsedBySource : Source → Finset Link) (x : Source → ℝ) (ℓ : Link) : ℝ :=
  ∑ s : Source, if ℓ ∈ linksUsedBySource s then x s else 0

-- Proof sketch: unfold `network_link_load`; it is definitionally the finite sum over all sources
-- with the indicator term selecting exactly those sources whose route contains `ℓ`.
/-- Evaluating `network_link_load linksUsedBySource x` at `ℓ` gives the sum of the rates
`x_s` over the sources whose routes use `ℓ`. -/
@[simp] theorem network_link_load_eq_sum
    (linksUsedBySource : Source → Finset Link) (x : Source → ℝ) (ℓ : Link) :
    network_link_load linksUsedBySource x ℓ =
      ∑ s : Source, if ℓ ∈ linksUsedBySource s then x s else 0 := by
  -- Unfolding the link load exposes the indicator-weighted sum over all sources.
  rfl

/-- Definition 8.25: the feasible rate vectors for the network utility maximization problem
`(8.91)` are those satisfying every link-capacity constraint
`∑_{s ∈ S(ℓ)} x_s ≤ c_ℓ` and every box constraint `x_s ∈ [0, M_s]`. -/
def network_utility_maximization_feasible_set
    (linksUsedBySource : Source → Finset Link) (c : Link → ℝ) (M : Source → ℝ) :
    Set (Source → ℝ) :=
  {x |
    (∀ ℓ : Link, network_link_load linksUsedBySource x ℓ ≤ c ℓ) ∧
      ∀ s : Source, x s ∈ Set.Icc 0 (M s)}

-- Proof sketch: unfold `network_utility_maximization_feasible_set`; membership is exactly the
-- conjunction of the link-capacity constraints and the interval constraints `x_s ∈ [0, M_s]`.
/-- Membership in `network_utility_maximization_feasible_set linksUsedBySource c M` means that
every link load is bounded by capacity and every source rate lies in its interval `[0, M_s]`. -/
@[simp] theorem mem_network_utility_maximization_feasible_set
    {linksUsedBySource : Source → Finset Link} {c : Link → ℝ} {M : Source → ℝ}
    {x : Source → ℝ} :
    x ∈ network_utility_maximization_feasible_set linksUsedBySource c M ↔
      (∀ ℓ : Link, network_link_load linksUsedBySource x ℓ ≤ c ℓ) ∧
        ∀ s : Source, x s ∈ Set.Icc 0 (M s) := by
  -- Membership is definitionally the conjunction of all capacity and box constraints.
  rfl

-- Proof sketch: rewrite `IsMaxOn` using `isMaxOn_iff` and keep the maximizer's own feasibility
-- explicit, since `IsMaxOn` alone only compares against feasible points and does not imply
-- membership of `x` in the feasible set.
/-- Helper for Definition 8.25: a feasible rate vector `x` maximizes the network utility
on `network_utility_maximization_feasible_set linksUsedBySource c M` exactly when every other
feasible rate vector has no larger total utility. -/
theorem mem_and_isMaxOn_network_utility_maximization_feasible_set_iff
    {u : Source → ℝ → ℝ} {linksUsedBySource : Source → Finset Link}
    {c : Link → ℝ} {M : Source → ℝ} {x : Source → ℝ} :
    x ∈ network_utility_maximization_feasible_set linksUsedBySource c M ∧
      IsMaxOn
        (network_utility_objective u)
        (network_utility_maximization_feasible_set linksUsedBySource c M)
        x ↔
      (∀ ℓ : Link, network_link_load linksUsedBySource x ℓ ≤ c ℓ) ∧
        (∀ s : Source, x s ∈ Set.Icc 0 (M s)) ∧
        ∀ y : Source → ℝ,
          (∀ ℓ : Link, network_link_load linksUsedBySource y ℓ ≤ c ℓ) →
            (∀ s : Source, y s ∈ Set.Icc 0 (M s)) →
              network_utility_objective u y ≤ network_utility_objective u x := by
  constructor
  · rintro ⟨hx, hmax⟩
    rw [isMaxOn_iff] at hmax
    refine ⟨hx.1, hx.2, ?_⟩
    -- Any feasible comparison point `y` lies in the same feasible set, so `hmax` applies.
    intro y hy_capacity hy_box
    exact hmax y ⟨hy_capacity, hy_box⟩
  · rintro ⟨hx_capacity, hx_box, hopt⟩
    refine ⟨⟨hx_capacity, hx_box⟩, ?_⟩
    rw [isMaxOn_iff]
    -- Repackaging feasibility as set membership reduces the comparison step to `hopt`.
    intro y hy
    exact hopt y hy.1 hy.2

-- Proof sketch: unfold `IsMaxOn` and rewrite feasibility with
-- `mem_network_utility_maximization_feasible_set`. This yields exactly the textbook statement
-- that `x` satisfies the NUM constraints and has utility at least that of every other feasible
-- rate vector.
/-- Solving the network utility maximization problem means maximizing
`network_utility_objective u x = ∑ s, u_s(x_s)` on
`network_utility_maximization_feasible_set linksUsedBySource c M`. -/
theorem isMaxOn_network_utility_maximization_feasible_set_iff
    {u : Source → ℝ → ℝ} {linksUsedBySource : Source → Finset Link}
    {c : Link → ℝ} {M : Source → ℝ} {x : Source → ℝ} :
    IsMaxOn
        (network_utility_objective u)
        (network_utility_maximization_feasible_set linksUsedBySource c M)
        x ↔
      (∀ ℓ : Link, network_link_load linksUsedBySource x ℓ ≤ c ℓ) ∧
        (∀ s : Source, x s ∈ Set.Icc 0 (M s)) ∧
        ∀ y : Source → ℝ,
          (∀ ℓ : Link, network_link_load linksUsedBySource y ℓ ≤ c ℓ) →
            (∀ s : Source, y s ∈ Set.Icc 0 (M s)) →
              network_utility_objective u y ≤ network_utility_objective u x := by
  -- Route correction: `IsMaxOn` does not encode `x ∈ feasible_set`, so the displayed
  -- right-hand side is stronger than the left-hand side. The corrected equivalence is
  -- `mem_and_isMaxOn_network_utility_maximization_feasible_set_iff`.
  sorry

end

/-! ### Theorem_8_25 (from Chap08) -/
universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k

/- Theorem 8.25 is `source-facing`: it is the convergence criterion for the concrete projected
subgradient iterates under a general positive stepsize rule. The canonical owners already present
in the chapter are the recursive iterate sequence `projected_subgradient_method`, the running-best
objective owner `best_achieved_function_value`, the standing problem assumptions
`IsConstrainedConvexProblem`, and the subgradient bound package `SubgradientNormBoundOn`.
Accordingly, the theorem is stated directly in terms of those owners and the textbook's ratio
condition on the partial sums of `t_k` and `t_k^2`, without introducing a surrogate wrapper for
dynamic stepsize schedules. -/

-- Proof sketch: apply Lemma 8.24 to an arbitrary optimal point `xStar ∈ XStar`, then use the
-- uniform bound from `h_bound` and the prefix-minimality of `best_achieved_function_value` to
-- derive
-- `f_best^k - fOpt ≤ ‖x0 - xStar‖^2 / (2 ∑_{n ≤ k} t_n) +
--   h_bound.L_f^2 * (∑_{n ≤ k} t_n^2) / (2 ∑_{n ≤ k} t_n)`.
-- The hypothesis on the ratio of partial sums forces the second term to vanish, and positivity of
-- the stepsizes implies `∑_{n ≤ k} t_n → ∞`, so the first term also tends to `0`.
/-- Theorem 8.25: under Assumptions 8.7 and 8.12, if the projected subgradient method uses
positive stepsizes and the ratio
`(∑_{n=0}^k t_n^2) / (∑_{n=0}^k t_n)` tends to `0`, then the best objective value achieved by the
first `k + 1` iterates converges to the optimal value `fOpt`. -/
theorem projected_subgradient_method_best_value_gap_tendsto_zero_of_stepsize_ratio
    (h_bound : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f (x[n] : E))
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_ratio :
      Filter.Tendsto
        (fun k ↦
          (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ)) /
            Finset.sum (Finset.range (k + 1)) fun n ↦ t n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k ↦
        best_achieved_function_value (fun y : E ↦ (f y).toReal) (fun n ↦ (x[n] : E)) k - fOpt)
      Filter.atTop (nhds 0) := sorry

end
