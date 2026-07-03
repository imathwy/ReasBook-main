import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_32
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

section

variable {m d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/- Proposition 3.33 is a `source-facing` optimality criterion for the owner objective
`fermatWeberObjective`. The relevant owner/bridge API already lives upstream in
`isMinOn_univ_iff_zero_mem_subdifferentialAt`, `euclideanSubdifferentialAt`,
`mem_euclideanSubdifferentialAt_iff`, and
`euclidean_subdifferentialAt_fermatWeberObjective_eq_finset_sum_piecewise`, so this file keeps
only the textbook minimizer criterion instead of introducing extra public wrapper predicates for
its two cases. -/
recall isMinOn_univ_iff_zero_mem_subdifferentialAt
recall euclideanSubdifferentialAt
recall mem_euclideanSubdifferentialAt_iff
recall fermatWeberObjective
recall euclidean_subdifferentialAt_fermatWeberObjective_eq_finset_sum_piecewise

-- Proof sketch: apply the real-valued Fermat criterion
-- `isMinOn_univ_iff_zero_mem_subdifferentialAt`, then rewrite zero subgradient membership through
-- the Euclidean bridge `euclideanSubdifferentialAt`. Away from the sites `Set.range a`, each
-- summand is differentiable, so the zero-subgradient condition becomes the vanishing of the
-- weighted sum of normalized displacement vectors. At a site `a j`, split off the nonsmooth term
-- indexed by `j`, use the Euclidean-norm subdifferential at the origin for that term, and rewrite
-- membership of the zero vector in the resulting translated closed ball as the residual norm bound.
/-- Proposition 3.33: for pairwise distinct sites and nonnegative weights, a point globally
minimizes the Fermat--Weber objective if and only if either it is not one of the sites and the
weighted normalized displacement vectors sum to zero, or it equals a site `a_j` and the norm of
the corresponding residual sum over the remaining sites is at most `ω_j`. -/
theorem isMinOn_fermatWeberObjective_iff_balance_or_site_bound
    (ω : Fin m → ℝ) (a : Fin m → E) (ha : Function.Injective a) (hω : ∀ i, 0 ≤ ω i) (x : E) :
    IsMinOn (fermatWeberObjective ω a) Set.univ x ↔
      let balance : Fin m → E := fun i ↦ ω i • ((‖x - a i‖)⁻¹ • (x - a i))
      (x ∉ Set.range a ∧ ∑ i, balance i = 0) ∨
        ∃ j : Fin m, x = a j ∧ ‖(Finset.univ.erase j).sum balance‖ ≤ ω j := sorry

end
