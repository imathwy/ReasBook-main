import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

noncomputable section

open scoped BigOperators Rockafellar

namespace Function

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.8 computes the one-multiplier Lagrangian and dual objective for
  the separable simplex program from the Section 28 setup, then rewrites the Kuhn--Tucker
  coefficient condition as minimization of `-g`.
- `core/canonical`: the existing owner abstractions needed here are the Chapter 12 conjugate
  notation `(·)⋆`, finite sums over `Fin n`, and the extrema owners `IsMaxOn` and `IsMinOn`.
- `bridge/view`: the source variables `x = (ξ₁, …, ξₙ)` and `v₁*` are represented directly as
  `x : Fin n → 𝕜` and `v : 𝕜`, and the coordinate interaction term is stated through the pairing
  owner `⟪·, ·⟫ₚ` instead of a concrete scalar-product model.

Domain-style sampling used here:
- the conjugate owner `(·)⋆` from `Chap03.Defn_12_2`;
- the simplex-coordinate owners from `Definition_6_28_11`;
- `IsMaxOn` / `IsMinOn` from mathlib's extrema API;
- the project-wide Chapter 1 extended codomain surface `WithBotTop 𝕜`.

Primitive data vs derived API:
- primitive source data: the scalar family `f₀ : Fin n → 𝕜 → WithBotTop 𝕜`;
- primitive owners: `standardSimplexCoordinateLagrangian`,
  `standardSimplexCoordinateDualObjective`, and `standardSimplexCoordinateDualCost`;
- derived API: the pointwise source formula for the Lagrangian, the coordinatewise-infimum
  formula for the dual objective, and the maximizer/minimizer bridge.

Layer target: `source-facing`. This item is a direct computation for the special one-equality
problem, so it is formalized directly in terms of the scalar coordinate family and the canonical
conjugate owner, without introducing a separate program package.
-/

section

variable {n : ℕ}
variable {𝕜 : Type*}
variable [AddCommGroup 𝕜] [HasPairing 𝕜 𝕜 𝕜]

/-- The specialized Lagrangian for the one-equality separable simplex program with scalar
coordinate branches `f₀ₖ`. -/
def standardSimplexCoordinateLagrangian
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) (v : 𝕜) (x : Fin n → 𝕜) : WithBotTop 𝕜 :=
  (-v : WithBotTop 𝕜) + ∑ k, (f₀ k (x k) - ⟪x k, -v⟫ₚ)

-- Proof sketch: unfold `standardSimplexCoordinateLagrangian`; the displayed formula is exactly
-- its defining separable sum.
/-- Evaluating the specialized simplex Lagrangian gives the source coordinate formula. -/
theorem standardSimplexCoordinateLagrangian_apply
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) (v : 𝕜) (x : Fin n → 𝕜) :
    standardSimplexCoordinateLagrangian f₀ v x =
      (-v : WithBotTop 𝕜) + ∑ k, (f₀ k (x k) - ⟪x k, -v⟫ₚ) := sorry

end

section

variable {n : ℕ}
variable {𝕜 : Type*}
variable [AddCommGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [HasPairing 𝕜 𝕜 𝕜]

/-- The dual objective `g(v) = -v - ∑ₖ f₀ₖ⋆(-v)` attached to the same one-multiplier simplex
program. -/
def standardSimplexCoordinateDualObjective
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) (v : 𝕜) : WithBotTop 𝕜 :=
  (-v : WithBotTop 𝕜) - ∑ k, (f₀ k)⋆ (-v)

/-- The negated dual objective `-g` from the final clause of Corollary 6.28.8. -/
def standardSimplexCoordinateDualCost
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) (v : 𝕜) : WithBotTop 𝕜 :=
  (v : WithBotTop 𝕜) + ∑ k, (f₀ k)⋆ (-v)

-- Proof sketch: for each coordinate `k`, use the defining relation between the conjugate and the
-- negative infimum at `-v`; summing the coordinate identities yields the displayed source formula
-- for the dual objective.
/-- The dual objective also has the source coordinatewise-infimum formula. -/
theorem standardSimplexCoordinateDualObjective_apply_eq_iInf
    [IsOrderedAddMonoid 𝕜]
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) (v : 𝕜) :
    standardSimplexCoordinateDualObjective f₀ v =
      (-v : WithBotTop 𝕜) +
        ∑ k, (⨅ ξ : 𝕜, f₀ k ξ - ⟪ξ, -v⟫ₚ) := sorry

-- Proof sketch: unfold `standardSimplexCoordinateDualCost` and
-- `standardSimplexCoordinateDualObjective`; pointwise, the former is exactly the negative of the
-- latter.
/-- The dual cost is the pointwise negative of the dual objective. -/
theorem standardSimplexCoordinateDualCost_eq_neg_dualObjective
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) :
    standardSimplexCoordinateDualCost f₀ = fun v ↦ -standardSimplexCoordinateDualObjective f₀ v :=
  sorry

-- Proof sketch: maximizing `g` is equivalent to minimizing `-g`; then identify `-g`
-- with `standardSimplexCoordinateDualCost` using
-- `standardSimplexCoordinateDualCost_eq_neg_dualObjective`.
/-- Corollary 6.28.8: for the one-multiplier separable simplex program with coordinate branches
`f₀ₖ`, a scalar `λ₁` maximizes the dual objective `g(v) = -v - ∑ₖ f₀ₖ⋆(-v)` exactly when it
minimizes the equivalent source quantity `v + ∑ₖ f₀ₖ⋆(-v)`, which is the minimization criterion
corresponding to the Kuhn--Tucker coefficient condition for `(P)`. -/
theorem isMaxOn_standardSimplexCoordinateDualObjective_iff_isMinOn_standardSimplexCoordinateDualCost
    (f₀ : Fin n → 𝕜 → WithBotTop 𝕜) (lam₁ : 𝕜) :
    IsMaxOn (standardSimplexCoordinateDualObjective f₀) Set.univ lam₁ ↔
      IsMinOn (standardSimplexCoordinateDualCost f₀) Set.univ lam₁ := sorry

end

end Function
