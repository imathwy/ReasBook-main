import Mathlib
import FirstOrderMethodsinOptimization.Chap10.Algorithm_10_13
import FirstOrderMethodsinOptimization.Chap10.Assumption_10_31
import FirstOrderMethodsinOptimization.Chap10.Definition_10_2
import FirstOrderMethodsinOptimization.Chap10.Definition_10_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open PosReal

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

variable {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ}
variable {Lf σ : PosReal}
variable [hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf)]
variable {xStar zMinusOne : E} {N : ℕ+} {R : ℝ}

local notation "F" => composite_model_objective f.toEReal g
local notation "κ" => κ(toNNReal Lf, σ)

/- Theorem 10.41 is `source-facing` in the restarted-FISTA complexity layer.

Domain sampling in the existing Chapter 10 API identifies:
- `IsFastProximalGradientProblem` as the owner of Assumption 10.31;
- `restarted_fista f g Lf zMinusOne N` from Algorithm 10.13 as the canonical owner of the
  restarted outer iterates `z^k`, with the standing problem instance supplying its regularity
  assumptions directly;
- `κ(Lf.toNNReal, σ)` from Definition 10.21 as the chapter owner of the condition
  number `L_f / σ`;
- Theorem 10.34's `fista_objective_gap_le_two_alpha_Lf_dist_sq_div_sq` as the canonical
  accelerated `O(1 / n^2)` estimate on each restart cycle.

Primitive data are the standing fast proximal-gradient problem, the strong-convexity modulus `σ`,
the chosen minimizer `xStar`, the initial restart point `zMinusOne`, the restart length `N`, and
the radius bound `R`. The geometric contraction factor and the explicit logarithmic complexity
bound are derived API, so this file should reuse the chapter owners `F`, `restarted_fista`, and
`κ` directly rather than restating the ratio `L_f / σ` through raw arithmetic. -/

set_option quotPrecheck false in
local notation "z" =>
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  restarted_fista f g Lf zMinusOne N

-- Proof sketch: apply the `O(1 / n^2)` FISTA estimate from Theorem 10.34 to each restart cycle,
-- use strong convexity of `f` to convert the cycle-end distance estimate into a contraction of the
-- objective gap by the factor `4 κ / (N + 1)^2`, and then use
-- `N = ⌈√(8 κ - 1)⌉` together with the initial prox-gradient bound at `z^{-1}` to obtain the
-- geometric factor `(1 / 2)^k`.
/-- Theorem 10.41 (1): if restarted FISTA uses the restart length
`N = ⌈√(8κ - 1)⌉` with `κ = L_f / σ`, then every outer iterate satisfies
`F(z^k) - F_opt ≤ (L_f R^2 / 2) (1 / 2)^k`, where `R` bounds `‖z^{-1} - x*‖`. -/
theorem restarted_fista_objective_gap_le_geometric_half_pow
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (hR : ‖zMinusOne - xStar‖ ≤ R)
    (hN :
      (N : ℕ) =
        Nat.ceil
          (Real.sqrt (8 * κ - 1)))
    (k : ℕ) :
    F (z k) -
      (FOpt : EReal) ≤
        ((((Lf : ℝ) * R ^ (2 : ℕ) / 2 * ((1 / 2 : ℝ) ^ k) : ℝ) : EReal)) := sorry

-- Proof sketch: apply part (1) to the restart point reached after the last completed cycle,
-- whose index is `⌊k / N⌋ = k / N` in natural-number division; then use the total-iteration
-- hypothesis in the faithful form `N * (...) ≤ k` to convert the completed-cycle count into the
-- required lower bound on `⌊k / N⌋`. Positivity of the logarithmic scale factor
-- `L_f R^2 / 2` is handled internally: under the radius bound `hR`, the only nonpositive case is
-- the degenerate radius-zero situation, where part (1) already gives the conclusion directly.
/-- Theorem 10.41 (2): after `k` FISTA iterations, if
`k ≥ N (log(1 / ε) / log 2 + log(L_f R^2 / 2) / log 2)` with
`N = ⌈√(8κ - 1)⌉`, then the restart point at the end of the last completed cycle is
`ε`-optimal; equivalently, `F(z^(⌊k / N⌋)) - F_opt ≤ ε`. The displayed iteration bound keeps the
textbook logarithmic expression, while the proof treats the degenerate radius-zero case
separately instead of exposing a positivity guard for `Real.log` in the public API. -/
theorem restarted_fista_objective_gap_le_epsilon_of_iteration_bound
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (hR : ‖zMinusOne - xStar‖ ≤ R)
    (hN :
      (N : ℕ) =
        Nat.ceil
          (Real.sqrt (8 * κ - 1)))
    (ε : PosReal) (k : ℕ)
    (hiter :
      ((N : ℕ) : ℝ) *
          (Real.log (1 / (ε : ℝ)) / Real.log 2 +
            Real.log ((Lf : ℝ) * R ^ (2 : ℕ) / 2) / Real.log 2) ≤
        (k : ℝ)) :
    F (z (k / (N : ℕ))) -
      (FOpt : EReal) ≤
        ((ε : ℝ) : EReal) := sorry

end
