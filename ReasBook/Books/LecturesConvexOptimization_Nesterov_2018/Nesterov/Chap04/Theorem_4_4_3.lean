import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Algorithm_4_4_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Assumption_4_4_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped InnerProduct Manifold
open scoped LevelSetNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

/- Theorem 4.4.3 lies in the modified Gauss--Newton / merit-threshold decrease domain.

Sampled owner-style declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate dynamics;
* `jacobian_lipschitz_taylor_remainder_le` in `Proposition_4_4_5`, the chapter owner for the
  first-order Taylor remainder bound on a convex Lipschitz domain;
* `abs_meritFunctionReformulation_sub_modifiedGaussNewtonLocalModel_le` in `Lemma_4_4_1`, the
  chapter owner for the merit/model discrepancy on that same convex domain;
* mathlib `LipschitzOnWith L (fderiv ℝ problem) 𝓕`, the canonical Jacobian-Lipschitz owner on a
  feasible set;
* `𝓛[f]((f x0)) ⊆ 𝓕`, the chapter's canonical initial-sublevel containment bridge already used in
  nearby Chapter 4 theorem surfaces;
* `HasUniformDualNondegeneracyOnInitialSublevelSet` in `Assumption_4_4_3`, the source-facing
  owner for the uniform dual nondegeneracy assumption.

Best owner abstraction:
* source-facing: the textbook one-step decrease and quadratic-decay estimates in the large-value
  and small-value regimes;
* core/canonical: a bundled smooth map `problem`, a sharp merit function `φ`, a modified
  Gauss--Newton method `method`, a convex feasible domain `𝓕`, the canonical sublevel-containment
  bridge `𝓛[f]((f x0)) ⊆ 𝓕`, the chapter dual-nondegeneracy owner, and the Jacobian-Lipschitz
  owner on `problem`;
* bridge/view: an explicit sharpness witness `γφ` for the merit function, because the displayed
  thresholds and decay constants depend on that particular witness, together with the convex-domain
  Taylor/model comparison supplied by Proposition 4.4.5 and Lemma 4.4.1.

Primitive data:
* the smooth map `problem`;
* the sharp merit function `φ`;
* the method `method`;
* the convex feasible domain `𝓕`;
* the Jacobian-Lipschitz hypothesis `LipschitzOnWith L (fderiv ℝ problem) 𝓕`;
* the sublevel containment bridge `𝓛[f]((f x0)) ⊆ 𝓕`;
* the threshold parameter `γφ`.

Derived API:
* convex feasible-domain geometry `Convex ℝ 𝓕`;
* positivity of `σ` and the initial-sublevel lower bound, bundled in
  `HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ`.

The earlier file put Theorem 4.4.3 on the scalar smoothness owner
`HasLipschitzDerivativeOnWith L 𝓕 (meritFunctionReformulation problem φ)`. That shifts the
mathematical content away from the Gauss--Newton residual map `problem`, while the chapter
comparison lemmas actually used here are stated on the Jacobian-Lipschitz owner
`LipschitzOnWith L (fderiv ℝ problem) 𝓕` over a convex domain. This refinement keeps the same
source-facing decrease theorems, but moves their smoothness hypothesis onto that canonical owner
and leaves the scalar merit reformulation as derived API rather than as the primitive smoothness
input.
-/

section

variable {problem : SmoothMap}
variable {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
variable {𝓕 : Set E₁}
variable {L0 : ℝ} {L : NNReal} {σ γφ : ℝ} {x0 : E₁}

local notation "f" => meritFunctionReformulation problem φ
local notation "𝓛0" => (𝓛[f]((f x0)) : Set E₁)

/-- The merit-value threshold `(σ² / (2L)) γ_φ²` separating the large-value and quadratic-decay
regimes in Theorem 4.4.3. -/
def modifiedGaussNewtonQuadraticMeritThreshold
    (σ γφ : ℝ) (L : NNReal) : ℝ :=
  ((σ ^ (2 : ℕ)) / (2 * (L : ℝ))) * γφ ^ (2 : ℕ)

-- Proof sketch: use monotonicity of the merit values along Algorithm 4.4.1 to keep `x_k` inside
-- the initial sublevel set, apply the uniform dual nondegeneracy assumption there, and invoke
-- Lemma 4.4.6 to obtain a correction `h_k*` with `‖h_k*‖ ≤ f(x_k) / (σ γφ)`. Evaluating the
-- quadratic-regularized local model along the segment `t ↦ t h_k*` and using the upper bound
-- `M_k ≤ 2L` yields a one-variable quadratic majorant; when
-- `f(x_k) ≥ (σ² / (2L)) γφ²`, its minimizer gives the decrease estimate `(4.4.23)`.
/-- Theorem 4.4.3 (1): under Assumptions 4.4.1, 4.4.2, and 4.4.3, if a modified Gauss--Newton
iterate satisfies `f(x_k) ≥ (σ² / (2L)) γ_φ²`, then the next merit value decreases by at least
`(σ² / (4L)) γ_φ²`. On the theorem surface, the only part of Assumption 4.4.2 used here is the
sublevel containment `𝓛[f]((f x₀)) ⊆ 𝓕`. -/
theorem modifiedGaussNewton_large_value_oneStep_decrease
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (k : ℕ)
    (hk :
      modifiedGaussNewtonQuadraticMeritThreshold σ γφ L ≤
        f (method k)) :
    f (method (k + 1)) ≤
      f (method k) - ((σ ^ (2 : ℕ)) / (4 * (L : ℝ))) * γφ ^ (2 : ℕ) := sorry

-- Proof sketch: follow the same comparison with the one-dimensional model along `t h_k*`. In the
-- regime `f(x_k) < (σ² / (2L)) γφ²`, the scalar majorant is minimized at `t = 1`, which yields
-- the quadratic estimate `(4.4.24)`.
/-- Theorem 4.4.3 (2): under the same hypotheses, if
`f(x_k) < (σ² / (2L)) γ_φ²`, then
`f(x_{k+1}) ≤ (L / (σ² γ_φ²)) f(x_k)^2`. -/
theorem modifiedGaussNewton_small_value_quadratic_decay
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (k : ℕ)
    (hk :
      f (method k) <
        modifiedGaussNewtonQuadraticMeritThreshold σ γφ L) :
    f (method (k + 1)) ≤
      ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) := sorry

-- Proof sketch: combine the threshold hypothesis
-- `f(x_k) < (σ² / (2L)) γφ²` with elementary scalar algebra to bound the quadratic factor from
-- Theorem 4.4.3 (2) by `1 / 2`.
/-- Under the small-value hypothesis from Theorem 4.4.3 (2), the quadratic upper bound is at most
half of the current merit value. -/
theorem modifiedGaussNewton_small_value_quadratic_decay_le_half_current
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (k : ℕ)
    (hk :
      f (method k) <
        modifiedGaussNewtonQuadraticMeritThreshold σ γφ L) :
    ((L : ℝ) / (σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * f (method k) := sorry

-- Proof sketch: repeat the argument from the first part, but use the fixed-parameter hypothesis
-- `M_k = L`. The same one-dimensional majorant now has quadratic coefficient `L / 2`, so when
-- `f(x_k) ≥ (σ² / L) γφ²` its minimizer yields the sharper linear decrease `(4.4.25)`.
/-- Theorem 4.4.3 (3): if Algorithm 4.4.1 is run with the fixed regularization rule `M_k ≡ L`
and `f(x_k) ≥ (σ² / L) γ_φ²`, then
`f(x_{k+1}) ≤ f(x_k) - (σ² / (2L)) γ_φ²`. As above, the feasible-set input is only the
sublevel containment `𝓛[f]((f x₀)) ⊆ 𝓕`. -/
theorem modifiedGaussNewton_fixed_regularization_large_value_oneStep_decrease
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (hregularization : ∀ k : ℕ, method.regularization k = (L : ℝ))
    (k : ℕ)
    (hk :
      ((σ ^ (2 : ℕ)) / (L : ℝ)) * γφ ^ (2 : ℕ) ≤
        f (method k)) :
    f (method (k + 1)) ≤
      f (method k) - ((σ ^ (2 : ℕ)) / (2 * (L : ℝ))) * γφ ^ (2 : ℕ) := sorry

-- Proof sketch: in the fixed-parameter case `M_k = L`, the scalar majorant from the textbook
-- proof is minimized at `t = 1` whenever `f(x_k) < (σ² / L) γφ²`. This gives the quadratic bound
-- in `(4.4.26)`.
/-- Theorem 4.4.3 (4): if Algorithm 4.4.1 is run with `M_k ≡ L` and
`f(x_k) < (σ² / L) γ_φ²`, then
`f(x_{k+1}) ≤ (L / (2 σ² γ_φ²)) f(x_k)^2`, again using only the sublevel containment
`𝓛[f]((f x₀)) ⊆ 𝓕` from Assumption 4.4.2. -/
theorem modifiedGaussNewton_fixed_regularization_small_value_quadratic_decay
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (h𝓕 : Convex ℝ 𝓕)
    (h_jacobian_lipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (h𝓛0_subset : 𝓛0 ⊆ 𝓕)
    (hσ : HasUniformDualNondegeneracyOnInitialSublevelSet problem φ x0 σ)
    (hγφ_pos : 0 < γφ)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (hregularization : ∀ k : ℕ, method.regularization k = (L : ℝ))
    (k : ℕ)
    (hk :
      f (method k) <
        ((σ ^ (2 : ℕ)) / (L : ℝ)) * γφ ^ (2 : ℕ)) :
    f (method (k + 1)) ≤
      ((L : ℝ) / (2 * σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) := sorry

-- Proof sketch: the stronger threshold `f(x_k) < (σ² / L) γφ²` implies by scalar algebra that
-- the quadratic upper bound from Theorem 4.4.3 (4) is bounded by one half of `f(x_k)`.
/-- In the fixed-regularization small-value regime, the quadratic upper bound from
`modifiedGaussNewton_fixed_regularization_small_value_quadratic_decay` is at most half of the
current merit value. -/
theorem modifiedGaussNewton_fixed_regularization_small_value_quadratic_decay_le_half_current
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    (k : ℕ)
    (hk :
      f (method k) <
        ((σ ^ (2 : ℕ)) / (L : ℝ)) * γφ ^ (2 : ℕ)) :
    ((L : ℝ) / (2 * σ ^ (2 : ℕ) * γφ ^ (2 : ℕ))) * (f (method k)) ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * f (method k) := sorry

end
