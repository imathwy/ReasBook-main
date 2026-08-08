import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {C : Set E} {ω : E → EReal} {σ : ℝ}

/- Lemma 9.4 is `source-facing`: it records the lower quadratic bound, nonnegativity, and
definiteness properties of the Chapter 9 Bregman distance on `C × (C ∩ dom(∂ ω))`. Its owner
abstractions are already upstream: `B[ω]` / `extendedRealBregmanDistance`, `IsBregmanPotentialOn`,
`subdifferential_domain`, and the strong-convexity support inequality behind clause (1). The
source item is therefore kept as three atomic Bregman lemmas rather than a new wrapper package. -/

-- Proof sketch: apply Theorem 5.24(ii) to the strongly convex real-valued restriction of
-- `ω + extendedIndicator C` given by `hω.strongConvexOn_add_indicator`. For `x ∈ C` and
-- `y ∈ C ∩ dom(∂ ω)`, the indicator terms vanish, `hy_subgrad` identifies the supporting
-- subgradient at `y` with the gradient of the finite-valued restriction of `ω`, and the resulting
-- quadratic lower-support inequality is exactly the displayed Bregman lower bound.
/-- Lemma 9.4 (1): if `ω` is a Bregman potential on `C`, then for every `x ∈ C` and every
`y ∈ C ∩ dom(∂ ω)`, the associated Bregman distance dominates the quadratic term
`(σ / 2) ‖x - y‖²`. -/
theorem bregmanDistance_lower_quadratic_bound
    (hω : IsBregmanPotentialOn ω C σ) (x y : E)
    (hx : x ∈ C) (hyC : y ∈ C) (hy_subgrad : y ∈ subdifferential_domain ω) :
    B[ω] x y ≥ (σ / 2) * ‖x - y‖ ^ (2 : ℕ) := sorry

-- Proof sketch: combine `bregmanDistance_lower_quadratic_bound` with `hω.sigma_pos`, which gives
-- `(σ / 2) * ‖x - y‖² ≥ 0`, and conclude that the Bregman distance is nonnegative.
/-- Lemma 9.4 (2): if `x ∈ C` and `y ∈ C ∩ dom(∂ ω)`, then the Bregman distance
`B_ω(x, y)` is nonnegative. -/
theorem bregmanDistance_nonneg_of_mem_subdifferential_domain
    (hω : IsBregmanPotentialOn ω C σ) (x y : E)
    (hx : x ∈ C) (hyC : y ∈ C) (hy_subgrad : y ∈ subdifferential_domain ω) :
    0 ≤ B[ω] x y := by
  have hnorm_sq_nonneg : 0 ≤ ‖x - y‖ ^ (2 : ℕ) := by
    positivity
  have hquad_nonneg : 0 ≤ (σ / 2) * ‖x - y‖ ^ (2 : ℕ) := by
    nlinarith [hω.sigma_pos, hnorm_sq_nonneg]
  exact hquad_nonneg.trans <| bregmanDistance_lower_quadratic_bound hω x y hx hyC hy_subgrad

-- Proof sketch: if `x = y`, then `bregmanDistance_eq_zero_of_eq` gives the reverse implication.
-- Conversely, `bregmanDistance_nonneg_of_mem_subdifferential_domain` and
-- `bregmanDistance_lower_quadratic_bound` force `‖x - y‖² = 0` when the Bregman distance
-- vanishes, hence `x = y`.
/-- Lemma 9.4 (3): for `x ∈ C` and `y ∈ C ∩ dom(∂ ω)`, the Bregman distance vanishes exactly on
the diagonal. -/
theorem bregmanDistance_eq_zero_iff_eq_of_mem_subdifferential_domain
    (hω : IsBregmanPotentialOn ω C σ) (x y : E)
    (hx : x ∈ C) (hyC : y ∈ C) (hy_subgrad : y ∈ subdifferential_domain ω) :
    B[ω] x y = 0 ↔ x = y := by
  constructor
  · intro hzero
    have hquad_le :
        (σ / 2) * ‖x - y‖ ^ (2 : ℕ) ≤ 0 := by
      rw [← hzero]
      exact bregmanDistance_lower_quadratic_bound hω x y hx hyC hy_subgrad
    have hnorm_sq_nonneg : 0 ≤ ‖x - y‖ ^ (2 : ℕ) := by
      positivity
    have hquad_nonneg : 0 ≤ (σ / 2) * ‖x - y‖ ^ (2 : ℕ) := by
      nlinarith [hω.sigma_pos, hnorm_sq_nonneg]
    have hquad_eq :
        (σ / 2) * ‖x - y‖ ^ (2 : ℕ) = 0 := by
      linarith
    have hsigma_half_pos : 0 < σ / 2 := by
      nlinarith [hω.sigma_pos]
    have hnorm_sq : ‖x - y‖ ^ (2 : ℕ) = 0 := by
      nlinarith
    have hnorm : ‖x - y‖ = 0 := by
      exact eq_zero_of_pow_eq_zero hnorm_sq
    exact sub_eq_zero.mp <| norm_eq_zero.mp hnorm
  · intro hxy
    exact bregmanDistance_eq_zero_of_eq ω hxy

end
