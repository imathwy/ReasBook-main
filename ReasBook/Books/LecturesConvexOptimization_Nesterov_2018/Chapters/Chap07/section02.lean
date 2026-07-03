import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_2 (from Chap07) -/
/- Definition 7.2 is a recall-only item in the metric / norm-ball domain.

Sampled owner-style declarations:
- `Metric.closedBall`
- `Metric.mem_closedBall`
- `mem_closedBall_zero_iff`
- `mem_closedBall_iff_norm`

Best owner abstraction:
- source-facing: `Metric.closedBall (0 : E) r`
- core/canonical: `Metric.closedBall`
- bridge/view: `mem_closedBall_zero_iff`

Primitive data:
- a seminormed additive group `E`
- a radius `r : ℝ`

Derived API:
- the zero-center membership view `mem_closedBall_zero_iff`

The previous `normBall` and `mem_normBall_iff` declarations were exact-interface duplicates of the
canonical metric closed ball at the origin and its standard norm-bound membership theorem. This
file therefore recalls the canonical owner expression directly instead of keeping a parallel local
wrapper. -/

universe u

section

variable {E : Type u} [SeminormedAddGroup E]
variable (r : ℝ) (a : E)

/- Definition 7.2: the textbook norm ball `B_{‖·‖}(r)` centered at the origin is exactly the
canonical metric closed ball `Metric.closedBall (0 : E) r`. -/
#check (Metric.closedBall (0 : E) r : Set E)

/- Membership in the origin-centered norm ball is exactly the standard norm-bound characterization.
-/
#check (show a ∈ Metric.closedBall (0 : E) r ↔ ‖a‖ ≤ r from mem_closedBall_zero_iff)

end

/-! ### Lemma_7_2 (from Chap07) -/
noncomputable section

open scoped SupportFunction

universe u v

/-
Lemma 7.2 lies in the chapter's support-function / dual-norm comparison domain.

Sampled owner-style declarations:
- Chapter 3 `ξ[Q]` and `supportFunction_apply`
- Chapter 3 `Seminorm.dualNorm` and `Seminorm.dualNorm_apply`
- mathlib `Seminorm.closedBall`
- mathlib `Seminorm.closedBall_zero_eq`

Best owner abstraction:
- source-facing: the support-function bound for `x ↦ (ξ[Q₂] (A x)).toReal`
- core/canonical: `ξ[Q₂]`, `Seminorm.dualNorm`, and `Seminorm.closedBall`
- bridge/view: the real-valued `toReal` surface of `ξ[Q₂]`

Primitive data:
- a real-linear map `A : X →ₗ[ℝ] F`
- a set `Q₂ : Set F`
- a seminorm `p : Seminorm ℝ F` with `[Seminorm.IsNorm p]`
- radii `γ₀`, `γ₁`

Derived API:
- the dual norm `p.dualNorm`
- the primal balls `p.closedBall 0 γ`
- the pointwise real-valued support function `x ↦ (ξ[Q₂] (A x)).toReal`

Source/core/bridge triage:
- source-facing: the sandwich estimate for the support function of `Aᵀ Q₂`
- core/canonical: the Chapter 3 support-function and dual-norm owners
- bridge/view: precomposition with `A` and the `toReal` passage for the support function

This refinement deletes the duplicate local owners `VectorNorm`, `supportFunction`,
`supportFunctionAlongLinearMap`, and `pulledDualNorm`. The public statement now uses the chapter
owners directly and only keeps the real-valued `toReal` bridge because the textbook inequality is
real-valued.
-/

section

variable {X : Type v} [AddCommGroup X] [Module ℝ X]
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-
Proof sketch: compare `ξ[Q₂]` with the support functions of the inner and outer `p`-balls using
`p.closedBall 0 γ₀ ⊆ Q₂ ⊆ p.closedBall 0 γ₁`; then identify the support functions of those balls
with `γ₀` and `γ₁` times `p.dualNorm`. The only explicit radius sign assumption needed in the public
API is `0 ≤ γ₀`: since `0 ∈ p.closedBall 0 γ₀`, the inclusions force `0 ∈ p.closedBall 0 γ₁`, so
`0 ≤ γ₁` is derived internally from the canonical closed-ball owner. -/
/-- Lemma 7.2: if `Q₂` contains the `p`-ball of radius `γ₀` and is contained in the `p`-ball of
radius `γ₁`, then the real-valued support function of `Aᵀ Q₂ = ∂f(0)` is sandwiched between `γ₀`
and `γ₁` times the pulled-back dual norm `x ↦ ‖A x‖_*`. The pointwise sandwich only needs the
inner radius to be explicitly nonnegative; the outer-radius nonnegativity follows from the two ball
inclusions. The stronger positivity hypotheses needed for the ratio `γ₀ / γ₁` are kept separate in
`gammaRatio_pos_and_le_one`. -/
theorem supportFunction_toReal_comp_linearMap_dualNorm_bounds
    (A : X →ₗ[ℝ] F) (Q2 : Set F) (p : Seminorm ℝ F) [Seminorm.IsNorm p]
    (γ₀ γ₁ : ℝ) (hγ₀_nonneg : 0 ≤ γ₀)
    (hQ2_lower : p.closedBall 0 γ₀ ⊆ Q2)
    (hQ2_upper : Q2 ⊆ p.closedBall 0 γ₁)
    (x : X) :
    γ₀ * p.dualNorm (A x) ≤ (ξ[Q2] (A x)).toReal ∧
      (ξ[Q2] (A x)).toReal ≤ γ₁ * p.dualNorm (A x) := sorry

-- Proof sketch: `0 < γ₀ ≤ γ₁` implies `0 < γ₁`, hence division by `γ₁` preserves order and gives
-- `0 < γ₀ / γ₁ ≤ 1`.
/-- The ratio `γ₀ / γ₁` is positive and at most `1`, which is the numerical content used for the
choice `α = γ₀ / γ₁` in the relative-scale condition. -/
theorem gammaRatio_pos_and_le_one {γ₀ γ₁ : ℝ}
    (hγ₀ : 0 < γ₀) (hγ₀γ₁ : γ₀ ≤ γ₁) :
    0 < γ₀ / γ₁ ∧ γ₀ / γ₁ ≤ 1 := sorry

end

/-! ### Proposition_7_2 (from Chap07) -/
noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.2 lies in the Euclidean direct-structure first-order complexity domain.

Sampled owner-style declarations:
- mathlib `EuclideanSpace ℝ (Fin n)` for the ambient model `ℝⁿ`;
- mathlib `NNReal` for the nonnegative constants `γ₁(F)` and `R`;
- mathlib `Real.sqrt` for the factor `√(N (N + 1))`;
- the chapter-style lower-level scheme surface `ℕ+ → NNReal → Eₙ → Eₙ`, matching the notation
  `S_N(R)`.

Best owner abstraction:
- source-facing: the textbook output guarantee for the method `S_N(R)` on every start point
  within Euclidean distance `R` of a chosen optimal point `x*`;
- core/canonical: a scheme `S` taking an iteration count, a radius parameter, and a start point;
- bridge/view: the positive parameters `γ₁(F)` and `R` are recorded as `NNReal` data.

Primitive data:
- the objective `f`;
- the method surface `S`;
- the coefficient `γ₁(F)`, the radius `R`, the iteration count `N`, the reference point `xStar`,
  and the start point `x₀`.

Derived API:
- the displayed complexity bound
  `f (S_N(R)) - f(x*) ≤ 2 γ₁(F) R / √(N (N + 1))`.

Source/core/bridge triage:
- source-facing: Proposition 7.2 itself;
- core/canonical: the scheme `S : ℕ+ → NNReal → Eₙ → Eₙ`;
- bridge/view: coercing the `NNReal` parameters to `ℝ` in the final bound.

As in nearby Chapter 7 item files, the proposition is stated directly on the method surface
`S_N(R)` and keeps only the data that appears in the displayed estimate. The convexity/minimizer
prose is part of the surrounding chapter setup for constructing this method, rather than separate
wrapper data in this item file.
-/

-- Proof sketch: instantiate the Chapter 6 direct-structure estimate for the method `S_N(R)` with
-- the homogeneous-model constants `‖A‖ = γ₁(F)`, `D₁ = R² / 2`, `D₂ = 1 / 2`, and `M = 0`, then
-- simplify the resulting coefficient.
/-- Proposition 7.2 [Chapter7_1.json:26]: for the Chapter 7 direct-structure method `S_N(R)`,
every start point `x₀` within Euclidean distance `R` of `x*` has objective gap at most
`2 γ₁(F) R / √(N (N + 1))` after `N` steps. -/
theorem direct_structure_method_output_sub_optimalValue_le
    (f : Eₙ → ℝ) (S : ℕ+ → NNReal → Eₙ → Eₙ) (γ₁ : NNReal) (N : ℕ+) (R : NNReal)
    (xStar : Eₙ) {x₀ : Eₙ} (hx₀ : ‖x₀ - xStar‖ ≤ (R : ℝ)) :
    f (S N R x₀) - f xStar ≤
      (2 * (γ₁ : ℝ) * (R : ℝ)) /
        Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) := sorry

end

/-! ### Theorem_7_2 (from Chap07) -/
universe u

section

/- Theorem 7.2 lies in the chapter's relative-accuracy / lower-level subgradient-scheme domain.

Sampled owner-style declarations:
- `aPrioriRadiusEstimate` in `Definition_7_9.lean`, the scalar radius-parameter owner used in
  Chapter 7;
- `relativeScaleSubgradientApproximationStep` in `Algorithm_7_2.lean`, whose lower-level scheme
  input has type `ℕ → ℝ → X`;
- `schemeSNRestartingStep` in `Algorithm_7_4.lean`, which uses the same scalar-parameter scheme
  surface;
- `direct_structure_iterate_value_le_one_add_delta_mul_optimal_value` in `Theorem_7_4.lean`, the
  sibling relative-error conversion theorem.

Best owner abstraction:
- source-facing: Theorem 7.2's conversion from a stagewise subgradient-approximation gap bound to
  a one-shot relative-value guarantee;
- core/canonical: a lower-level scheme `G : ℕ → ℝ → X` evaluated at a scalar radius parameter
  `rhoHat`;
- bridge/view: the specific floor-chosen index `⌊1 / (α⁴ δ²)⌋`.

Primitive data:
- `f`, `G`, `rhoHat`, `α`, `δ`, and `fStar`;
- the stagewise estimate for `G k rhoHat`.

Derived API:
- the chosen stage index `⌊1 / (α⁴ δ²)⌋`;
- the final relative-value inequality.

This file keeps the source-facing theorem directly, but it aligns the scheme input with the
chapter's canonical scalar-parameter owner surface and exposes the active scalar side conditions
instead of a stronger interval wrapper plus a hidden sign assumption on `fStar`.
-/

variable {X : Type u}

-- Proof sketch: apply the assumed estimate at
-- `N = Nat.floor (1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)))`, then use
-- `Nat.floor_lt_add_one` to deduce `1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)) ≤ N + 1` and hence
-- `1 / (α ^ (2 : ℕ) * Real.sqrt (N + 1 : ℝ)) ≤ δ` from `0 < α` and `0 < δ`, then multiply by
-- `fStar` using `0 ≤ fStar`.
/-- Theorem 7.2 [Chapter7_1.json:15]: if `α` and `δ` are positive, `fStar` is nonnegative, and every iterate
`G k rhoHat` satisfies the subgradient approximation estimate
`f (G k rhoHat) - fStar ≤ (1 / (α^2 * √(k + 1))) * fStar`, then the iterate with index
`⌊1 / (α^4 δ^2)⌋` satisfies `f (G_N rhoHat) ≤ (1 + δ) fStar`. -/
theorem subgradient_approximation_scheme_value_le_one_add_delta_mul_optimal_value
    (f : X → ℝ) (G : ℕ → ℝ → X) (rhoHat α δ fStar : ℝ)
    (hα : 0 < α) (hδ : 0 < δ) (hfStar_nonneg : 0 ≤ fStar)
    (hEstimate :
      ∀ k : ℕ,
        f (G k rhoHat) - fStar ≤
          (1 / (α ^ (2 : ℕ) * Real.sqrt (k + 1 : ℝ))) * fStar) :
    f (G (Nat.floor (1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)))) rhoHat) ≤ (1 + δ) * fStar := sorry

end
