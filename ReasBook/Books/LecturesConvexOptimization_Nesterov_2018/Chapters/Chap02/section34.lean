

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_34 (from Chap02) -/
noncomputable section

open Metric

universe u

section

variable {E : Type u} [PseudoMetricSpace E]

/- Definition 2.34 lies in the distance-to-set / projection domain.

Sampled owner-style declarations:
* `Metric.infDist`, the canonical distance-to-set owner;
* `Metric.lipschitz_infDist_pt`, showing that pointwise distance-to-set constructions are owned by
  `Metric.infDist`;
* `Metric.continuous_infDist_pt`, the intrinsic continuity bridge attached to the same owner;
* `IsProjectionPointOn Q x p` in `Chap07/Definition_7_3`, the project owner predicate for nearest
  points, used only in the normed bridge below.

Source/core/bridge triage:
* source-facing: the half squared distance to a set;
* core/canonical: `Metric.infDist`;
* bridge/view: the projection-point evaluation formula below.

Primitive data:
* the set `Q` and the ambient point `x`.

Derived API:
* continuity/Lipschitz consequences inherited from `Metric.infDist`;
* the projection-point evaluation formula.

Accordingly, this file exposes the source-facing owner directly as a set-based function derived
from `Metric.infDist`, without hard-coding convexity or the Euclidean `ℝⁿ` display model into the
public owner. -/

/-- Definition 2.34: the half squared distance to a set sends `x` to one half of the square of
its minimal distance to `Q`. The textbook Euclidean statement is the specialization to `ℝⁿ`. -/
def Set.halfSquaredDistance (Q : Set E) : E → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * infDist x Q ^ 2

end

section

variable {E : Type u} [SeminormedAddCommGroup E]

/-- For any projection point `p` of `x` onto `Q`, the half squared distance equals one half of
the squared norm of the displacement `x - p`. -/
-- Proof sketch: if `p` is a projection point of `x` onto `Q`, then by definition
-- `‖x - p‖ = infDist x Q`. Substitute this equality into the definition based on `Metric.infDist`.
theorem IsProjectionPointOn.halfSquaredDistance_eq
    {Q : Set E} {x p : E} (hp : IsProjectionPointOn Q x p) :
    Q.halfSquaredDistance x = (1 / 2 : ℝ) * ‖x - p‖ ^ 2 := by
  simp [Set.halfSquaredDistance, hp.2.symm, dist_eq_norm]

end

end

/-! ### Proposition_2_34 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]
variable {m : ℕ} {μ L : ℝ}

section

variable {problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L}

variable {κ t0 tStar ε Qf : ℝ} {x0 : problem.ambientSet} {hL : 0 < L}
variable
  {hStep1a : ∀ xBar : problem.ambientSet, ∀ t : ℝ, ∃ j, step1aAt problem κ xBar t hL j}

local notation "initialViolation" =>
  problem.toLagrangianProblem.constrainedAuxiliaryObjective t0 x0

local notation "fullIterationBound" =>
  Real.log ((tStar - t0) / ((1 - κ) * ε)) / Real.log (2 * (1 - κ))

local notation "perIterationCost" =>
  1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / κ)

/- Primary domain: total internal complexity bounds for the Chapter 2 constrained minimization
scheme `(2.3.22)`.

Owner abstractions sampled before refining:
- `ConstrainedMinimizationMethod` in `Algorithm_2_11.lean`, the source-facing owner of the master
  process and the full internal stopping counts `j(k)`;
- `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` in
  `Definition_2_47.lean`, the owner fixed-`t` smooth minimax problem whose regularized exact
  value is the local-model quantity used in the stopping tests and terminal count bounds;
- `constrainedMinimization_error_le_target_of_iterationThreshold_le` in Proposition 2.29, the
  Chapter 2 owner of the logarithmic master-iteration bound `N(ε)`;
- `constrainedMinimization_totalIterationCount_le_logarithmic_bound` in Proposition 2.33, the
  owner corollary bound on `j* + ∑_{k=0}^N j(k)`;
- `LagrangianProblem.constrainedAuxiliaryObjective` in Lemma 2.21, the owner initial
  max-violation term `max {f₀(x₀) - t₀, fᵢ(x₀)}`.

Best owner abstraction:
- `ConstrainedMinimizationMethod`, together with the fixed-`t` owner
  `problem.toParametricSmoothMinimaxProblem t`; the displayed total-complexity estimate is then
  obtained by feeding the scheme's full-step counts into the upstream scalar owner bound from
  Proposition 2.33 and substituting the upstream master-iteration bound from Proposition 2.29.
  The textbook Euclidean statement is the specialization `E = EuclideanSpace ℝ (Fin n)`.

Primitive data here are the recursive outer owner together with the explicit Step `1(a)`
existence hypothesis `hStep1a`, the source index `N` of the last full master iteration, the final
internal-iteration count `jStar`, and the positive stage sequence `Δ` already used in
Proposition 2.33.
The public theorem below specializes the owner Proposition 2.33 hypotheses to
`j(k) = ConstrainedMinimizationMethod.stopIndex ... k` and then substitutes the Proposition 2.29
bound on `N`; it no longer stores the Proposition 2.33 conclusion itself as primitive input.

Source/core/bridge triage:
- source-facing: Proposition 2.34 itself, a bound for the total internal iterations of process
  `(2.3.22)`;
- core/canonical: `ConstrainedMinimizationMethod` and
  `constrainedMinimization_totalIterationCount_le_logarithmic_bound`;
- bridge/view: the specialization of Proposition 2.33 to `scheme.stopIndex` and the scalar
  substitution `N ≤ N(ε)`.
-/

namespace ConstrainedMinimizationMethod

local notation "stopSeq" => stopIndex problem κ t0 x0 hL hStep1a

/-- Helper for Proposition 2.34: the cost of one full outer update is nonnegative on the source
domain for `κ`. -/
private theorem perIterationCost_nonneg
    (hκ_domain : κ ∈ Set.Ioo (0 : ℝ) (2 * (Qf - 1))) :
    0 ≤ perIterationCost := by
  -- The logarithmic term is nonnegative, so adding the leading `1` keeps the cost nonnegative.
  have hlog_pos : 0 < Real.log (2 * (Qf - 1) / κ) := by
    refine Real.log_pos ?_
    rw [one_lt_div₀ hκ_domain.1]
    exact hκ_domain.2
  have hmul_nonneg :
      0 ≤ Real.sqrt Qf * Real.log (2 * (Qf - 1) / κ) := by
    exact mul_nonneg (Real.sqrt_nonneg _) hlog_pos.le
  linarith

/-- Proposition 2.34: if `N` is the source index of the last full iteration of process
`(2.3.22)`, if `N` satisfies the logarithmic master-iteration bound from Proposition 2.29, and if
the final count `j*`, the full-step counts `j(k) = scheme.stopIndex k`, and the stage sequence
`Δ` satisfy the specialized Proposition 2.33 hypotheses, then the total number of internal
iterations is bounded by the displayed formula `(2.3.27)`. The initial max-violation term is the
owner auxiliary objective
`initialViolation = problem.toLagrangianProblem.constrainedAuxiliaryObjective t0 x0`.
The textbook `ℝⁿ` statement is recovered by specializing `E = EuclideanSpace ℝ (Fin n)`. -/
theorem totalInternalIterations_le_logarithmic_bound
    (N jStar : ℕ) (Δ : ℕ → ℝ)
    (hκ_domain : κ ∈ Set.Ioo (0 : ℝ) (2 * (Qf - 1)))
    (hε : 0 < ε)
    (hΔ_zero : Δ 0 = initialViolation)
    (hfullIterations : (N : ℝ) ≤ fullIterationBound)
    (hΔ_pos : ∀ ⦃k : ℕ⦄, k ≤ N + 1 → 0 < Δ k)
    (hjStar_bound :
      (jStar : ℝ) ≤
        1 + Real.sqrt Qf * Real.log ((2 * (Qf - 1) * Δ (N + 1)) / (κ * ε)))
    (hj_bound :
      ∀ ⦃k : ℕ⦄, k ≤ N →
        (stopSeq k : ℝ) ≤
          1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / κ) +
            Real.sqrt Qf * Real.log (Δ k / Δ (k + 1))) :
    (jStar : ℝ) +
        Finset.sum (Finset.range (N + 1)) (fun k ↦ (stopSeq k : ℝ)) ≤
      (fullIterationBound + 2) * perIterationCost +
        Real.sqrt Qf * Real.log (initialViolation / ε) := by
  -- First package the entire inner-iteration accounting through Proposition 2.33.
  have htotalCount :
      (jStar : ℝ) +
          Finset.sum (Finset.range (N + 1)) (fun k ↦ (stopSeq k : ℝ)) ≤
        (N + 2 : ℝ) * perIterationCost +
          Real.sqrt Qf * Real.log (initialViolation / ε) :=
    by
      simpa [hΔ_zero] using
        constrainedMinimization_totalIterationCount_le_logarithmic_bound
          N
          (fun k ↦ (stopSeq k : ℝ))
          (jStar : ℝ)
          Δ
          Qf
          κ
          ε
          hκ_domain
          hε
          hΔ_pos
          hjStar_bound
          hj_bound
  -- Then substitute the logarithmic outer-iteration bound into the prefactor.
  have hperIterationBound :
      (N + 2 : ℝ) * perIterationCost ≤
        (fullIterationBound + 2) * perIterationCost := by
    refine mul_le_mul_of_nonneg_right ?_ (perIterationCost_nonneg hκ_domain)
    linarith
  have htotalCount' :
      (N + 2 : ℝ) * perIterationCost + Real.sqrt Qf * Real.log (initialViolation / ε) ≤
        (fullIterationBound + 2) * perIterationCost +
          Real.sqrt Qf * Real.log (initialViolation / ε) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hperIterationBound
        (Real.sqrt Qf * Real.log (initialViolation / ε))
  exact htotalCount.trans htotalCount'

end ConstrainedMinimizationMethod

end

/-! ### Theorem_2_34 (from Chap02) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 2.34 lies in the nearest-point / convex-geometry domain.

Sampled owner-style declarations:
* `IsProjectionPointOn Q x p` in `Chap07/Definition_7_3`, the project owner predicate for
  nearest-point geometry;
* `IsProjectionPointOn.inner_sub_nonneg` in `Lemma_2_13`, the owner variational inequality for a
  projection point on a convex set;
* `euclideanProjection` and `euclideanProjection_isProjectionPointOn` in `Theorem_2_33`, the
  chosen map and its bridge back to the owner predicate once existence is available;
* `Submodule.lipschitzWith_orthogonalProjection` in mathlib's linear-subspace projection API,
  showing that the canonical map-level output for a projection operator is `LipschitzWith 1`.

Best owner abstraction:
* `IsProjectionPointOn Q x p`.

Source/core/bridge triage:
* source-facing: nonexpansiveness of metric projection onto a convex set;
* core/canonical: owner-level projection points `IsProjectionPointOn Q x p`;
* bridge/view: the selector-level `LipschitzWith 1` theorem and its specialization to the chosen
  map `euclideanProjection`.

Primitive data:
* the convex set `Q`, ambient points `x₁`, `x₂`, and projection points `p₁`, `p₂`.

Derived API:
* the intrinsic metric comparison `dist p₁ p₂ ≤ dist x₁ x₂` for owner-level projection points;
* the `LipschitzWith 1` theorem for any projection selector on `Q`;
* the chosen-map corollary for `euclideanProjection` once completeness supplies that selector.

The proof uses only real inner-product geometry. Completeness is therefore kept out of the
owner-level and selector-level statements, and is introduced only for the final bridge to the
chosen projection map from `Theorem_2_33`.
-/

namespace IsProjectionPointOn

/-- Any two projection points onto a convex set are at most as far apart as their base points. -/
-- Proof sketch: apply the projection variational inequality to `hp₁` with the feasible point `p₂`
-- and to `hp₂` with the feasible point `p₁`. Adding the two inequalities gives
-- `‖p₁ - p₂‖ ^ 2 ≤ ⟪p₁ - p₂, x₁ - x₂⟫`, and Cauchy--Schwarz yields the desired bound.
theorem dist_le_dist
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x₁ p₁ x₂ p₂ : E}
    (hp₁ : IsProjectionPointOn Q x₁ p₁) (hp₂ : IsProjectionPointOn Q x₂ p₂) :
    dist p₁ p₂ ≤ dist x₁ x₂ := by
  have h₁ : 0 ≤ inner ℝ (p₁ - x₁) (p₂ - p₁) :=
    hp₁.inner_sub_nonneg hQ_convex hp₂.1
  have h₂ : 0 ≤ inner ℝ (p₂ - x₂) (p₁ - p₂) :=
    hp₂.inner_sub_nonneg hQ_convex hp₁.1
  have hpair : p₂ - p₁ = -(p₁ - p₂) := by
    abel
  have h₁' : inner ℝ (p₁ - x₁) (p₁ - p₂) ≤ 0 := by
    rw [hpair, inner_neg_right] at h₁
    linarith
  have haux : 0 ≤ inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) := by
    have hrewrite :
        inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) =
          inner ℝ (p₂ - x₂) (p₁ - p₂) - inner ℝ (p₁ - x₁) (p₁ - p₂) := by
      simp [sub_eq_add_neg, inner_add_left, add_comm, add_left_comm, add_assoc]
    rw [hrewrite]
    linarith
  have hmain : ‖p₁ - p₂‖ ^ (2 : ℕ) ≤ inner ℝ (p₁ - p₂) (x₁ - x₂) := by
    have hrewrite :
        inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) =
          inner ℝ (p₁ - p₂) (x₁ - x₂) - ‖p₁ - p₂‖ ^ (2 : ℕ) := by
      rw [inner_sub_left, real_inner_comm (x₁ - x₂), real_inner_self_eq_norm_sq]
    rw [hrewrite] at haux
    linarith
  have hcs : inner ℝ (p₁ - p₂) (x₁ - x₂) ≤ ‖p₁ - p₂‖ * ‖x₁ - x₂‖ := by
    simpa [Real.norm_eq_abs] using real_inner_le_norm (p₁ - p₂) (x₁ - x₂)
  have hnorm : ‖p₁ - p₂‖ ≤ ‖x₁ - x₂‖ := by
    nlinarith [hmain, hcs, norm_nonneg (p₁ - p₂), norm_nonneg (x₁ - x₂)]
  simpa [dist_eq_norm] using hnorm

/-- Any projection selector on a convex set is nonexpansive, recorded in the canonical map-level
form `LipschitzWith 1`. -/
theorem lipschitzWith
    {Q : Set E} (hQ_convex : Convex ℝ Q) {projQ : E → E}
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x)) :
    LipschitzWith 1 projQ := by
  refine LipschitzWith.mk_one ?_
  intro x₁ x₂
  exact (hproj x₁).dist_le_dist hQ_convex (hproj x₂)

end IsProjectionPointOn

section

variable [CompleteSpace E]

/-- Theorem 2.34: the Euclidean projection onto a nonempty closed convex set in a complete real
inner product space is nonexpansive, recorded in the canonical map-level form `LipschitzWith 1`.
The textbook Euclidean-space statement is the specialization to `ℝⁿ`. -/
theorem euclideanProjection_nonexpansive
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q) :
    LipschitzWith 1 (euclideanProjection Q hQ_nonempty hQ_closed hQ_convex) :=
  IsProjectionPointOn.lipschitzWith hQ_convex
    (fun x ↦ euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex x)

end
