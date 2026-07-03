import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_33 (from Chap02) -/
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

/- Definition 2.33 lies in the nearest-point / constrained-argmin domain.

Sampled owner-style declarations:
* `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical
  constrained minimizer-set owner;
* `IsProjectionPointOn` and `isProjectionPointOn_iff_eq_sInf` in `Chap07/Definition_7_3`, the
  project owner for pointwise projection data;
* `IsMinOn` and `isMinOn_iff` in mathlib, the canonical minimizing-property owner.

Source/core/bridge triage:
* source-facing: the projection set `π_Q(x₀)` and its elements;
* core/canonical: `argmin[Q] (fun x ↦ ‖x - x₀‖)`;
* bridge/view: the pointwise owner predicate `IsProjectionPointOn Q x₀ p` and its minimizing
  reformulation below.

The textbook definition is therefore recorded through the canonical constrained argmin set, with
pointwise projection language recovered by companion bridge lemmas rather than by a parallel local
wrapper. -/

section

variable (Q : Set E) (x₀ : E)

set_option linter.hashCommand false in
/- Definition 2.33: for a nonempty closed set `Q`, the textbook projection set `π_Q(x₀)` is
formalized by the canonical constrained argmin set of the distance function
`x ↦ ‖x - x₀‖` on `Q`. -/
#check (argmin[Q] (fun x : E ↦ ‖x - x₀‖) : Set E)

end

namespace IsProjectionPointOn

/-- A projection point of `x₀` onto `Q` realizes the norm infimum of the distance-to-`x₀`
function on `Q`. -/
theorem norm_eq_iInf {Q : Set E} {x₀ p : E} (hp : IsProjectionPointOn Q x₀ p) :
    ‖x₀ - p‖ = ⨅ w : Q, ‖x₀ - w‖ := by
  simpa [Metric.infDist_eq_iInf, dist_eq_norm] using hp.2

/-- Any feasible point whose norm distance to `x₀` realizes the infimum over `Q` is a projection
point of `x₀` onto `Q`. -/
theorem of_norm_eq_iInf {Q : Set E} {x₀ p : E} (hpQ : p ∈ Q)
    (hpinf : ‖x₀ - p‖ = ⨅ w : Q, ‖x₀ - w‖) :
    IsProjectionPointOn Q x₀ p := by
  exact ⟨hpQ, by simpa [Metric.infDist_eq_iInf, dist_eq_norm] using hpinf⟩

/-- A projection point of `x₀` onto `Q` minimizes the distance-to-`x₀` function on `Q`. -/
-- Proof sketch: unpack `IsProjectionPointOn Q x₀ p` into feasibility and the equality
-- `dist x₀ p = Metric.infDist x₀ Q`; then compare `Metric.infDist x₀ Q` with `dist x₀ y` for each
-- feasible `y ∈ Q`, and rewrite the distances as norms.
theorem isMinOn {Q : Set E} {x₀ p : E} (hp : IsProjectionPointOn Q x₀ p) :
    IsMinOn (fun y ↦ ‖y - x₀‖) Q p := by
  rw [isMinOn_iff]
  intro y hy
  have hdist : dist x₀ p ≤ dist x₀ y := by
    calc
      dist x₀ p = Metric.infDist x₀ Q := hp.2
      _ ≤ dist x₀ y := Metric.infDist_le_dist_of_mem hy
  simpa [dist_eq_norm, norm_sub_rev] using hdist

/-- A point is a projection point of `x₀` onto `Q` exactly when it belongs to `Q` and minimizes
the distance-to-`x₀` function on `Q`. -/
-- Proof sketch: one direction is `isMinOn`. For the converse, combine feasibility with the
-- minimizing inequality, use `Metric.le_infDist` and `Metric.infDist_le_dist_of_mem`, and rewrite
-- the resulting distance equality back into the owner predicate `IsProjectionPointOn`.
theorem iff_isMinOn {Q : Set E} {x₀ p : E} :
    IsProjectionPointOn Q x₀ p ↔
      p ∈ Q ∧ IsMinOn (fun y ↦ ‖y - x₀‖) Q p := by
  constructor
  · intro hp
    exact ⟨hp.1, hp.isMinOn⟩
  · rintro ⟨hpQ, hpmin⟩
    refine ⟨hpQ, le_antisymm ?_ (Metric.infDist_le_dist_of_mem hpQ)⟩
    rw [Metric.le_infDist ⟨p, hpQ⟩]
    intro y hy
    simpa [dist_eq_norm, norm_sub_rev] using (isMinOn_iff.mp hpmin y hy)

/-- Membership in the canonical projection set of `x₀` onto `Q` is equivalent to being a
projection point in the owner predicate `IsProjectionPointOn`. -/
-- Proof sketch: unfold membership in `argmin[Q] (fun y ↦ ‖y - x₀‖)` using
-- `mem_constrainedArgmin_iff`, then apply `iff_isMinOn`.
theorem mem_argmin_iff {Q : Set E} {x₀ p : E} :
    p ∈ argmin[Q] (fun y : E ↦ ‖y - x₀‖) ↔ IsProjectionPointOn Q x₀ p := by
  rw [mem_constrainedArgmin_iff]
  exact iff_isMinOn.symm

end IsProjectionPointOn

end

/-! ### Proposition_2_33 (from Chap02) -/
open scoped BigOperators

/- Primary domain: scalar logarithmic complexity bounds for total internal costs in Chapter 2.

Owner abstractions sampled before refining:
- `sum_le_of_log_ratio_step_bounds` in `Proposition_2_32.lean`, the Chapter 2 owner for
  the accumulated internal cost `∑_{k=0}^N j(k)`;
- `accuracyStoppingIndex_le_one_add_sqrt_condition_log_ratio` in `Lemma_2_28.lean`, the Chapter 2
  owner bound for the terminal stopping index `j^*`;
- `Real.log_mul` for the canonical recombination of the intermediate logarithms
  `log (Δ₀ / Δ_{N+1})` and `log (Δ_{N+1} / ε)`.

Best owner abstraction:
- the source-facing owner theorem
  `constrainedMinimization_totalIterationCount_le_logarithmic_bound`, obtained by combining the
  Chapter 2 accumulated-cost owner theorem `sum_le_of_log_ratio_step_bounds` with the
  terminal logarithmic bound.

Source/core/bridge triage:
- source-facing: Proposition 2.33 itself, which packages the total internal iteration count on the
  positive domain `x ∈ (0, 2 * (Q_f - 1))`, `ε > 0`, and positive `Δ₀, …, Δ_{N+1}`;
- core/canonical: the Chapter 2 accumulated-cost owner
  `sum_le_of_log_ratio_step_bounds`;
- bridge/view: the private recombination lemma
  `combine_terminal_and_accumulated_log_bounds`.

Primitive data:
- the cost sequence `j`, the terminal contribution `jStar`, and the positive stage sequence `Δ`;
- the source-domain parameters `Qf`, `x`, and `ε`.

Derived API:
- the final total logarithmic estimate after recombining the endpoint ratios.
-/

/-- Helper for Proposition 2.33: combine the scalar terminal bound for `jStar` with the scalar
accumulated bound for `∑_{k=0}^N j(k)` after splitting and recombining the endpoint logarithms. -/
private theorem combine_terminal_and_accumulated_log_bounds
    (N : ℕ) (jStar accumulatedCost Δfinal Δ0 Qf x ε : ℝ)
    (hconst_pos : 0 < 2 * (Qf - 1) / x)
    (hΔ0 : 0 < Δ0) (hΔfinal : 0 < Δfinal) (hε : 0 < ε)
    (hjStar_bound :
      jStar ≤
        1 + Real.sqrt Qf * Real.log ((2 * (Qf - 1) * Δfinal) / (x * ε)))
    (hsum_bound :
      accumulatedCost ≤
        (N + 1 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x)) +
          Real.sqrt Qf * Real.log (Δ0 / Δfinal)) :
    jStar + accumulatedCost ≤
      (N + 2 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x)) +
        Real.sqrt Qf * Real.log (Δ0 / ε) := by
  let c : ℝ := 1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x)
  have hx_ne : x ≠ 0 := by
    intro hx
    simp [hx] at hconst_pos
  have hinitial_ratio_pos : 0 < Δ0 / Δfinal := div_pos hΔ0 hΔfinal
  have hterminal_ratio_pos : 0 < Δfinal / ε := div_pos hΔfinal hε
  -- Split the terminal logarithm into the common constant part and the final endpoint ratio.
  have hlog_jStar :
      Real.log ((2 * (Qf - 1) * Δfinal) / (x * ε)) =
        Real.log (2 * (Qf - 1) / x) + Real.log (Δfinal / ε) := by
    calc
      Real.log ((2 * (Qf - 1) * Δfinal) / (x * ε)) =
          Real.log ((2 * (Qf - 1) / x) * (Δfinal / ε)) := by
            congr 1
            field_simp [hx_ne, hε.ne']
      _ = Real.log (2 * (Qf - 1) / x) + Real.log (Δfinal / ε) := by
            rw [Real.log_mul hconst_pos.ne' hterminal_ratio_pos.ne']
  -- Recombine the initial and terminal endpoint ratios into the public `Δ 0 / ε` quantity.
  have hlog_total :
      Real.log (Δ0 / Δfinal) + Real.log (Δfinal / ε) =
        Real.log (Δ0 / ε) := by
    calc
      Real.log (Δ0 / Δfinal) + Real.log (Δfinal / ε) =
          Real.log ((Δ0 / Δfinal) * (Δfinal / ε)) := by
            symm
            rw [Real.log_mul hinitial_ratio_pos.ne' hterminal_ratio_pos.ne']
      _ = Real.log (Δ0 / ε) := by
            congr 1
            field_simp [hΔfinal.ne', hε.ne']
  have hjStar_bound' :
      jStar ≤ c + Real.sqrt Qf * Real.log (Δfinal / ε) := by
    calc
      jStar ≤
          1 +
            Real.sqrt Qf *
              (Real.log (2 * (Qf - 1) / x) + Real.log (Δfinal / ε)) := by
                simpa [hlog_jStar] using hjStar_bound
      _ = c + Real.sqrt Qf * Real.log (Δfinal / ε) := by
            simp [c]
            ring
  calc
    jStar + accumulatedCost ≤
        (c + Real.sqrt Qf * Real.log (Δfinal / ε)) +
          ((N + 1 : ℝ) * c + Real.sqrt Qf * Real.log (Δ0 / Δfinal)) := by
            exact add_le_add hjStar_bound' (by simpa [c] using hsum_bound)
    _ = (N + 2 : ℝ) * c +
          (Real.sqrt Qf * Real.log (Δ0 / Δfinal) +
            Real.sqrt Qf * Real.log (Δfinal / ε)) := by
          ring
    _ = (N + 2 : ℝ) * c +
          Real.sqrt Qf *
            (Real.log (Δ0 / Δfinal) + Real.log (Δfinal / ε)) := by
          ring
    _ = (N + 2 : ℝ) * c + Real.sqrt Qf * Real.log (Δ0 / ε) := by
          rw [hlog_total]
    _ = (N + 2 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x)) +
          Real.sqrt Qf * Real.log (Δ0 / ε) := by
          simp [c]

/-- Proposition 2.33: if `x ∈ (0, 2 * (Q_f - 1))` (so in particular `Q_f > 1`), `ε > 0`, the
stage values `Δ₀, …, Δ_{N+1}` are positive, the terminal index `j^*` satisfies the Lemma 2.28
bound with `Δ_{N+1}`, and each internal cost `j(k)` satisfies the Proposition 2.32 hypothesis,
then the total internal iteration count is bounded by
`(N + 2) * (1 + √Q_f * log (2 (Q_f - 1) / x)) + √Q_f * log (Δ₀ / ε)`. -/
-- Proof sketch: first specialize `sum_le_of_log_ratio_step_bounds` with `L = Q_f`,
-- `μ = 1`, and `κ = x` to obtain the accumulated bound for `∑_{k=0}^N j(k)`.
-- Then combine that estimate with the assumed terminal bound for `j^*` and use `Real.log_mul`
-- to eliminate the intermediate quantity `Δ_{N+1}` from the final logarithm.
theorem constrainedMinimization_totalIterationCount_le_logarithmic_bound
    (N : ℕ) (j : ℕ → ℝ) (jStar : ℝ) (Δ : ℕ → ℝ) (Qf x ε : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) (2 * (Qf - 1)))
    (hε : 0 < ε)
    (hΔ_pos : ∀ ⦃k : ℕ⦄, k ≤ N + 1 → 0 < Δ k)
    (hjStar_bound :
      jStar ≤
        1 + Real.sqrt Qf * Real.log ((2 * (Qf - 1) * Δ (N + 1)) / (x * ε)))
    (hj_bound :
      ∀ ⦃k : ℕ⦄, k ≤ N →
        j k ≤
          1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x) +
            Real.sqrt Qf * Real.log (Δ k / Δ (k + 1))) :
    jStar + Finset.sum (Finset.range (N + 1)) j ≤
      (N + 2 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x)) +
        Real.sqrt Qf * Real.log (Δ 0 / ε) := by
  have hsum_bound :
      Finset.sum (Finset.range (N + 1)) j ≤
        (N + 1 : ℝ) * (1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / x)) +
          Real.sqrt Qf * Real.log (Δ 0 / Δ (N + 1)) := by
    have hΔ_pos' : ∀ k ≤ N + 1, 0 < Δ k := fun k hk ↦ hΔ_pos hk
    have hj_bound' :
        ∀ k ≤ N,
          j k ≤
            1 + Real.sqrt Qf * Real.log (2 * (Qf - 1) / (x * 1)) +
              Real.sqrt Qf * Real.log (Δ k / Δ (k + 1)) := by
      intro k hk
      simpa [mul_one] using hj_bound hk
    simpa [mul_one] using sum_le_of_log_ratio_step_bounds N j Δ Qf Qf 1 x hΔ_pos' hj_bound'
  -- The interval hypothesis provides the positive logarithm domain needed by the helper theorem.
  have hQf_sub_pos : 0 < Qf - 1 := by
    nlinarith [hx.1, hx.2]
  have hconst_pos : 0 < 2 * (Qf - 1) / x := by
    exact div_pos (mul_pos two_pos hQf_sub_pos) hx.1
  have hDelta0 : 0 < Δ 0 := by
    exact hΔ_pos (show 0 ≤ N + 1 by simp)
  have hdeltaFinal : 0 < Δ (N + 1) := by
    exact hΔ_pos (Nat.le_refl _)
  -- Finish by combining the accumulated sum estimate with the assumed terminal bound.
  exact
    combine_terminal_and_accumulated_log_bounds
      N jStar (Finset.sum (Finset.range (N + 1)) j) (Δ (N + 1)) (Δ 0) Qf x ε
      hconst_pos hDelta0 hdeltaFinal hε hjStar_bound hsum_bound

/-! ### Theorem_2_33 (from Chap02) -/
noncomputable section

open Metric

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace IsProjectionPointOn

/-- Projection points onto a convex set are unique. -/
theorem eq
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x₀ p₁ p₂ : E}
    (hp₁ : IsProjectionPointOn Q x₀ p₁) (hp₂ : IsProjectionPointOn Q x₀ p₂) :
    p₁ = p₂ := by
  have hp₁' : ‖x₀ - p₁‖ = ⨅ w : Q, ‖x₀ - w‖ := hp₁.norm_eq_iInf
  have hp₂' : ‖x₀ - p₂‖ = ⨅ w : Q, ‖x₀ - w‖ := hp₂.norm_eq_iInf
  have h₁ : inner ℝ (x₀ - p₁) (p₂ - p₁) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hQ_convex hp₁.1).1 hp₁' p₂ hp₂.1
  have h₂ : inner ℝ (x₀ - p₂) (p₁ - p₂) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hQ_convex hp₂.1).1 hp₂' p₁ hp₁.1
  have h₁' : 0 ≤ inner ℝ (x₀ - p₁) (p₁ - p₂) := by
    have hpair : p₂ - p₁ = -(p₁ - p₂) := by
      abel
    rw [hpair, inner_neg_right] at h₁
    linarith
  have h₂' : inner ℝ (x₀ - p₁) (p₁ - p₂) + ‖p₁ - p₂‖ ^ (2 : ℕ) ≤ 0 := by
    have hrewrite :
        inner ℝ (x₀ - p₂) (p₁ - p₂) =
          inner ℝ (x₀ - p₁) (p₁ - p₂) + ‖p₁ - p₂‖ ^ (2 : ℕ) := by
      calc
        inner ℝ (x₀ - p₂) (p₁ - p₂)
            = inner ℝ ((x₀ - p₁) + (p₁ - p₂)) (p₁ - p₂) := by
                abel_nf
        _ = inner ℝ (x₀ - p₁) (p₁ - p₂) + inner ℝ (p₁ - p₂) (p₁ - p₂) := by
              rw [inner_add_left]
        _ = inner ℝ (x₀ - p₁) (p₁ - p₂) + ‖p₁ - p₂‖ ^ (2 : ℕ) := by
              rw [real_inner_self_eq_norm_sq]
    rw [hrewrite] at h₂
    exact h₂
  have hnorm : ‖p₁ - p₂‖ = 0 := by
    nlinarith [h₁', h₂', norm_nonneg (p₁ - p₂)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end IsProjectionPointOn

/-
Theorem 2.33 lies in the nearest-point / convex-geometry domain.

Owner declarations sampled for this refinement:
* `IsProjectionPointOn Q x₀ p` and `isProjectionPointOn_iff_eq_sInf` from
  `Chap07/Definition_7_3`, the project owner predicate for nearest-point geometry;
* `exists_norm_eq_iInf_of_complete_convex` in
  `Mathlib/Analysis/InnerProductSpace/Projection/Minimal`, the mathlib existence theorem for
  nearest points in complete convex sets;
* `ExistsUnique.choose_eq_iff` in `Mathlib/Logic/ExistsUnique`, the canonical chooser API once
  existence and uniqueness are established;
* `Metric.infDist_zero_of_mem`, the metric owner lemma used for the `Set.univ` specialization.

Best owner abstraction:
* `IsProjectionPointOn Q x₀ p`.

Source/core/bridge triage:
* source-facing: existence and uniqueness of the Euclidean projection point on a nonempty closed
  convex set;
* core/canonical: `IsProjectionPointOn Q x₀ p`;
* bridge/view: the chosen point `euclideanProjection` and the bridge identifying any
  owner-level projection point with that chosen point.

Primitive data:
* the set `Q` and ambient point `x₀`;
* the nonempty / closed / convex hypotheses exactly when they are needed to produce the chosen
  projection point.

Derived API:
* the chosen projection point;
* its owner predicate;
* the equality bridge from an owner-level projection point to the chosen point;
* the specialization to `Set.univ`.

The textbook statement is for `ℝⁿ`, but the owner data and sampled mathlib API show that no
coordinate structure is used. The canonical public owner therefore lives in a complete real inner
product space, and the Euclidean-space version is a specialization.
-/

section ClosedConvexProjection

variable [CompleteSpace E]

variable
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (x₀ : E)

/-- Theorem 2.33, stated at the owner level: every point of a complete real inner product space
has a unique projection point on a nonempty closed convex set `Q`. The Euclidean-space statement
is the specialization to `ℝⁿ`. -/
-- Proof sketch: `hQ_closed.isComplete` upgrades the closed set `Q` to a complete set. Apply
-- `exists_norm_eq_iInf_of_complete_convex` for existence, then use strict convexity of the norm
-- in a real inner product space to show that two minimizing points of `Q` must coincide.
theorem exists_unique_projection_point_of_nonempty_closed_convex
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (x₀ : E) :
    ∃! p : E, IsProjectionPointOn Q x₀ p := by
  obtain ⟨p, hpQ, hpinf⟩ :=
    exists_norm_eq_iInf_of_complete_convex hQ_nonempty hQ_closed.isComplete hQ_convex x₀
  have hp : IsProjectionPointOn Q x₀ p :=
    IsProjectionPointOn.of_norm_eq_iInf hpQ hpinf
  refine ExistsUnique.intro p hp ?_
  intro q hq
  exact hq.eq hQ_convex hp

/-- The Euclidean projection of `x₀` onto a nonempty closed convex set `Q`. -/
noncomputable def euclideanProjection
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (x₀ : E)
    : E :=
  (exists_unique_projection_point_of_nonempty_closed_convex
    Q hQ_nonempty hQ_closed hQ_convex x₀).choose

/-- The chosen Euclidean projection is a projection point in the owner predicate
`IsProjectionPointOn`. -/
theorem euclideanProjection_isProjectionPointOn
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (x₀ : E) :
    IsProjectionPointOn Q x₀ (euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x₀) := by
  exact
    (exists_unique_projection_point_of_nonempty_closed_convex
      Q hQ_nonempty hQ_closed hQ_convex x₀).choose_spec.1

namespace IsProjectionPointOn

/-- Any Euclidean projection point onto a nonempty closed convex set agrees with the chosen
projection `euclideanProjection`. -/
theorem eq_euclideanProjection
    {Q : Set E} {x₀ p : E}
    (hp : IsProjectionPointOn Q x₀ p) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q) :
    p = euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x₀ := by
  exact
    (exists_unique_projection_point_of_nonempty_closed_convex
      Q hQ_nonempty hQ_closed hQ_convex x₀).unique hp
      (euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex x₀)

end IsProjectionPointOn

end ClosedConvexProjection

section

variable [CompleteSpace E]

/-- The Euclidean projection onto the whole space is the ambient point itself. -/
@[simp] theorem euclideanProjection_univ
    (x : E) :
    euclideanProjection (Set.univ : Set E)
      Set.univ_nonempty isClosed_univ convex_univ x = x := by
  have hxproj : IsProjectionPointOn (Set.univ : Set E) x x := by
    refine ⟨by simp, ?_⟩
    simp [infDist_zero_of_mem (by simp : x ∈ (Set.univ : Set E))]
  simpa using
    (hxproj.eq_euclideanProjection Set.univ_nonempty isClosed_univ convex_univ).symm

end
