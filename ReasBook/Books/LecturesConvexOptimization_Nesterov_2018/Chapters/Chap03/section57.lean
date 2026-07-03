import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_57 (from Chap03) -/
variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

open Matrix
open scoped EllipsoidNotation

/-
Definition 3.57 lies in the chapter's Euclidean ellipsoid / cutting-plane domain.

Sampled owner-style declarations:
- `centerCutEllipsoid` in `Lemma_3_2_7`, the earlier Chapter 3 source-facing owner of the
  half-ellipsoid cut `E₊`;
- `mem_centerCutEllipsoid_iff` in `Lemma_3_2_7`, the canonical companion membership theorem;
- `affineEllipsoid` and `mem_affineEllipsoid_iff` in `Lemma_3_2_7`, the owner/view for the
  ambient ellipsoid `E(H, x̄)`;
- `Matrix.toEuclideanLin` in mathlib, the owner of the matrix action on `EuclideanSpace ℝ (Fin n)`.

Best owner abstraction:
- source-facing/core owner: `centerCutEllipsoid`;
- bridge/view: the textbook sign-reversed inequality `0 ≤ inner ℝ g (xBar - x)`.

Primitive data:
- `H : Mat`;
- `xBar : E`;
- `g : E`.

Derived API:
- the half-ellipsoid `centerCutEllipsoid H xBar g`;
- its canonical membership theorem `mem_centerCutEllipsoid_iff`;
- the textbook reformulation below, obtained by expanding ellipsoid membership and rewriting
  `inner ℝ g (x - xBar) ≤ 0` as `0 ≤ inner ℝ g (xBar - x)`.

Source/core/bridge triage:
- source-facing: the half-ellipsoid `E₊`;
- core/canonical: the existing chapter owner from `Lemma_3_2_7`;
- bridge/view: the expanded textbook membership formula.

This file should therefore reuse the owner directly and keep only the thin bridge needed to match
the textbook phrasing, rather than maintaining a parallel local definition `halfEllipsoid`.
-/

recall centerCutEllipsoid
    (H : Mat) (xBar g : E) :
    Set E

recall mem_centerCutEllipsoid_iff
    {H : Mat} {xBar g x : E} :
    x ∈ E₊(H, xBar, g) ↔
      x ∈ E(H, xBar) ∧ inner ℝ g (x - xBar) ≤ 0

/-- Membership in `E₊` is exactly the defining quadratic inequality for `E(H, x̄)` together with
the textbook halfspace inequality `⟪g, xBar - x⟫ ≥ 0`. -/
theorem mem_centerCutEllipsoid_textbook_iff
    {H : Mat} {xBar g x : E} :
    x ∈ E₊(H, xBar, g) ↔
      inner ℝ (toEuclideanLin H⁻¹ (x - xBar)) (x - xBar) ≤ 1 ∧
        0 ≤ inner ℝ g (xBar - x) := by
  rw [mem_centerCutEllipsoid_iff, mem_affineEllipsoid_iff]
  constructor
  · rintro ⟨hxEll, hxCut⟩
    refine ⟨hxEll, ?_⟩
    simpa [inner_sub_right, sub_nonneg] using hxCut
  · rintro ⟨hxEll, hxCut⟩
    refine ⟨hxEll, ?_⟩
    simpa [inner_sub_right, sub_nonneg] using hxCut

/-! ### Proposition_3_57 (from Chap03) -/
noncomputable section

/- Proposition 3.57 lies in the constrained level-method total internal-complexity domain.

Relevant owner declarations sampled before refining:
- `ConstrainedLevelMethod.stoppingIndex` in `Algorithm_3_11`, the canonical full-step internal
  iteration count at one master step;
- `ConstrainedLevelMethod.globalStopIndex` in `Algorithm_3_11`, the canonical terminal-step
  internal iteration count at the first globally stopping master step;
- `constrainedLevelMethodInternalIterationBound` in `Theorem_3_3_3`, the uniform per-step
  internal-iteration bound;
- `constrained_level_total_internal_iterations_le` in `Theorem_3_3_3`, the chapter owner theorem
  for the total internal-iteration estimate.

Best owner abstraction:
- source-facing: the total internal iteration count of a constrained level method up to the first
  globally stopping master step;
- core/canonical: `constrained_level_total_internal_iterations_le`;
- bridge/view: none.

Primitive data:
- the constrained level method and its canonical full-step and terminal-step iteration counts;
- the logarithmic outer-step threshold and uniform per-step complexity bound.

Derived API:
- none beyond direct recall of the chapter owner theorem.

Source/core/bridge triage:
- source-facing: the constrained level method and its actual internal iteration counts;
- core/canonical: `constrained_level_total_internal_iterations_le`;
- bridge/view: none.

The former file duplicated the theorem from `Theorem_3_3_3` under a second public name with the
same interface. This refinement removes that parallel wrapper and keeps Proposition 3.57 as a
direct recall of the canonical chapter theorem. -/

/- Proposition 3.57 is the direct recall of the chapter owner theorem
`constrained_level_total_internal_iterations_le`. -/
recall constrained_level_total_internal_iterations_le

end

/-! ### Theorem_3_57 (from Chap03) -/
noncomputable section

universe u

variable {X : Type u} [PseudoMetricSpace X]

open scoped LevelMethodNotation

/- Theorem 3.57 lies in the chapter's level-method scalar-history / feasible-set-diameter domain.

Primary domain:
* stopping-time bounds for a level-method scalar history, parameterized by a bounded feasible
  set and its diameter.

Sampled owner declarations:
* `LevelMethodHistory` in `Lemma_3_3_1`
* `LevelMethodHistory.gap` in `Lemma_3_3_1`
* `LevelMethodHistory.shouldStop` in `Lemma_3_3_1`
* `Bornology.IsBounded`
* `Metric.diam`
* `Metric.diam_eq_zero_of_unbounded`
* `exists_stopping_index_le_levelMethodIterationCap_and_optimalValue_sub_fStar_le_epsilon` in
  `Theorem_3_3_1`

Best owner abstraction:
* the scalar history is the canonical owner `LevelMethodHistory`
* the feasible-set size is organized by the canonical bounded-set predicate
  `Bornology.IsBounded Q` together with the metric owner `Metric.diam Q`

Primitive data:
* the scalar history `history`
* the feasible set `Q`
* the boundedness witness `Bornology.IsBounded Q`
* the reference value `fStar`

Derived API:
* the feasible-set diameter `Metric.diam Q`
* the canonical gap notation `δ[history](k)`
* `history.shouldStop`
* `levelMethodIterationCap`

Source/core/bridge triage:
* source-facing: the bounded-feasible-set diameter specialization of the stopping statement
* core/canonical: the scalar-history theorem from `Theorem_3_3_1`
* bridge/view: the specialization `D = Metric.diam Q` under the boundedness guard that makes
  this real-valued diameter source-faithful

Once the block-length estimate is supplied explicitly, the separate convexity and Lipschitz
assumptions are not primitive inputs to this theorem statement. This file therefore reuses the
chapter owner abstractions directly instead of rebuilding parallel raw-sequence notions of the gap,
stopping rule, and iteration cap. Because mathlib defines the real-valued diameter by
`Metric.diam Q = ENNReal.toReal (Metric.ediam Q)`, it collapses to `0` on unbounded sets. The
textbook theorem is about a genuine finite feasible-set diameter, so this source-facing
specialization records `Bornology.IsBounded Q` explicitly and only then reuses `Metric.diam Q`.
The textbook ambient model `Q ⊆ ℝⁿ` still enters only through boundedness and diameter, so the
public theorem surface stays at the intrinsic metric level, with the Euclidean case as a direct
specialization.
-/

/-- Theorem 3.57: for a bounded feasible set `Q`, a level-method scalar history `history`, and a
reference value `fStar`, if the history lower bounds stay below `fStar` and the textbook
block-length estimate holds on every positive-terminal-gap interval where the gap `δ_k` does not
shrink by more than the factor `1 - α`, then the method satisfies the
stopping criterion after at most
`⌊M_f^2 D^2 / (ε^2 α (1 - α)^2 (2 - α))⌋ + 1` iterations; moreover any stopping index `k`
satisfies `f_k^* - fStar ≤ ε`, with the source-faithful specialization `D = Metric.diam Q`. -/
-- Proof sketch: argue by contradiction and assume `δ_k > ε` up to the claimed cap. Partition the
-- indices into maximal consecutive blocks on which the terminal gap stays at least `(1 - α)`
-- times the initial gap. The block-length hypothesis bounds each block by
-- `M_f^2 D^2 / ((1 - α)^2 δ_{p(j)}^2)`, while the block-start gaps grow geometrically by the
-- factor `(1 - α)⁻¹`; summing the resulting geometric series yields the displayed iteration cap.
theorem levelMethod_stops_and_optimalValue_sub_fStar_le_epsilon_of_diam
    {Q : Set X} (hQ_bounded : Bornology.IsBounded Q)
    {history : LevelMethodHistory} {fStar : ℝ}
    {M_f : NNReal} {ε : Set.Ioi (0 : ℝ)} {α : Set.Ioo (0 : ℝ) 1}
    (hvalidLower : ∀ k : ℕ, history.approximateOptimalValue k ≤ fStar)
    (hblock :
      ∀ {k p : ℕ}, k ≤ p →
        δ[history](p) ≥ (1 - α) * δ[history](k) →
        0 < δ[history](p) →
        ((p + 1 - k : ℕ) : ℝ) ≤
          (M_f ^ (2 : ℕ) * (Metric.diam Q) ^ (2 : ℕ)) /
            ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ))) :
    (∃ k ≤ levelMethodIterationCap M_f (Metric.diam Q) ε α,
      history.shouldStop ε k) ∧
      ∀ k : ℕ,
        history.shouldStop ε k →
          history.optimalValue k - fStar ≤ ε := by
  have _ : Metric.ediam Q ≠ ⊤ := hQ_bounded.ediam_ne_top
  simpa using
    exists_stopping_index_le_levelMethodIterationCap_and_optimalValue_sub_fStar_le_epsilon
      history ε.2 α.2 hvalidLower hblock
