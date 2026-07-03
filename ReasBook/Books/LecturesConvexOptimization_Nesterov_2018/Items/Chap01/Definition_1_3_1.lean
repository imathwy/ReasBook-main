import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_3_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.3.1 lies in the finite-dimensional Euclidean box domain.

Relevant owner-style declarations sampled before refining:
* `Set.Icc`, the canonical scalar owner for the interval `[0, 1]`;
* `Set.mem_Icc`, the canonical bridge from interval membership to inequalities;
* `zeroOneBox` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_1.lean`, the chapter owner of the textbook box
  `B_n = [0,1]^n`;
* `mem_zeroOneBox_iff` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_1.lean`, the chapter bridge exposing
  the coordinatewise interval condition.

Best owner abstraction:
* the chapter owner `zeroOneBox`

Primitive data:
* the dimension `n`

Derived API:
* the membership bridge `mem_zeroOneBox_iff`
* the origin-feasibility lemma `zeroOneBox_zero_mem`

Source/core/bridge triage:
* source-facing: the textbook box `B_n = [0,1]^n`
* core/canonical: the chapter owner `zeroOneBox n : Set (EuclideanSpace ℝ (Fin n))`
* bridge/view: `mem_zeroOneBox_iff` and the inherited feasibility lemma `zeroOneBox_zero_mem`

This item is therefore refined to reuse the exact chapter owner directly, instead of keeping a
parallel local copy of the same box definition or its already-owned companion lemmas. -/

/- Definition 1.3.1: the textbook box `B_n = [0,1]^n` in `ℝⁿ` is the chapter owner
`zeroOneBox n`. -/
recall zeroOneBox (n : ℕ) : Set (EuclideanSpace ℝ (Fin n))

/- Membership in `zeroOneBox n` is exactly the coordinatewise interval condition. -/
recall mem_zeroOneBox_iff {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ zeroOneBox n ↔ ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1

/- The origin belongs to the textbook box `zeroOneBox n`. -/
recall zeroOneBox_zero_mem (n : ℕ) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ zeroOneBox n
