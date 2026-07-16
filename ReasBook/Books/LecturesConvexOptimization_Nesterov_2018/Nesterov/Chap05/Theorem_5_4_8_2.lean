import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_8_5
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Example_5_3_1_3
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Theorem 5.4.8.2 lies in the chapter's logarithmic-barrier / epigraph-lifting domain.

Sampled owner declarations:
* `negLog_isSelfConcordantBarrierOnWith_nonnegativeRay` in `Example_5_3_1_3`, the scalar owner
  for the base barrier `x ↦ -log x`;
* `epigraphLogBarrier_isSelfConcordantBarrierOnWith` in `Theorem_5_3_5`, the chapter owner for
  lifting a barrier to the strict epigraph on the canonical `WithLp 2 (E × ℝ)` product;
* mathlib `WithLp 2 (ℝ × ℝ)` together with `WithLp.ofLp`, the canonical `L²` ambient owner and
  the public bridge back to the textbook raw pairs;
* `constrainedEpigraph` and `mem_constrainedEpigraph_iff` in `Chap03/Definition_3_3`, the
  chapter owner for the closed epigraph from Definition 5.4.8.5;
* `strictConstrainedEpigraph` and `epigraphLogBarrier` in `Theorem_5_3_5`, the source-facing
  strict-epigraph and lifted-barrier owners reused by the specialization below.

Best owner abstraction:
* source-facing: the interior of the closed epigraph from Definition 5.4.8.5;
* core/canonical: the lifted barrier owner
  `epigraphLogBarrier_isSelfConcordantBarrierOnWith`;
* bridge/view: the interior-identification theorem below, which rewrites the closed epigraph
  interior as the corresponding strict epigraph.

Primitive data:
* the base logarithmic barrier `x ↦ -Real.log x`;
* the closed epigraph owner
  `constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ))`.

Derived API:
* the source-facing interior membership theorem;
* the specialized lifted barrier statement for the canonical epigraph logarithmic barrier.

The file therefore keeps the source-facing interior statement, but the barrier theorem is intended
to be a thin specialization of the chapter owners for the scalar `-log` barrier and epigraph
lifting, rather than a second local barrier construction. -/

local notation "Z" => WithLp 2 (ℝ × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → ℝ × ℝ)
local notation "Q₁" =>
  constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ))

-- Proof sketch: the interior of the canonical closed epigraph from Definition 5.4.8.5 is
-- obtained by replacing the boundary inequality `t ≥ -\log x` with the strict inequality
-- `t > -\log x` while keeping `x > 0`.
/-- A point lies in the interior of the canonical epigraph for Definition 5.4.8.5 exactly when
`x > 0` and `t > -\log x`. -/
theorem mem_interior_constrainedEpigraph_negLog_iff {x t : ℝ} :
    (x, t) ∈ interior Q₁ ↔ 0 < x ∧ t > -Real.log x := sorry

-- Proof sketch: first rewrite the interior of the canonical closed epigraph from
-- Definition 5.4.8.5 as the strict epigraph of `x ↦ -\log x` via
-- `mem_interior_constrainedEpigraph_negLog_iff`. Then specialize the scalar owner
-- `negLog_isSelfConcordantBarrierOnWith_nonnegativeRay` and the canonical epigraph-lifting owner
-- `epigraphLogBarrier_isSelfConcordantBarrierOnWith`; since the scalar barrier parameter is `1`,
-- the lifted epigraph barrier has the exact source parameter `1 + 1 = 2`.
/-- Theorem 5.4.8.2: the canonical epigraph logarithmic barrier specialized to `x ↦ -\log x`,
namely `F₁(x, t) = -\log x - \log (\log x + t)`, is a `2`-self-concordant barrier for the
canonical epigraph of Definition 5.4.8.5, viewed on the canonical `L²` product owner
`Z = WithLp 2 (ℝ × ℝ)` through `z ↦ z.ofLp`. -/
theorem epigraphLogBarrier_negLog_is_two_selfConcordantBarrier :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' interior Q₁)
      (2 : NNReal)
      (epigraphLogBarrier (fun x : ℝ ↦ -Real.log x) ∘ ofZ) := by
  have hQ₁ :
      interior Q₁ = strictConstrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -Real.log x) := by
    ext z
    rcases z with ⟨x, t⟩
    rw [mem_strictConstrainedEpigraph_iff]
    simpa [gt_iff_lt] using
      (show (x, t) ∈ interior Q₁ ↔ 0 < x ∧ t > -Real.log x from
        mem_interior_constrainedEpigraph_negLog_iff)
  have hν : (1 : NNReal) + 1 = 2 := by
    norm_num
  simpa [hQ₁, hν] using
    (epigraphLogBarrier_isSelfConcordantBarrierOnWith
      negLog_isSelfConcordantBarrierOnWith_nonnegativeRay)
