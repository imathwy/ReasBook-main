import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_3_12

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory intervalIntegral

/- Definition 1.3.12 lies in the one-dimensional interval-integral / quadrature domain.

Relevant owner-style declarations sampled before refining:
* `∫ x in (0 : ℝ)..1, f x`, the canonical mathlib interval-integral owner for the exact quantity
  on `[0, 1]`;
* `uniformGridRiemannSum` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_3_12.lean`, the chapter owner of the
  source-facing right-endpoint uniform-grid approximation;
* `Finset.range`, the canonical finite owner for the `N` right-endpoint sample cells.

Best owner abstraction:
* source-facing: `uniformGridRiemannSum f N`;
* core/canonical: the interval integral and the finite sum over `Finset.range (N : ℕ)`;
* bridge/view: the sampled nodes `((i + 1 : ℝ) / N)`.

Primitive data:
* `f : ℝ → ℝ`;
* `N : ℕ+`.

Derived API:
* the exact quantity `∫ x in (0 : ℝ)..1, f x`;
* the explicit right-endpoint formula for `uniformGridRiemannSum`.

The chapter file already owns the source-facing Riemann-sum definition with the correct positivity
discipline on the mesh size. This item is therefore recall-first: it reuses that owner directly
instead of keeping a parallel local copy with an over-weak `ℕ` parameter and a redundant node
wrapper. -/

section

variable (f : ℝ → ℝ) (N : ℕ+)

/- Definition 1.3.12: the exact quantity is the canonical interval integral `∫_0^1 f(x) dx`. -/
#check (∫ x in (0 : ℝ)..1, f x)

/- Definition 1.3.12: the right-endpoint uniform-grid approximation on `[0, 1]` is the chapter
owner `uniformGridRiemannSum`. -/
recall uniformGridRiemannSum (f : ℝ → ℝ) (N : ℕ+) : ℝ

recall uniformGridRiemannSum_def (f : ℝ → ℝ) (N : ℕ+) :
    uniformGridRiemannSum f N =
      (1 / (N : ℝ)) * ∑ i ∈ Finset.range (N : ℕ), f ((i + 1 : ℝ) / N)

end
