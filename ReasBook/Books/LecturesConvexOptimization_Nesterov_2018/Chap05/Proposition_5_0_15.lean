import Mathlib
import Nesterov.Chap05.Definition_5_0_13
import Nesterov.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DikinEllipsoidNotation Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantOnWith

/- Proposition 5.0.15 lies in the Chapter 5 self-concordance / Hessian-comparison domain.

Sampled owner declarations:
* `IsSelfConcordantOnWith` in `Definition_5_1_1`, the quantitative source-facing owner for
  self-concordance on a domain;
* `hessian` in `Chap01/Definition_1_4_16`, the canonical second-order operator owner;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` in `Definition_5_1_1`, the chapter owner for
  the local Hessian norm;
* `openDikinEllipsoid` together with the notation `W⁰[f; x](r)` in `Definition_5_0_13`, the
  source-facing owner for the Dikin-radius hypothesis.

Source/core/bridge triage:
* source-facing: the pointwise Hessian comparison between `x` and `y` under the textbook
  open-Dikin hypothesis;
* core/canonical: `IsSelfConcordantOnWith dom Mf f`, `hessian f z`, and `W⁰[f; x](r)`;
* bridge/view: the local-norm inequality encoded by membership in `W⁰[f; x](r)`.

Primitive data:
* a domain `dom`, a self-concordance constant `Mf`, and a function `f`;
* points `x y : E` and a radius `r`;
* the owner hypothesis `hself : IsSelfConcordantOnWith dom Mf f`;
* the source-facing inputs `hx : x ∈ dom`, `hr : r < 1 / (Mf : ℝ)`, and
  `hxy : y ∈ W⁰[f; x](r)`.

Derived API:
* the lower and upper Loewner-order bounds comparing `hessian f x` and `hessian f y`.

The theorem should therefore stay directly on the bundled self-concordance owner and the canonical
Hessian owner, rather than reintroducing scalarized quadratic-form wrappers as primitive public
data. -/

-- Proof sketch: for a fixed direction `v`, apply the one-dimensional self-concordance estimate
-- along the segment from `x` to `y` to the univariate function obtained by restricting the
-- Hessian quadratic form in the direction `v`. The Dikin-radius bound
-- `hessianLocalNorm f x (y - x) < r < 1 / M_f` then yields the factor `(1 - M_f r)^2` and its
-- reciprocal uniformly in `v`, which is exactly the Loewner-order comparison of the intrinsic
-- Hessian operators at `x` and `y`. The hypotheses `y ∈ dom`, `0 ≤ r`, and `0 < M_f` are
-- redundant here: `hxy` together with `hr` already forces `r > 0`, and the Chapter 5 Dikin-ball
-- inclusion theorem then recovers `y ∈ dom`.
/-- Proposition 5.0.15: if `f` is self-concordant on `dom` with parameter `M_f`, `x ∈ dom`,
`r < 1 / M_f`, and `y ∈ W⁰[f; x](r)`, then the Hessians at `x` and `y` are comparable in
Loewner order by the factors `(1 - M_f r)^2` and `(1 - M_f r)⁻²`. The statement is expressed
with the canonical Hessian owner `hessian f`. -/
theorem hessian_loewner_bounds_of_mem_openDikinEllipsoid
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} {r : ℝ} (hx : x ∈ dom) (hr : r < 1 / (Mf : ℝ))
    (hxy : y ∈ W⁰[f; x](r)) :
    ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * r) ^ (2 : ℕ))⁻¹ • hessian f x := sorry

end IsSelfConcordantOnWith

end
