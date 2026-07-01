import Mathlib.Tactic.Recall
import Nesterov.Chap01.Definition_1_5_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.5.1 lies in the higher-order Taylor-coefficient regularity domain.

Relevant owner-style declarations sampled before refining:
* `taylorCoeffLipschitzClass` in `Nesterov/Chap01/Definition_1_5_1.lean`, the project's
  source-facing owner for the textbook class `C^{k,p}_L(Q)`;
* `HasFTaylorSeriesUpToOn`, the canonical mathlib owner for Taylor data on a set;
* `mem_taylorCoeffLipschitzClass_notation_iff`, the source-facing membership bridge for the
  textbook notation;
* `taylorCoeffLipschitzClass.exists_taylorSeries`, the canonical witness-extraction theorem used
  by direct downstream files such as `Chap04/Definition_4_2_10`.

Best owner abstraction:
* source-facing owner: `taylorCoeffLipschitzClass k p L Q`;
* core/canonical owner: `HasFTaylorSeriesUpToOn`;
* bridge/view: the notation surface `f ∈ 𝒞^{k,p}_{L}(Q)` and the witness-extraction API.

Primitive data:
* the orders `k` and `p`;
* the Lipschitz constant `L`;
* the set `Q`;
* a Taylor witness `P` together with `HasFTaylorSeriesUpToOn k f P Q`;
* the Lipschitz bound on the `p`-th Taylor coefficient.

Derived API:
* the source-facing class membership `f ∈ 𝒞^{k,p}_{L}(Q)`;
* the order consequence `p ≤ k`;
* extraction of the Taylor witness and its Lipschitz estimate.

Source/core/bridge triage:
* source-facing: the textbook class `C^{k,p}_L(Q)`;
* core/canonical: `HasFTaylorSeriesUpToOn`;
* bridge/view: the notation and witness theorems exported by the Chapter 1 owner file.

This item is therefore a source-facing recall of the existing Chapter 1 owner rather than a new
local definition. Keeping a second item-local set-valued wrapper here would duplicate the owner
already used downstream. -/

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (k p : ℕ) (L : NNReal) (Q : Set E) (f : E → ℝ)

/- Definition 1.5.1: the textbook class `C^{k,p}_L(Q)` is the Chapter 1 owner
`taylorCoeffLipschitzClass k p L Q`. -/
recall taylorCoeffLipschitzClass

/- The textbook notation already uses this owner directly. -/
#check (f ∈ 𝒞^{k,p}_{L}(Q))

/- Membership in the textbook notation is exactly the source-facing Taylor-witness condition. -/
recall mem_taylorCoeffLipschitzClass_notation_iff

/- Membership provides the textbook order bound `p ≤ k`. -/
recall taylorCoeffLipschitzClass.order_le

/- Membership also provides the underlying Taylor witness and its Lipschitz coefficient bound. -/
recall taylorCoeffLipschitzClass.exists_taylorSeries

end
