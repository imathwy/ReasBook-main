import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_3_2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_4_2
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped RealSymmetricMatrixSpace

section

variable (n : ℕ)

/- Lemma 5.4.4.2 lies in the Chapter 5 self-concordant-barrier / positive-semidefinite-cone
domain.

Sampled owner-style declarations:
* `𝕊^n₊₊` from `Definition_5_4_4_5`, the source-facing owner for the strict cone
  `int(𝕊ⁿ₊)`;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the Chapter 5 owner for
  `ν`-self-concordant barriers;
* `IsSelfConcordantBarrierOnWith.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions`
  from `Theorem_5_4_1_2`, the canonical owner theorem behind this lower bound;
* `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone` from
  `Theorem_5_4_4_3`, the chapter barrier instance on the same strict cone.

Best owner abstraction:
* source-facing: the strict cone `𝕊^n₊₊`;
* core/canonical: `IsSelfConcordantBarrierOnWith`;
* bridge/view: `𝕊^n₊₊ = interior (𝕊^n₊)`.

Primitive data:
* `n : ℕ`.

Derived API:
* the barrier-owner hypothesis on `𝕊^n₊₊`;
* the dimension lower bound `(n : ℝ) ≤ (ν : ℝ)`.

This file therefore uses the strict-cone owner already introduced upstream instead of keeping the
raw `interior (𝕊^n₊)` surface in the main statement, and it reuses the Chapter 5 symmetric-space
owner file for the ambient Hilbert-space and completeness structure instead of rebuilding a
parallel local instance tower.
-/

-- Proof sketch: apply
-- `barrierParameter_ge_sum_alpha_div_beta_of_recession_directions` to the cone `𝕊^n₊` in the
-- intrinsic symmetric space `𝕊^n`, with base point the identity matrix,
-- recession directions the rank-one matrices `eᵢ eᵢᵀ`, and coefficients `αᵢ = βᵢ = 1`. Then
-- `I - ∑ i, eᵢ eᵢᵀ = 0` lies in the cone, each backward step `I - eᵢ eᵢᵀ` lies on the boundary
-- rather than in the interior, and the left-hand side becomes `∑ i, 1 = n`.
/-- Lemma 5.4.4.2: every `ν`-self-concordant barrier for the cone `𝕊ⁿ₊` of positive semidefinite
real `n × n` matrices has barrier parameter at least `n`. -/
theorem positiveSemidefiniteCone_barrierParameter_ge_dimension
    {ν : NNReal} {F : 𝕊^n → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (𝕊^n₊₊ : Set (𝕊^n)) ν F) :
    (n : ℝ) ≤ (ν : ℝ) := by
  letI : IsSelfConcordantBarrierOnWith (𝕊^n₊₊ : Set (𝕊^n)) ν F := hF
  sorry

end

end
