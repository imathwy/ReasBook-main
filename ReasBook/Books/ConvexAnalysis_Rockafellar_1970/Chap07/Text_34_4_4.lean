import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_5
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_34_1_3

noncomputable section

open Bifunction (productSignSaddle)

namespace SaddleFunction

/-!
Source/core/bridge triage:

- `source-facing`: this item gives a concrete concave-convex saddle-function on `ℝ × ℝ` whose
  slice domains show that the Chapter 34 simplicity condition fails.
- `core/canonical`: the relevant owner predicates are `SaddleFunction.IsConcaveConvex ℝ` and
  `SaddleFunction.IsSimple ℝ`, together with the Chapter 34 domain owners used inside
  `IsSimple`.
- `bridge/view`: the explicit bifunction itself is already owned upstream by
  `Bifunction.productSignSaddle` in `Text_34_1_3`, so this file should reuse that owner rather
  than redefine it locally.

Primary mathematical domain:
- saddle-functions and simplicity in convex analysis.

Domain-style sampling used here:
- `Bifunction.productSignSaddle` from `Text_34_1_3`;
- `SaddleFunction.IsConcaveConvex` from `Definition33_0_1`;
- `SaddleFunction.IsSimple` from `Defn_34_5`;
- the Chapter 34 slice-domain owners `dom₁`, `dom₂`, and the one-variable effective-domain owner
  `dom`, which already sit behind `IsSimple`.

Primitive data vs derived API:
- primitive source data reused from upstream: `Bifunction.productSignSaddle`;
- derived API: its three branch formulas, the concave-convexity fact, and the failure of
  simplicity.

Layer target: `source-facing`.
-/

-- Proof sketch: unfold `productSignSaddle`; the first branch of the defining `if` is selected
-- directly by the hypothesis `0 < u * v`.
/-- On the region where `uv > 0`, `productSignSaddle` is `+∞`. -/
theorem productSignSaddle_apply_of_mul_pos
    {u v : ℝ} (h : 0 < u * v) :
    productSignSaddle ℝ u v = ⊤ := sorry

-- Proof sketch: unfold `productSignSaddle`; the second branch of the defining `if` is selected
-- because the first inequality fails and the product is exactly zero.
/-- On the zero set of the product, `productSignSaddle` is `0`. -/
theorem productSignSaddle_apply_of_mul_eq_zero
    {u v : ℝ} (h : u * v = 0) :
    productSignSaddle ℝ u v = 0 := sorry

-- Proof sketch: unfold `productSignSaddle`; a negative product rules out the positive and zero
-- branches, leaving the `-∞` branch.
/-- On the region where `uv < 0`, `productSignSaddle` is `-∞`. -/
theorem productSignSaddle_apply_of_mul_neg
    {u v : ℝ} (h : u * v < 0) :
    productSignSaddle ℝ u v = ⊥ := sorry

section

variable [Module ℝ EReal] [PosSMulMono ℝ EReal]

-- Proof sketch: fix one variable and split on the sign of the other. Each row is constant `0`
-- when `u = 0`, identically `+∞` on one open half-line and `-∞` on the other when `u ≠ 0`, and
-- the same description holds symmetrically for columns. These slice descriptions yield concavity
-- in the first variable and convexity in the second variable.
/-- `productSignSaddle` is a concave-convex saddle-function on `ℝ × ℝ`. -/
theorem isConcaveConvex_productSignSaddle :
    IsConcaveConvex ℝ (productSignSaddle ℝ) := sorry

end

-- Proof sketch: compute `dom₁ (productSignSaddle ℝ) = {0}` and
-- `dom₂ (productSignSaddle ℝ) = {0}`.
-- Their relative interiors and closures are therefore both `{0}`. At `u = 0`, however, the slice
-- `productSignSaddle ℝ 0` is identically `0`, so `dom (productSignSaddle ℝ 0) = Set.univ`,
-- which is not contained in `closure (dom₂ (productSignSaddle ℝ)) = {0}`. This violates the first
-- field of
-- `SaddleFunction.IsSimple ℝ (productSignSaddle ℝ)`.
/-- Text 34.4.4: the concave-convex saddle-function `productSignSaddle` on `ℝ × ℝ`, defined by
`K(u, v) = +∞` for `uv > 0`, `K(u, v) = 0` for `uv = 0`, and `K(u, v) = -∞` for `uv < 0`, is
not simple. -/
theorem not_isSimple_productSignSaddle :
    ¬ IsSimple ℝ (productSignSaddle ℝ) := sorry

end SaddleFunction
