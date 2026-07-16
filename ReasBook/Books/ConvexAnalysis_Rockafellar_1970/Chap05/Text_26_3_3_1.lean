import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_3

noncomputable section

universe u

open Metric
open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.3.3.1 concerns the powered distance-to-set function `x ↦ d(x, C)^p`.
  For calculus this is the finite real branch `x ↦ (d(x, C)).toReal ^ p`.
- `core/canonical`: the real-valued owner is `Metric.infDist`, while the chapter notation
  `d(x, C)` is the `EReal`-valued bridge coming from `Metric.infEDist`.
- `bridge/view`: the source-facing chapter notation is related to the canonical owner by
  `distanceToSet_toReal_eq_infDist`.

Domain-style sampling used here:
- `Metric.infDist` and `Metric.infDist_closure` from mathlib;
- `distanceToSet_toReal_eq_infDist` and `distanceToSet_eq_infDist` from
  `Chap01.Defintion_4_8_3`;
- `distanceToSet_isConvex` from `Chap01.Text_5_4_1_5`;
- `ConvexOn.rpow_of_one_lt` from `Chap01.Text_5_1_2`;
- `Function.continuous_gradient_realBranch_on_open_convex` from `Chap05.Corollary_25_5_1` for
  the finite-dimensional `C¹` upgrade.

Primitive data vs derived API:
- primitive data: the set `C`, the exponent `p`, and the owner `fun x ↦ infDist x C ^ p`;
- derived API: the metric bridge to `d(x, C)`, the global convexity/differentiability theorem,
  the finite-dimensional `ContDiff ℝ 1` upgrade, and the source-facing restatements.

Layer target:
- `infDist_rpow_convexOn_univ_and_differentiable` and its `d(x, C)` restatement:
  Hilbert-space `core/canonical` plus `bridge/view`;
- `infDist_rpow_contDiff` and its `d(x, C)` restatement: stronger finite-dimensional corollaries.
-/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: the nonempty closed convex case is the source argument from Chapter 26. For an
-- arbitrary convex set, pass to `closure C`: convexity is preserved by closure and
-- `infDist x (closure C) = infDist x C`, so the canonical real-valued owner is unchanged while
-- the closedness hypothesis disappears. The empty-set case is then the constant-zero function at
-- the core `infDist` layer. The source-facing chapter notation is recovered through the global
-- finite-branch bridge `(d(x, C)).toReal = infDist x C`, so no separate nonemptiness hypothesis
-- remains on the public real-valued theorem surface.
/-- Canonical real-valued Hilbert-space owner form of Text 26.3.3.1: for a convex set `C` and
`1 < p`, the function `x ↦ infDist x C ^ p` is convex on the whole space and differentiable
everywhere. -/
theorem infDist_rpow_convexOn_univ_and_differentiable
    {C : Set E} (hC_convex : Convex ℝ C) {p : ℝ} (hp : 1 < p) :
    ConvexOn ℝ Set.univ (fun x ↦ infDist x C ^ p) ∧
      Differentiable ℝ (fun x ↦ infDist x C ^ p) := sorry

/-- Source-facing real-branch restatement of Text 26.3.3.1: for a convex set `C` and `1 < p`, the
function `x ↦ (d(x, C)).toReal ^ p` is convex on the whole space and differentiable
everywhere. -/
theorem distanceToSet_toReal_rpow_convexOn_univ_and_differentiable
    {C : Set E} (hC_convex : Convex ℝ C) {p : ℝ} (hp : 1 < p) :
    ConvexOn ℝ Set.univ (fun x ↦ (d(x, C)).toReal ^ p) ∧
      Differentiable ℝ (fun x ↦ (d(x, C)).toReal ^ p) := by
  have hdist :
      (fun x ↦ (d(x, C)).toReal ^ p) = fun x ↦ infDist x C ^ p := by
    funext x
    rw [distanceToSet_toReal_eq_infDist]
  simpa [hdist] using infDist_rpow_convexOn_univ_and_differentiable hC_convex hp

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: the Hilbert-space theorem above gives convexity together with everywhere
-- differentiability on the open set `univ`. Corollary 25.5.1 upgrades a convex real-valued
-- function differentiable on an open set to `C¹` there, so applying it to
-- `fun x ↦ infDist x C ^ p` on `univ` yields the finite-dimensional claim.
/-- In the finite-dimensional inner-product setting, the powered real-valued distance-to-set owner
is continuously differentiable when `1 < p`. -/
theorem infDist_rpow_contDiff
    {C : Set E} (hC_convex : Convex ℝ C) {p : ℝ} (hp : 1 < p) :
    ContDiff ℝ 1 (fun x ↦ infDist x C ^ p) := sorry

/-- Source-facing `C¹` restatement on the finite real branch of the chapter distance notation for a
convex set. -/
theorem distanceToSet_toReal_rpow_contDiff
    {C : Set E} (hC_convex : Convex ℝ C) {p : ℝ} (hp : 1 < p) :
    ContDiff ℝ 1 (fun x ↦ (d(x, C)).toReal ^ p) := by
  have hdist :
      (fun x ↦ (d(x, C)).toReal ^ p) = fun x ↦ infDist x C ^ p := by
    funext x
    rw [distanceToSet_toReal_eq_infDist]
  simpa [hdist] using infDist_rpow_contDiff hC_convex hp

end
