import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_1_1_2
import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric
open scoped ConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 6.1 lies in the chapter's Fenchel-conjugacy / dual-norm domain.

Primary domain:
- growth bounds for the continuous-dual effective domain of a Fenchel conjugate.

Sampled owner-style declarations:
- `fenchelConjugate` in `Definition_6_1`, the chapter owner for conjugates on `Module.Dual ℝ E`;
- `fenchelConjugate_apply` in `Definition_6_1`, the owner evaluation theorem;
- `strongFenchelConjugate` in `Definition_6_1`, the continuous-dual bridge owner used in Chapter 6
  normed-space statements;
- `extendedRealEffectiveDomain` / the notation `dom` in `Definition_3_1_1_2`, the chapter owner
  for finite-value domains of `EReal`-valued functions;
- `fenchelDual` in `Chap03/Definition_3_1_2_1`, the nearby bridge/view pattern that specializes
  the same owner surface instead of rebuilding it.

Best owner abstraction:
- `strongFenchelConjugate` together with `dom`.

Primitive data:
- `f : E → ℝ`.

Derived API:
- the closed-ball containment and boundedness consequences for the continuous-dual effective
  domain of `strongFenchelConjugate`.

Source/core/bridge triage:
- source-facing: Proposition 6.1's boundedness statement for the continuous-dual finite-value
  domain of the conjugate of a real-valued function;
- core/canonical: `fenchelConjugate` and `dom`;
- bridge/view: `strongFenchelConjugate`.

This file therefore uses the reusable Chapter 6 bridge owner `strongFenchelConjugate` instead of
repeating a theorem-local `StrongDual` lambda for the continuous-dual restriction of
`fenchelConjugate`. The previous local `convexConjugate` definition duplicated the owner
`fenchelConjugate`, the previous local domain alias duplicated the chapter owner `dom`, and the
previous specialized membership wrapper duplicated `mem_extendedRealEffectiveDomain_iff`; all
three are removed here. The linear-growth conclusion itself does not use convexity,
finite-dimensionality, or a separate `0 ≤ L` witness, so the theorem surface is reduced to the
actual primitive data: a nonnegative radius `L : NNReal` and the growth bound.
-/

/-- Proposition 6.1: if a real-valued function is bounded above by `f 0 + L ‖x‖`, then the
finite-value domain of its Fenchel conjugate on the continuous dual is contained in the closed
dual ball of radius `L`. -/
-- Proof sketch: if `‖s‖ > L`, choose `u` in the unit ball with `s u > L`; then along the ray
-- `t • u` the maximand `s (t • u) - f (t • u)` is bounded below by
-- `t * (s u - L) - f 0`, which diverges to `+∞`, so `s` cannot lie in the finite-value domain.
theorem dom_fenchelConjugate_subset_closedBall_of_upper_linear_growth
    (f : E → ℝ) (L : NNReal) (hgrowth : ∀ x : E, f x ≤ f 0 + (L : ℝ) * ‖x‖) :
    dom (strongFenchelConjugate f) ⊆ closedBall 0 L := sorry

/-- The finite-value domain of the conjugate is bounded under the same upper linear-growth
hypothesis. -/
-- Proof sketch: apply the closed-ball containment theorem and `Metric.isBounded_closedBall`.
theorem dom_fenchelConjugate_bounded_of_upper_linear_growth
    (f : E → ℝ) (L : NNReal) (hgrowth : ∀ x : E, f x ≤ f 0 + (L : ℝ) * ‖x‖) :
    Bornology.IsBounded (dom (strongFenchelConjugate f)) := sorry

end
