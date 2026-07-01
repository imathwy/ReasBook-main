import Nesterov.Chap06.Definition_6_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Theorem 6.1 lies in the chapter's prox-smoothed maximization domain.

Sampled owner-style declarations:
- `smoothedPrimalObjective` in `Definition_6_30`, the chapter owner of the regularized-max
  smoothing formula;
- `smoothedPrimalObjectiveArgmax` in `Definition_6_30`, the canonical argmax-set owner for the
  textbook maximizer `u_μ(x)`;
- `smoothedPrimalObjective_apply` in `Definition_6_30`, the source-facing supremum formula for the
  smoothed objective;
- `smoothed_maximizer_unique` in `Proposition_6_6`, the chapter uniqueness theorem showing that
  convexity of `phiHat` together with strong convexity of `d2` is the actual structural input for
  uniqueness of the maximizer.

Best owner abstraction:
- source-facing: the prox-smoothed objective `smoothedPrimalObjective A Q 0 phiHat d2 μ` and its
  differentiability properties;
- core/canonical: `smoothedPrimalObjective` together with the pointwise argmax owner
  `smoothedPrimalObjectiveArgmax`;
- bridge/view: a choice `uMu : E₁ → E₂` recorded only through the membership hypothesis
  `uMu x ∈ smoothedPrimalObjectiveArgmax ... x`, used only when the selected maximizer itself
  appears in the conclusion.

Primitive data:
- the linear map `A`, feasible set `Q`, nonsmooth term `phiHat`, prox term `d2`, and smoothing
  parameter `μ`;
- existence of points in the canonical argmax set;
- when needed for derivative-identification statements, a pointwise choice `uMu` of elements of the
  canonical argmax set.

Derived API:
- evaluation of the smoothed supremum at an argmax point;
- convexity and continuous differentiability of the smoothed objective from canonical argmax
  existence;
- derivative identification and Lipschitz control from a chosen argmax selection.

Source/core/bridge triage:
- source-facing: Theorem 6.1's four properties of the prox-smoothed objective;
- core/canonical: `smoothedPrimalObjective` and `smoothedPrimalObjectiveArgmax`;
- bridge/view: a selected map `uMu` into the argmax set.

The previous version introduced a parallel public predicate
`IsSmoothedObjectiveMaximizerSelection` and carried stronger ambient hypotheses than the owner
surface needs. This file now uses the canonical argmax owner directly and keeps only the convexity
and strong-convexity hypotheses that match the uniqueness/smoothness mechanism. -/

/-- Any point of `smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x` realizes the supremum defining
the smoothed objective at `x`. -/
-- Proof sketch: the argmax property makes `u` an upper bound for the image of the penalized
-- maximand on `Q`, and evaluating at `u` gives the matching lower bound.
theorem smoothedPrimalObjectiveArgmax.value_eq
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {Q : Set E₂} {phiHat d2 : E₂ → ℝ} {μ : ℝ}
    {x : E₁} {u : E₂}
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x) :
    smoothedPrimalObjective A Q 0 phiHat d2 μ x =
      smoothedPrimalObjectiveMaximand A phiHat d2 μ x u := sorry

/-- Theorem 6.1 (1): the prox-smoothed dual supremum is convex on all of `E₁`. -/
-- Proof sketch: each map `x ↦ A x u - phiHat u - μ * d2 u` is affine in `x`, so the supremum
-- over `u ∈ Q` is convex.
theorem smoothedObjective_convex
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q : Set E₂) (phiHat d2 : E₂ → ℝ) (μ : ℝ) :
    ConvexOn ℝ Set.univ (smoothedPrimalObjective A Q 0 phiHat d2 μ) := sorry

/-
Theorem 6.1 splits into four atomic declarations: if `phiHat` is convex on `Q`, `d2` is `C¹` and
`1`-strongly convex on `Q`, and the canonical argmax set is nonempty at each `x`, then the
smoothed objective is convex and continuously differentiable. When a selected maximizer
`uMu x ∈ smoothedPrimalObjectiveArgmax ... x` is also fixed, the derivative is `A.flip (uMu x)` at
each `x`, and this derivative map is Lipschitz with constant `(1 / μ) * ‖A‖^2`.
-/
section Theorem61

variable
  (A : E₁ →L[ℝ] StrongDual ℝ E₂)
  (Q : Set E₂) (phiHat d2 : E₂ → ℝ) {μ : ℝ}
  (uMu : E₁ → E₂)

/-- Theorem 6.1 (2): under the smoothing hypotheses, the smoothed objective is continuously
differentiable. -/
-- Proof sketch: apply Danskin's theorem to the supremum formula, using convexity of `phiHat`,
-- strong convexity of `d2`, and the nonemptiness of the canonical argmax set to obtain the unique
-- maximizer at each `x`.
theorem smoothedObjective_contDiff
    (hphi : ConvexOn ℝ Q phiHat)
    (hd2_contDiff : ContDiffOn ℝ 1 d2 Q)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (hargmax : ∀ x, (smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x).Nonempty) :
    ContDiff ℝ 1 (smoothedPrimalObjective A Q 0 phiHat d2 μ) := sorry

/-- Theorem 6.1 (3): under the smoothing hypotheses, the derivative of the smoothed objective at
`x` is `A.flip (uMu x)`. -/
-- Proof sketch: combine the unique-maximizer form of Danskin's theorem with the canonical pairing
-- identity `(A.flip u) x = A x u`.
theorem smoothedObjective_hasFDerivAt
    (hphi : ConvexOn ℝ Q phiHat)
    (hd2_contDiff : ContDiffOn ℝ 1 d2 Q)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (huMu : ∀ y, uMu y ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ y)
    (x : E₁) :
    HasFDerivAt (smoothedPrimalObjective A Q 0 phiHat d2 μ) (A.flip (uMu x)) x := sorry

/-- Theorem 6.1 (4): under the smoothing hypotheses, the derivative selection
`x ↦ A.flip (uMu x)` is Lipschitz with constant `(1 / μ) * ‖A‖^2`. -/
-- Proof sketch: compare the optimality conditions at two points, use monotonicity of the convex
-- part together with convexity of `phiHat` and the `1`-strong convexity of `d2`, and bound the
-- adjoint difference by
-- `‖A‖^2 / μ`.
theorem smoothedObjective_gradient_lipschitz
    (hphi : ConvexOn ℝ Q phiHat)
    (hd2_strong : StrongConvexOn Q 1 d2)
    (hμ : 0 < μ)
    (huMu : ∀ x, uMu x ∈ smoothedPrimalObjectiveArgmax A Q phiHat d2 μ x) :
    LipschitzWith (Real.toNNReal ((1 / μ) * ‖A‖ ^ (2 : ℕ))) (fun x ↦ A.flip (uMu x)) := sorry

end Theorem61

end
