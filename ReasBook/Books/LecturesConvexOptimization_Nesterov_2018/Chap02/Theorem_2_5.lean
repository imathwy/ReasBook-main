import LecturesConvexOptimization_Nesterov_2018.Chap02.Definition_2_4
import LecturesConvexOptimization_Nesterov_2018.Chap02.Definition_2_5
import LecturesConvexOptimization_Nesterov_2018.Chap02.Lemma_2_3
import LecturesConvexOptimization_Nesterov_2018.Chap02.Proposition_2_1
import LecturesConvexOptimization_Nesterov_2018.Chap02.Theorem_2_3
import LecturesConvexOptimization_Nesterov_2018.Chap01.Proposition_1_5_9
import LecturesConvexOptimization_Nesterov_2018.Chap01.Theorem_1_4_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open AffineMap
open scoped ConvexC1 Gradient SeminormDualNorm

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]
variable {p : Seminorm ℝ E} [Seminorm.IsNorm p] {L : NNReal}
variable {Q : Set E} {f : E → ℝ}

/- Primary domain: first-order smooth convex analysis on real Hilbert spaces with an arbitrary
norm-like seminorm.

Sampled owner-style declarations:
* `ConvexC1On` in `Definition_2_4`
* mathlib `HasGradientAt`
* mathlib `gradient`
* `convexC1On_iff_gradient_monotone` in `Theorem_2_3`
* `Seminorm.dualNorm` in `Definition_2_5`
* `Seminorm.dualNorm_normSeminorm_eq_norm` in `Lemma_2_3`

Source/core/bridge triage:
* source-facing: `ConvexC1SeminormSmoothOn p L Q f`
* core/canonical: `ConvexC1On Q f` together with actual ambient-gradient data
  `HasGradientAt f (∇ f x) x` on `Q` and the dual-norm Lipschitz inequality for `∇ f`
* bridge/view: the whole-space specialization `ConvexC1SeminormSmooth p L f` and, for
  `p = normSeminorm ℝ E`, the metric reformulation `ConvexC1SeminormSmooth.gradient_lipschitz`

Primitive data:
* the set `Q`
* the function `f`
* the owner predicate `ConvexC1On Q f`
* the ambient gradient witnesses `HasGradientAt f (∇ f x) x` on `Q`
* the dual-norm Lipschitz bound for `∇ f` on `Q`

Derived API:
* owner projections to `ContDiffOn` and `ConvexOn`
* the whole-space owner view with ambient gradient `∇ f`
* the ambient-norm `LipschitzWith` reformulation for `p = normSeminorm ℝ E`
-/

/-- A function belongs to the smooth-convex class `𝓕_L^{1,1}(Q, ‖·‖)` when it is `C¹` convex on
`Q`, its ambient gradient is defined at every feasible point, and that ambient gradient is
`L`-Lipschitz on `Q` with respect to the seminorm `p` and the dual seminorm `‖·‖[p,*]`. This
keeps the arbitrary-set API faithful to the textbook gradient inequalities instead of relying on
the total fallback behavior of `gradientWithin`. -/
abbrev ConvexC1SeminormSmoothOn
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (Q : Set E) (f : E → ℝ) : Prop :=
  ConvexC1On Q f ∧
    (∀ ⦃x⦄, x ∈ Q → HasGradientAt f (∇ f x) x) ∧
    ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
      ‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y)

scoped[SmoothConvex] notation "𝓕[" L ", " p "]¹¹(" Q ")" =>
  setOf (ConvexC1SeminormSmoothOn p L Q)

open scoped SmoothConvex

/-- Membership in `𝓕[L, p]¹¹(Q)` includes the owner `C¹` convexity data on `Q`. -/
theorem ConvexC1SeminormSmoothOn.convexC1On
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    ConvexC1On Q f :=
  hf.1

/-- Membership in `𝓕[L, p]¹¹(Q)` includes `C¹` regularity on `Q`. -/
theorem ConvexC1SeminormSmoothOn.contDiffOn
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    ContDiffOn ℝ 1 f Q :=
  convexC1On_contDiffOn hf.1

/-- Membership in `𝓕[L, p]¹¹(Q)` includes the ambient gradient witness at every feasible point. -/
theorem ConvexC1SeminormSmoothOn.hasGradientAt
    (hf : ConvexC1SeminormSmoothOn p L Q f)
    {x : E} (hx : x ∈ Q) :
    HasGradientAt f (∇ f x) x :=
  hf.2.1 hx

/-- Membership in `𝓕[L, p]¹¹(Q)` includes convexity on `Q`. -/
theorem ConvexC1SeminormSmoothOn.convexOn
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    ConvexOn ℝ Q f :=
  convexC1On_convexOn hf.1

/-- Membership in `𝓕[L, p]¹¹(Q)` forces the feasible set `Q` itself to be convex. -/
theorem ConvexC1SeminormSmoothOn.convex
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    Convex ℝ Q :=
  hf.convexOn.1

/-- The whole-space class `𝓕_L^{1,1}(E, ‖·‖)` is the ambient-gradient view of the set-based owner
`ConvexC1SeminormSmoothOn`. The textbook Euclidean class is the finite-dimensional
specialization. -/
abbrev ConvexC1SeminormSmooth
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (f : E → ℝ) : Prop :=
  ConvexC1SeminormSmoothOn p L Set.univ f

scoped[SmoothConvex] notation "𝓕[" L ", " p "]¹¹" =>
  setOf (ConvexC1SeminormSmooth p L)

/-- The set-based notation `𝓕[L, p]¹¹(Q)` is the source-facing set view of the owner predicate
`ConvexC1SeminormSmoothOn p L Q`. -/
theorem mem_F11On_iff : f ∈ 𝓕[L, p]¹¹(Q) ↔ ConvexC1SeminormSmoothOn p L Q f :=
  Iff.rfl

/-- The whole-space notation `𝓕[L, p]¹¹` is the source-facing set view of the owner predicate
`ConvexC1SeminormSmooth p L`. -/
theorem mem_F11_iff : f ∈ 𝓕[L, p]¹¹ ↔ ConvexC1SeminormSmooth p L f :=
  Iff.rfl

/-- Membership in `𝓕[L, p]¹¹` retains the whole-space `ConvexC1On` owner predicate. -/
theorem ConvexC1SeminormSmooth.convexC1On
    (hf : ConvexC1SeminormSmooth p L f) :
    ConvexC1On Set.univ f :=
  hf.1

/-- Membership in `𝓕[L, p]¹¹` includes global `C¹` regularity. -/
theorem ConvexC1SeminormSmooth.contDiff
    (hf : ConvexC1SeminormSmooth p L f) :
    ContDiff ℝ 1 f :=
  contDiffOn_univ.mp (convexC1On_contDiffOn hf.1)

/-- Membership in `𝓕[L, p]¹¹` includes the canonical ambient gradient at every point. -/
theorem ConvexC1SeminormSmooth.hasGradientAt
    (hf : ConvexC1SeminormSmooth p L f) (x : E) :
    HasGradientAt f (∇ f x) x :=
  hf.2.1 (by simp)

/-- Membership in `𝓕[L, p]¹¹` includes whole-space convexity. -/
theorem ConvexC1SeminormSmooth.convexOn
    (hf : ConvexC1SeminormSmooth p L f) :
    ConvexOn ℝ Set.univ f :=
  convexC1On_convexOn hf.1

/-- Membership in `𝓕[L, p]¹¹` gives the defining dual-norm Lipschitz bound for the ambient
gradient on the whole space. -/
theorem ConvexC1SeminormSmooth.dualNorm_gradient_sub_le
    (hf : ConvexC1SeminormSmooth p L f)
    (x y : E) :
    ‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y) :=
  hf.2.2 (by simp) (by simp)

/-- For the ambient norm seminorm, membership in `𝓕[L, normSeminorm ℝ E]¹¹` makes the gradient
`L`-Lipschitz in the ordinary norm. -/
theorem ConvexC1SeminormSmooth.gradient_lipschitz
    (hf : ConvexC1SeminormSmooth (normSeminorm ℝ E) L f) :
    LipschitzWith L (∇ f) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  simpa [dist_eq_norm, Seminorm.dualNorm_normSeminorm_eq_norm] using
    hf.dualNorm_gradient_sub_le x y

/-- A global minimizer of a smooth convex objective carries the canonical stationary-point witness
`HasGradientAt f 0 xStar`. -/
theorem ConvexC1SeminormSmooth.hasGradientAt_zero_of_isMinOn
    (hf : ConvexC1SeminormSmooth (normSeminorm ℝ E) L f)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar) :
    HasGradientAt f 0 xStar :=
  isMinOn_hasGradientAt_zero_of_differentiableAt (hf.contDiff.differentiable_one xStar) hxStar

/-- Every global minimizer of a smooth convex objective in `𝓕[L, normSeminorm ℝ E]¹¹` is
stationary. -/
theorem ConvexC1SeminormSmooth.gradient_eq_zero_of_isMinOn
    (hf : ConvexC1SeminormSmooth (normSeminorm ℝ E) L f)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar) :
    ∇ f xStar = 0 := by
  exact (hf.hasGradientAt_zero_of_isMinOn hxStar).gradient

/-- Membership in `𝓕[L, p]¹¹(Q)` gives the defining dual-norm Lipschitz bound for the ambient
gradient on `Q`. -/
-- Proof sketch: unfold `ConvexC1SeminormSmoothOn` and project to the gradient-Lipschitz clause.
theorem ConvexC1SeminormSmoothOn.dualNorm_gradient_sub_le
    (hf : ConvexC1SeminormSmoothOn p L Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    ‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y) :=
  hf.2.2 hx hy

/-- The whole-space view `𝓕[L, p]¹¹` is the `Q = Set.univ` specialization of the set-based owner
`𝓕[L, p]¹¹(Q)`. -/
theorem ConvexC1SeminormSmooth.toOn
    (hf : ConvexC1SeminormSmooth p L f) :
    ConvexC1SeminormSmoothOn p L Set.univ f :=
  hf

section TangentErrorBoundsOn

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : Seminorm ℝ E} {L : NNReal} {g : E → E} {Q : Set E} {f : E → ℝ}

/-- The condition `(2.1.9)` on a set `Q`: the tangent-plane error of `f` is nonnegative and at
most `(L / 2) ‖x - y‖²` with respect to the seminorm `p`, measured with an explicit gradient field
`g` on `Q`.
-/
def smoothConvexTangentErrorBoundsOn
    (p : Seminorm ℝ E) (L : NNReal) (g : E → E) (Q : Set E) (f : E → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
    0 ≤ f y - f x - inner ℝ (g x) (y - x) ∧
      f y - f x - inner ℝ (g x) (y - x) ≤
        ((L : ℝ) / 2) * (p (x - y)) ^ 2

/-- Membership in `(2.1.9)` gives the nonnegativity half of the tangent error bound. -/
theorem smoothConvexTangentErrorBoundsOn.nonneg
    (hf : smoothConvexTangentErrorBoundsOn p L g Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    0 ≤ f y - f x - inner ℝ (g x) (y - x) :=
  (hf hx hy).1

/-- Membership in `(2.1.9)` gives the quadratic upper bound for the tangent error. -/
theorem smoothConvexTangentErrorBoundsOn.upperBound
    (hf : smoothConvexTangentErrorBoundsOn p L g Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y - f x - inner ℝ (g x) (y - x) ≤
      ((L : ℝ) / 2) * (p (x - y)) ^ 2 :=
  (hf hx hy).2

end TangentErrorBoundsOn

/-- The condition `(2.1.10)` on a set `Q`: the value at `y` dominates the tangent model at `x`
plus the squared dual norm of the gradient-field difference. The separate positivity
assumption `0 < L` belongs to the surrounding theorem hypotheses, not to this displayed
inequality itself. -/
def smoothConvexGradientQuadraticLowerBoundOn
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (g : E → E) (Q : Set E)
    (f : E → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
    f x + inner ℝ (g x) (y - x) +
        (1 / (2 * (L : ℝ))) *
          (‖g x - g y‖[p,*]) ^ 2 ≤
      f y

/-- The condition `(2.1.11)` on a set `Q`: the gradient field `g` is `1 / L`-cocoercive with
respect to the seminorm `p` and its dual norm. The separate positivity assumption `0 < L` belongs
to the surrounding theorem hypotheses, not to this displayed inequality itself. -/
def smoothConvexCocoerciveGradientOn
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (g : E → E) (Q : Set E) : Prop :=
  ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
    (1 / (L : ℝ)) * (‖g x - g y‖[p,*]) ^ 2 ≤
      inner ℝ (g x - g y) (x - y)

section MonotoneGradientBoundsOn

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : Seminorm ℝ E} {L : NNReal} {g : E → E} {Q : Set E}

/-- The condition `(2.1.12)` on a set `Q`: the gradient field `g` is monotone and the
monotonicity pairing is bounded above by `L ‖x - y‖²` with respect to `p`. -/
def smoothConvexMonotoneGradientBoundsOn
    (p : Seminorm ℝ E) (L : NNReal) (g : E → E) (Q : Set E) : Prop :=
  (∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q → 0 ≤ inner ℝ (g x - g y) (x - y)) ∧
    ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
      inner ℝ (g x - g y) (x - y) ≤
        (L : ℝ) * (p (x - y)) ^ 2

/-- Membership in `(2.1.12)` recovers the monotonicity half of the gradient-field bound. -/
theorem smoothConvexMonotoneGradientBoundsOn.monotone
    (hf : smoothConvexMonotoneGradientBoundsOn p L g Q) :
    ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q → 0 ≤ inner ℝ (g x - g y) (x - y) :=
  hf.1

/-- Membership in `(2.1.12)` gives the upper quadratic bound for the monotonicity pairing. -/
theorem smoothConvexMonotoneGradientBoundsOn.upperBound
    (hf : smoothConvexMonotoneGradientBoundsOn p L g Q) :
    ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
      inner ℝ (g x - g y) (x - y) ≤
        (L : ℝ) * (p (x - y)) ^ 2 :=
  hf.2

end MonotoneGradientBoundsOn

/-- The condition `(2.1.13)` on a set `Q`: every convex combination of two values of `f`
dominates the value at the convex-combination point by a term involving the squared dual norm of
the gradient-field difference. The separate positivity assumption `0 < L` belongs to the
surrounding theorem hypotheses, not to this displayed inequality itself. -/
def smoothConvexConvexCombinationGradientBoundOn
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (g : E → E) (Q : Set E)
    (f : E → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Icc (0 : ℝ) 1 →
    α * f x + (1 - α) * f y ≥
      f (α • x + (1 - α) • y) +
        (α * (1 - α) / (2 * (L : ℝ))) *
          (‖g x - g y‖[p,*]) ^ 2

section ConvexCombinationQuadraticBoundOn

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {p : Seminorm ℝ E} {L : NNReal} {Q : Set E} {f : E → ℝ}

/-- The condition `(2.1.14)` on a set `Q`: the Jensen gap of `f` is nonnegative and at most
`α (1 - α) (L / 2) ‖x - y‖²` with respect to `p`. -/
def smoothConvexConvexCombinationQuadraticBoundOn
    (p : Seminorm ℝ E) (L : NNReal) (Q : Set E) (f : E → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Icc (0 : ℝ) 1 →
    0 ≤ α * f x + (1 - α) * f y - f (α • x + (1 - α) • y) ∧
      α * f x + (1 - α) * f y - f (α • x + (1 - α) • y) ≤
        α * (1 - α) * ((L : ℝ) / 2) * (p (x - y)) ^ 2

/-- Membership in `(2.1.14)` gives the nonnegativity of the Jensen gap. -/
theorem smoothConvexConvexCombinationQuadraticBoundOn.nonneg
    (hf : smoothConvexConvexCombinationQuadraticBoundOn p L Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ α * f x + (1 - α) * f y - f (α • x + (1 - α) • y) :=
  (hf hx hy hα).1

/-- Membership in `(2.1.14)` gives the quadratic upper bound for the Jensen gap. -/
theorem smoothConvexConvexCombinationQuadraticBoundOn.upperBound
    (hf : smoothConvexConvexCombinationQuadraticBoundOn p L Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    α * f x + (1 - α) * f y - f (α • x + (1 - α) • y) ≤
      α * (1 - α) * ((L : ℝ) / 2) * (p (x - y)) ^ 2 :=
  (hf hx hy hα).2

end ConvexCombinationQuadraticBoundOn

/-- Helper for Theorem 2.5: along a feasible segment, the corrected first-order remainder has
derivative given by the gradient increment paired with the segment direction. -/
private lemma segment_corrected_remainder_hasDerivAt
    (hf : ConvexC1SeminormSmoothOn p L Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun u : ℝ ↦ f (x + u • (y - x)) - f x - u * inner ℝ (∇ f x) (y - x))
      (inner ℝ (∇ f (x + t • (y - x)) - ∇ f x) (y - x)) t := by
  -- Route correction: differentiate the segment remainder directly from the ambient
  -- `HasGradientAt` witnesses along the feasible line segment.
  have hseg_mem : x + t • (y - x) ∈ Q := by
    simpa [AffineMap.lineMap_apply, add_comm, add_left_comm, add_assoc] using
      hf.convex.mapsTo_lineMap hx hy ⟨ht.1.le, ht.2.le⟩
  have hdiff : DifferentiableAt ℝ f (x + t • (y - x)) :=
    (hf.hasGradientAt hseg_mem).differentiableAt
  have hseg :
      HasDerivAt (fun u : ℝ ↦ f (x + u • (y - x)))
        ((fderiv ℝ f (x + t • (y - x))) (y - x)) t := by
    have hline : HasDerivAt (fun u : ℝ ↦ x + u • (y - x)) (y - x) t := by
      simpa [one_smul] using (((hasDerivAt_id t).smul_const (y - x)).const_add x)
    simpa [Function.comp] using (hdiff.hasFDerivAt.comp t hline.hasFDerivAt).hasDerivAt
  have hlin :
      HasDerivAt (fun u : ℝ ↦ u * inner ℝ (∇ f x) (y - x))
        (inner ℝ (∇ f x) (y - x)) t := by
    simpa [one_mul] using (hasDerivAt_id t).mul_const (inner ℝ (∇ f x) (y - x))
  have hmain :
      HasDerivAt
        (fun u : ℝ ↦ f (x + u • (y - x)) - f x - u * inner ℝ (∇ f x) (y - x))
        (((fderiv ℝ f (x + t • (y - x))) (y - x)) - inner ℝ (∇ f x) (y - x)) t := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hseg.sub ((hasDerivAt_const t (f x)).add hlin)
  -- Rewrite the Fréchet derivative through the canonical gradient pairing.
  convert hmain using 1
  rw [inner_sub_left]
  rw [inner_gradient_left (y := y - x) hdiff]

/-- Helper for Theorem 2.5: the tangent error on a feasible segment is bounded above by the
quadratic seminorm term obtained by integrating the gradient increment bound. -/
private lemma tangent_error_upperBound
    (hf : ConvexC1SeminormSmoothOn p L Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y - f x - inner ℝ (∇ f x) (y - x) ≤
      ((L : ℝ) / 2) * (p (x - y)) ^ 2 := by
  let d : E := y - x
  have hmaps : Set.MapsTo (fun t : ℝ ↦ x + t • d) (Set.Icc (0 : ℝ) 1) Q := by
    intro t ht
    simpa [d, AffineMap.lineMap_apply, add_comm, add_left_comm, add_assoc] using
      hf.convex.mapsTo_lineMap hx hy ht
  -- The corrected segment remainder is continuous on `[0, 1]`.
  have hcont :
      ContinuousOn (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d)
        (Set.Icc (0 : ℝ) 1) := by
    have hsegCont :
        ContinuousOn (fun t : ℝ ↦ f (x + t • d)) (Set.Icc (0 : ℝ) 1) :=
      hf.contDiffOn.continuousOn.comp (by fun_prop) hmaps
    have hlinCont : Continuous (fun t : ℝ ↦ t * inner ℝ (∇ f x) d) := by
      fun_prop
    exact ((hsegCont.sub continuousOn_const).sub hlinCont.continuousOn)
  -- The derivative formula from the previous helper gives differentiability on `(0, 1)`.
  have hdiff :
      DifferentiableOn ℝ (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d)
        (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    exact (segment_corrected_remainder_hasDerivAt (hf := hf) hx hy ht).differentiableAt
      |>.differentiableWithinAt
  -- Control the scalar derivative by dual Cauchy and the defining dual-norm Lipschitz estimate.
  have hbound :=
    norm_sub_le_integral_of_norm_deriv_le_of_le
      (f := fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d)
      (B := fun t : ℝ ↦ (L : ℝ) * t * (p d) ^ (2 : ℕ))
      (a := (0 : ℝ)) (b := 1)
      (by norm_num) hcont hdiff
      (Filter.Eventually.of_forall fun t ht ↦ by
        have hderivAt := segment_corrected_remainder_hasDerivAt (hf := hf) hx hy ht
        rw [hderivAt.deriv]
        have hseg_mem : x + t • d ∈ Q := hmaps ⟨ht.1.le, ht.2.le⟩
        have hinner_abs :
            |inner ℝ (∇ f (x + t • d) - ∇ f x) d| ≤
              ‖∇ f (x + t • d) - ∇ f x‖[p,*] * p d := by
          refine abs_le.2 ?_
          constructor
          · have hneg :=
              Seminorm.inner_le_dualNorm_mul p (-d) (∇ f (x + t • d) - ∇ f x)
            have hneg' :
                -(inner ℝ (∇ f (x + t • d) - ∇ f x) d) ≤
                  ‖∇ f (x + t • d) - ∇ f x‖[p,*] * p d := by
              simpa [inner_neg_right] using hneg
            linarith
          · exact Seminorm.inner_le_dualNorm_mul p d (∇ f (x + t • d) - ∇ f x)
        have hgrad_bound :
            ‖∇ f (x + t • d) - ∇ f x‖[p,*] ≤
              (L : ℝ) * p ((x + t • d) - x) :=
          hf.dualNorm_gradient_sub_le hseg_mem hx
        have hseg_norm : p ((x + t • d) - x) = t * p d := by
          calc
            p ((x + t • d) - x) = p (t • d) := by simp
            _ = |t| * p d := by
                  simpa [Real.norm_eq_abs] using (map_smul_eq_mul p t d)
            _ = t * p d := by rw [abs_of_pos ht.1]
        calc
          |inner ℝ (∇ f (x + t • d) - ∇ f x) d| ≤
              ‖∇ f (x + t • d) - ∇ f x‖[p,*] * p d := hinner_abs
          _ ≤ ((L : ℝ) * p ((x + t • d) - x)) * p d := by
                exact mul_le_mul_of_nonneg_right hgrad_bound (apply_nonneg p d)
          _ = ((L : ℝ) * (t * p d)) * p d := by rw [hseg_norm]
          _ = (L : ℝ) * t * (p d) ^ (2 : ℕ) := by ring)
      (by
        have hint : IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 :=
          Continuous.intervalIntegrable continuous_id 0 1
        simpa [mul_assoc] using hint.const_mul ((L : ℝ) * (p d) ^ (2 : ℕ)))
  have hR0 :
      (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d) 0 = 0 := by
    simp [d]
  have hR1 :
      (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d) 1 =
        f y - f x - inner ℝ (∇ f x) (y - x) := by
    simp [d]
  have habs :
      |f y - f x - inner ℝ (∇ f x) (y - x)| ≤
        ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
    rw [hR1, hR0, sub_zero, Real.norm_eq_abs] at hbound
    calc
      |f y - f x - inner ℝ (∇ f x) (y - x)| ≤
          ∫ t in (0 : ℝ)..1, (L : ℝ) * t * (p d) ^ (2 : ℕ) := hbound
      _ = ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
            calc
              ∫ t in (0 : ℝ)..1, (L : ℝ) * t * (p d) ^ (2 : ℕ) =
                  ∫ t in (0 : ℝ)..1, ((L : ℝ) * (p d) ^ (2 : ℕ)) * t := by
                    congr with t
                    ring
              _ = ((L : ℝ) * (p d) ^ (2 : ℕ)) * ∫ t in (0 : ℝ)..1, t := by
                    rw [intervalIntegral.integral_const_mul]
              _ = ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
                    rw [integral_id]
                    norm_num
                    ring
  -- Extract the needed upper inequality from the absolute remainder bound.
  have hupper : f y - f x - inner ℝ (∇ f x) (y - x) ≤ ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) :=
    (abs_le.mp habs).2
  have hp : p d = p (x - y) := by
    simpa [d, neg_sub] using (map_neg_eq_map p (x - y))
  have hp_sym : (p d) ^ (2 : ℕ) = (p (x - y)) ^ (2 : ℕ) := by
    rw [hp]
  calc
    f y - f x - inner ℝ (∇ f x) (y - x) ≤ ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := hupper
    _ = ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := by rw [hp_sym]

/-- Helper for Theorem 2.5: every separated seminorm on the finite-dimensional ambient Hilbert
space is bounded above by a positive multiple of the ambient norm. -/
private lemma seminorm_le_mul_norm
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] :
    ∃ C > 0, ∀ x : E, p x ≤ C * ‖x‖ := by
  let b := Module.finBasis ℝ E
  let C : ℝ :=
    (∑ i, ‖((b.coord i).toContinuousLinearMap)‖ * p (b i)) + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro x
  have hx : x = ∑ i, (b.repr x i) • b i := by
    exact (b.sum_repr x).symm
  have hsum :
      p (∑ i, (b.repr x i) • b i) ≤
        ∑ i, p ((b.repr x i) • b i) := by
    exact
      Finset.le_sum_of_subadditive p (by simp) (map_add_le_add p) Finset.univ
        (fun i ↦ (b.repr x i) • b i)
  calc
    p x = p (∑ i, (b.repr x i) • b i) := congrArg p hx
    _ ≤ ∑ i, p ((b.repr x i) • b i) := by
      simpa using hsum
    _ = ∑ i, |b.repr x i| * p (b i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      simpa [Real.norm_eq_abs] using
        (map_smul_eq_mul p (b.repr x i) (b i))
    _ ≤ ∑ i, (‖((b.coord i).toContinuousLinearMap)‖ * p (b i)) * ‖x‖ := by
      exact Finset.sum_le_sum fun i _ ↦ by
        have hcoeff :
            |b.repr x i| ≤ ‖((b.coord i).toContinuousLinearMap)‖ * ‖x‖ := by
          simpa [Real.norm_eq_abs] using
            ((b.coord i).toContinuousLinearMap.le_opNorm x)
        have hpi_nonneg : 0 ≤ p (b i) := apply_nonneg p (b i)
        calc
          |b.repr x i| * p (b i) ≤
              (‖((b.coord i).toContinuousLinearMap)‖ * ‖x‖) * p (b i) := by
            exact mul_le_mul_of_nonneg_right hcoeff hpi_nonneg
          _ = (‖((b.coord i).toContinuousLinearMap)‖ * p (b i)) * ‖x‖ := by
            ring
    _ ≤ C * ‖x‖ := by
      dsimp [C]
      have hsum_le :
          ∑ i, ‖((b.coord i).toContinuousLinearMap)‖ * p (b i) ≤ C := by
        linarith
      exact le_trans (by rw [← Finset.sum_mul]) (mul_le_mul_of_nonneg_right hsum_le (norm_nonneg _))

/-- Helper for Theorem 2.5: every separated seminorm on the ambient finite-dimensional Hilbert
space is continuous. -/
private lemma seminorm_continuous
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] :
    Continuous p := by
  obtain ⟨C, hC_pos, hC⟩ := seminorm_le_mul_norm (E := E) p
  have hball : p.ball 0 1 ∈ nhds (0 : E) := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) (inv_pos.mpr hC_pos)) ?_
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
    rw [Seminorm.mem_ball_zero]
    calc
      p y ≤ C * ‖y‖ := hC y
      _ < C * C⁻¹ := mul_lt_mul_of_pos_left hy hC_pos
      _ = 1 := by rw [mul_inv_cancel₀ hC_pos.ne']
  exact Seminorm.continuous (r := 1) hball

/-- Helper for Theorem 2.5: the dual norm is attained on the closed primal unit ball. -/
private lemma dualNorm_attained_on_closedBall
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (g : E) :
    ∃ u ∈ p.closedBall 0 1,
      inner ℝ g u = ‖g‖[p,*] ∧
      IsMaxOn (fun v : E ↦ inner ℝ g v) (p.closedBall 0 1) u := by
  obtain ⟨D, hD_pos, hD⟩ := p.exists_norm_le_mul
  have hp_cont : Continuous p := seminorm_continuous (E := E) p
  have hclosed : IsClosed (p.closedBall 0 1) := by
    rw [p.closedBall_zero_eq_preimage_closedBall]
    exact IsClosed.preimage hp_cont Metric.isClosed_closedBall
  have hsubset : p.closedBall 0 1 ⊆ Metric.closedBall (0 : E) D := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hpu : p u ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hu
    calc
      ‖u‖ ≤ D * p u := hD u
      _ ≤ D * 1 := by
        gcongr
      _ = D := by ring
  have hcompact : IsCompact (p.closedBall 0 1) :=
    (isCompact_closedBall (0 : E) D).of_isClosed_subset hclosed hsubset
  have hnonempty : (p.closedBall 0 1).Nonempty := by
    exact ⟨0, by simpa [Seminorm.mem_closedBall_zero]⟩
  have hcont : ContinuousOn (fun v : E ↦ inner ℝ g v) (p.closedBall 0 1) := by
    simpa using (continuous_const.inner continuous_id).continuousOn
  obtain ⟨u, hu, huMax⟩ := hcompact.exists_isMaxOn hnonempty hcont
  have himage_bdd :
      BddAbove ((fun v : E ↦ inner ℝ g v) '' p.closedBall 0 1) :=
    (hcompact.image (continuous_const.inner continuous_id)).bddAbove
  have himage_nonempty :
      ((fun v : E ↦ inner ℝ g v) '' p.closedBall 0 1).Nonempty := by
    exact ⟨inner ℝ g 0, ⟨0, by simpa [Seminorm.mem_closedBall_zero], by simp⟩⟩
  have hsup_le :
      sSup ((fun v : E ↦ inner ℝ g v) '' p.closedBall 0 1) ≤ inner ℝ g u := by
    refine csSup_le himage_nonempty ?_
    rintro t ⟨v, hv, rfl⟩
    exact huMax hv
  have hu_le :
      inner ℝ g u ≤ sSup ((fun v : E ↦ inner ℝ g v) '' p.closedBall 0 1) := by
    exact le_csSup himage_bdd ⟨u, hu, rfl⟩
  refine ⟨u, hu, ?_, huMax⟩
  rw [Seminorm.dualNorm]
  exact le_antisymm hu_le hsup_le

/-- Helper for Theorem 2.5: the dual norm is nonnegative. -/
private lemma dualNorm_nonneg
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (g : E) :
    0 ≤ ‖g‖[p,*] := by
  obtain ⟨u, hu, hu_eq, huMax⟩ := dualNorm_attained_on_closedBall (E := E) p g
  have hzero : (0 : E) ∈ p.closedBall 0 1 := by
    simpa [Seminorm.mem_closedBall_zero]
  have hmax0 : inner ℝ g 0 ≤ inner ℝ g u := huMax hzero
  simpa [hu_eq] using hmax0

/-- Helper for Theorem 2.5: the dual norm is invariant under negation. -/
private lemma dualNorm_neg_eq
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (g : E) :
    ‖-g‖[p,*] = ‖g‖[p,*] := by
  have hle : ‖-g‖[p,*] ≤ ‖g‖[p,*] := by
    obtain ⟨u, hu, hu_eq, _⟩ := dualNorm_attained_on_closedBall (E := E) p (-g)
    have hneg_mem : -u ∈ p.closedBall 0 1 := by
      simpa [Seminorm.mem_closedBall_zero, map_neg_eq_map] using hu
    have hpu : p (-u) ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hneg_mem
    have hinner :
        inner ℝ (-g) u ≤ ‖g‖[p,*] := by
      calc
        inner ℝ (-g) u = inner ℝ g (-u) := by simp
        _ ≤ ‖g‖[p,*] * p (-u) := Seminorm.inner_le_dualNorm_mul p (-u) g
        _ ≤ ‖g‖[p,*] := by
              have hnonneg := dualNorm_nonneg (E := E) p g
              nlinarith
    simpa [hu_eq] using hinner
  have hge : ‖g‖[p,*] ≤ ‖-g‖[p,*] := by
    obtain ⟨u, hu, hu_eq, _⟩ := dualNorm_attained_on_closedBall (E := E) p g
    have hneg_mem : -u ∈ p.closedBall 0 1 := by
      simpa [Seminorm.mem_closedBall_zero, map_neg_eq_map] using hu
    have hpu : p (-u) ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hneg_mem
    have hinner :
        inner ℝ g u ≤ ‖-g‖[p,*] := by
      calc
        inner ℝ g u = inner ℝ (-g) (-u) := by simp
        _ ≤ ‖-g‖[p,*] * p (-u) := Seminorm.inner_le_dualNorm_mul p (-u) (-g)
        _ ≤ ‖-g‖[p,*] := by
              have hnonneg := dualNorm_nonneg (E := E) p (-g)
              nlinarith
    simpa [hu_eq] using hinner
  exact le_antisymm hle hge

/-- Helper for Theorem 2.5: the dual norm satisfies the triangle inequality. -/
private lemma dualNorm_add_le
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (g h : E) :
    ‖g + h‖[p,*] ≤ ‖g‖[p,*] + ‖h‖[p,*] := by
  obtain ⟨u, hu, hu_eq, _⟩ := dualNorm_attained_on_closedBall (E := E) p (g + h)
  have hpu : p u ≤ 1 := by
    simpa [Seminorm.mem_closedBall_zero] using hu
  have hg_le : inner ℝ g u ≤ ‖g‖[p,*] := by
    calc
      inner ℝ g u ≤ ‖g‖[p,*] * p u := Seminorm.inner_le_dualNorm_mul p u g
      _ ≤ ‖g‖[p,*] := by
            have hnonneg := dualNorm_nonneg (E := E) p g
            nlinarith
  have hh_le : inner ℝ h u ≤ ‖h‖[p,*] := by
    calc
      inner ℝ h u ≤ ‖h‖[p,*] * p u := Seminorm.inner_le_dualNorm_mul p u h
      _ ≤ ‖h‖[p,*] := by
            have hnonneg := dualNorm_nonneg (E := E) p h
            nlinarith
  calc
    ‖g + h‖[p,*] = inner ℝ (g + h) u := hu_eq.symm
    _ = inner ℝ g u + inner ℝ h u := by rw [inner_add_left]
    _ ≤ ‖g‖[p,*] + ‖h‖[p,*] := add_le_add hg_le hh_le

/-- Helper for Theorem 2.5: the dual norm of a difference is controlled by the two intermediate
dual norms. -/
private lemma dualNorm_sub_le_add
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (x y z : E) :
    ‖x - y‖[p,*] ≤ ‖x - z‖[p,*] + ‖y - z‖[p,*] := by
  calc
    ‖x - y‖[p,*] = ‖(x - z) + (z - y)‖[p,*] := by congr 1; abel
    _ ≤ ‖x - z‖[p,*] + ‖z - y‖[p,*] := dualNorm_add_le (E := E) p (x - z) (z - y)
    _ = ‖x - z‖[p,*] + ‖y - z‖[p,*] := by
          rw [show z - y = -(y - z) by abel, dualNorm_neg_eq (E := E) p (y - z)]

/-- Helper for Theorem 2.5: every dual vector admits a primal displacement whose quadratic model
attains the source extremal-direction bound `-(2L)⁻¹ ‖g‖[p,*]²`. -/
private lemma extremal_direction_quadratic_model_bound
    (g : E) (hL : 0 < L) :
    ∃ d : E,
      inner ℝ g d + ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) ≤
        -(1 / (2 * (L : ℝ))) * (‖g‖[p,*]) ^ (2 : ℕ) := by
  obtain ⟨u, hu, hu_eq, _⟩ := dualNorm_attained_on_closedBall (E := E) p g
  let a : ℝ := ‖g‖[p,*] / (L : ℝ)
  let d : E := -(a • u)
  refine ⟨d, ?_⟩
  have hLr : 0 < (L : ℝ) := by
    exact_mod_cast hL
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (dualNorm_nonneg (E := E) p g) hLr.le
  have hpu : p u ≤ 1 := by
    simpa [Seminorm.mem_closedBall_zero] using hu
  have hpd_le : p d ≤ a := by
    calc
      p d = p (a • u) := by
        dsimp [d]
        simp [map_neg_eq_map]
      _ = |a| * p u := by
        simpa [Real.norm_eq_abs] using (map_smul_eq_mul p a u)
      _ = a * p u := by
        rw [abs_of_nonneg ha_nonneg]
      _ ≤ a * 1 := by
        gcongr
      _ = a := by ring
  have hinner_eq : inner ℝ g d = -a * ‖g‖[p,*] := by
    calc
      inner ℝ g d = inner ℝ g (-(a • u)) := by rfl
      _ = -(a * inner ℝ g u) := by
            rw [inner_neg_right, inner_smul_right]
      _ = -(a * ‖g‖[p,*]) := by rw [hu_eq]
      _ = -a * ‖g‖[p,*] := by ring
  have hsq_le : (p d) ^ (2 : ℕ) ≤ a ^ (2 : ℕ) := by
    nlinarith [hpd_le, apply_nonneg p d, ha_nonneg]
  have hquad_le :
      ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) ≤ ((L : ℝ) / 2) * a ^ (2 : ℕ) := by
    have hcoef_nonneg : 0 ≤ (L : ℝ) / 2 := by
      positivity
    exact mul_le_mul_of_nonneg_left hsq_le hcoef_nonneg
  calc
    inner ℝ g d + ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) ≤
        -a * ‖g‖[p,*] + ((L : ℝ) / 2) * a ^ (2 : ℕ) := by
          rw [hinner_eq]
          linarith
    _ = -(1 / (2 * (L : ℝ))) * (‖g‖[p,*]) ^ (2 : ℕ) := by
          dsimp [a]
          field_simp [hLr.ne']
          ring

/-- Helper for Theorem 2.5: the tangent-error bounds `(2.1.9)` imply the quadratic
gradient lower bound `(2.1.10)` by applying the upper tangent model to the translated objective
`z ↦ f z - ⟪∇f x, z⟫` and optimizing that quadratic model in a dual-norm extremal direction. -/
private lemma gradient_quadratic_lower_bound_of_tangent_error_bounds
    (h1 : smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f)
    (hL : 0 < L) :
    smoothConvexGradientQuadraticLowerBoundOn p L (∇ f) Set.univ f := by
  intro x _ y _
  let φ : E → ℝ := fun z ↦ f z - inner ℝ (∇ f x) z
  let gy : E := ∇ f y - ∇ f x
  let a : ℝ := (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ)
  -- The translated objective has `x` as a minimizer because the lower tangent error is nonnegative.
  have hx_min : ∀ z : E, φ x ≤ φ z := by
    intro z
    have hnonneg := h1.nonneg (x := x) (by simp) (y := z) (by simp)
    have hphi_nonneg : 0 ≤ φ z - φ x := by
      have hphi_eq : φ z - φ x = f z - f x - inner ℝ (∇ f x) (z - x) := by
        dsimp [φ]
        rw [inner_sub_right]
        ring_nf
      rw [hphi_eq]
      exact hnonneg
    linarith
  obtain ⟨d, hd⟩ :=
    extremal_direction_quadratic_model_bound (E := E) (p := p) (L := L) gy hL
  have hnorm :
      (‖gy‖[p,*]) ^ (2 : ℕ) = a := by
    dsimp [gy, a]
    rw [show ∇ f y - ∇ f x = -(∇ f x - ∇ f y) by abel, dualNorm_neg_eq (E := E) p]
  have hd' :
      inner ℝ gy d + ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) ≤
        -(1 / (2 * (L : ℝ))) * a := by
    simpa [hnorm] using hd
  -- Apply the upper tangent model to the translated objective at `y` and the trial point `y + d`.
  have hup :
      φ (y + d) ≤ φ y + inner ℝ gy d + ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
    have hy' := h1.upperBound (x := y) (by simp) (y := y + d) (by simp)
    have hy'' :
        f (y + d) - f y - inner ℝ (∇ f y) d ≤
          ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
      have hpneg : p (y - (y + d)) = p d := by
        calc
          p (y - (y + d)) = p (-d) := by abel_nf
          _ = p d := by simpa using (map_neg_eq_map p d)
      simpa [hpneg] using hy'
    have hphi_upper :
        φ (y + d) - φ y - inner ℝ gy d ≤
          ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
      have hphi_eq :
          φ (y + d) - φ y - inner ℝ gy d =
            f (y + d) - f y - inner ℝ (∇ f y) d := by
        calc
          φ (y + d) - φ y - inner ℝ gy d =
              f (y + d) - inner ℝ (∇ f x) (y + d) -
                (f y - inner ℝ (∇ f x) y) - inner ℝ gy d := by
                  rfl
          _ = f (y + d) - inner ℝ (∇ f x) y - inner ℝ (∇ f x) d -
                (f y - inner ℝ (∇ f x) y) - inner ℝ gy d := by
                  rw [inner_add_right]
                  ring
          _ = f (y + d) - f y - inner ℝ (∇ f x) d - inner ℝ gy d := by
                ring
          _ = f (y + d) - f y - inner ℝ (∇ f y) d := by
                dsimp [gy]
                rw [inner_sub_left]
                ring
      rw [hphi_eq]
      exact hy''
    linarith
  -- Comparing the minimizing point `x` with the extremal trial point yields `(2.1.10)`.
  have hphi :
      φ x ≤ φ y - (1 / (2 * (L : ℝ))) * a := by
    calc
      φ x ≤ φ (y + d) := hx_min (y + d)
      _ ≤ φ y + inner ℝ gy d + ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := hup
      _ ≤ φ y - (1 / (2 * (L : ℝ))) * a := by linarith [hd']
  have hfinal :
      f x + inner ℝ (∇ f x) (y - x) + (1 / (2 * (L : ℝ))) * a ≤
        f y := by
    have hphi' :
        f x - inner ℝ (∇ f x) x + (1 / (2 * (L : ℝ))) * a ≤
          f y - inner ℝ (∇ f x) y := by
      dsimp [φ] at hphi
      linarith
    have hrewrite :
        f x + inner ℝ (∇ f x) (y - x) + (1 / (2 * (L : ℝ))) * a =
          f x - inner ℝ (∇ f x) x + (1 / (2 * (L : ℝ))) * a +
            inner ℝ (∇ f x) y := by
      rw [inner_sub_right]
      ring
    rw [hrewrite]
    linarith
  simpa [a] using hfinal

/-- Helper for Theorem 2.5: the quadratic lower bound `(2.1.10)` implies cocoercivity
`(2.1.11)` after adding the inequalities with the two endpoints interchanged. -/
private lemma cocoerciveGradient_of_gradient_quadratic_lower_bound
    (h2 : smoothConvexGradientQuadraticLowerBoundOn p L (∇ f) Set.univ f)
    (hL : 0 < L) :
    smoothConvexCocoerciveGradientOn p L (∇ f) Set.univ := by
  intro x _ y _
  -- Add the two endpoint-swapped copies of `(2.1.10)` after normalizing the dual norm.
  have hxy := h2 (x := x) (by simp) (y := y) (by simp)
  have hyx := h2 (x := y) (by simp) (y := x) (by simp)
  let a : ℝ := (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ)
  have hnorm :
      (‖∇ f y - ∇ f x‖[p,*]) ^ (2 : ℕ) = (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ) := by
    rw [show ∇ f y - ∇ f x = -(∇ f x - ∇ f y) by abel, dualNorm_neg_eq (E := E) p]
  have hxy' :
      f x + inner ℝ (∇ f x) (y - x) + (1 / (2 * (L : ℝ))) * a ≤ f y := by
    simpa [a] using hxy
  have hyx' :
      f y + inner ℝ (∇ f y) (x - y) +
          (1 / (2 * (L : ℝ))) * a ≤
        f x := by
    rw [hnorm] at hyx
    simpa [a] using hyx
  -- The linear terms collapse to the monotonicity pairing of the gradient difference.
  have hlin :
      inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y) =
        -inner ℝ (∇ f x - ∇ f y) (x - y) := by
    calc
      inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y)
          = -inner ℝ (∇ f x) (x - y) + inner ℝ (∇ f y) (x - y) := by
              rw [show y - x = -(x - y) by abel, inner_neg_right]
      _ = -inner ℝ (∇ f x - ∇ f y) (x - y) := by
            rw [inner_sub_left]
            ring
  have hLr : 0 < (L : ℝ) := by
    exact_mod_cast hL
  have hlinear :
      inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y) +
          (1 / (L : ℝ)) * a ≤ 0 := by
    have hsum := add_le_add hxy' hyx'
    ring_nf at hsum ⊢
    linarith
  rw [hlin] at hlinear
  simpa [a] using (show (1 / (L : ℝ)) * a ≤ inner ℝ (∇ f x - ∇ f y) (x - y) by
    nlinarith [hlinear, hLr])

/-- Helper for Theorem 2.5: cocoercivity `(2.1.11)` yields the monotonicity and upper pairing
bound `(2.1.12)` after combining it with dual Cauchy. -/
private lemma monotoneGradientBounds_of_cocoerciveGradient
    (h3 : smoothConvexCocoerciveGradientOn p L (∇ f) Set.univ)
    (hL : 0 < L) :
    smoothConvexMonotoneGradientBoundsOn p L (∇ f) Set.univ := by
  refine ⟨?_, ?_⟩
  · intro x _ y _
    -- Cocoercivity already places a nonnegative quantity below the gradient pairing.
    have hxy := h3 (x := x) (by simp) (y := y) (by simp)
    have hnonneg :
        0 ≤ (1 / (L : ℝ)) * (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ) := by
      positivity
    exact le_trans hnonneg hxy
  · intro x _ y _
    -- Dual Cauchy turns cocoercivity into the Lipschitz-style upper pairing bound.
    have hxy := h3 (x := x) (by simp) (y := y) (by simp)
    have hinner :
        inner ℝ (∇ f x - ∇ f y) (x - y) ≤
          ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
      Seminorm.inner_le_dualNorm_mul p (x - y) (∇ f x - ∇ f y)
    have hp_nonneg : 0 ≤ p (x - y) := apply_nonneg p (x - y)
    have hbound : ‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y) := by
      by_cases hgrad0 : ‖∇ f x - ∇ f y‖[p,*] = 0
      · have hLr_nonneg : 0 ≤ (L : ℝ) := by
          exact_mod_cast hL.le
        simpa [hgrad0] using mul_nonneg hLr_nonneg hp_nonneg
      · have hdual_nonneg : 0 ≤ ‖∇ f x - ∇ f y‖[p,*] :=
          dualNorm_nonneg (E := E) p (∇ f x - ∇ f y)
        have hdual_pos : 0 < ‖∇ f x - ∇ f y‖[p,*] :=
          lt_of_le_of_ne hdual_nonneg (Ne.symm hgrad0)
        let a : ℝ := ‖∇ f x - ∇ f y‖[p,*]
        let s : ℝ := p (x - y)
        have hchain :
            (1 / (L : ℝ)) * a ^ (2 : ℕ) ≤ a * s := by
          simpa [a, s] using le_trans hxy hinner
        have hLr : 0 < (L : ℝ) := by
          exact_mod_cast hL
        have hchain' : a * a ≤ a * ((L : ℝ) * s) := by
          have hscaled := mul_le_mul_of_nonneg_left hchain hLr.le
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, hLr.ne'] using hscaled
        have hbound' : a ≤ (L : ℝ) * s := by
          refine le_of_mul_le_mul_left ?_ hdual_pos
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hchain'
        simpa [a, s] using hbound'
    calc
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤
          ‖∇ f x - ∇ f y‖[p,*] * p (x - y) := hinner
      _ ≤ ((L : ℝ) * p (x - y)) * p (x - y) := by
            exact mul_le_mul_of_nonneg_right hbound hp_nonneg
      _ = (L : ℝ) * (p (x - y)) ^ (2 : ℕ) := by
            ring

/-- Helper for Theorem 2.5: the tangent-error bounds `(2.1.9)` imply the convex-combination
quadratic gap estimate `(2.1.14)` by applying those tangent inequalities at the midpoint
`αx + (1 - α)y` to both endpoints and adding them with weights `α` and `1 - α`. -/
private lemma convexCombinationQuadraticBound_of_tangent_error_bounds
    (h1 : smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f) :
    smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f := by
  intro x _ y _ α hα
  let z : E := α • x + (1 - α) • y
  have hx_bound := h1 (x := z) (by simp) (y := x) (by simp)
  have hy_bound := h1 (x := z) (by simp) (y := y) (by simp)
  have hz_line : z = AffineMap.lineMap y x α := by
    simp [z, AffineMap.lineMap_apply_module, add_comm]
  have hz_sub_x : z - x = (1 - α) • (y - x) := by
    simpa [hz_line, vsub_eq_sub] using AffineMap.lineMap_vsub_right y x α
  have hz_sub_y : z - y = α • (x - y) := by
    simpa [hz_line, vsub_eq_sub] using AffineMap.lineMap_vsub_left y x α
  have hp_sub : p (y - x) = p (x - y) := by
    simpa [neg_sub] using (map_neg_eq_map p (x - y))
  have hx_disp : x - z = (1 - α) • (x - y) := by
    calc
      x - z = -((z - x)) := by abel
      _ = -((1 - α) • (y - x)) := by rw [hz_sub_x]
      _ = (1 - α) • (x - y) := by simp [smul_neg, sub_eq_add_neg]
  have hy_disp : y - z = α • (y - x) := by
    calc
      y - z = -(z - y) := by abel
      _ = -(α • (x - y)) := by rw [hz_sub_y]
      _ = α • (y - x) := by simp [smul_neg, sub_eq_add_neg]
  have hcancel_vec : α • (x - z) + (1 - α) • (y - z) = 0 := by
    rw [hx_disp, hy_disp]
    rw [show y - x = -(x - y) by abel]
    rw [smul_smul, smul_smul, smul_neg]
    calc
      (α * (1 - α)) • (x - y) + -(((1 - α) * α) • (x - y)) =
          ((α * (1 - α)) - ((1 - α) * α)) • (x - y) := by
            rw [← sub_eq_add_neg, sub_smul]
      _ = 0 := by
            have hcoeff : α * (1 - α) - ((1 - α) * α) = 0 := by ring
            simp [hcoeff]
  have hcancel :
      α * inner ℝ (∇ f z) (x - z) + (1 - α) * inner ℝ (∇ f z) (y - z) = 0 := by
    calc
      α * inner ℝ (∇ f z) (x - z) + (1 - α) * inner ℝ (∇ f z) (y - z) =
          inner ℝ (∇ f z) (α • (x - z) + (1 - α) • (y - z)) := by
            rw [inner_add_right, inner_smul_right, inner_smul_right]
      _ = 0 := by simp [hcancel_vec]
  have hgap_eq :
      α * f x + (1 - α) * f y - f z =
        α * (f x - f z - inner ℝ (∇ f z) (x - z)) +
          (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) := by
    linarith
  have hx_scaled :
      α * (f x - f z - inner ℝ (∇ f z) (x - z)) ≤
        α * (((L : ℝ) / 2) * (p (z - x)) ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hx_bound.2 hα.1
  have hy_scaled :
      (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) ≤
        (1 - α) * (((L : ℝ) / 2) * (p (z - y)) ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hy_bound.2 (sub_nonneg.mpr hα.2)
  have hupper :
      α * f x + (1 - α) * f y - f z ≤
        α * (1 - α) * ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := by
    have hsum := add_le_add hx_scaled hy_scaled
    calc
      α * f x + (1 - α) * f y - f z
          = α * (f x - f z - inner ℝ (∇ f z) (x - z)) +
              (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) := hgap_eq
      _ ≤ α * (((L : ℝ) / 2) * (p (z - x)) ^ (2 : ℕ)) +
            (1 - α) * (((L : ℝ) / 2) * (p (z - y)) ^ (2 : ℕ)) := hsum
      _ = α * (1 - α) * ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := by
            rw [hz_sub_x, hz_sub_y]
            simp [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hα.1,
              hp_sub, abs_of_nonneg (sub_nonneg.mpr hα.2)]
            ring
  have hx_nonneg :
      0 ≤ α * (f x - f z - inner ℝ (∇ f z) (x - z)) := by
    exact mul_nonneg hα.1 hx_bound.1
  have hy_nonneg :
      0 ≤ (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) := by
    exact mul_nonneg (sub_nonneg.mpr hα.2) hy_bound.1
  have hnonneg :
      0 ≤ α * f x + (1 - α) * f y - f z := by
    rw [hgap_eq]
    exact add_nonneg hx_nonneg hy_nonneg
  exact ⟨hnonneg, by simpa [z] using hupper⟩

/-- Helper for Theorem 2.5: the quadratic lower bound `(2.1.10)` implies the convex-combination
gradient bound `(2.1.13)` by applying `(2.1.10)` at the convex-combination point
`αx + (1 - α)y` toward each endpoint and combining the results. -/
private lemma convexCombinationGradientBound_of_gradient_quadratic_lower_bound
    (h2 : smoothConvexGradientQuadraticLowerBoundOn p L (∇ f) Set.univ f)
    (hL : 0 < L) :
    smoothConvexConvexCombinationGradientBoundOn p L (∇ f) Set.univ f := by
  intro x _ y _ α hα
  let z : E := α • x + (1 - α) • y
  have hx_bound := h2 (x := z) (by simp) (y := x) (by simp)
  have hy_bound := h2 (x := z) (by simp) (y := y) (by simp)
  have hz_line : z = AffineMap.lineMap y x α := by
    simp [z, AffineMap.lineMap_apply_module, add_comm]
  have hx_disp : x - z = (1 - α) • (x - y) := by
    calc
      x - z = -((z - x)) := by abel
      _ = -((1 - α) • (y - x)) := by
            rw [show z - x = (1 - α) • (y - x) by
              simpa [hz_line, vsub_eq_sub] using AffineMap.lineMap_vsub_right y x α]
      _ = (1 - α) • (x - y) := by
            simp [smul_neg, sub_eq_add_neg]
  have hy_disp : y - z = α • (y - x) := by
    calc
      y - z = -(z - y) := by abel
      _ = -(α • (x - y)) := by
            rw [show z - y = α • (x - y) by
              simpa [hz_line, vsub_eq_sub] using AffineMap.lineMap_vsub_left y x α]
      _ = α • (y - x) := by
            simp [smul_neg, sub_eq_add_neg]
  -- The two tangent directions from `z` to the endpoints cancel after weighting.
  have hcancel_vec : α • (x - z) + (1 - α) • (y - z) = 0 := by
    rw [hx_disp, hy_disp]
    rw [show y - x = -(x - y) by abel]
    rw [smul_smul, smul_smul, smul_neg]
    calc
      (α * (1 - α)) • (x - y) + -(((1 - α) * α) • (x - y)) =
          ((α * (1 - α)) - ((1 - α) * α)) • (x - y) := by
            rw [← sub_eq_add_neg, sub_smul]
      _ = 0 := by
            have hcoeff : α * (1 - α) - ((1 - α) * α) = 0 := by
              ring
            simp [hcoeff]
  have hcancel :
      α * inner ℝ (∇ f z) (x - z) + (1 - α) * inner ℝ (∇ f z) (y - z) = 0 := by
    calc
      α * inner ℝ (∇ f z) (x - z) + (1 - α) * inner ℝ (∇ f z) (y - z) =
          inner ℝ (∇ f z) (α • (x - z) + (1 - α) • (y - z)) := by
            rw [inner_add_right, inner_smul_right, inner_smul_right]
      _ = 0 := by
            simp [hcancel_vec]
  -- After weighting the two `(2.1.10)` inequalities, only the dual-norm squares remain.
  have hx_scaled :
      α *
          (f z + inner ℝ (∇ f z) (x - z) +
            (1 / (2 * (L : ℝ))) * (‖∇ f z - ∇ f x‖[p,*]) ^ (2 : ℕ)) ≤
        α * f x := by
    exact mul_le_mul_of_nonneg_left hx_bound hα.1
  have hy_scaled :
      (1 - α) *
          (f z + inner ℝ (∇ f z) (y - z) +
            (1 / (2 * (L : ℝ))) * (‖∇ f z - ∇ f y‖[p,*]) ^ (2 : ℕ)) ≤
        (1 - α) * f y := by
    exact mul_le_mul_of_nonneg_left hy_bound (sub_nonneg.mpr hα.2)
  have hmain :
      f z +
          (1 / (2 * (L : ℝ))) *
            (α * (‖∇ f z - ∇ f x‖[p,*]) ^ (2 : ℕ) +
              (1 - α) * (‖∇ f z - ∇ f y‖[p,*]) ^ (2 : ℕ)) ≤
        α * f x + (1 - α) * f y := by
    have hsum := add_le_add hx_scaled hy_scaled
    nlinarith [hsum, hcancel]
  -- The endpoint gradient gap is controlled by the two intermediate gaps through `z`.
  let a : ℝ := ‖∇ f z - ∇ f x‖[p,*]
  let b : ℝ := ‖∇ f z - ∇ f y‖[p,*]
  let c : ℝ := ‖∇ f x - ∇ f y‖[p,*]
  have htriangle : c ≤ a + b := by
    have htriangle' :=
      dualNorm_sub_le_add (E := E) p (∇ f x) (∇ f y) (∇ f z)
    have hzx : ‖∇ f x - ∇ f z‖[p,*] = a := by
      dsimp [a]
      rw [show ∇ f x - ∇ f z = -(∇ f z - ∇ f x) by abel, dualNorm_neg_eq (E := E) p]
    have hzy : ‖∇ f y - ∇ f z‖[p,*] = b := by
      dsimp [b]
      rw [show ∇ f y - ∇ f z = -(∇ f z - ∇ f y) by abel, dualNorm_neg_eq (E := E) p]
    have htriangle'' : c ≤ ‖∇ f x - ∇ f z‖[p,*] + ‖∇ f y - ∇ f z‖[p,*] := by
      simpa [c] using htriangle'
    rw [hzx, hzy] at htriangle''
    exact htriangle''
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact dualNorm_nonneg (E := E) p (∇ f z - ∇ f x)
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    exact dualNorm_nonneg (E := E) p (∇ f z - ∇ f y)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact dualNorm_nonneg (E := E) p (∇ f x - ∇ f y)
  have hsum_nonneg : 0 ≤ a + b := add_nonneg ha_nonneg hb_nonneg
  have hc_sq : c ^ (2 : ℕ) ≤ (a + b) ^ (2 : ℕ) := by
    nlinarith [htriangle, hc_nonneg, hsum_nonneg]
  have hsq_aux :
      α * (1 - α) * (a + b) ^ (2 : ℕ) ≤ α * a ^ (2 : ℕ) + (1 - α) * b ^ (2 : ℕ) := by
    have hsquare : 0 ≤ (α * a - (1 - α) * b) ^ (2 : ℕ) := sq_nonneg _
    nlinarith [hsquare, hα.1, hα.2]
  have hsq :
      α * (1 - α) * c ^ (2 : ℕ) ≤ α * a ^ (2 : ℕ) + (1 - α) * b ^ (2 : ℕ) := by
    have hleft :
        α * (1 - α) * c ^ (2 : ℕ) ≤ α * (1 - α) * (a + b) ^ (2 : ℕ) := by
      have hα_nonneg : 0 ≤ α * (1 - α) := by
        nlinarith [hα.1, hα.2]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hc_sq hα_nonneg
    exact le_trans hleft hsq_aux
  have hcoef_nonneg : 0 ≤ 1 / (2 * (L : ℝ)) := by
    positivity
  have hsq_scaled :
      (1 / (2 * (L : ℝ))) * (α * (1 - α) * c ^ (2 : ℕ)) ≤
        (1 / (2 * (L : ℝ))) * (α * a ^ (2 : ℕ) + (1 - α) * b ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hsq hcoef_nonneg
  have htail :
      f z + (α * (1 - α) / (2 * (L : ℝ))) * (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ) ≤
        f z +
          (1 / (2 * (L : ℝ))) *
            (α * (‖∇ f z - ∇ f x‖[p,*]) ^ (2 : ℕ) +
              (1 - α) * (‖∇ f z - ∇ f y‖[p,*]) ^ (2 : ℕ)) := by
    dsimp [a, b, c] at hsq_scaled
    have htail' := add_le_add_left hsq_scaled (f z)
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using htail'
  exact le_trans htail hmain

/-- Helper for Theorem 2.5: the tangent-error bounds `(2.1.9)` reconstruct the owner
membership `f ∈ 𝓕[L,p]¹¹` by recovering `HasGradientAt` from a global quadratic affine-model
bound, deriving convexity from the lower tangent planes, and extracting the dual-norm Lipschitz
estimate from the cocoercivity inequality. -/
private lemma mem_F11_of_tangent_error_bounds
    (h1 : smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f)
    (hL : 0 < L) :
    f ∈ 𝓕[L, p]¹¹ := by
  obtain ⟨C, hC_pos, hC⟩ := seminorm_le_mul_norm (E := E) p
  let K : NNReal := ⟨(L : ℝ) * C ^ (2 : ℕ), by positivity⟩
  -- The tangent-error bounds imply the absolute affine-model estimate needed by Proposition 1.5.9.
  have hquad :
      ∀ x y,
        |f y - affineModelAt f (∇ f) x y| ≤
          (K : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
    intro x y
    have hnonneg := h1.nonneg (x := x) (by simp) (y := y) (by simp)
    have hupper := h1.upperBound (x := x) (by simp) (y := y) (by simp)
    have habs :
        |f y - affineModelAt f (∇ f) x y| ≤
          ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := by
      have hnonneg' :
          0 ≤ f y - affineModelAt f (∇ f) x y := by
        dsimp [affineModelAt]
        linarith
      have hlower :
          -(((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ)) ≤
            f y - affineModelAt f (∇ f) x y := by
        linarith
      have hupper' :
          f y - affineModelAt f (∇ f) x y ≤
            ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := by
        dsimp [affineModelAt]
        linarith
      exact abs_le.mpr ⟨hlower, hupper'⟩
    have hp_le : p (x - y) ≤ C * ‖x - y‖ := hC (x - y)
    have hsq_le :
        (p (x - y)) ^ (2 : ℕ) ≤ C ^ (2 : ℕ) * ‖x - y‖ ^ (2 : ℕ) := by
      nlinarith [hp_le, apply_nonneg p (x - y), norm_nonneg (x - y)]
    have hcoef_nonneg : 0 ≤ (L : ℝ) / 2 := by
      positivity
    calc
      |f y - affineModelAt f (∇ f) x y| ≤
          ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := habs
      _ ≤ ((L : ℝ) / 2) * (C ^ (2 : ℕ) * ‖x - y‖ ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hsq_le hcoef_nonneg
      _ = (K : ℝ) / 2 * ‖y - x‖ ^ (2 : ℕ) := by
            have hK : (K : ℝ) = (L : ℝ) * C ^ (2 : ℕ) := rfl
            rw [hK]
            rw [norm_sub_rev]
            ring
  have hgradAt :
      ∀ x : E, HasGradientAt f (∇ f x) x :=
    hasGradientAt_of_sub_affineApproximation_norm_sq_bound
      (L := K) (f := f) (g := ∇ f) hquad
  have hC1Lip :
      ContDiff ℝ 1 f ∧ LipschitzWith K (∇ f) :=
    mem_contDiffOne_withLipschitzGradient_of_sub_affineApproximation_norm_sq_bound
      (L := K) (f := f) (g := ∇ f) hquad
  -- The lower tangent inequality recovers convexity once the canonical gradient is known.
  have hconv : ConvexOn ℝ Set.univ f := by
    refine
      (convexOn_iff_lower_tangent_plane_of_contDiffOn
        (Q := Set.univ) (f := f) convex_univ (contDiffOn_univ.2 hC1Lip.1)).2 ?_
    intro x hx y hy
    have htangent : f x + inner ℝ (∇ f x) (y - x) ≤ f y := by
      have hnonneg := h1.nonneg (x := x) (by simp) (y := y) (by simp)
      linarith
    simpa [gradientWithin, gradient, fderivWithin_univ] using htangent
  have h2 :=
    gradient_quadratic_lower_bound_of_tangent_error_bounds
      (f := f) (p := p) (L := L) h1 hL
  have h3 :=
    cocoerciveGradient_of_gradient_quadratic_lower_bound
      (f := f) (p := p) (L := L) h2 hL
  -- Cocoercivity plus dual Cauchy recovers the defining dual-norm Lipschitz estimate.
  have hdual :
      ∀ x y, ‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y) := by
    intro x y
    have hxy := h3 (x := x) (by simp) (y := y) (by simp)
    have hinner :
        inner ℝ (∇ f x - ∇ f y) (x - y) ≤
          ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
      Seminorm.inner_le_dualNorm_mul p (x - y) (∇ f x - ∇ f y)
    by_cases hzero : ‖∇ f x - ∇ f y‖[p,*] = 0
    · have hLr_nonneg : 0 ≤ (L : ℝ) := by
        exact_mod_cast hL.le
      simpa [hzero] using mul_nonneg hLr_nonneg (apply_nonneg p (x - y))
    · let a : ℝ := ‖∇ f x - ∇ f y‖[p,*]
      let s : ℝ := p (x - y)
      have ha_nonneg : 0 ≤ a := by
        dsimp [a]
        exact dualNorm_nonneg (E := E) p (∇ f x - ∇ f y)
      have ha_pos : 0 < a := by
        have hzero' : a ≠ 0 := by
          simpa [a] using hzero
        exact lt_of_le_of_ne ha_nonneg (Ne.symm hzero')
      have hineq :
          (1 / (L : ℝ)) * a ^ (2 : ℕ) ≤ a * s := by
        simpa [a, s] using le_trans hxy hinner
      have hLr : 0 < (L : ℝ) := by
        exact_mod_cast hL
      have hscaled : a * a ≤ a * ((L : ℝ) * s) := by
        have hscaled' := mul_le_mul_of_nonneg_left hineq hLr.le
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, hLr.ne'] using hscaled'
      refine le_of_mul_le_mul_left ?_ ha_pos
      simpa [a, s, pow_two, mul_assoc, mul_left_comm, mul_comm] using hscaled
  refine ⟨⟨contDiffOn_univ.2 hC1Lip.1, hconv⟩, ?_, ?_⟩
  · intro x hx
    exact hgradAt x
  · intro x hx y hy
    exact hdual x y

/-- Helper for Theorem 2.5: the convex-combination gradient bound `(2.1.13)` recovers the
gradient quadratic lower bound `(2.1.10)` by the scalar endpoint limit `α → 1` along the segment
from `x` to `y`. -/
private lemma gradient_quadratic_lower_bound_of_convexCombinationGradientBound
    (h6 : smoothConvexConvexCombinationGradientBoundOn p L (∇ f) Set.univ f)
    (hL : 0 < L) :
    smoothConvexGradientQuadraticLowerBoundOn p L (∇ f) Set.univ f := by
  -- TODO: follow the source line-restriction argument with `t = 1 - α`, divide the Jensen-gap
  -- inequality by `t`, and pass to the endpoint limit using the recovered tangent term at `x`.
  sorry

/-- Helper for Theorem 2.5: the convex-combination quadratic bound `(2.1.14)` recovers the
tangent-error bounds `(2.1.9)` by the same scalar endpoint limit `α → 1` on the line segment from
`x` to `y`. -/
private lemma tangent_error_bounds_of_convexCombinationQuadraticBound
    (h7 : smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f)
    (hL : 0 < L) :
    smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f := by
  -- TODO: use the scalar line restriction `t = 1 - α`, divide the Jensen-gap estimate by `t`,
  -- and let `t → 0⁺` to recover both halves of the tangent-plane inequality at `x`.
  sorry

/-- Helper for Theorem 2.5: the monotone-gradient bounds `(2.1.12)` recover the tangent-error
bounds `(2.1.9)` by integrating the gradient pairing estimate along the segment from `x` to `y`.
-/
private lemma tangent_error_bounds_of_monotoneGradientBounds
    (h5 : smoothConvexMonotoneGradientBoundsOn p L (∇ f) Set.univ)
    (hL : 0 < L) :
    smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f := by
  -- TODO: follow the source integration proof for `(2.1.12) -> (2.1.9)` by applying the
  -- monotone pairing bounds to `x + t • (y - x)` and integrating the corrected segment remainder.
  sorry

/-- Theorem 2.5: for a positive smoothness constant `L`, membership in `𝓕[L, p]¹¹` is equivalent
to each of the six standard smooth convex inequalities `(2.1.9)` through `(2.1.14)`. The
textbook Euclidean theorem is the finite-dimensional specialization. -/
-- Proof sketch: derive `(2.1.9)` from the gradient Lipschitz bound by integrating the derivative
-- of `τ ↦ f (x + τ • (y - x))` along the segment from `x` to `y`; obtain `(2.1.10)` by applying
-- `(2.1.9)` to the translated function `y ↦ f y - ⟪∇ f x, y⟫`; deduce `(2.1.11)` by adding the
-- two copies of `(2.1.10)` with `(x, y)` interchanged; derive `(2.1.12)` from `(2.1.9)` and the
-- dual-norm Lipschitz bound; and pass between `(2.1.10)`, `(2.1.13)`, `(2.1.14)`, and `(2.1.9)`
-- by applying the two-point inequalities at the convex-combination point and taking the limit
-- `α → 1`.
theorem convexC1SeminormSmooth_tfae
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    {L : NNReal} (hL : 0 < L) (f : E → ℝ) :
    List.TFAE
      [ f ∈ 𝓕[L, p]¹¹
      , smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f
      , smoothConvexGradientQuadraticLowerBoundOn p L (∇ f) Set.univ f
      , smoothConvexCocoerciveGradientOn p L (∇ f) Set.univ
      , smoothConvexMonotoneGradientBoundsOn p L (∇ f) Set.univ
      , smoothConvexConvexCombinationGradientBoundOn p L (∇ f) Set.univ f
      , smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f ] := by
  -- Route correction: the translated-objective bridge and owner reconstruction now live in
  -- standalone helpers, so the final theorem is reduced to the planned `TFAE` graph.
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hf
      intro x _ y _
      refine ⟨?_, tangent_error_upperBound (hf := hf) (hx := by simp) (hy := by simp)⟩
      have hsupport :=
        hf.convexOn.lower_tangent_plane_of_hasGradientWithinAt
          x (by simp) (∇ f x) ((hasGradientWithinAt_univ).2 (hf.hasGradientAt x)) y (by simp)
      linarith
    · intro h1
      exact mem_F11_of_tangent_error_bounds (f := f) (p := p) (L := L) h1 hL
  tfae_have 2 → 3 := by
    intro h1
    exact gradient_quadratic_lower_bound_of_tangent_error_bounds
      (f := f) (p := p) (L := L) h1 hL
  tfae_have 3 → 4 := by
    intro h2
    exact cocoerciveGradient_of_gradient_quadratic_lower_bound
      (f := f) (p := p) (L := L) h2 hL
  tfae_have 4 → 5 := by
    intro h3
    exact monotoneGradientBounds_of_cocoerciveGradient
      (f := f) (p := p) (L := L) h3 hL
  tfae_have 5 → 2 := by
    intro h5
    exact tangent_error_bounds_of_monotoneGradientBounds
      (f := f) (p := p) (L := L) h5 hL
  tfae_have 3 → 6 := by
    intro h2
    exact convexCombinationGradientBound_of_gradient_quadratic_lower_bound
      (f := f) (p := p) (L := L) h2 hL
  tfae_have 2 → 7 := by
    intro h1
    exact convexCombinationQuadraticBound_of_tangent_error_bounds
      (f := f) (p := p) (L := L) h1
  tfae_have 6 → 3 := by
    intro h6
    exact gradient_quadratic_lower_bound_of_convexCombinationGradientBound
      (f := f) (p := p) (L := L) h6 hL
  tfae_have 7 → 2 := by
    intro h7
    exact tangent_error_bounds_of_convexCombinationQuadraticBound
      (f := f) (p := p) (L := L) h7 hL
  tfae_finish

/-- Theorem 2.5 gives the gradient quadratic lower bound `(2.1.10)` as a named consequence of
membership in `𝓕[L, p]¹¹`. -/
theorem ConvexC1SeminormSmooth.gradientQuadraticLowerBound
    (hf : ConvexC1SeminormSmooth p L f) (hL : 0 < L) :
    smoothConvexGradientQuadraticLowerBoundOn p L (∇ f) Set.univ f :=
  ((convexC1SeminormSmooth_tfae p hL f).out 0 2).mp hf

/-- Theorem 2.5 gives the cocoercivity inequality `(2.1.11)` as a named consequence of membership
in `𝓕[L, p]¹¹`. -/
theorem ConvexC1SeminormSmooth.cocoerciveGradient
    (hf : ConvexC1SeminormSmooth p L f) (hL : 0 < L) :
    smoothConvexCocoerciveGradientOn p L (∇ f) Set.univ :=
  ((convexC1SeminormSmooth_tfae p hL f).out 0 3).mp hf

/-- Theorem 2.5 gives the convex-combination gradient bound `(2.1.13)` as a named consequence of
membership in `𝓕[L, p]¹¹`. -/
theorem ConvexC1SeminormSmooth.convexCombinationGradientBound
    (hf : ConvexC1SeminormSmooth p L f) (hL : 0 < L) :
    smoothConvexConvexCombinationGradientBoundOn p L (∇ f) Set.univ f :=
  ((convexC1SeminormSmooth_tfae p hL f).out 0 5).mp hf

/-- On an arbitrary set `Q`, membership in `𝓕[L, p]¹¹(Q)` implies the tangent error bounds
`(2.1.9)` for all pairs of points in `Q`. -/
-- Proof sketch: localize the proof of `(2.1.9)` from the whole-space case to the segment joining
-- `x` and `y`, using only the ambient-gradient Lipschitz bound and first-order convexity on
-- `Q`.
theorem ConvexC1SeminormSmoothOn.tangentErrorBounds
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    smoothConvexTangentErrorBoundsOn p L (∇ f) Q f := by
  intro x hx y hy
  -- The lower bound is the usual supporting-hyperplane inequality from convexity.
  have hgradWithin : HasGradientWithinAt f (∇ f x) Q x := by
    simpa using (hf.hasGradientAt hx).hasFDerivAt.hasFDerivWithinAt.hasGradientWithinAt
  have hlower :=
    hf.convexOn.lower_tangent_plane_of_hasGradientWithinAt
      x hx (∇ f x) hgradWithin y hy
  -- The upper bound is obtained by integrating the corrected segment remainder.
  refine ⟨?_, tangent_error_upperBound (hf := hf) hx hy⟩
  linarith

/-- On an arbitrary set `Q`, membership in `𝓕[L, p]¹¹(Q)` implies the monotonicity and upper
bound `(2.1.12)` for the ambient-gradient pairing on `Q`. -/
-- Proof sketch: combine the first-order convexity inequality from `ConvexC1On Q f` with the
-- ambient-gradient Lipschitz bound measured by `‖·‖[p,*]` and apply the dual
-- Cauchy--Schwarz estimate.
theorem ConvexC1SeminormSmoothOn.monotoneGradientBounds
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    smoothConvexMonotoneGradientBoundsOn p L (∇ f) Q := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    -- Add the two tangent-error lower bounds with the base points interchanged.
    have hxy := (hf.tangentErrorBounds (x := x) hx (y := y) hy).1
    have hyx := (hf.tangentErrorBounds (x := y) hy (y := x) hx).1
    have hsum :
        inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y) ≤ 0 := by
      linarith
    have hrewrite :
        inner ℝ (∇ f x - ∇ f y) (x - y) =
          -(inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y)) := by
      have hxswap :
          inner ℝ (∇ f x) (x - y) = -inner ℝ (∇ f x) (y - x) := by
        calc
          inner ℝ (∇ f x) (x - y) = inner ℝ (∇ f x) (-(y - x)) := by
                  congr 2
                  abel
          _ = -inner ℝ (∇ f x) (y - x) := by rw [inner_neg_right]
      calc
        inner ℝ (∇ f x - ∇ f y) (x - y)
            = inner ℝ (∇ f x) (x - y) - inner ℝ (∇ f y) (x - y) := by
                rw [inner_sub_left]
        _ = -(inner ℝ (∇ f x) (y - x)) - inner ℝ (∇ f y) (x - y) := by
              rw [hxswap]
        _ = -(inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y)) := by
              ring
    rw [hrewrite]
    linarith
  · intro x hx y hy
    -- Bound the monotonicity pairing by dual Cauchy and the defining smoothness estimate.
    have hinner :
        inner ℝ (∇ f x - ∇ f y) (x - y) ≤
          ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
      Seminorm.inner_le_dualNorm_mul p (x - y) (∇ f x - ∇ f y)
    have hgrad := hf.dualNorm_gradient_sub_le hx hy
    have hp_nonneg : 0 ≤ p (x - y) := apply_nonneg p (x - y)
    calc
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤
          ‖∇ f x - ∇ f y‖[p,*] * p (x - y) := hinner
      _ ≤ ((L : ℝ) * p (x - y)) * p (x - y) := by
            exact mul_le_mul_of_nonneg_right hgrad hp_nonneg
      _ = (L : ℝ) * (p (x - y)) ^ (2 : ℕ) := by ring

/-- On an arbitrary set `Q`, membership in `𝓕[L, p]¹¹(Q)` implies the Jensen gap bounds
`(2.1.14)` for all pairs of points in `Q`. -/
-- Proof sketch: apply the tangent error bounds at the convex-combination point to both endpoints,
-- weight the resulting inequalities by `α` and `1 - α`, and add them.
theorem ConvexC1SeminormSmoothOn.convexCombinationQuadraticBound
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    smoothConvexConvexCombinationQuadraticBoundOn p L Q f := by
  intro x hx y hy α hα
  let z : E := α • x + (1 - α) • y
  have hz : z ∈ Q := hf.convex hx hy hα.1 (sub_nonneg.mpr hα.2) (by ring)
  have hx_bound := hf.tangentErrorBounds (x := z) hz (y := x) hx
  have hy_bound := hf.tangentErrorBounds (x := z) hz (y := y) hy
  have hz_line : z = AffineMap.lineMap y x α := by
    simp [z, AffineMap.lineMap_apply_module, add_comm]
  have hz_sub_x : z - x = (1 - α) • (y - x) := by
    simpa [hz_line, vsub_eq_sub] using AffineMap.lineMap_vsub_right y x α
  have hz_sub_y : z - y = α • (x - y) := by
    simpa [hz_line, vsub_eq_sub] using AffineMap.lineMap_vsub_left y x α
  have hp_sub : p (y - x) = p (x - y) := by
    simpa [neg_sub] using (map_neg_eq_map p (x - y))
  have hx_disp : x - z = (1 - α) • (x - y) := by
    calc
      x - z = -((z - x)) := by abel
      _ = -((1 - α) • (y - x)) := by rw [hz_sub_x]
      _ = (1 - α) • (x - y) := by simp [smul_neg, sub_eq_add_neg]
  have hy_disp : y - z = α • (y - x) := by
    calc
      y - z = -(z - y) := by abel
      _ = -(α • (x - y)) := by rw [hz_sub_y]
      _ = α • (y - x) := by simp [smul_neg, sub_eq_add_neg]
  have hcancel_vec : α • (x - z) + (1 - α) • (y - z) = 0 := by
    rw [hx_disp, hy_disp]
    rw [show y - x = -(x - y) by abel]
    rw [smul_smul, smul_smul, smul_neg]
    calc
      (α * (1 - α)) • (x - y) + -(((1 - α) * α) • (x - y)) =
          ((α * (1 - α)) - ((1 - α) * α)) • (x - y) := by
            rw [← sub_eq_add_neg, sub_smul]
      _ = 0 := by
            have hcoeff : α * (1 - α) - ((1 - α) * α) = 0 := by ring
            simp [hcoeff]
  have hcancel :
      α * inner ℝ (∇ f z) (x - z) + (1 - α) * inner ℝ (∇ f z) (y - z) = 0 := by
    calc
      α * inner ℝ (∇ f z) (x - z) + (1 - α) * inner ℝ (∇ f z) (y - z) =
          inner ℝ (∇ f z) (α • (x - z) + (1 - α) • (y - z)) := by
            rw [inner_add_right, inner_smul_right, inner_smul_right]
      _ = 0 := by simp [hcancel_vec]
  have hgap_eq :
      α * f x + (1 - α) * f y - f z =
        α * (f x - f z - inner ℝ (∇ f z) (x - z)) +
          (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) := by
    linarith
  have hx_scaled :
      α * (f x - f z - inner ℝ (∇ f z) (x - z)) ≤
        α * (((L : ℝ) / 2) * (p (z - x)) ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hx_bound.2 hα.1
  have hy_scaled :
      (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) ≤
        (1 - α) * (((L : ℝ) / 2) * (p (z - y)) ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hy_bound.2 (sub_nonneg.mpr hα.2)
  have hupper :
      α * f x + (1 - α) * f y - f z ≤
        α * (1 - α) * ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := by
    have hsum := add_le_add hx_scaled hy_scaled
    calc
      α * f x + (1 - α) * f y - f z
          = α * (f x - f z - inner ℝ (∇ f z) (x - z)) +
              (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) := hgap_eq
      _ ≤ α * (((L : ℝ) / 2) * (p (z - x)) ^ (2 : ℕ)) +
            (1 - α) * (((L : ℝ) / 2) * (p (z - y)) ^ (2 : ℕ)) := hsum
      _ = α * (1 - α) * ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := by
            rw [hz_sub_x, hz_sub_y]
            simp [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hα.1,
              hp_sub,
              abs_of_nonneg (sub_nonneg.mpr hα.2)]
            ring
  have hx_nonneg :
      0 ≤ α * (f x - f z - inner ℝ (∇ f z) (x - z)) := by
    exact mul_nonneg hα.1 hx_bound.1
  have hy_nonneg :
      0 ≤ (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) := by
    exact mul_nonneg (sub_nonneg.mpr hα.2) hy_bound.1
  have hnonneg :
      0 ≤ α * f x + (1 - α) * f y - f z := by
    rw [hgap_eq]
    exact add_nonneg hx_nonneg hy_nonneg
  exact ⟨hnonneg, by simpa [z] using hupper⟩

/-- The tangent-error bounds `(2.1.9)` for a smooth convex objective are the `Q = Set.univ`
specialization of `ConvexC1SeminormSmoothOn.tangentErrorBounds`. -/
theorem ConvexC1SeminormSmooth.tangentErrorBounds
    (hf : ConvexC1SeminormSmooth p L f) :
    smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f :=
  hf.toOn.tangentErrorBounds

/-- The monotone-gradient bounds `(2.1.12)` for a smooth convex objective are the
`Q = Set.univ` specialization of `ConvexC1SeminormSmoothOn.monotoneGradientBounds`. -/
theorem ConvexC1SeminormSmooth.monotoneGradientBounds
    (hf : ConvexC1SeminormSmooth p L f) :
    smoothConvexMonotoneGradientBoundsOn p L (∇ f) Set.univ :=
  hf.toOn.monotoneGradientBounds

/-- The convex-combination quadratic bounds `(2.1.14)` for a smooth convex objective are the
`Q = Set.univ` specialization of
`ConvexC1SeminormSmoothOn.convexCombinationQuadraticBound`. -/
theorem ConvexC1SeminormSmooth.convexCombinationQuadraticBound
    (hf : ConvexC1SeminormSmooth p L f) :
    smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f :=
  hf.toOn.convexCombinationQuadraticBound

end
