import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_17 (from Chap02) -/
open scoped Gradient

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A function on a real Hilbert space belongs to the strongly convex smooth class with
parameters `μ` and `L` when it is `C¹`, `μ`-strongly convex on the whole space, and has
`L`-Lipschitz gradient. Chapter 2 specializes this owner predicate to `ℝⁿ`, but the same
mathematics applies unchanged to `ℓ²(ℕ, ℝ)` and other real Hilbert spaces. -/
def IsStrongConvexSmoothObjective (μ L : ℝ) (f : E → ℝ) : Prop :=
  0 < μ ∧
    ContDiff ℝ 1 f ∧
    StrongConvexOn Set.univ μ f ∧
    ∀ x y : E, ‖∇ f x - ∇ f y‖ ≤ L * ‖x - y‖

scoped[StrongConvexSmooth] notation "𝓢[" μ ", " L "]¹¹" =>
  setOf (IsStrongConvexSmoothObjective μ L)

scoped[StrongConvexSmooth] notation "q[" μ ", " L "]" => (μ / L : ℝ)

open scoped StrongConvexSmooth

/-- The whole-space notation `𝓢[μ, L]¹¹` is the source-facing set view of the owner predicate
`IsStrongConvexSmoothObjective μ L`. -/
theorem mem_S11_iff {μ L : ℝ} {f : E → ℝ} :
    f ∈ 𝓢[μ, L]¹¹ ↔ IsStrongConvexSmoothObjective μ L f :=
  Iff.rfl

namespace IsStrongConvexSmoothObjective

/-- Membership in the strongly convex smooth class forces the strong-convexity parameter to be
positive. -/
theorem mu_pos {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f) :
    0 < μ :=
  hf.1

/-- Membership in the strongly convex smooth class includes `C^1` regularity. -/
theorem contDiff {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f) :
    ContDiff ℝ 1 f :=
  hf.2.1

/-- Membership in the strongly convex smooth class includes strong convexity on the whole space. -/
theorem strongConvexOn {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f) :
    StrongConvexOn Set.univ μ f :=
  hf.2.2.1

/-- A strongly convex smooth objective is strictly convex on the whole ambient space. -/
theorem strictConvexOn {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f) :
    StrictConvexOn ℝ Set.univ f :=
  hf.strongConvexOn.strictConvexOn hf.mu_pos

/-- Membership in the strongly convex smooth class includes the gradient-Lipschitz bound with
constant `L`. -/
theorem gradient_lipschitz {μ L : ℝ} {f : E → ℝ}
    (hf : IsStrongConvexSmoothObjective μ L f) (x y : E) :
    ‖∇ f x - ∇ f y‖ ≤ L * ‖x - y‖ :=
  hf.2.2.2 x y

/-- Translating the ambient coordinates of a strongly convex smooth objective preserves
membership in the same owner class. -/
-- Proof sketch: precompose `f` with the affine translation `x ↦ x - x₀`; translation preserves
-- `C¹` regularity, whole-space strong convexity, and the gradient-Lipschitz constant.
theorem translate {μ L : ℝ} {f : E → ℝ}
    (hf : IsStrongConvexSmoothObjective μ L f) (x0 : E) :
    IsStrongConvexSmoothObjective μ L (fun x ↦ f (x - x0)) := by
  refine ⟨hf.mu_pos, ?_, ?_, ?_⟩
  · -- Compose the `C¹` objective with the ambient translation map.
    have htranslate : ContDiff ℝ 1 (fun x : E ↦ x - x0) := by
      simpa [sub_eq_add_neg] using
        contDiff_id.add (contDiff_const : ContDiff ℝ 1 fun _ : E ↦ -x0)
    simpa [Function.comp_def] using hf.contDiff.comp htranslate
  · -- Whole-space strong convexity is preserved by translating the argument.
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    let u := x - x0
    let v := y - x0
    have h :
        f (a • u + b • v) ≤
          a * f u + b * f v - a * b * ((μ / 2) * ‖u - v‖ ^ (2 : ℕ)) :=
      hf.strongConvexOn.2 (by simp [u]) (by simp [v]) ha hb hab
    have hcomb : a • u + b • v = (a • x + b • y) - x0 := by
      dsimp [u, v]
      calc
        a • (x - x0) + b • (y - x0)
            = a • x + a • (-x0) + (b • y + b • (-x0)) := by
                simp [sub_eq_add_neg, smul_add]
        _ = a • x + b • y + (a • (-x0) + b • (-x0)) := by
              abel_nf
        _ = a • x + b • y + (a + b) • (-x0) := by
              rw [← add_smul]
        _ = a • x + b • y + -x0 := by
              simp [hab]
        _ = (a • x + b • y) - x0 := by
              simp [sub_eq_add_neg]
    have huv : u - v = x - y := by
      dsimp [u, v]
      abel_nf
    rw [hcomb, huv] at h
    simpa [u, v, sub_eq_add_neg, hab, add_assoc, add_left_comm, add_comm] using h
  · intro x y
    have hx : HasGradientAt f (∇ f (x - x0)) (x - x0) :=
      hf.contDiff.differentiable_one (x - x0) |>.hasGradientAt
    have hy : HasGradientAt f (∇ f (y - x0)) (y - x0) :=
      hf.contDiff.differentiable_one (y - x0) |>.hasGradientAt
    have hsubx : HasFDerivAt (fun z : E ↦ z - x0) (ContinuousLinearMap.id ℝ E) x := by
      simpa using (hasFDerivAt_id x).sub_const x0
    have hsuby : HasFDerivAt (fun z : E ↦ z - x0) (ContinuousLinearMap.id ℝ E) y := by
      simpa using (hasFDerivAt_id y).sub_const x0
    have hx_translate :
        HasGradientAt (fun z : E ↦ f (z - x0)) (∇ f (x - x0)) x := by
      simpa [Function.comp_def] using (hx.hasFDerivAt.comp x hsubx).hasGradientAt
    have hy_translate :
        HasGradientAt (fun z : E ↦ f (z - x0)) (∇ f (y - x0)) y := by
      simpa [Function.comp_def] using (hy.hasFDerivAt.comp y hsuby).hasGradientAt
    rw [hx_translate.gradient, hy_translate.gradient]
    simpa [sub_eq_add_neg, sub_add_eq_sub_sub] using
      hf.gradient_lipschitz (x - x0) (y - x0)

/-- A strongly convex smooth objective canonically yields the earlier Chapter 2 smooth-convex
owner. This is the objective-side bridge/view: strong convexity is extra source-facing structure,
while `ConvexC1SeminormSmooth` owns the reusable smooth-convex API on the finite-dimensional
Chapter 2 owner layer. -/
theorem toConvexC1SeminormSmooth {μ L : ℝ} {f : E → ℝ} [FiniteDimensional ℝ E]
    (hf : IsStrongConvexSmoothObjective μ L f) :
    ConvexC1SeminormSmooth (normSeminorm ℝ E) (Real.toNNReal L) f := by
  refine ⟨⟨contDiffOn_univ.2 hf.contDiff, ?_⟩, ?_, ?_⟩
  · have hμ : 0 ≤ μ := hf.mu_pos.le
    exact hf.strongConvexOn.convexOn (fun _ ↦ by positivity)
  · intro x _
    exact hf.contDiff.differentiable_one x |>.hasGradientAt
  · intro x _ y _
    have hL : L ≤ (Real.toNNReal L : ℝ) := by
      by_cases hL : 0 ≤ L
      · simp [Real.toNNReal_of_nonneg hL]
      · rw [Real.toNNReal_of_nonpos (le_of_not_ge hL)]
        exact le_of_lt (lt_of_not_ge hL)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
    simpa [gradient, gradientWithin, fderivWithin_univ,
      Seminorm.dualNorm_normSeminorm_eq_norm] using
      hf.gradient_lipschitz x y

/-- Expanding `IsStrongConvexSmoothObjective μ L f` yields the canonical `C¹`-plus-strong-convex
data together with the equivalent whole-space strong gradient-monotonicity formulation. -/
theorem iff_contDiff_and_gradient_strong_mono {μ L : ℝ} {f : E → ℝ} :
    IsStrongConvexSmoothObjective μ L f ↔
      0 < μ ∧
        ContDiff ℝ 1 f ∧
        (∀ x y : E,
          μ * ‖x - y‖ ^ (2 : ℕ) ≤ inner ℝ (∇ f x - ∇ f y) (x - y)) ∧
        ∀ x y : E, ‖∇ f x - ∇ f y‖ ≤ L * ‖x - y‖ := by
  constructor
  · intro hf
    let hf_diff : DifferentiableOn ℝ f (Set.univ : Set E) :=
      (contDiffOn_univ.2 hf.contDiff).differentiableOn (by simp)
    have hstrong :
        StrongConvexOn (Set.univ : Set E) μ f ↔
          ∀ x y : E,
            μ * ‖x - y‖ ^ (2 : ℕ) ≤
              inner ℝ
                (gradientWithin f Set.univ x - gradientWithin f Set.univ y)
                (x - y) := by
      let hstrong' :
          StrongConvexOn (Set.univ : Set E) μ f ↔
            ∀ ⦃x y : E⦄, x ∈ Set.univ → y ∈ Set.univ →
              μ * ‖x - y‖ ^ (2 : ℕ) ≤
                inner ℝ
                  (gradientWithin f Set.univ x - gradientWithin f Set.univ y)
                  (x - y) :=
        strongConvexOn_iff_gradient_monotone convex_univ hf_diff
      simpa using hstrong'
    refine ⟨hf.mu_pos, hf.contDiff, ?_, hf.gradient_lipschitz⟩
    simpa [gradientWithin, gradient, fderivWithin_univ] using
      hstrong.mp hf.strongConvexOn
  · rintro ⟨hμ, hf_contDiff, hmono, hf_lip⟩
    let hf_diff : DifferentiableOn ℝ f (Set.univ : Set E) :=
      (contDiffOn_univ.2 hf_contDiff).differentiableOn (by simp)
    have hstrong :
        StrongConvexOn (Set.univ : Set E) μ f ↔
          ∀ x y : E,
            μ * ‖x - y‖ ^ (2 : ℕ) ≤
              inner ℝ
                (gradientWithin f Set.univ x - gradientWithin f Set.univ y)
                (x - y) := by
      let hstrong' :
          StrongConvexOn (Set.univ : Set E) μ f ↔
            ∀ ⦃x y : E⦄, x ∈ Set.univ → y ∈ Set.univ →
              μ * ‖x - y‖ ^ (2 : ℕ) ≤
                inner ℝ
                  (gradientWithin f Set.univ x - gradientWithin f Set.univ y)
                  (x - y) :=
        strongConvexOn_iff_gradient_monotone convex_univ hf_diff
      simpa using hstrong'
    refine ⟨hμ, hf_contDiff, ?_, hf_lip⟩
    exact hstrong.mpr (by simpa [gradientWithin, gradient, fderivWithin_univ] using hmono)

/-- A strongly convex smooth objective has `μ`-strongly monotone gradient on the whole space. -/
theorem gradient_strong_mono {μ L : ℝ} {f : E → ℝ}
    (hf : IsStrongConvexSmoothObjective μ L f) (x y : E) :
    μ * ‖x - y‖ ^ (2 : ℕ) ≤ inner ℝ (∇ f x - ∇ f y) (x - y) :=
  (IsStrongConvexSmoothObjective.iff_contDiff_and_gradient_strong_mono.mp hf).2.2.1 x y

/-- A strongly convex smooth objective satisfies the standard quadratic lower tangent bound on the
whole space. -/
-- Proof sketch: apply the whole-space strong-convexity tangent inequality at the base point `x`.
theorem lower_tangent_quadratic {μ L : ℝ} {f : E → ℝ}
    (hf : IsStrongConvexSmoothObjective μ L f) (x y : E) :
    f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  have hgrad : HasGradientAt f (∇ f x) x :=
    hf.contDiff.differentiable_one x |>.hasGradientAt
  simpa using
    StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
      hf.strongConvexOn (by simp) (by simp) hgrad

/-- On a nontrivial real Hilbert space, the strong-convexity parameter of a strongly convex smooth
objective cannot exceed the gradient-Lipschitz constant. -/
-- Proof sketch: add the lower tangent inequalities at `x, y` and `y, x` to obtain strong
-- monotonicity of the gradient, then bound the resulting inner product by Cauchy-Schwarz and the
-- gradient-Lipschitz estimate. Dividing by `‖x - y‖² > 0` gives `μ ≤ L`.
theorem mu_le_L {μ L : ℝ} {f : E → ℝ} [Nontrivial E]
    (hf : IsStrongConvexSmoothObjective μ L f) :
    μ ≤ L := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne E
  have hmono := hf.gradient_strong_mono x y
  have hupper :
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤ L * ‖x - y‖ ^ (2 : ℕ) := by
    calc
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤ ‖∇ f x - ∇ f y‖ * ‖x - y‖ := by
        exact real_inner_le_norm _ _
      _ ≤ (L * ‖x - y‖) * ‖x - y‖ := by
        exact mul_le_mul_of_nonneg_right (hf.gradient_lipschitz x y) (norm_nonneg _)
      _ = L * ‖x - y‖ ^ (2 : ℕ) := by
        ring
  have hnormsq_pos : 0 < ‖x - y‖ ^ (2 : ℕ) := by
    exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) 2
  exact le_of_mul_le_mul_right (le_trans hmono hupper) hnormsq_pos

/-- A strongly convex smooth objective satisfies the standard quadratic upper tangent bound on the
whole space. -/
-- Proof sketch: combine `C¹` regularity and the gradient-Lipschitz bound to control the tangent
-- error by `(L / 2) * ‖y - x‖²`.
theorem upper_tangent_quadratic {μ L : ℝ} {f : E → ℝ}
    (hf : IsStrongConvexSmoothObjective μ L f) (x y : E) :
    f y ≤ f x + inner ℝ (∇ f x) (y - x) + (L / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  by_cases hE : Subsingleton E
  · have hxy : x = y := hE.elim x y
    subst hxy
    simp
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hL : 0 ≤ L := le_trans hf.mu_pos.le hf.mu_le_L
    have hgrad : LipschitzWith (Real.toNNReal L) (∇ f) := by
      refine LipschitzWith.of_dist_le_mul ?_
      intro x' y'
      have hdist :
          ‖∇ f x' - ∇ f y'‖ ≤ L * ‖x' - y'‖ :=
        hf.gradient_lipschitz x' y'
      have hL' : L ≤ (Real.toNNReal L : ℝ) := by
        simp [Real.toNNReal_of_nonneg hL]
      simpa [dist_eq_norm] using
        le_trans hdist (mul_le_mul_of_nonneg_right hL' (norm_nonneg _))
    have hupper :=
      taylor_upper_bound_of_contDiffOne_withLipschitzGradient
        hf.contDiff hgrad x y
    simpa [firstOrderTaylorModelAt_apply, Real.toNNReal_of_nonneg hL] using hupper

/-- A global minimizer of a strongly convex smooth objective is stationary. -/
theorem gradient_eq_zero_of_isMinOn
    {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar) :
    ∇ f xStar = 0 := by
  exact
    (isMinOn_hasGradientAt_zero_of_differentiableAt
      (hf.contDiff.differentiable_one xStar) hxStar).gradient

/-- A stationary point of a strongly convex smooth objective is a global minimizer. -/
theorem isMinOn_of_gradient_eq_zero
    {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f)
    (xStar : E) (hgrad : ∇ f xStar = 0) :
    IsMinOn f Set.univ xStar := by
  rw [isMinOn_univ_iff]
  intro x
  have hbound : f x ≥ f xStar + (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    simpa [hgrad] using hf.lower_tangent_quadratic xStar x
  have hnormsq : 0 ≤ ‖x - xStar‖ ^ (2 : ℕ) := by positivity
  nlinarith [hf.mu_pos, hnormsq, hbound]

/-- For a strongly convex smooth objective on a real Hilbert space, global minimizers are exactly
the stationary points. -/
theorem isMinOn_iff_gradient_eq_zero
    {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f)
    (xStar : E) :
    IsMinOn f Set.univ xStar ↔ ∇ f xStar = 0 :=
  ⟨hf.gradient_eq_zero_of_isMinOn, hf.isMinOn_of_gradient_eq_zero xStar⟩

end IsStrongConvexSmoothObjective

section ApproximateSolution

variable {μ L : ℝ}

/- Definition 2.17 next adds the textbook approximate-solution clause relative to a chosen
minimizer `xStar`. The objective-side owner `IsStrongConvexSmoothObjective μ L` already lives on
the intrinsic real-Hilbert-space ambient type `E`, and the approximate-solution data below use
only that same ambient owner `SetConstrainedMinimizationProblem.unconstrained f` together with the
squared-distance bound to `xStar`. The textbook `ℝⁿ` statement is therefore recovered by
specializing `E = EuclideanSpace ℝ (Fin n)`, rather than by keeping a separate Euclidean owner.

Source/core/bridge triage:
* source-facing: an objective `f : E → ℝ` in `𝓢^{1,1}_{μ,L}` together with a minimizing point
  `xStar`;
* bridge/view on the objective side: `hf.toConvexC1SeminormSmooth`, which reuses the earlier
  Chapter 2 smooth-convex owner `ConvexC1SeminormSmooth` for smooth-only consequences;
* core/canonical: the Chapter 1 owner `SetConstrainedMinimizationProblem E`, specialized to
  feasible set `Set.univ`, and the minimizer predicate `IsMinOn f Set.univ xStar`;
* bridge/view: the ambient owner problem `SetConstrainedMinimizationProblem.unconstrained f`, the
  Chapter 1 derived notions of optimal value and approximate minimizer for that owner problem, and
  the local value-gradient map `x ↦ (f x, ∇ f x)`.

Primitive data:
* the objective `f : E → ℝ`;
* the owner objective hypothesis `hf : IsStrongConvexSmoothObjective μ L f`;
* a minimizing point `xStar : E` with `hxStar : IsMinOn f Set.univ xStar`.

Derived API:
* strict convexity and hence uniqueness of minimizers, via `hf.strictConvexOn`;
* the whole-space lower and upper quadratic tangent bounds, via
  `hf.lower_tangent_quadratic` and `hf.upper_tangent_quadratic`;
* the ambient owner problem on `Set.univ`;
* optimal values, approximate minimizers, and first-order locality statements, all taken directly
  from the Chapter 1 owner problem and the value-gradient map rather than from a parallel wrapper.

No separate public `StrongConvexSmoothMinimizationProblem`, local `optimalValue`, or first-order
data wrapper is introduced here. The source-facing approximate-solution predicate below is kept as
a thin bridge over the Chapter 1 approximate-minimizer owner together with the squared-distance
condition from the textbook. -/

variable (f : E → ℝ) (xStar : E)
variable (sameDataNear : (E → ℝ) → (E → ℝ) → E → Prop)

#check f ∈ 𝓢[μ, L]¹¹
#check IsMinOn f Set.univ xStar
#check (SetConstrainedMinimizationProblem.unconstrained f : SetConstrainedMinimizationProblem E)
#check fun x : E ↦ (f x, ∇ f x)
/- The first-order local black-box oracle clause is the Chapter 1 class-level value-gradient
oracle `fun f x ↦ (f x, ∇ f x)` together with its locality predicate. -/
set_option linter.hashCommand false in
#check ((fun f x ↦ (f x, ∇ f x)) : (E → ℝ) → E → ℝ × E)
set_option linter.hashCommand false in
#check OptimizationOracle.IsLocal (fun f x ↦ (f x, ∇ f x)) sameDataNear

/-- Definition 2.17: relative to a chosen minimizer `x*` of an objective in
`𝓢^{1,1}_{μ,L}`, a point `x̄` is an approximate solution with accuracy `ε` when both the
objective gap `f(x̄) - f(x*)` and the squared distance `‖x̄ - x*‖²` are at most `ε`. The
textbook `ℝⁿ` version is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
def IsStrongConvexSmoothApproximateSolution (f : E → ℝ) (xStar : E) (ε : ℝ) (xBar : E) : Prop :=
  f xBar - f xStar ≤ ε ∧ ‖xBar - xStar‖ ^ (2 : ℕ) ≤ ε

section

variable {E : Type*} [NormedAddCommGroup E]

/-- The source-facing Definition 2.17 approximate-solution predicate is the Chapter 1
unconstrained approximate-minimizer predicate together with the extra squared-distance bound to
the chosen minimizer `x*`. No Euclidean coordinates or finite-dimensional structure enter this
owner-level equivalence; those are only a specialization layer for the textbook presentation. -/
-- Proof sketch: rewrite the objective-gap inequality with the canonical upstream bridge
-- `SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le`, then keep
-- the squared-distance clause unchanged.
theorem isStrongConvexSmoothApproximateSolution_iff_isApproximateMinimizer_and_sqdist_le
    {f : E → ℝ} {xStar xBar : E} (hxStar : IsMinOn f Set.univ xStar) (ε : ℝ) :
    IsStrongConvexSmoothApproximateSolution f xStar ε xBar ↔
      (SetConstrainedMinimizationProblem.unconstrained f).IsApproximateMinimizer ε xBar ∧
        ‖xBar - xStar‖ ^ (2 : ℕ) ≤ ε := by
  -- Rewrite only the objective-gap clause through the Chapter 1 owner bridge.
  constructor
  · rintro ⟨hgap, hsqdist⟩
    -- Keep the squared-distance bound unchanged while converting the gap inequality.
    refine ⟨?_, hsqdist⟩
    exact
      (SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le
        f hxStar ε).2 hgap
  · rintro ⟨happrox, hsqdist⟩
    -- Convert the approximate-minimizer clause back to the textbook objective-gap form.
    refine ⟨?_, hsqdist⟩
    exact
      (SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le
        f hxStar ε).1 happrox

end

end ApproximateSolution

/-! ### Lemma_2_17 (from Chap02) -/
open scoped Gradient SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Primary domain: smooth convex objectives on real Hilbert spaces, with a finite-dimensional
Chapter 2 specialization.

Sampled owner-style declarations:
* `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt` in `Definition_2_2`
* `taylor_upper_bound_of_contDiffOne_withLipschitzGradient` in `Chap01/Lemma_1_5_10`
* `ConvexC1SeminormSmooth.convexOn` / `hasGradientAt` / `gradient_lipschitz` in `Theorem_2_5`
* `gradient_step_value_descent_of_lipschitzGradient` in `Lemma_2_16`

Source/core/bridge triage:
* source-facing: Lemma 2.17, the minimizer-pairing inequality for a smooth convex objective;
* core/canonical: `ConvexOn ℝ Set.univ f`, `∀ x, HasGradientAt f (∇ f x) x`,
  `LipschitzWith L (∇ f)`, and `IsMinOn f Set.univ xStar`;
* bridge/view: the finite-dimensional Chapter 2 notation `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`,
  recovered below as a specialization theorem.

Primitive data:
* whole-space convexity of `f`;
* the ambient gradient witnesses `HasGradientAt f (∇ f x) x`;
* the `L`-Lipschitz bound for `∇ f`;
* a global minimizer `xStar`.

Derived API:
* the local `C¹` bridge from the gradient witness and Lipschitz-gradient hypotheses;
* the quadratic upper tangent bound;
* the gradient quadratic lower bound and its cocoercive consequence;
* the finite-dimensional `𝓕[L, p]¹¹` specialization.

Accordingly, the main public theorem is stated on the intrinsic smooth-convex owner layer
`ConvexOn + HasGradientAt + LipschitzWith`, while `f ∈ 𝓕[L, p]¹¹` is kept only as the direct
finite-dimensional bridge view. -/

namespace ConvexC1SeminormSmooth

section

variable [CompleteSpace E]
variable {L : NNReal} {f : E → ℝ}

private theorem contDiff_one_of_hasGradientAt_lipschitz
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    ContDiff ℝ 1 f := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x ↦ (hgrad x).differentiableAt, ?_⟩
  have hEq : fderiv ℝ f = fun x ↦ InnerProductSpace.toDual ℝ E (∇ f x) := by
    funext x
    simpa using (hgrad x).hasFDerivAt.fderiv
  have hcont : Continuous (fun x ↦ InnerProductSpace.toDual ℝ E (∇ f x)) :=
    (InnerProductSpace.toDual ℝ E).continuous.comp hgrad_lipschitz.continuous
  simpa [hEq] using hcont

private theorem upper_tangent_quadratic_of_hasGradientAt_lipschitz
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (x y : E) :
    f y ≤ f x + inner ℝ (∇ f x) (y - x) + ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  have hfC1 :
      ContDiff ℝ 1 f :=
    contDiff_one_of_hasGradientAt_lipschitz hgrad hgrad_lipschitz
  have hupper :=
    taylor_upper_bound_of_contDiffOne_withLipschitzGradient hfC1 hgrad_lipschitz x y
  simpa [firstOrderTaylorModelAt_apply] using hupper

private theorem gradient_quadratic_lower_bound_of_convex_hasGradientAt_lipschitz
    (hconv : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hL : 0 < L)
    (x y : E) :
    f y + inner ℝ (∇ f y) (x - y) +
        (1 / (2 * (L : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) ≤
      f x := by
  let d := ∇ f x - ∇ f y
  let z := x - (1 / (L : ℝ)) • d
  have hupper :
      f z ≤
        f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
    have h :=
      upper_tangent_quadratic_of_hasGradientAt_lipschitz hgrad hgrad_lipschitz x z
    have hz : z - x = -((1 / (L : ℝ)) • d) := by
      simp [z]
    calc
      f z ≤ f x + inner ℝ (∇ f x) (z - x) + ((L : ℝ) / 2) * ‖z - x‖ ^ (2 : ℕ) := h
      _ = f x + inner ℝ (∇ f x) (-((1 / (L : ℝ)) • d)) +
            ((L : ℝ) / 2) * ‖-((1 / (L : ℝ)) • d)‖ ^ (2 : ℕ) := by rw [hz]
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            ((L : ℝ) / 2) * ((1 / (L : ℝ)) ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ)) := by
            simp [inner_smul_right, norm_smul, sq]
            ring
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
            have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
            field_simp [hL0]
  have hlower :
      f z ≥
        f y + inner ℝ (∇ f y) (x - y) -
          (1 / (L : ℝ)) * inner ℝ (∇ f y) d := by
    have h :=
      hconv.lower_tangent_plane_of_hasGradientWithinAt
        y (by simp) (∇ f y) ((hasGradientWithinAt_univ).2 (hgrad y)) z (by simp)
    have hz : z - y = (x - y) - (1 / (L : ℝ)) • d := by
      simp [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    calc
      f z ≥ f y + inner ℝ (∇ f y) (z - y) := h
      _ = f y + inner ℝ (∇ f y) ((x - y) - (1 / (L : ℝ)) • d) := by rw [hz]
      _ = f y + inner ℝ (∇ f y) (x - y) -
            (1 / (L : ℝ)) * inner ℝ (∇ f y) d := by
            rw [inner_sub_right, inner_smul_right]
            ring
  have hinner :
      inner ℝ (∇ f x) d = inner ℝ (∇ f y) d + ‖d‖ ^ (2 : ℕ) := by
    calc
      inner ℝ (∇ f x) d = inner ℝ (d + ∇ f y) d := by
        congr 1
        dsimp [d]
        abel_nf
      _ = inner ℝ d d + inner ℝ (∇ f y) d := by
        rw [inner_add_left]
      _ = inner ℝ (∇ f y) d + ‖d‖ ^ (2 : ℕ) := by
        simp [inner_self_eq_norm_sq_to_K, add_comm]
  have hupper' :
      f z ≤
        f x - (1 / (L : ℝ)) * inner ℝ (∇ f y) d -
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
    calc
      f z ≤
          f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := hupper
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f y) d -
            (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
            rw [hinner]
            ring
  have hmid :
      f y + inner ℝ (∇ f y) (x - y) -
          (1 / (L : ℝ)) * inner ℝ (∇ f y) d ≤
        f x - (1 / (L : ℝ)) * inner ℝ (∇ f y) d -
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) :=
    le_trans hlower hupper'
  have hmid' :
      f y + inner ℝ (∇ f y) (x - y) ≤
        f x - (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
    linarith
  have hfinal :
      f y + inner ℝ (∇ f y) (x - y) +
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) ≤
        f x := by
    linarith
  simpa [d] using hfinal

/-- Lemma 2.17 on the intrinsic real-Hilbert-space smooth-convex owner layer: if `f` is convex on
the whole space, admits the ambient gradient `∇ f` everywhere, has `L`-Lipschitz gradient, and
`xStar` is a global minimizer, then every point `x` satisfies
`(1 / L) ‖∇ f x‖² ≤ ⟪∇ f x, x - xStar⟫`. The textbook `ℝⁿ` statement is recovered by the
finite-dimensional specialization theorem below. -/
-- Proof sketch: if `0 < L`, first derive the quadratic lower bound `(2.1.10)` from the canonical
-- convex lower-tangent inequality and the quadratic upper Taylor bound coming from the
-- Lipschitz-gradient hypothesis, then add the two orientations to obtain the usual cocoercivity
-- inequality. Since a global minimizer is stationary, specializing that cocoercive bound to
-- `(x, xStar)` yields the result. If `L = 0`, the gradient field is constant, and stationarity at
-- `xStar` forces `∇ f x = 0`.
theorem gradient_pairing_with_minimizer_gap_ge_norm_sq_div
    (hconv : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x : E) :
    (1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ) ≤ inner ℝ (∇ f x) (x - xStar) := by
  have hgrad0 : ∇ f xStar = 0 := by
    exact
      (isMinOn_hasGradientAt_zero_of_differentiableAt
        (hgrad xStar).differentiableAt hxStar).gradient
  by_cases hL : 0 < L
  · have hxy :=
      gradient_quadratic_lower_bound_of_convex_hasGradientAt_lipschitz
        hconv hgrad hgrad_lipschitz hL x xStar
    have hyx :=
      gradient_quadratic_lower_bound_of_convex_hasGradientAt_lipschitz
        hconv hgrad hgrad_lipschitz hL xStar x
    have hxy' :
        f xStar + (1 / (2 * (L : ℝ))) * ‖∇ f x‖ ^ (2 : ℕ) ≤ f x := by
      simpa [hgrad0, sub_zero] using hxy
    have hyx' :
        f x - inner ℝ (∇ f x) (x - xStar) +
            (1 / (2 * (L : ℝ))) * ‖∇ f x‖ ^ (2 : ℕ) ≤
          f xStar := by
      have hsub : xStar - x = -(x - xStar) := by
        abel_nf
      have hyx'' := hyx
      rw [hgrad0, norm_sub_rev, hsub, inner_neg_right, sub_zero] at hyx''
      exact hyx''
    have hpair :
        (1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ) ≤
          inner ℝ (∇ f x) (x - xStar) := by
      have hsum := add_le_add hxy' hyx'
      ring_nf at hsum ⊢
      linarith
    exact hpair
  · have hL0 : L = 0 := le_antisymm (le_of_not_gt hL) bot_le
    have hgrad_eq : ∇ f x = ∇ f xStar := by
      have hdist := hgrad_lipschitz.dist_le_mul x xStar
      have hdist0 : dist (∇ f x) (∇ f xStar) = 0 := by
        apply le_antisymm
        · simpa [hL0] using hdist
        · exact dist_nonneg
      exact eq_of_dist_eq_zero hdist0
    simp [hL0, hgrad_eq, hgrad0]

end

section

variable [FiniteDimensional ℝ E]

local notation "p" => normSeminorm ℝ E

local instance lemma17FiniteDimensionalComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

variable {L : NNReal} {f : E → ℝ}

/-- Finite-dimensional Chapter 2 specialization of Lemma 2.17: the source-facing notation
`f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` supplies the intrinsic owner hypotheses used by
`gradient_pairing_with_minimizer_gap_ge_norm_sq_div`. -/
theorem gradient_pairing_with_minimizer_gap_ge_norm_sq_div_of_mem_F11
    (hf : f ∈ 𝓕[L, p]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x : E) :
    (1 / (L : ℝ)) * ‖∇ f x‖ ^ (2 : ℕ) ≤ inner ℝ (∇ f x) (x - xStar) :=
  gradient_pairing_with_minimizer_gap_ge_norm_sq_div
    hf.convexOn hf.hasGradientAt hf.gradient_lipschitz hxStar x

end

end ConvexC1SeminormSmooth

/-! ### Proposition_2_17 (from Chap02) -/
open Set
open PointedCone
open scoped Pointwise

local notation "Q" => reciprocalEpigraphOnPositiveRay

/-- The reciprocal epigraph owner set is convex. -/
theorem reciprocalEpigraphOnPositiveRay_convex : Convex ℝ reciprocalEpigraphOnPositiveRay := by
  intro x hx y hy a b ha hb hab
  rcases (mem_reciprocalEpigraphOnPositiveRay_iff x).1 hx with ⟨hx1, hx2⟩
  rcases (mem_reciprocalEpigraphOnPositiveRay_iff y).1 hy with ⟨hy1, hy2⟩
  refine (mem_reciprocalEpigraphOnPositiveRay_iff (a • x + b • y)).2 ?_
  constructor
  · have hpos : 0 < a * x.1 + b * y.1 := by
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simp [ha0, hb1, hy1]
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
        exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx1) (mul_nonneg hb hy1.le)
    simpa using hpos
  · have hrecip : 1 / (a * x.1 + b * y.1) ≤ a / x.1 + b / y.1 := by
      have hden : 0 < a * x.1 + b * y.1 := by
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          simp [ha0, hb1, hy1]
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
          exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx1) (mul_nonneg hb hy1.le)
      field_simp [hden.ne', hx1.ne', hy1.ne']
      ring_nf
      have hsq : 2 * x.1 * y.1 ≤ x.1 ^ 2 + y.1 ^ 2 := by
        nlinarith [sq_nonneg (x.1 - y.1)]
      have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
      have hpoly :
          x.1 * y.1 ≤
            x.1 * y.1 * a ^ 2 + x.1 * y.1 * b ^ 2 + x.1 ^ 2 * a * b + y.1 ^ 2 * a * b := by
        calc
          x.1 * y.1 = x.1 * y.1 * 1 := by ring
          _ = x.1 * y.1 * (a ^ 2 + 2 * (a * b) + b ^ 2) := by
                have hab_sq : a ^ 2 + 2 * (a * b) + b ^ 2 = 1 := by
                  nlinarith [hab]
                rw [hab_sq]
          _ =
              x.1 * y.1 * a ^ 2 + 2 * x.1 * y.1 * (a * b) + x.1 * y.1 * b ^ 2 := by
                ring
          _ ≤ x.1 * y.1 * a ^ 2 + (x.1 ^ 2 + y.1 ^ 2) * (a * b) + x.1 * y.1 * b ^ 2 := by
                gcongr
          _ =
              x.1 * y.1 * a ^ 2 + x.1 * y.1 * b ^ 2 + x.1 ^ 2 * a * b + y.1 ^ 2 * a * b := by
                ring
      exact hpoly
    have hbound : a / x.1 + b / y.1 ≤ a * x.2 + b * y.2 := by
      have hax : a / x.1 ≤ a * x.2 := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left hx2 ha
      have hby : b / y.1 ≤ b * y.2 := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left hy2 hb
      exact add_le_add hax hby
    simpa [smul_add, add_comm, add_left_comm, add_assoc, smul_eq_mul] using
      le_trans hrecip hbound

/-- Helper for Proposition 2.17: the reciprocal epigraph contains the point `(1, 1)`. -/
private theorem reciprocalEpigraphOnPositiveRay_nonempty : Set.Nonempty Q := by
  -- We use the obvious point on the reciprocal graph to witness nonemptiness.
  exact ⟨(1, 1), (mem_reciprocalEpigraphOnPositiveRay_iff (1, 1)).2 ⟨zero_lt_one, by norm_num⟩⟩

/-- Helper for Proposition 2.17: a point of `convexHull ℝ (insert 0 Q)` lies on a segment from the
origin to a point of `Q`, hence is a scalar multiple `t • y` with `0 ≤ t ≤ 1`. -/
private theorem mem_convexHull_zero_insert_reciprocalEpigraph_iff (x : ℝ × ℝ) :
    x ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q) ↔
      ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ t • Q := by
  -- Rewrite the convex hull of `{0} ∪ Q` as the join of `{0}` with the convex set `Q`.
  rw [convexHull_insert reciprocalEpigraphOnPositiveRay_nonempty,
    reciprocalEpigraphOnPositiveRay_convex.convexHull_eq, convexJoin_singleton_left]
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨y, hy, hx⟩
    -- Unpack the segment description into the coefficient of `y`.
    rcases hx with ⟨a, t, ha, ht, hat, rfl⟩
    refine ⟨t, ⟨ht, by linarith⟩, y, hy, ?_⟩
    simp
  · rintro ⟨t, ht, y, hy, rfl⟩
    -- Conversely, every coefficient `t ∈ [0, 1]` gives a point on the segment `[0, y]`.
    refine ⟨y, hy, 1 - t, t, sub_nonneg.mpr ht.2, ht.1, by linarith, ?_⟩
    simp

/-- Helper for Proposition 2.17: scaling a point of `Q` by a factor at least `1` keeps it in `Q`.
-/
private theorem smul_mem_reciprocalEpigraphOnPositiveRay_of_one_le {t : ℝ} {y : ℝ × ℝ}
    (hy : y ∈ Q) (ht : 1 ≤ t) : t • y ∈ Q := by
  rcases (mem_reciprocalEpigraphOnPositiveRay_iff y).1 hy with ⟨hy1, hy2⟩
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hy2_nonneg : 0 ≤ y.2 := le_trans (by positivity) hy2
  refine (mem_reciprocalEpigraphOnPositiveRay_iff (t • y)).2 ?_
  constructor
  · -- The first coordinate stays positive under a positive scaling.
    simpa [smul_eq_mul] using mul_pos ht_pos hy1
  · -- Compare reciprocals after scaling the first coordinate and use `t ≥ 1`.
    rw [show (t • y).1 = t * y.1 by simp [smul_eq_mul],
      show (t • y).2 = t * y.2 by simp [smul_eq_mul]]
    have h_inv_t : 1 / t ≤ 1 := by
      rw [div_le_iff₀ ht_pos]
      nlinarith
    have h_step : (1 / t) * (1 / y.1) ≤ 1 / y.1 := by
      nlinarith [h_inv_t, one_div_nonneg.mpr hy1.le]
    have h_mul : y.2 ≤ t * y.2 := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right ht hy2_nonneg
    calc
      1 / (t * y.1) = (1 / t) * (1 / y.1) := by
        field_simp [ht_pos.ne', hy1.ne']
      _ ≤ 1 / y.1 := h_step
      _ ≤ y.2 := hy2
      _ ≤ t * y.2 := h_mul

/-- Helper for Proposition 2.17: every positive multiple of a point of `Q` belongs to
`convexHull ℝ (insert 0 Q)`. -/
private theorem positive_smul_mem_convexHull_zero_insert_of_mem_reciprocalEpigraph
    {t : ℝ} {y : ℝ × ℝ} (ht : 0 < t) (hy : y ∈ Q) :
    t • y ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q) := by
  by_cases ht_one : t ≤ 1
  · -- When `t ≤ 1`, this is the segment from `0` to `y`.
    exact (mem_convexHull_zero_insert_reciprocalEpigraph_iff (t • y)).2
      ⟨t, ⟨ht.le, ht_one⟩, y, hy, rfl⟩
  · -- When `t ≥ 1`, first show `t • y ∈ Q`, then include it into the convex hull.
    have h_one_le : 1 ≤ t := le_of_not_ge ht_one
    exact subset_convexHull ℝ _ (mem_insert_of_mem _
      (smul_mem_reciprocalEpigraphOnPositiveRay_of_one_le hy h_one_le))

/-- Helper for Proposition 2.17: `convexHull ℝ (insert 0 Q)` is closed under nonnegative scalar
multiplication. -/
private theorem smul_mem_convexHull_zero_insert_reciprocalEpigraph_of_nonneg
    {x : ℝ × ℝ} {r : ℝ} (hx : x ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q)) (hr : 0 ≤ r) :
    r • x ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q) := by
  rcases (mem_convexHull_zero_insert_reciprocalEpigraph_iff x).1 hx with ⟨t, ht, y, hy, rfl⟩
  rw [smul_smul]
  by_cases hrt : r * t ≤ 1
  · -- If the new coefficient is still at most `1`, stay on the same segment.
    exact (mem_convexHull_zero_insert_reciprocalEpigraph_iff ((r * t) • y)).2
      ⟨r * t, ⟨mul_nonneg hr ht.1, hrt⟩, y, hy, rfl⟩
  · -- Otherwise the product coefficient is at least `1`, so the ray enters `Q` itself.
    have hrt_pos : 0 < r * t := lt_of_lt_of_le zero_lt_one (le_of_not_ge hrt)
    simpa [mul_assoc] using
      positive_smul_mem_convexHull_zero_insert_of_mem_reciprocalEpigraph hrt_pos hy

/-- Helper for Proposition 2.17: `convexHull ℝ (insert 0 Q)` is closed under conical combinations,
so it can be used as a pointed cone containing `Q`. -/
private theorem convexHull_zero_insert_reciprocalEpigraph_cone_comb
    {x y : ℝ × ℝ}
    (hx : x ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q))
    (hy : y ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • x + b • y ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q) := by
  let s : ℝ := a + b
  by_cases hs : s = 0
  · -- If the total weight vanishes, both coefficients are zero.
    have ha_zero : a = 0 := by linarith
    have hb_zero : b = 0 := by linarith
    simpa [ha_zero, hb_zero] using
      (subset_convexHull ℝ (insert (0 : ℝ × ℝ) Q) (by simp : (0 : ℝ × ℝ) ∈ insert (0 : ℝ × ℝ) Q))
  · -- Otherwise normalize to a convex combination, then scale back by `s`.
    have hs_pos : 0 < s := by
      have hs_ne : a + b ≠ 0 := by
        simpa [s] using hs
      dsimp [s]
      exact lt_of_le_of_ne (add_nonneg ha hb) hs_ne.symm
    have hs_nonneg : 0 ≤ s := hs_pos.le
    have hconv :
        (a / s) • x + (b / s) • y ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q) := by
      refine (convex_convexHull ℝ _ ) hx hy (div_nonneg ha hs_nonneg) (div_nonneg hb hs_nonneg) ?_
      have hsum : a / s + b / s = 1 := by
        dsimp [s]
        field_simp [hs_pos.ne']
        exact div_self hs_pos.ne'
      exact hsum
    have hsmul :
        s • ((a / s) • x + (b / s) • y) ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q) :=
      smul_mem_convexHull_zero_insert_reciprocalEpigraph_of_nonneg hconv hs_nonneg
    have hs_mul_a : s * (a / s) = a := by
      field_simp [hs_pos.ne']
    have hs_mul_b : s * (b / s) = b := by
      field_simp [hs_pos.ne']
    simpa [s, smul_add, smul_smul, hs_mul_a, hs_mul_b] using hsmul

/-- Proposition 2.17: the convex hull of `{(0, 0)} ∪ Q` equals the canonical cone hull of `Q`,
where `Q = reciprocalEpigraphOnPositiveRay`. -/
theorem convexHull_zero_union_reciprocalEpigraphOnPositiveRay_eq_conicHull :
    convexHull ℝ (insert (0 : ℝ × ℝ) reciprocalEpigraphOnPositiveRay) =
      (hull ℝ reciprocalEpigraphOnPositiveRay : Set (ℝ × ℝ)) := by
  -- Route correction: avoid the later Definition 2.28 shortcut and prove cone closure of the
  -- convex hull directly from its segment description.
  refine Subset.antisymm ?_ ?_
  · intro x hx
    -- Every convex-hull point has the form `t • y` with `0 ≤ t ≤ 1` and `y ∈ Q`.
    rcases (mem_convexHull_zero_insert_reciprocalEpigraph_iff x).1 hx with ⟨t, ht, y, hy, rfl⟩
    exact (hull ℝ Q).smul_mem ht.1 (subset_hull hy)
  · let C : PointedCone ℝ (ℝ × ℝ) :=
      PointedCone.ofConeComb
        (convexHull ℝ (insert (0 : ℝ × ℝ) Q))
        (by
          refine ⟨0, ?_⟩
          exact subset_convexHull ℝ _ (mem_insert 0 Q))
        (fun x hx y hy a ha b hb ↦
          convexHull_zero_insert_reciprocalEpigraph_cone_comb hx hy ha hb)
    have hQ : Q ⊆ C := by
      -- The convex hull contains `Q`, so the pointed hull of `Q` lies inside this cone.
      intro y hy
      exact subset_convexHull ℝ _ (mem_insert_of_mem _ hy)
    have hHull : hull ℝ Q ≤ C := Submodule.span_le.mpr hQ
    intro x hx
    exact hHull hx

/-! ### Theorem_2_17 (from Chap02) -/
open scoped Gradient StrongConvexSmooth
open HasGeometricRateOfConvergence

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: linear convergence of gradient descent on strongly convex smooth objectives over
real Hilbert spaces.

Owner-style declarations sampled before refining this file:
* `IsStrongConvexSmoothObjective` in `Definition_2_17`
* `gradientMethod` in `Algorithm_2_1`
* `IsStrongConvexSmoothObjective.pairing_lower_bound` in `Theorem_2_13`
* `HasGeometricRateOfConvergence.of_step_bound` in `Chap01/Definition_1_2_6`

Source/core/bridge triage:
* source-facing: Theorem 2.17 and its optimal-step corollaries, whose public hypothesis surface
  uses the textbook class notation `f ∈ 𝓢[μ, L]¹¹`;
* core/canonical: `IsStrongConvexSmoothObjective μ L f`, `IsMinOn f Set.univ xStar`,
  `gradientMethod (fun _ ↦ h) f x0`, and the scalar rate owner
  `HasGeometricRateOfConvergence` for the squared-distance sequence;
* bridge/view: the Euclidean specialization of these owner theorems, together with the optimal-step
  rate simplifications.

Primitive data:
* `hf : IsStrongConvexSmoothObjective μ L f`, equivalently `f ∈ 𝓢[μ, L]¹¹`;
* `hxStar : IsMinOn f Set.univ xStar`;
* the step size `h` for the general-rate theorem and the initial point `x0`.

Derived API:
* `hf.mu_pos`;
* `hf.pairing_lower_bound`;
* `hf.gradient_eq_zero_of_isMinOn hxStar`;
* `hf.upper_tangent_quadratic`;
* the subsingleton/nontrivial split used only to turn the optimal squared-distance estimate into a
  distance estimate without adding `μ ≤ L` as primitive data.

Accordingly, this file keeps the source-facing theorem hypotheses in the textbook notation
`f ∈ 𝓢[μ, L]¹¹` while deriving the statements from the core owner predicate
`IsStrongConvexSmoothObjective μ L f`, the canonical gradient-method trajectory, and the minimizer
hypothesis. Internally, the main contraction proof is routed through the scalar owner
`HasGeometricRateOfConvergence` rather than a handwritten induction, while the textbook `ℝⁿ`
formulation is refined to the intrinsic real-Hilbert-space owner layer, with the Euclidean case
recovered by specialization rather than kept as the primary ambient model.
-/

section

variable {μ L : ℝ} {f : E → ℝ}

/-- Helper for Theorem 2.17: one gradient step with a constant stepsize in
`(0, 2 / (μ + L)]` contracts the squared distance to the minimizer by the
textbook factor `1 - 2 h μ L / (μ + L)`. -/
private theorem gradientMethod_sqdist_step_le
    [Nontrivial E]
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (h : ℝ) (hh0 : 0 < h) (hh : h ≤ 2 / (μ + L))
    (x : E) :
    ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) ≤
      (1 - (2 * h * μ * L) / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) := by
  have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
  have hμL : μ ≤ L := hf'.mu_le_L
  have hden : 0 < μ + L := by
    nlinarith [hf'.mu_pos, hμL]
  have hgrad0 : ∇ f xStar = 0 := hf'.gradient_eq_zero_of_isMinOn hxStar
  have hpair := hf'.pairing_lower_bound x xStar
  have hpair' :
      (μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) +
          (1 / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ) ≤
        inner ℝ (∇ f x) (x - xStar) := by
    simpa [hgrad0, sub_zero] using hpair
  -- The stepsize restriction makes the residual gradient-norm coefficient nonpositive.
  have hcoeff : 0 ≤ 2 * h / (μ + L) - h ^ (2 : ℕ) := by
    have hh' : h * h ≤ h * (2 / (μ + L)) :=
      mul_le_mul_of_nonneg_left hh hh0.le
    have hsq : h ^ (2 : ℕ) ≤ 2 * h / (μ + L) := by
      calc
        h ^ (2 : ℕ) = h * h := by ring
        _ ≤ h * (2 / (μ + L)) := hh'
        _ = 2 * h / (μ + L) := by ring
    exact sub_nonneg.mpr hsq
  -- Expand the next squared distance exactly as in the source proof.
  have h_expand :
      ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) =
        ‖x - xStar‖ ^ (2 : ℕ) - 2 * h * inner ℝ (∇ f x) (x - xStar) +
          h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := by
    calc
      ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ)
          = ‖(x - xStar) - h • ∇ f x‖ ^ (2 : ℕ) := by
              abel_nf
      _ = ‖x - xStar‖ ^ (2 : ℕ) - 2 * inner ℝ (x - xStar) (h • ∇ f x) +
            ‖h • ∇ f x‖ ^ (2 : ℕ) := by
            simpa using norm_sub_sq_real (x - xStar) (h • ∇ f x)
      _ = ‖x - xStar‖ ^ (2 : ℕ) - 2 * h * inner ℝ (∇ f x) (x - xStar) +
            h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := by
            rw [real_inner_smul_right, real_inner_comm]
            simp [norm_smul, Real.norm_of_nonneg hh0.le, sq]
            ring
  have h2h_nonneg : 0 ≤ 2 * h := by
    positivity
  have hpair'' :
      2 * h *
          ((μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) +
            (1 / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ)) ≤
        2 * h * inner ℝ (∇ f x) (x - xStar) := by
    exact mul_le_mul_of_nonneg_left hpair' h2h_nonneg
  have hgrad_sq_nonneg : 0 ≤ ‖∇ f x‖ ^ (2 : ℕ) := by
    positivity
  have hcoeff' :
      h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) ≤
        (2 * h / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_right (sub_nonneg.mp hcoeff) hgrad_sq_nonneg
  have hpair''' :
      (2 * h * μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) +
          (2 * h / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ) ≤
        2 * h * inner ℝ (∇ f x) (x - xStar) := by
    ring_nf at hpair'' ⊢
    exact hpair''
  have hstep₁ :
      ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) ≤
        ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h * μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ) +
          h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := by
    rw [h_expand]
    nlinarith [hpair''']
  have hstep₂ :
      ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h * μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ) +
          h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) ≤
        ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h * μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) := by
    nlinarith [hcoeff']
  -- Substitute the lower pairing bound into the expansion and drop the nonpositive remainder.
  calc
    ‖(x - h • ∇ f x) - xStar‖ ^ (2 : ℕ) ≤
        ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h * μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h / (μ + L)) * ‖∇ f x‖ ^ (2 : ℕ) +
          h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := hstep₁
    _ ≤ ‖x - xStar‖ ^ (2 : ℕ) -
          (2 * h * μ * L / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) := hstep₂
    _ = (1 - (2 * h * μ * L) / (μ + L)) * ‖x - xStar‖ ^ (2 : ℕ) := by
      ring

/-- Helper for Theorem 2.17: the one-step squared-distance contraction packages
into the owner geometric-rate bound for the whole gradient trajectory. -/
private theorem gradientMethod_sqdist_le_geometric_rate_nontrivial
    [Nontrivial E]
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (h : ℝ)
    (hh0 : 0 < h) (hh : h ≤ 2 / (μ + L))
    (x0 : E) (k : ℕ) :
    ‖gradientMethod (fun _ ↦ h) f x0 k - xStar‖ ^ (2 : ℕ) ≤
      (1 - (2 * h * μ * L) / (μ + L)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by
  let r : ℕ → ℝ := fun j ↦ ‖gradientMethod (fun _ ↦ h) f x0 j - xStar‖ ^ (2 : ℕ)
  -- Bound the owner contraction parameter by `1` so that the scalar iteration API applies.
  have hq₁ : (2 * h * μ * L) / (μ + L) ≤ 1 := by
    have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
    have hμL : μ ≤ L := hf'.mu_le_L
    have hden : 0 < μ + L := by
      nlinarith [hf'.mu_pos, hμL]
    have hstep : h * (μ + L) ≤ 2 := by
      exact (le_div_iff₀ hden).mp hh
    have hAMGM : 4 * μ * L ≤ (μ + L) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (L - μ)]
    have hbound_num : 4 * h * μ * L ≤ h * (μ + L) ^ (2 : ℕ) := by
      have hmulg := mul_le_mul_of_nonneg_left hAMGM hh0.le
      nlinarith [hmulg]
    have hbound :
        (2 * h * μ * L) / (μ + L) ≤ h * (μ + L) / 2 := by
      have h_eq₁ :
          (2 * h * μ * L) / (μ + L) = (4 * h * μ * L) / (2 * (μ + L)) := by
        have hden_ne : μ + L ≠ 0 := ne_of_gt hden
        field_simp [hden_ne]
        ring
      have h_eq₂ :
          h * (μ + L) / 2 = (h * (μ + L) ^ (2 : ℕ)) / (2 * (μ + L)) := by
        have hden_ne : μ + L ≠ 0 := ne_of_gt hden
        field_simp [hden_ne]
      have h2den_nonneg : 0 ≤ 2 * (μ + L) := by
        positivity
      calc
        (2 * h * μ * L) / (μ + L) = (4 * h * μ * L) / (2 * (μ + L)) := h_eq₁
        _ ≤ (h * (μ + L) ^ (2 : ℕ)) / (2 * (μ + L)) := by
          exact div_le_div_of_nonneg_right hbound_num h2den_nonneg
        _ = h * (μ + L) / 2 := h_eq₂.symm
    have hhalf : h * (μ + L) / 2 ≤ 1 := by
      nlinarith [hstep]
    exact le_trans hbound hhalf
  -- Rewrite the gradient recursion into the one-step contraction already proved above.
  have hstep :
      ∀ j : ℕ, r (j + 1) ≤ (1 - (2 * h * μ * L) / (μ + L)) * r j := by
    intro j
    dsimp [r]
    simpa [gradientMethod_succ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      gradientMethod_sqdist_step_le hf hxStar h hh0 hh
        (gradientMethod (fun _ ↦ h) f x0 j)
  -- The owner geometric-rate constructor now iterates the one-step bound automatically.
  have hgeom :
      HasGeometricRateOfConvergence r ((2 * h * μ * L) / (μ + L)) (r 0) := by
    refine of_step_bound hq₁ le_rfl hstep
  simpa [r, mul_comm, mul_left_comm, mul_assoc] using hgeom k

/-- Helper for Theorem 2.17: at the optimal step `2 / (μ + L)`, the generic
contraction factor simplifies to `((L - μ) / (L + μ))²`. -/
private theorem optimal_step_contraction_factor_sq
    [Nontrivial E]
    (hf : f ∈ 𝓢[μ, L]¹¹) :
    1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L) =
      (((L - μ) / (L + μ)) ^ (2 : ℕ)) := by
  have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
  have hμL : μ ≤ L := hf'.mu_le_L
  have hden : 0 < μ + L := by
    nlinarith [hf'.mu_pos, hμL]
  have hden₁ : μ + L ≠ 0 := ne_of_gt hden
  have hden₂ : L + μ ≠ 0 := by
    simpa [add_comm] using hden₁
  -- This is the scalar simplification used by both optimal-step corollaries.
  field_simp [hden₁, hden₂]
  ring

/-- Helper for Theorem 2.17: smoothness bounds the objective gap by `(L / 2)` times
the squared distance to a minimizer. -/
private theorem objective_gap_le_half_L_mul_sqdist_to_minimizer
    [Nontrivial E]
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x : E) :
    f x - f xStar ≤ (L / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
  have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
  have hupper' := hf'.upper_tangent_quadratic xStar x
  have hgrad0 : ∇ f xStar = 0 := hf'.gradient_eq_zero_of_isMinOn hxStar
  -- Apply the upper tangent inequality at the minimizer and remove the zero-gradient term.
  have hupper'' :
      f x - f xStar ≤
        inner ℝ (∇ f xStar) (x - xStar) + (L / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    nlinarith [hupper']
  simpa [hgrad0] using hupper''

/- Theorem 2.17 is split into one labeled main contraction statement and two unlabeled optimal-step
companions so that the public API stays atomic rather than packaging three conclusions into one
large conjunction. -/
/-- Theorem 2.17: if `f : E → ℝ` lies in the strongly convex smooth class `𝓢^{1,1}_{μ,L}`,
`xStar` is a minimizer of `f`, and `0 < h ≤ 2 / (μ + L)`, then the gradient-method iterates
satisfy the geometric squared-distance contraction
`‖x_k - xStar‖² ≤ (1 - 2 h μ L / (μ + L))^k ‖x₀ - xStar‖²`. -/
-- Proof sketch: combine `gradientMethod_succ` for the constant schedule `fun _ ↦ h` with the
-- owner secant inequality `IsStrongConvexSmoothObjective.pairing_lower_bound` applied to
-- `(x_k, xStar)`. Since `xStar` minimizes `f`, the owner stationarity theorem
-- `hf.gradient_eq_zero_of_isMinOn hxStar` gives `∇ f xStar = 0`; substituting this into the
-- one-step expansion of `‖x_{k+1} - xStar‖²` yields
-- a contraction factor, and the stepsize bound makes the remaining gradient term nonpositive.
-- Iterate the resulting one-step estimate over `k`.
theorem gradientMethod_sqdist_le_geometric_rate
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (h : ℝ)
    (hh0 : 0 < h) (hh : h ≤ 2 / (μ + L))
    (x0 : E) (k : ℕ) :
    ‖gradientMethod (fun _ ↦ h) f x0 k - xStar‖ ^ (2 : ℕ) ≤
      (1 - (2 * h * μ * L) / (μ + L)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by
  by_cases hE : Subsingleton E
  · have hxStar0 : xStar = x0 := hE.elim _ _
    have hxk : gradientMethod (fun _ ↦ h) f x0 k = x0 := hE.elim _ _
    simp [hxStar0, hxk]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    exact gradientMethod_sqdist_le_geometric_rate_nontrivial hf hxStar h hh0 hh x0 k

/-- With the optimal constant step size `2 / (μ + L)`, the gradient method contracts the distance
to the minimizer at the sharp linear rate `((L - μ) / (L + μ))^k`, equivalently
`((Q - 1) / (Q + 1))^k` for `Q = L / μ`. In nontrivial ambient spaces the owner hypothesis already
forces `μ ≤ L`, while the subsingleton case is tautological. -/
-- Proof sketch: specialize `gradientMethod_sqdist_le_geometric_rate` to `h = 2 / (μ + L)`,
-- simplify the contraction factor to `((L - μ) / (L + μ))²`, use the owner-derived inequality
-- `hf.mu_le_L` in the nontrivial case to identify the nonnegative square root, and note that the
-- subsingleton case is immediate.
theorem gradientMethod_dist_le_optimal_geometric_rate
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E) (k : ℕ) :
    ‖gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k - xStar‖ ≤
      ((L - μ) / (L + μ)) ^ k * ‖x0 - xStar‖ := by
  by_cases hE : Subsingleton E
  · have hxStar0 : xStar = x0 := hE.elim _ _
    have hxk : gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k = x0 := hE.elim _ _
    simp [hxStar0, hxk]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    let ρ : ℝ := (L - μ) / (L + μ)
    have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
    have hμL : μ ≤ L := hf'.mu_le_L
    have hden : 0 < μ + L := by
      nlinarith [hf'.mu_pos, hμL]
    have hh0 : 0 < 2 / (μ + L) := by
      positivity
    have hρsq :
        1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L) = ρ ^ (2 : ℕ) := by
      simpa [ρ] using optimal_step_contraction_factor_sq (E := E) (f := f) (μ := μ) (L := L) hf
    have hsq :=
      gradientMethod_sqdist_le_geometric_rate_nontrivial
        hf hxStar (2 / (μ + L)) hh0 le_rfl x0 k
    have hρ_nonneg : 0 ≤ ρ := by
      dsimp [ρ]
      simpa [add_comm] using div_nonneg (sub_nonneg.mpr hμL) hden.le
    -- Rewrite the squared-distance estimate with the optimal textbook factor `ρ²`.
    have hsq' :
        ‖gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k - xStar‖ ^ (2 : ℕ) ≤
          (ρ ^ k * ‖x0 - xStar‖) ^ (2 : ℕ) := by
      calc
        ‖gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k - xStar‖ ^ (2 : ℕ) ≤
            (1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) :=
          hsq
        _ = (ρ ^ (2 : ℕ)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by rw [hρsq]
        _ = (ρ ^ k * ‖x0 - xStar‖) ^ (2 : ℕ) := by ring_nf
    exact
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg hρ_nonneg _) (norm_nonneg _))).1 hsq'

/-- With the optimal constant step size `2 / (μ + L)`, the gradient method satisfies the linear
objective-gap estimate
`f(x_k) - f(xStar) ≤ (L / 2) * ((L - μ) / (L + μ))^(2k) * ‖x₀ - xStar‖²`, equivalently
`(L / 2) * ((Q - 1) / (Q + 1))^(2k) * ‖x₀ - xStar‖²` for `Q = L / μ`. As above, no separate
`μ ≤ L` hypothesis is needed: it is derived from `hf` off the subsingleton case. -/
-- Proof sketch: apply the owner smooth upper tangent estimate at `(xStar, x_k)`, use
-- `hf.gradient_eq_zero_of_isMinOn hxStar` to remove the linear term at `xStar`, and then
-- substitute the optimal-step squared-distance estimate obtained from
-- `gradientMethod_sqdist_le_geometric_rate`.
theorem gradientMethod_objective_gap_le_optimal_geometric_rate
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E) (k : ℕ) :
    f (gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k) - f xStar ≤
      (L / 2) * (((L - μ) / (L + μ)) ^ (2 * k)) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
  by_cases hE : Subsingleton E
  · have hxStar0 : xStar = x0 := hE.elim _ _
    have hxk : gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k = x0 := hE.elim _ _
    simp [hxStar0, hxk]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    let xk : E := gradientMethod (fun _ ↦ 2 / (μ + L)) f x0 k
    let ρ : ℝ := (L - μ) / (L + μ)
    have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
    have hμL : μ ≤ L := hf'.mu_le_L
    have hden : 0 < μ + L := by
      nlinarith [hf'.mu_pos, hμL]
    have hh0 : 0 < 2 / (μ + L) := by
      positivity
    have hL_nonneg : 0 ≤ L / 2 := by
      nlinarith [hf'.mu_pos, hμL]
    have hρsq :
        1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L) = ρ ^ (2 : ℕ) := by
      simpa [ρ] using optimal_step_contraction_factor_sq (E := E) (f := f) (μ := μ) (L := L) hf
    have hsq :=
      gradientMethod_sqdist_le_geometric_rate_nontrivial
        hf hxStar (2 / (μ + L)) hh0 le_rfl x0 k
    -- Rewrite the optimal-step squared-distance estimate into the textbook factor `ρ^(2k)`.
    have hsq' :
        ‖xk - xStar‖ ^ (2 : ℕ) ≤ ρ ^ (2 * k) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
      calc
        ‖xk - xStar‖ ^ (2 : ℕ) ≤
            (1 - (2 * (2 / (μ + L)) * μ * L) / (μ + L)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by
          simpa [xk] using hsq
        _ = (ρ ^ (2 : ℕ)) ^ k * ‖x0 - xStar‖ ^ (2 : ℕ) := by rw [hρsq]
        _ = ρ ^ (2 * k) * ‖x0 - xStar‖ ^ (2 : ℕ) := by rw [pow_mul]
    have hupper : f xk - f xStar ≤ (L / 2) * ‖xk - xStar‖ ^ (2 : ℕ) :=
      objective_gap_le_half_L_mul_sqdist_to_minimizer
        (E := E) (f := f) (μ := μ) (L := L) hf hxStar xk
    calc
      f xk - f xStar ≤ (L / 2) * ‖xk - xStar‖ ^ (2 : ℕ) := hupper
      _ ≤ (L / 2) * (ρ ^ (2 * k) * ‖x0 - xStar‖ ^ (2 : ℕ)) := by
        gcongr
      _ = (L / 2) * (ρ ^ (2 * k)) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
        ring

end
