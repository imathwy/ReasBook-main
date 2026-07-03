import Mathlib
import Mathlib.Analysis.Matrix.Order

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_4 (from Chap02) -/
universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Primary domain: first-order convex analysis on real normed spaces.

Sampled owner-style declarations in this domain:
* mathlib `ContDiffOn ℝ 1 f Q`
* mathlib `ConvexOn ℝ Q f`
* mathlib `ConcaveOn ℝ Q f`
* Chapter 2 `ConvexC1SeminormSmoothOn p L Q f`, which later specializes the present owner
  abstraction on Euclidean spaces by adding gradient-Lipschitz control

Best owner abstraction:
* primitive core: `ContDiffOn ℝ 1 f Q` together with `ConvexOn ℝ Q f`
* bridge/view: the concave side via the canonical sign change `f ↦ -f`

Source/core/bridge triage:
* source-facing: the textbook class `𝓕¹(Q)`
* core/canonical: the owner pair `ContDiffOn ℝ 1 f Q` and `ConvexOn ℝ Q f`
* bridge/view: the concave counterpart `ConcaveC1On Q f`, derived from `ConvexC1On Q (-f)`

Primitive data:
* the feasible set `Q`
* the objective `f`
* `ContDiffOn ℝ 1 f Q`
* `ConvexOn ℝ Q f`

Derived API:
* projections `convexC1On_contDiffOn` and `convexC1On_convexOn`
* affine-precomposition closure via `ConvexC1On.comp_continuousAffineMap` and its Euclidean
  specialization `ConvexC1On.comp_affineMap`
* the concave view `ConcaveC1On` and its owner projections
-/

/-- Definition 2.4: a function on a convex set `Q` belongs to `𝓕¹(Q)` when it is
continuously differentiable on `Q` and is convex there in the canonical owner sense
`ConvexOn ℝ Q f`. Supporting-hyperplane arguments should use the owner theorem
`ConvexOn.lower_tangent_plane` through `convexC1On_convexOn hf`, so no duplicate wrapper theorem
is kept here. -/
abbrev ConvexC1On (Q : Set E) (f : E → ℝ) : Prop :=
  ContDiffOn ℝ 1 f Q ∧ ConvexOn ℝ Q f

scoped[ConvexC1] notation "𝓕¹(" Q ")" => setOf (ConvexC1On Q)
open scoped ConvexC1

/-- A function on `Q` is `C¹` concave when its negative belongs to `ConvexC1On Q`. This keeps
the convex owner pair `ContDiffOn ℝ 1` plus `ConvexOn` as primitive data and treats concavity as
the canonical sign-reversed view. -/
abbrev ConcaveC1On (Q : Set E) (f : E → ℝ) : Prop :=
  ConvexC1On Q (-f)

variable {Q : Set E} {f : E → ℝ}

/-- The textbook class notation `𝓕¹(Q)` is the source-facing set view of the owner predicate
`ConvexC1On Q`. -/
theorem mem_F1_iff : f ∈ 𝓕¹(Q) ↔ ConvexC1On Q f :=
  Iff.rfl

/-- Membership in `ConvexC1On Q f` includes `C¹` regularity on `Q`. -/
theorem convexC1On_contDiffOn (hf : ConvexC1On Q f) : ContDiffOn ℝ 1 f Q :=
  hf.1

/-- Membership in `ConvexC1On Q f` includes convexity on `Q`. -/
theorem convexC1On_convexOn (hf : ConvexC1On Q f) : ConvexOn ℝ Q f :=
  hf.2

/-- Nonnegative scalar multiplication preserves membership in `ConvexC1On`. -/
theorem ConvexC1On.smul
    {Q : Set E} {f : E → ℝ} (hf : ConvexC1On Q f) {α : ℝ} (hα : 0 ≤ α) :
    ConvexC1On Q (α • f) := by
  refine ⟨?_, ?_⟩
  · simpa [Pi.smul_apply] using (convexC1On_contDiffOn hf).const_smul α
  · simpa [Pi.smul_apply] using (convexC1On_convexOn hf).smul hα

/-- Addition preserves membership in `ConvexC1On`. -/
theorem ConvexC1On.add
    {Q : Set E} {f g : E → ℝ} (hf : ConvexC1On Q f) (hg : ConvexC1On Q g) :
    ConvexC1On Q (f + g) := by
  refine ⟨?_, ?_⟩
  · simpa using (convexC1On_contDiffOn hf).add (convexC1On_contDiffOn hg)
  · simpa using (convexC1On_convexOn hf).add (convexC1On_convexOn hg)

/-- Nonnegative linear combinations preserve membership in `ConvexC1On`. -/
theorem ConvexC1On.nonneg_combo
    {Q : Set E} {f₁ f₂ : E → ℝ} (hf₁ : ConvexC1On Q f₁) (hf₂ : ConvexC1On Q f₂)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ConvexC1On Q (α • f₁ + β • f₂) := by
  exact (hf₁.smul hα).add (hf₂.smul hβ)

/-- Precomposing a `C¹` convex function with a continuous affine map preserves membership in
`ConvexC1On`. This is the canonical owner-level precomposition theorem; Euclidean affine-map
specializations should be derived from it. -/
theorem ConvexC1On.comp_continuousAffineMap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Q : Set E} {f : E → ℝ} (hf : ConvexC1On Q f)
    (g : F →ᴬ[ℝ] E) :
    ConvexC1On (g ⁻¹' Q) (f ∘ g) := by
  refine ⟨?_, ?_⟩
  · exact (convexC1On_contDiffOn hf).comp g.contDiff.contDiffOn (fun _ hx ↦ hx)
  · simpa using (convexC1On_convexOn hf).comp_affineMap (g : F →ᵃ[ℝ] E)

/-- In Euclidean spaces, affine precomposition preserves membership in `ConvexC1On`. This is the
source-facing finite-dimensional specialization of `ConvexC1On.comp_continuousAffineMap`. -/
theorem ConvexC1On.comp_affineMap
    {m n : ℕ}
    {Q : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : ConvexC1On Q f)
    (g : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ConvexC1On (g ⁻¹' Q) (f ∘ g) := by
  simpa using hf.comp_continuousAffineMap ⟨g, g.continuous_of_finiteDimensional⟩

/-- Membership in `ConcaveC1On Q f` includes `C¹` regularity on `Q`. -/
theorem concaveC1On_contDiffOn (hf : ConcaveC1On Q f) : ContDiffOn ℝ 1 f Q := by
  simpa using (convexC1On_contDiffOn hf).neg

/-- Membership in `ConcaveC1On Q f` includes concavity on `Q`. -/
theorem concaveC1On_concaveOn (hf : ConcaveC1On Q f) : ConcaveOn ℝ Q f := by
  simpa using (convexC1On_convexOn hf).neg

/-! ### Lemma_2_4 (from Chap02) -/
noncomputable section

/- Primary domain: quadratic norm inequalities over a seminormed additive group.

Sampled owner-style declarations in this domain:
- `sq_nonneg`, the exact algebraic owner for the weighted quadratic inequality;
- `norm_sub_le`, the triangle inequality in subtraction form;
- `sq_le_sq₀`, the canonical passage from a nonnegative inequality to the squared inequality;
- `mul_le_mul_of_nonneg_left`, the owner monotonicity lemma for nonnegative scalar multiplication;

Best owner abstraction:
- there is no higher project owner object here; the canonical owners are the four mathlib scalar
  and norm inequalities above, and this file should remain a thin source-facing bridge.

Source/core/bridge triage:
- source-facing: the two-step weighted quadratic chain from the textbook lemma;
- core/canonical: the four owner lemmas above;
- bridge/view: specializing those owner inequalities to the weights `α` and `1 - α`.

Primitive data:
- a seminormed additive group `E`,
- points `x y : E`,
- a weight `α : ℝ`.

Derived API:
- the two atomic weighted quadratic inequalities below;
- the chained quadratic bound of Lemma 2.4, recovered as a thin wrapper.
-/

variable {E : Type*} [SeminormedAddGroup E]

/-- For every real weight `α`, the weighted square of `‖x‖ + ‖y‖` is bounded above by the
corresponding affine combination of `‖x‖²` and `‖y‖²`. -/
-- Proof sketch: the difference between the right-hand side and the left-hand side is the exact
-- square `(α * ‖x‖ - (1 - α) * ‖y‖)^2`.
theorem weighted_norm_sum_sq_le_convex_combination_norm_sq
    (x y : E) (α : ℝ) :
    α * (1 - α) * (‖x‖ + ‖y‖) ^ 2 ≤ α * ‖x‖ ^ 2 + (1 - α) * ‖y‖ ^ 2 := by
  nlinarith [sq_nonneg (α * ‖x‖ - (1 - α) * ‖y‖)]

/-- For `α ∈ [0, 1]`, the weighted squared distance `‖x - y‖²` is bounded above by the weighted
squared sum bound coming from the triangle inequality. -/
-- Proof sketch: square `norm_sub_le x y` and multiply by the nonnegative factor
-- `α * (1 - α)`.
theorem weighted_norm_sub_sq_le_weighted_norm_sum_sq
    (x y : E) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    α * (1 - α) * ‖x - y‖ ^ 2 ≤ α * (1 - α) * (‖x‖ + ‖y‖) ^ 2 := by
  have hα0 : 0 ≤ α := hα.1
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα.2
  have hsq : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
      (norm_sub_le x y)
  exact mul_le_mul_of_nonneg_left hsq (mul_nonneg hα0 h1α)

/-- Lemma 2.4: for `α ∈ [0, 1]`, the weighted squared distance is bounded by the intermediate
weighted square of `‖x‖ + ‖y‖`, which is bounded by the convex combination of `‖x‖²` and
`‖y‖²`. -/
theorem convex_combination_norm_sq_bounds
    (x y : E) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    α * (1 - α) * ‖x - y‖ ^ 2 ≤ α * (1 - α) * (‖x‖ + ‖y‖) ^ 2 ∧
      α * (1 - α) * (‖x‖ + ‖y‖) ^ 2 ≤ α * ‖x‖ ^ 2 + (1 - α) * ‖y‖ ^ 2 := by
  exact ⟨weighted_norm_sub_sq_le_weighted_norm_sum_sq x y α hα,
    weighted_norm_sum_sq_le_convex_combination_norm_sq x y α⟩

end

/-! ### Proposition_2_4 (from Chap02) -/
open scoped Gradient MatrixOrder StrongConvexSmooth
open Matrix

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Proposition 2.4 lies in finite-dimensional quadratic optimization on `ℝⁿ`.

Sampled owner-style declarations:
* `quadraticObjective` and `symmetric_quadratic_contDiff_and_gradient_lipschitz`
* `IsStrongConvexSmoothObjective`
* `Matrix.PosSemidef.convexOn_quadraticObjective`
* `strongConvexOn_iff_convex`

Best owner abstraction:
* `IsStrongConvexSmoothObjective μ L` for the objective class

Primitive data:
* the quadratic data `α`, `a`, `A`
* the matrix Loewner bounds `μ I ≤ A ≤ L I`

Derived API:
* symmetry of `A`, recovered from the Loewner lower bound via `Matrix.PosSemidef`
* `C¹` regularity and gradient Lipschitzness from
  `symmetric_quadratic_contDiff_and_gradient_lipschitz`
* `μ`-strong convexity by rewriting
  `quadraticObjective α a A - (μ / 2) * ‖·‖²` as the shifted quadratic
  `quadraticObjective α a (A - μ • 1)` and applying `strongConvexOn_iff_convex`

Source/core/bridge triage:
* source-facing: a quadratic objective satisfying the textbook Hessian bounds
* core/canonical: `quadraticObjective`, `StrongConvexOn`, `IsStrongConvexSmoothObjective`
* bridge/view: positivity of `A - μ • 1` and the induced operator-order estimate on
  `A.toEuclideanLin`
-/

/-- Proposition 2.4: if `A` satisfies `μ I ≤ A ≤ L I` with `0 < μ`, then the canonical quadratic
objective `quadraticObjective α a A` belongs to the source-facing class `𝓢[μ, L]¹¹`. -/
-- Proof sketch: use the owner definition `quadraticObjective α a A` with constant Hessian
-- `A.toEuclideanLin`. Proposition 1.5.7 supplies the `C¹` and gradient-Lipschitz parts, while
-- the lower matrix bound makes `A - μ I` positive semidefinite, so
-- `strongConvexOn_iff_convex` reduces `μ`-strong convexity of `quadraticObjective α a A` to
-- convexity of the shifted quadratic `quadraticObjective α a (A - μ I)`. The Loewner lower bound
-- already forces symmetry of `A`, so that input is derived rather than primitive. The positivity
-- hypothesis `0 < μ` matches the chapter owner predicate `IsStrongConvexSmoothObjective`, and the
-- theorem surface is the chapter notation `𝓢[μ, L]¹¹`.
theorem quadraticObjective_mem_S11
    (μ L α : ℝ) (a : E) (A : Mat)
    (hμ : 0 < μ)
    (hμA : μ • (1 : Mat) ≤ A)
    (hAL : A ≤ L • (1 : Mat)) :
    quadraticObjective α a A ∈ 𝓢[μ, L]¹¹ := by
  let B : E →L[ℝ] E := A.toEuclideanLin.toContinuousLinearMap
  have hshift : (A - μ • (1 : Mat)).PosSemidef := by
    simpa [Matrix.le_iff] using hμA
  have hA : A.IsSymm := by
    have hshift_symm : (A - μ • (1 : Mat)).IsSymm := by
      simpa [Matrix.IsHermitian, Matrix.IsSymm] using hshift.isHermitian
    rw [← sub_add_cancel A (μ • (1 : Mat))]
    exact hshift_symm.add (Matrix.isSymm_one.smul μ)
  obtain ⟨hcontDiff, hgradLip⟩ :=
    symmetric_quadratic_contDiff_and_gradient_lipschitz α a A hA
  have hshifted_eq :
      (fun x : E ↦ quadraticObjective α a A x - (μ / 2) * ‖x‖ ^ (2 : ℕ)) =
        quadraticObjective α a (A - μ • (1 : Mat)) := by
    ext x
    simp [quadraticObjective, inner_sub_left, inner_smul_left]
    ring
  have hstrong : StrongConvexOn Set.univ μ (quadraticObjective α a A) := by
    rw [strongConvexOn_iff_convex, hshifted_eq]
    exact hshift.convexOn_quadraticObjective α a
  have hshift_toEuclideanLin :
      (A - μ • (1 : Mat)).toEuclideanLin =
        (A.toEuclideanLin : E →ₗ[ℝ] E) - μ • LinearMap.id := by
    ext x i
    simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hμB : μ • (1 : E →L[ℝ] E) ≤ B := by
    have hpos :
        ((A.toEuclideanLin : E →ₗ[ℝ] E) - μ • LinearMap.id).IsPositive := by
      rw [← hshift_toEuclideanLin]
      exact Matrix.isPositive_toEuclideanLin_iff.2 hshift
    rw [ContinuousLinearMap.le_def]
    change ((B : E →ₗ[ℝ] E) - μ • LinearMap.id).IsPositive
    simpa [B] using hpos
  have hB_nonneg : (0 : E →L[ℝ] E) ≤ B := by
    have hμI_nonneg : (0 : E →L[ℝ] E) ≤ μ • (1 : E →L[ℝ] E) := by
      rw [ContinuousLinearMap.nonneg_iff_isPositive]
      simpa using ContinuousLinearMap.isPositive_one.smul_of_nonneg hμ.le
    exact le_trans hμI_nonneg hμB
  have hupper_toEuclideanLin :
      (L • (1 : Mat) - A).toEuclideanLin =
        (L : ℝ) • LinearMap.id - (A.toEuclideanLin : E →ₗ[ℝ] E) := by
    ext x i
    simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hB_le : B ≤ L • (1 : E →L[ℝ] E) := by
    have hLA_pos : (L • (1 : Mat) - A).PosSemidef := by
      simpa [Matrix.le_iff] using hAL
    have hpos :
        ((L : ℝ) • LinearMap.id - (A.toEuclideanLin : E →ₗ[ℝ] E)).IsPositive := by
      rw [← hupper_toEuclideanLin]
      exact Matrix.isPositive_toEuclideanLin_iff.2 hLA_pos
    rw [ContinuousLinearMap.le_def]
    change ((L : ℝ) • LinearMap.id - (B : E →ₗ[ℝ] E)).IsPositive
    simpa [B] using hpos
  have hcore : IsStrongConvexSmoothObjective μ L (quadraticObjective α a A) := by
    refine ⟨hμ, hcontDiff, hstrong, ?_⟩
    intro x y
    by_cases hxy : x = y
    · simp [hxy]
    · have hL_nonneg : 0 ≤ L := by
        have hLI_nonneg : (0 : E →L[ℝ] E) ≤ L • (1 : E →L[ℝ] E) := le_trans hB_nonneg hB_le
        have hposLI : (L • (1 : E →L[ℝ] E)).IsPositive :=
          (ContinuousLinearMap.nonneg_iff_isPositive _).1 hLI_nonneg
        have hquad : 0 ≤ inner ℝ ((L • (1 : E →L[ℝ] E)) (x - y)) (x - y) :=
          hposLI.inner_nonneg_left (x - y)
        have hquad' : 0 ≤ L * ‖x - y‖ ^ (2 : ℕ) := by
          simpa [inner_smul_left, inner_self_eq_norm_sq_to_K] using hquad
        exact nonneg_of_mul_nonneg_left hquad'
          (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) 2)
      have hnorm : ‖B‖ ≤ L := by
        have hsymm : (B : E →ₗ[ℝ] E).IsSymmetric := by
          have hAherm : A.IsHermitian := by
            simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA
          have hsymm0 : A.toEuclideanLin.IsSymmetric :=
            Matrix.isSymmetric_toEuclideanLin_iff.mpr hAherm
          simpa [B] using hsymm0
        have hbound : ∀ z : E, |B.rayleighQuotient z| ≤ L := by
          intro z
          by_cases hz : z = 0
          · simpa [hz] using hL_nonneg
          · have hz_norm_sq_pos : 0 < ‖z‖ ^ (2 : ℕ) := by
              positivity
            have hLI_pos : (L • (1 : E →L[ℝ] E) - B).IsPositive := by
              simpa [ContinuousLinearMap.le_def] using hB_le
            have hquad : inner ℝ (B z) z ≤ L * ‖z‖ ^ (2 : ℕ) := by
              have hnonneg := hLI_pos.inner_nonneg_left z
              simpa [inner_smul_left, inner_sub_left, inner_self_eq_norm_sq_to_K] using hnonneg
            have hnonneg : 0 ≤ inner ℝ (B z) z :=
              ((ContinuousLinearMap.nonneg_iff_isPositive _).1 hB_nonneg).inner_nonneg_left z
            rw [ContinuousLinearMap.rayleighQuotient, abs_of_nonneg]
            · exact (div_le_iff₀ hz_norm_sq_pos).2 hquad
            · exact div_nonneg hnonneg hz_norm_sq_pos.le
        rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient B hsymm]
        exact ciSup_le hbound
      have hnnorm : (‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖₊ : ℝ) ≤ L := by
        change (‖B‖₊ : ℝ) ≤ L
        exact_mod_cast hnorm
      exact (hgradLip.norm_sub_le x y).trans <|
        mul_le_mul_of_nonneg_right hnnorm (norm_nonneg _)
  exact mem_S11_iff.mpr hcore

/-! ### Text_2_4 (from Chap02) -/
noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type v} [Fintype ι] [Nonempty ι]
variable {m : ℕ} {μ L : ℝ}

namespace SmoothMinimaxProblem

/- Text 2.4 also yields the canonical owner inequalities for a smooth minimax problem and its
quadratically regularized affine models.

Sampled owner declarations before drafting:
* `SmoothMinimaxProblem` in `Definition_2_38.lean`, which owns the feasible set and the max-type
  objective;
* `SmoothMinimaxProblem.affineApproximation` in `Definition_2_38.lean`, which owns the affine
  max-type model at `xBar`;
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17.lean`, which adds the centered
  quadratic penalty to that affine model;
* `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` in
  `Definition_2_47.lean`, which shows that the constrained source item factors through this owner.

Best owner abstraction:
* `problem : SmoothMinimaxProblem E ι μ L`.

Primitive data:
* the minimax owner `problem`;
* the base point `xBar`.

Derived API:
* the `μ`- and `L`-regularized affine models at `xBar`;
* the constrained optimal value `sInf (problem '' problem.feasibleSet)`;
* the regularized model values obtained by taking infima over `problem.feasibleSet`.

The four comparison theorems below are the clean canonical owner form of the sandwich estimates in
Text 2.4. They are kept as separate atomic statements because the source gives distinct pointwise
and optimal-value bounds, and later files reuse these owner inequalities directly. -/

section

variable (problem : SmoothMinimaxProblem E ι μ L) (xBar : E)

local notation "modelValue" =>
  fun γ ↦
    sInf
      ((quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar) ''
        problem.feasibleSet)

local notation "valueFunction" =>
  sInf (problem '' problem.feasibleSet)

/-- Helper for Text 2.4: the affine approximation of a smooth minimax problem is continuous,
because it is the finite maximum of continuous first-order Taylor models. -/
theorem affineApproximation_continuous :
    Continuous (problem.affineApproximation xBar) := by
  classical
  -- Each first-order Taylor model is affine, hence continuous, and finite maxima preserve continuity.
  change Continuous (maxTypeAffineApproximation problem.components xBar)
  have hcont :
      Continuous
        (fun x : E ↦
          Finset.univ.sup' Finset.univ_nonempty
            (fun i : ι ↦ firstOrderTaylorModelAt (problem.components i) xBar x)) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty fun i _ ↦ by
      simpa [firstOrderTaylorModelAt_apply] using
        continuous_const.add
          ((innerSL ℝ (gradient (problem.components i) xBar)).continuous.comp
            (continuous_id.sub continuous_const))
  simpa [maxTypeAffineApproximation_apply_firstOrderTaylorModelAt] using hcont

/-- Helper for Text 2.4: the quadratically regularized affine approximation is continuous on the
ambient space. -/
theorem regularizedAffineApproximation_continuous
    (γ : ℝ) :
    Continuous
      (quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar) := by
  -- Add the continuous quadratic penalty to the continuous affine max-type model.
  simpa [quadraticallyRegularizedObjective_apply] using
    (problem.affineApproximation_continuous xBar).add
      (continuous_const.mul (((continuous_id.sub continuous_const).norm).pow (2 : ℕ)))

/-- Helper for Text 2.4: a positive quadratic regularization makes the affine model bounded below
on the feasible set. -/
theorem regularizedAffineApproximation_image_bddBelow
    (γ : NNRealˣ) :
    BddBelow
      ((quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar) ''
        problem.feasibleSet) := by
  classical
  let i0 : ι := Classical.choice inferInstance
  let g0 : E := gradient (problem.components i0) xBar
  let c : ℝ := problem.components i0 xBar - ‖g0‖ ^ (2 : ℕ) / (2 * (γ : ℝ))
  have hγ : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  refine ⟨c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hcomponent_le :
      firstOrderTaylorModelAt (problem.components i0) xBar x ≤
        problem.affineApproximation xBar x := by
    -- One Taylor component is bounded above by the finite maximum defining the affine model.
    rw [SmoothMinimaxProblem.affineApproximation, maxTypeAffineApproximation_apply_firstOrderTaylorModelAt]
    exact Finset.le_sup' (fun j : ι ↦ firstOrderTaylorModelAt (problem.components j) xBar x)
      (by simp)
  have hquad :
      -(‖g0‖ ^ (2 : ℕ)) / (2 * (γ : ℝ)) ≤
        inner ℝ g0 (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) :=
    inner_add_quadratic_lower_bound (γ : ℝ) hγ g0 (x - xBar)
  have hlower :
      c ≤
        quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar x := by
    -- Lower-bound the regularized model by one affine component plus the positive quadratic term.
    have hbase_raw :
        problem.components i0 xBar + -(‖g0‖ ^ (2 : ℕ)) / (2 * (γ : ℝ)) ≤
          problem.components i0 xBar +
            (inner ℝ g0 (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_left hquad (problem.components i0 xBar)
    have hbase :
        c ≤
          problem.components i0 xBar +
            inner ℝ g0 (x - xBar) +
            ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
      -- Route correction: normalize the added lower bound algebraically before comparing with the
      -- affine Taylor component.
      calc
        c = problem.components i0 xBar + -(‖g0‖ ^ (2 : ℕ)) / (2 * (γ : ℝ)) := by
          dsimp [c]
          ring
        _ ≤
            problem.components i0 xBar +
              (inner ℝ g0 (x - xBar) + ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ)) := hbase_raw
        _ =
            problem.components i0 xBar +
              inner ℝ g0 (x - xBar) +
              ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
                ring
    calc
      c ≤
          problem.components i0 xBar +
            inner ℝ g0 (x - xBar) +
            ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := hbase
      _ =
          firstOrderTaylorModelAt (problem.components i0) xBar x +
            ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
              simp [g0]
      _ ≤
          problem.affineApproximation xBar x +
            ((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_right hcomponent_le (((γ : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ))
      _ =
          quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar x := by
            simp [quadraticallyRegularizedObjective_apply]
  exact hlower

/-- Helper for Text 2.4: a positive regularized affine model of a smooth minimax problem has a
unique feasible minimizer. -/
theorem existsUnique_isMinOn_regularizedAffineApproximation
    (γ : NNRealˣ) :
    ∃! xPlus : E,
      xPlus ∈ problem.feasibleSet ∧
        IsMinOn
          (quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar)
          problem.feasibleSet
          xPlus := by
  let regularizedModel :=
    quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar
  have hγ : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  have hstrong_univ :
      StrongConvexOn Set.univ (γ : ℝ) regularizedModel := by
    -- The centered quadratic term provides the strong convexity modulus `γ`.
    simpa [regularizedModel, SmoothMinimaxProblem.affineApproximation] using
      regularizedMaxTypeObjective_strongConvexOn_univ problem.components xBar γ
  have hstrong :
      StrongConvexOn problem.feasibleSet (γ : ℝ) regularizedModel := by
    -- Restrict the ambient strong-convexity estimate to the feasible set.
    rw [strongConvexOn_iff_convex] at hstrong_univ ⊢
    exact hstrong_univ.subset (by simp) problem.feasible_convex
  obtain ⟨xPlus, hxPlus, hmin⟩ :=
    exists_isMinOn_of_isClosed_of_complete_of_bddBelow
      problem.feasible_closed
      problem.feasible_nonempty
      (problem.regularizedAffineApproximation_continuous xBar (γ : ℝ)).continuousOn
      hstrong
      hγ
      (problem.regularizedAffineApproximation_image_bddBelow xBar γ)
  refine ⟨xPlus, ⟨hxPlus, hmin⟩, ?_⟩
  intro y hy
  -- Strict convexity upgrades existence to uniqueness of the feasible minimizer.
  exact
    (hstrong.strictConvexOn hγ).eq_of_isMinOn
      hy.2
      hmin
      hy.1
      hxPlus

/-- Helper for Text 2.4: an attained minimizer of the regularized affine model realizes the real
infimum `modelValue`. -/
lemma regularizedModelValue_eq_of_isMinOn
    {γ : ℝ} {x : E}
    (hx : x ∈ problem.feasibleSet)
    (hmin :
      IsMinOn
        (quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar)
        problem.feasibleSet
        x) :
    modelValue γ =
      quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar x := by
  let regularizedModel :=
    quadraticallyRegularizedObjective (problem.affineApproximation xBar) γ xBar
  have hglb : IsGLB (regularizedModel '' problem.feasibleSet) (regularizedModel x) :=
    hmin.isGLB hx
  -- The minimizing value is exactly the infimum of the model-image set.
  change sInf (regularizedModel '' problem.feasibleSet) = regularizedModel x
  simpa using hglb.csInf_eq ⟨regularizedModel x, ⟨x, hx, rfl⟩⟩

/-- Text 2.4 (2): the `μ`-regularized affine model at `xBar` is a global lower quadratic model
for the minimax objective. -/
-- Proof sketch: apply the lower tangent quadratic bound to each component of the minimax family,
-- pass to the finite maximum defining `problem`, and rewrite the resulting affine model as
-- `problem.affineApproximation xBar`.
theorem lowerRegularizedModel_le_objective
    (x : E) :
    quadraticallyRegularizedObjective (problem.affineApproximation xBar) μ xBar x ≤
      problem x := by
  -- Rewrite the owner lower quadratic bound into the regularized affine-model notation.
  simpa [quadraticallyRegularizedObjective_apply, SmoothMinimaxProblem.affineApproximation,
    SmoothMinimaxProblem.objective, ge_iff_le] using
    (maxTypeObjective_quadratic_bounds_of_components_mem
      problem.components μ L problem.components_mem x xBar).1

/-- Text 2.4 (3): the minimax objective is bounded above by the `L`-regularized affine model at
`xBar`. -/
-- Proof sketch: apply the upper tangent quadratic bound to each component of the minimax family,
-- pass to the finite maximum defining `problem`, and rewrite the resulting affine model as
-- `problem.affineApproximation xBar`.
theorem objective_le_upperRegularizedModel
    (x : E) :
    problem x ≤
      quadraticallyRegularizedObjective (problem.affineApproximation xBar) L xBar x := by
  -- Rewrite the owner upper quadratic bound into the regularized affine-model notation.
  simpa [quadraticallyRegularizedObjective_apply, SmoothMinimaxProblem.affineApproximation,
    SmoothMinimaxProblem.objective] using
    (maxTypeObjective_quadratic_bounds_of_components_mem
      problem.components μ L problem.components_mem x xBar).2

/-- Text 2.4 (4): the optimal value of the `μ`-regularized affine model is bounded above by the
optimal value of the minimax objective. -/
-- Proof sketch: apply `lowerRegularizedModel_le_objective` pointwise on `problem.feasibleSet`,
-- then pass to infima over that feasible set using existence and uniqueness of the minimizer of
-- `problem`.
theorem lowerRegularizedModelValue_le_optimalValue
    :
    modelValue μ ≤ valueFunction := by
  classical
  let i0 : ι := Classical.choice inferInstance
  have hμ_pos : 0 < μ := (mem_S11_iff.mp (problem.components_mem i0)).mu_pos
  let γμ : NNRealˣ :=
    Units.mk0 (Real.toNNReal μ) (ne_of_gt (by rwa [Real.toNNReal_pos]))
  have hγμ : (γμ : ℝ) = μ := by
    simp [γμ, Real.toNNReal_of_nonneg hμ_pos.le]
  obtain ⟨xμ, hxμ, hminμ_units⟩ :=
    ExistsUnique.exists (problem.existsUnique_isMinOn_regularizedAffineApproximation xBar γμ)
  have hminμ :
      IsMinOn
        (quadraticallyRegularizedObjective (problem.affineApproximation xBar) μ xBar)
        problem.feasibleSet
        xμ := by
    -- Rewrite the unit-valued curvature back to the scalar `μ`.
    simpa [hγμ] using hminμ_units
  have hmodel_eq :
      modelValue μ =
        quadraticallyRegularizedObjective (problem.affineApproximation xBar) μ xBar xμ := by
    exact regularizedModelValue_eq_of_isMinOn (problem := problem) (xBar := xBar) hxμ hminμ
  have hobjective_nonempty : (problem '' problem.feasibleSet).Nonempty := by
    rcases problem.feasible_nonempty with ⟨x, hx⟩
    exact ⟨problem x, ⟨x, hx, rfl⟩⟩
  rw [hmodel_eq]
  rw [isMinOn_iff] at hminμ
  refine le_csInf hobjective_nonempty ?_
  rintro _ ⟨x, hx, rfl⟩
  -- Compare the attained lower model value with each feasible objective value.
  exact le_trans (hminμ x hx) (problem.lowerRegularizedModel_le_objective xBar x)

/-- Text 2.4 (5): the optimal value of the minimax objective is bounded above by the optimal value
of the `L`-regularized affine model. -/
-- Proof sketch: apply `objective_le_upperRegularizedModel` pointwise on `problem.feasibleSet`,
-- then pass to infima over that feasible set using existence and uniqueness of the minimizer of
-- `problem`.
theorem optimalValue_le_upperRegularizedModelValue
    :
    valueFunction ≤ modelValue L := by
  have hupper_nonempty :
      ((quadraticallyRegularizedObjective (problem.affineApproximation xBar) L xBar) ''
        problem.feasibleSet).Nonempty := by
    rcases problem.feasible_nonempty with ⟨x, hx⟩
    exact ⟨_, ⟨x, hx, rfl⟩⟩
  refine le_csInf hupper_nonempty ?_
  rintro _ ⟨x, hx, rfl⟩
  -- Bound the optimal value by each feasible objective value, then by the upper regularized model.
  exact le_trans
    (csInf_le (problem.objective_image_bddBelow) ⟨x, hx, rfl⟩)
    (problem.objective_le_upperRegularizedModel xBar x)

end

end SmoothMinimaxProblem

namespace SmoothFunctionalConstraintsMinimizationProblem

/- Text 2.4 lies in the constrained smooth minimax bridge/view domain for Chapter 2.

Sampled owner declarations before drafting:
* `SmoothFunctionalConstraintsMinimizationProblem` in `Definition_2_44.lean`, which owns the
  ambient set `Q`, the objective `f₀`, and the constraint family `fᵢ`;
* `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` in
  `Definition_2_47.lean`, which is the fixed-`t` bridge to the canonical owner
  `SmoothMinimaxProblem`;
* `SmoothMinimaxProblem.affineApproximation` in `Definition_2_38.lean`, which owns the affine
  max-type local model;
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17.lean`, which owns the centered
  quadratic regularization of that affine model.

Best owner abstraction:
* source-facing: the constrained exact-step subproblem for the fixed-`t` bridge problem;
* core/canonical: the owner regularized affine model
  `quadraticallyRegularizedObjective
    ((problem.toParametricSmoothMinimaxProblem t).affineApproximation xBar)
    γ
    xBar`;
* bridge/view: `problem.toParametricSmoothMinimaxProblem t`.

Primitive data:
* the constrained problem `problem`;
* the scalar parameter `t`;
* the base point `xBar`;
* the regularization parameter `γ`.

Derived API:
* existence and uniqueness of the constrained exact step for the fixed-`t` regularized affine
  model.

The source-facing constrained statement is therefore kept on the
`toParametricSmoothMinimaxProblem` bridge rather than by introducing a second chosen-point owner
or an existential wrapper around the exact step. -/

section

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
variable (t : ℝ) (xBar : E)

/-- Text 2.4 (1): for every fixed parameter `t` and every positive regularization parameter `γ`,
the quadratically regularized affine model of the fixed-`t` parametric problem has a unique
minimizer on the ambient set `Q`; equivalently, the constrained gradient mapping is well defined.
-/
-- Proof sketch: pass to the fixed-`t` smooth minimax owner, apply the owner existence/uniqueness
-- theorem for the regularized affine model, and rewrite the feasible set back to `Q`.
theorem existsUnique_isMinOn_regularizedAffineApproximation
    (γ : NNRealˣ) :
    ∃! xPlus : E,
      xPlus ∈ problem.ambientSet ∧
        IsMinOn
          (quadraticallyRegularizedObjective
            ((problem.toParametricSmoothMinimaxProblem t).affineApproximation xBar)
            γ
            xBar)
          problem.ambientSet
          xPlus := by
  -- Reuse the fixed-`t` smooth minimax owner theorem and rewrite its feasible set back to `Q`.
  simpa using
    SmoothMinimaxProblem.existsUnique_isMinOn_regularizedAffineApproximation
      (problem := problem.toParametricSmoothMinimaxProblem t)
      (xBar := xBar)
      γ

end

end SmoothFunctionalConstraintsMinimizationProblem

/-! ### Theorem_2_4 (from Chap02) -/
open InnerProductSpace
noncomputable section

open scoped Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: twice continuously differentiable convexity criteria on open convex subsets of
real Hilbert spaces.

Sampled owner-style declarations:
* mathlib `ConvexOn`
* mathlib `(hessian f x).IsPositive`
* mathlib `ContinuousLinearMap.isPositive_iff`
* Chapter 1 `fderiv_gradient_isSymmetric_of_contDiffAt`
* Chapter 2 `ConvexOn.gradient_monotone`

Best owner abstraction:
* source-facing convexity owner: `ConvexOn ℝ Q f`
* canonical Hessian object at `x`: `hessian f x`

Source/core/bridge triage:
* source-facing: convexity of `f` on the open convex set `Q`
* core/canonical: pointwise positivity of the Hessian operator
* bridge/view: nonnegativity of the associated quadratic form

Primitive data:
* the feasible set `Q`
* the objective `f`
* openness and convexity of `Q`
* `C²` regularity `ContDiffOn ℝ 2 f Q`

Derived API:
* `convexOn_iff_hessian_quadratic_form_nonneg`, obtained as the quadratic-form bridge from the
  canonical Hessian owner
* `convexOn_iff_hessian_isPositive`

The public theorem therefore stays centered on `ConvexOn ℝ Q f` and the owner property
`(hessian f x).IsPositive`. The quadratic-form statement is kept only as
the minimal bridge needed by downstream Hessian-bound files, and the textbook `ℝⁿ` statement is a
direct specialization. -/

section

variable {Q : Set E} {f : E → ℝ}

/-- Helper for Theorem 2.4: on an open set, the within-gradient agrees with the ambient
gradient. -/
private theorem gradientWithin_eq_gradient_of_mem_open
    (hQ_open : IsOpen Q) (hf_C1 : ContDiffOn ℝ 1 f Q) {x : E} (hx : x ∈ Q) :
    gradientWithin f Q x = ∇ f x := by
  -- On an open set, the within-derivative and the ambient derivative agree at differentiable
  -- points, so the corresponding gradients agree as well.
  rw [gradientWithin, gradient]
  congr
  exact fderivWithin_eq_fderiv (hQ_open.uniqueDiffWithinAt hx)
    ((hf_C1.contDiffAt (hQ_open.mem_nhds hx)).differentiableAt_one)

/-- Helper for Theorem 2.4: positivity of the Hessian operator is equivalent to nonnegativity of
its quadratic form at a point of the domain. -/
private theorem hessian_isPositive_iff_quadratic_form_nonneg_at
    (hQ_open : IsOpen Q) (hf_C2 : ContDiffOn ℝ 2 f Q) {x : E} (hx : x ∈ Q) :
    (hessian f x).IsPositive ↔
      ∀ s : E, 0 ≤ inner ℝ (hessian f x s) s := by
  constructor
  · intro hpos s
    -- Positive operators have nonnegative quadratic form on every vector.
    exact hpos.inner_nonneg_left s
  · intro hquad
    -- Recover positivity from the Chapter 1 symmetry owner and the quadratic-form condition.
    exact (ContinuousLinearMap.isPositive_iff _).2
      ⟨fderiv_gradient_isSymmetric_of_contDiffAt (hf_C2.contDiffAt (hQ_open.mem_nhds hx)),
        hquad⟩

/-- Helper for Theorem 2.4: pointwise nonnegativity of the Hessian quadratic form implies the
monotonicity of the ambient gradient on the open convex domain. -/
private theorem gradient_monotone_of_hessian_quadratic_form_nonneg
    (hQ_open : IsOpen Q) (hQ_conv : Convex ℝ Q) (hf_C2 : ContDiffOn ℝ 2 f Q)
    (hquad : ∀ x ∈ Q, ∀ s : E, 0 ≤ inner ℝ (hessian f x s) s) :
    ∀ x ∈ Q, ∀ y ∈ Q, 0 ≤ inner ℝ (∇ f x - ∇ f y) (x - y) := by
  intro x hx y hy
  let d : E := x - y
  let φ := (toDual ℝ E) d
  let g : E → ℝ := fun w ↦ φ (∇ f w)
  have hg_deriv :
      ∀ z ∈ Q,
        HasFDerivWithinAt g (φ.comp (hessian f z)) Q z := by
    intro z hz
    -- Differentiate the scalarized gradient by differentiating `fderiv ℝ f`
    -- and then transporting through the Hilbert-space `toDual` equivalence.
    have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) z := by
      exact
        ((hf_C2.fderiv_of_isOpen hQ_open
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
          (by simp) z hz).differentiableAt (hQ_open.mem_nhds hz)
    have hgrad : DifferentiableAt ℝ (∇ f) z := by
      unfold gradient
      simpa using ((toDual ℝ E).symm.differentiableAt.comp z hfderiv)
    have hscalar :
        HasFDerivAt g (φ.comp (hessian f z)) z := by
      simpa [g, φ, Function.comp] using (φ.hasFDerivAt.comp z hgrad.hasFDerivAt)
    exact hscalar.hasFDerivWithinAt
  -- Apply the mean value theorem to the scalarized gradient along the segment from `y` to `x`.
  rcases domain_mvt hg_deriv hQ_conv hy hx with ⟨z, hzseg, hzEq⟩
  have hzQ : z ∈ Q := hQ_conv.segment_subset hy hx hzseg
  have hz_nonneg : 0 ≤ inner ℝ (hessian f z d) d := hquad z hzQ d
  have hleft : g x - g y = inner ℝ d (∇ f x - ∇ f y) := by
    calc
      g x - g y
          = inner ℝ x (∇ f x) - inner ℝ y (∇ f x) -
              (inner ℝ x (∇ f y) - inner ℝ y (∇ f y)) := by
              simp [g, φ, d, InnerProductSpace.toDual_apply_apply, sub_eq_add_neg]
      _ = inner ℝ (x - y) (∇ f x - ∇ f y) := by
            calc
              inner ℝ x (∇ f x) - inner ℝ y (∇ f x) -
                  (inner ℝ x (∇ f y) - inner ℝ y (∇ f y))
                  =
                    (inner ℝ x (∇ f x) - inner ℝ y (∇ f x)) -
                      (inner ℝ x (∇ f y) - inner ℝ y (∇ f y)) := by
                        ring
              _ = inner ℝ (x - y) (∇ f x) - inner ℝ (x - y) (∇ f y) := by
                    rw [inner_sub_left, inner_sub_left]
              _ = inner ℝ (x - y) (∇ f x - ∇ f y) := by
                    rw [inner_sub_right]
      _ = inner ℝ d (∇ f x - ∇ f y) := by
            simp [d]
  have hright :
      (φ.comp (hessian f z)) (x - y) =
        inner ℝ d (hessian f z d) := by
    calc
      (φ.comp (hessian f z)) (x - y)
          =
            inner ℝ x (hessian f z x - hessian f z y) -
              inner ℝ y (hessian f z x - hessian f z y) := by
                simp [d, φ, InnerProductSpace.toDual_apply_apply]
      _ = inner ℝ (x - y) (hessian f z x - hessian f z y) := by
            rw [inner_sub_left]
      _ = inner ℝ (x - y) (hessian f z (x - y)) := by
            rw [map_sub]
      _ = inner ℝ d (hessian f z d) := by
            simp [d]
  have hEq : inner ℝ d (∇ f x - ∇ f y) = inner ℝ d (hessian f z d) := by
    rw [← hleft, hzEq, hright]
  have hEq' : inner ℝ (∇ f x - ∇ f y) d = inner ℝ (hessian f z d) d := by
    simpa [real_inner_comm] using hEq
  have hfinal : 0 ≤ inner ℝ (∇ f x - ∇ f y) d := by
    rw [hEq']
    exact hz_nonneg
  simpa [d] using hfinal

/-- Helper for Theorem 2.4: convexity on the open convex domain forces nonnegativity of every
Hessian quadratic form. -/
private theorem hessian_quadratic_form_nonneg_of_convexOn
    (hQ_open : IsOpen Q) (hf_C2 : ContDiffOn ℝ 2 f Q) (hconv : ConvexOn ℝ Q f) :
    ∀ x ∈ Q, ∀ s : E, 0 ≤ inner ℝ (hessian f x s) s := by
  let hf_C1 : ContDiffOn ℝ 1 f Q := hf_C2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hmono_within :=
    ConvexOn.gradient_monotone hconv (hf_C1.differentiableOn (by simp))
  have hmono :
      ∀ u ∈ Q, ∀ v ∈ Q, 0 ≤ inner ℝ (∇ f u - ∇ f v) (u - v) := by
    intro u hu v hv
    -- On the open set `Q`, the within-gradient from Theorem 2.3 agrees with the ambient one.
    simpa [gradientWithin_eq_gradient_of_mem_open hQ_open hf_C1 hu,
      gradientWithin_eq_gradient_of_mem_open hQ_open hf_C1 hv] using
      hmono_within hu hv
  intro x hx s
  let γ : ℝ → E := fun t ↦ x + t • s
  let g : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (γ t)) s
  let D : Set ℝ := γ ⁻¹' Q
  have hD_open : IsOpen D := by
    simpa [D, γ] using
      hQ_open.preimage
        (continuous_const.add (continuous_id.smul continuous_const) :
          Continuous (fun t : ℝ ↦ x + t • s))
  have h0D : (0 : ℝ) ∈ D := by
    simp [D, γ, hx]
  rcases Metric.mem_nhds_iff.mp (hD_open.mem_nhds h0D) with ⟨ε, hεpos, hεsub⟩
  let I : Set ℝ := Set.Icc (0 : ℝ) (ε / 2)
  have hhalf_pos : 0 < ε / 2 := by positivity
  have hI_subset : I ⊆ D := by
    intro t ht
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq]
    have ht_lt : t < ε := by linarith [ht.2, hεpos]
    simpa [abs_of_nonneg ht.1] using ht_lt
  have hg_mono : MonotoneOn g I := by
    intro a ha b hb hab
    have haQ : γ a ∈ Q := hI_subset ha
    have hbQ : γ b ∈ Q := hI_subset hb
    -- Compare the ambient gradients at the two feasible points `γ a` and `γ b`.
    have hpair : 0 ≤ inner ℝ (∇ f (γ b) - ∇ f (γ a)) (γ b - γ a) := hmono _ hbQ _ haQ
    have hγsub : γ b - γ a = (b - a) • s := by
      calc
        γ b - γ a = b • s - a • s := by
          dsimp [γ]
          abel_nf
        _ = (b - a) • s := by
          rw [sub_smul]
    by_cases hab_eq : a = b
    · subst hab_eq
      rfl
    · have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
      have hdiff_pos : 0 < b - a := sub_pos.mpr hab_lt
      rw [hγsub, real_inner_smul_right] at hpair
      have hscalar : 0 ≤ inner ℝ (∇ f (γ b) - ∇ f (γ a)) s := by
        exact nonneg_of_mul_nonneg_right hpair hdiff_pos
      have hrewrite : g b - g a = inner ℝ (∇ f (γ b) - ∇ f (γ a)) s := by
        simp [g, inner_sub_left]
      linarith
  have hderivAt0 : HasDerivAt g (inner ℝ (hessian f x s) s) 0 := by
    -- Differentiate the scalarized gradient along the line `t ↦ x + t • s`.
    let φ := (toDual ℝ E) s
    have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) x := by
      exact
        ((hf_C2.fderiv_of_isOpen hQ_open
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
          (by simp) x hx).differentiableAt (hQ_open.mem_nhds hx)
    have hgrad : DifferentiableAt ℝ (∇ f) x := by
      unfold gradient
      simpa using ((toDual ℝ E).symm.differentiableAt.comp x hfderiv)
    have hγ : HasDerivAt γ s 0 := by
      simpa [γ] using
        (HasDerivAt.const_add x
          ((HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) s)))
    have hgrad0 : HasFDerivAt (∇ f) (hessian f x) (γ 0) := by
      simpa [γ] using hgrad.hasFDerivAt
    have hgradLine :
        HasFDerivAt (fun t : ℝ ↦ ∇ f (γ t))
          ((hessian f x).comp (ContinuousLinearMap.toSpanSingleton ℝ s)) 0 := by
      simpa [γ] using
        (hgrad0.comp 0 hγ.hasFDerivAt)
    have hscalar :
        HasFDerivAt
          (fun t : ℝ ↦ φ (∇ f (γ t)))
          (φ.comp
            ((hessian f x).comp (ContinuousLinearMap.toSpanSingleton ℝ s))) 0 := by
      simpa [γ] using
        ((φ.hasFDerivAt).comp 0 hgradLine)
    simpa [g, γ, φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      hscalar.hasDerivAt
  have h0I : (0 : ℝ) ∈ I := by
    exact ⟨le_rfl, by positivity⟩
  have hderivWithin :
      derivWithin g I 0 = inner ℝ (hessian f x s) s := by
    exact
      HasDerivWithinAt.derivWithin
        (hderivAt0.hasDerivWithinAt)
        ((uniqueDiffOn_Icc hhalf_pos).uniqueDiffWithinAt h0I)
  have hnonneg : 0 ≤ derivWithin g I 0 := by
    simpa using (hg_mono.derivWithin_nonneg : 0 ≤ derivWithin g I 0)
  rw [hderivWithin] at hnonneg
  exact hnonneg

/-- The Hessian-positivity condition in Theorem 2.4 is equivalently the nonnegativity of the
associated quadratic form at every point of `Q`. -/
-- Proof sketch: the forward direction uses monotonicity of the within-gradient from Theorem 2.3,
-- upgraded to the ambient gradient on the open set `Q`, and differentiates the line restriction
-- `t ↦ ∇ f (x + t • s)` at `t = 0`. The reverse direction first proves ambient gradient
-- monotonicity from the quadratic-form hypothesis by a mean-value argument, then returns to
-- Theorem 2.3 through `gradientWithin`. This is the real-Hilbert-space owner statement; the
-- textbook Euclidean theorem is its finite-dimensional specialization.
theorem convexOn_iff_hessian_quadratic_form_nonneg
    (hQ_open : IsOpen Q) (hQ_conv : Convex ℝ Q) (hf_C2 : ContDiffOn ℝ 2 f Q) :
    ConvexOn ℝ Q f ↔
      ∀ x ∈ Q, ∀ s : E, 0 ≤ inner ℝ (hessian f x s) s := by
  constructor
  · intro hconv
    simpa using hessian_quadratic_form_nonneg_of_convexOn hQ_open hf_C2 hconv
  · intro hquad
    let hf_C1 : ContDiffOn ℝ 1 f Q := hf_C2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hmono :=
      gradient_monotone_of_hessian_quadratic_form_nonneg hQ_open hQ_conv hf_C2 hquad
    have hmono_within : GradientMonotoneOn Q f := by
      refine fun {x} ↦ ?_
      refine fun {y} ↦ ?_
      intro hx hy
      -- The reverse route first proves ambient gradient monotonicity, then re-enters
      -- Theorem 2.3 through the within-gradient API valid on open sets.
      simpa
          [gradientWithin_eq_gradient_of_mem_open hQ_open hf_C1 hx,
            gradientWithin_eq_gradient_of_mem_open hQ_open hf_C1 hy] using
        hmono x hx y hy
    exact
      ConvexOn.of_gradient_monotone hQ_conv (hf_C1.differentiableOn (by simp)) hmono_within

/-- Theorem 2.4, stated on the canonical real Hilbert-space owner layer: on an open convex set
`Q`, a `C²` function is convex on `Q` if and only if its Hessian is positive at every point of
`Q`; the textbook Euclidean theorem is the finite-dimensional specialization. -/
-- Proof sketch: for the forward direction, restrict `f` to each affine line `t ↦ x + t • s`,
-- use convexity to show that the resulting one-variable `C²` function has nonnegative second
-- derivative, and identify that second derivative with `⟪hessian f x s, s⟫`. For the
-- reverse direction, use the Hessian positivity hypothesis along each segment in the convex set
-- `Q` to obtain convexity of every one-variable restriction, then lift this back to
-- `ConvexOn ℝ Q f`.
theorem convexOn_iff_hessian_isPositive
    (hQ_open : IsOpen Q) (hQ_conv : Convex ℝ Q) (hf_C2 : ContDiffOn ℝ 2 f Q) :
    ConvexOn ℝ Q f ↔
      ∀ x ∈ Q, (hessian f x).IsPositive := by
  constructor
  · intro hconv x hx
    -- First pass through the scalar quadratic-form criterion, then rewrite positivity pointwise.
    simpa using (hessian_isPositive_iff_quadratic_form_nonneg_at hQ_open hf_C2 hx).2
      ((convexOn_iff_hessian_quadratic_form_nonneg hQ_open hQ_conv hf_C2).1 hconv x hx)
  · intro hpos
    -- Translate the operator-valued hypothesis back to the scalar quadratic-form criterion.
    have hquad : ∀ x ∈ Q, ∀ s, 0 ≤ inner ℝ (hessian f x s) s := by
      intro x hx s
      exact
        (hessian_isPositive_iff_quadratic_form_nonneg_at hQ_open hf_C2 hx).1 (hpos x hx) s
    simpa using
      (convexOn_iff_hessian_quadratic_form_nonneg hQ_open hQ_conv hf_C2).2 hquad

end
