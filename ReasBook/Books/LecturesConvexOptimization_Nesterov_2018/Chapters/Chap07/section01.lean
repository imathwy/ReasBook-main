import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_1 (from Chap07) -/
universe u

section

variable {α : Type u} [Semiring α] [Preorder α]

/-
Definition 7.1 lies in the chapter's relative-accuracy / approximate-solution domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem.IsApproximateMinimizer` in
  `Chap01/Definition_1_3_7`, the project owner for additive approximate minimizers on a feasible
  set;
* `IsApproximateSolution` in `Chap03/Definition_3_34`, where the primitive data are reduced to a
  scalar objective-gap predicate relative to a chosen minimizer;
* `IsRelativeDeltaApproximateSolutionOn` in `Chap07/Definition_7_92`, where the optimization-layer
  relative notion is owned by a direct `Prop`, not by a typeclass packaging of its fields;
* `HasMixedAccuracy` in `Chap07/Definition_7_89`, which shows the local chapter style for small
  accuracy predicates.

Best owner abstraction:
* source-facing: the statement that an attained objective value is a relative-`δ` approximation of
  a positive optimal value;
* core/canonical: a scalar `Prop` on `(fStar, δ, fBar)` over the semiring / preorder layer;
* bridge/view: evaluation at `f xBar` for a real-valued objective.

Primitive data:
* the positive optimal value `fStar`;
* the relative-accuracy parameter `delta`;
* the attained value `fBar`.

Derived API:
* the source-facing specialization to `f xBar`.

The previous file used a typeclass wrapper and a `Fact` instance for four scalar inequalities.
Those inequalities are the mathematics, so the owner surface should be the direct scalar `Prop`.
Because the notion only uses order, `0`, `1`, addition, and multiplication, the scalar owner
should live directly over the semiring / preorder layer; the stronger linear-order and
strict-positivity monotonicity assumptions are needed only for the derived nonnegativity
consequence.
The objective-evaluation view remains a thin real-valued bridge theorem.
-/

/-- Definition 7.1: a value `fBar` has relative accuracy `delta` with respect to a positive
optimal value `fStar` when it lies between `fStar` and `(1 + delta) * fStar`. The nonnegativity
of `delta` is then forced by these bounds together with `0 < fStar`. -/
def IsRelativeAccuracy (fStar delta fBar : α) : Prop :=
  0 < fStar ∧ fStar ≤ fBar ∧ fBar ≤ (1 + delta) * fStar

end

/-- Unfolding `IsRelativeAccuracy fStar delta fBar` gives positivity of `fStar` together with the
two-sided relative bound on `fBar`. The nonnegativity of `delta` is derived separately from these
inequalities. -/
theorem isRelativeAccuracy_iff {α : Type u} [Semiring α] [Preorder α]
    (fStar delta fBar : α) :
    IsRelativeAccuracy fStar delta fBar ↔
      0 < fStar ∧ fStar ≤ fBar ∧ fBar ≤ (1 + delta) * fStar :=
  Iff.rfl

section

variable {α : Type u} [Semiring α] [LinearOrder α] [IsOrderedCancelAddMonoid α]
  [MulPosStrictMono α]

/-- Relative accuracy forces the relative-error parameter to be nonnegative. -/
theorem isRelativeAccuracy_delta_nonneg {fStar delta fBar : α}
    (h : IsRelativeAccuracy fStar delta fBar) :
    0 ≤ delta := by
  rcases h with ⟨hfStar_pos, hfStar_le_fBar, hfBar_le⟩
  have hbound : fStar ≤ (1 + delta) * fStar :=
    hfStar_le_fBar.trans hfBar_le
  have hdelta_mul : 0 ≤ delta * fStar := by
    have hsum : fStar ≤ fStar + delta * fStar := by
      simpa [add_mul, one_mul, add_assoc, add_left_comm, add_comm] using hbound
    exact (le_add_iff_nonneg_right fStar).1 hsum
  exact nonneg_of_mul_nonneg_left hdelta_mul hfStar_pos

end

/-- Source-facing form of Definition 7.1: the objective value at `xBar` has relative accuracy
`delta` with respect to `fStar` exactly when it satisfies the displayed positivity and two-sided
relative-error bounds. The condition `0 ≤ delta` is a derived consequence, not primitive data. -/
theorem isRelativeAccuracy_objectiveValue_iff
    {X : Type u} (f : X → ℝ) (fStar delta : ℝ) (xBar : X) :
    IsRelativeAccuracy fStar delta (f xBar) ↔
      0 < fStar ∧
        fStar ≤ f xBar ∧
          f xBar ≤ (1 + delta) * fStar :=
  Iff.rfl

/-! ### Lemma_7_1 (from Chap07) -/
noncomputable section

open scoped BigOperators
open scoped SupportFunction

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

/- Lemma 7.1 lies in the finite-range support-function / pullback-seminorm domain.

Sampled owner declarations:
- `ξ[Q]` and `supportFunction_apply` from `Chap03/Definition_3_9`
- `Seminorm.comp` and `normSeminorm` for canonical pullback seminorms
- `LinearMap.pi` and `EuclideanSpace.equiv` for the canonical finite row map into
  `EuclideanSpace ℝ (Fin m)`
- `SatisfiesAsphericityCondition` from `Chap07/Definition_7_7`
- `Seminorm.IsNorm` from `Chap02/Definition_2_5`, recalled in `Chap07/Definition_7_84`

Best owner abstraction:
- source-facing: the Chapter 3 support function `ξ[Set.range a]` and the Euclidean pullback
  seminorm attached to the finite row family `a`
- core/canonical: `ξ[Set.range a]`, `Seminorm.comp`, `LinearMap.pi`, and `EuclideanSpace.equiv`
- bridge/view: the concrete `sSup` and `sqrt` evaluation formulas below

Primitive data:
- a finite family `a : Fin m → E`

Derived API kept here:
- the finite-range evaluation of the support function
- the coordinate formula for the canonical pullback seminorm
- the norm / asphericity statement of Lemma 7.1

This refinement removes the previous public convenience owners
`polyhedralMaxFunction`, `rowInnerMap`, and `rowInnerSeminorm`. The public surface is stated
directly with the established Chapter 3 support-function owner and the canonical pullback-seminorm
construction instead of parallel wrapper names.
-/

section

variable (a : Fin m → E)

/-- Evaluating the Chapter 3 support-function owner on the finite set `Set.range a` recovers the
supremum of the finitely many inner products `⟪aᵢ, x⟫`. -/
theorem supportFunction_range_toReal_eq_sSup_inner (x : E) :
    (ξ[Set.range a] x).toReal = sSup (Set.range fun i : Fin m ↦ inner ℝ (a i) x) := sorry

-- Proof sketch: rewrite the pullback seminorm as the Euclidean norm of the finite row map
-- `((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
--   (LinearMap.pi fun i ↦ (innerSL ℝ (a i)).toLinearMap)` applied to `x`, then expand the
-- Euclidean norm coordinatewise.
/-- The canonical Euclidean pullback seminorm attached to `a` evaluates to the square root of the
summed squared inner products `∑ i ⟪aᵢ, x⟫²`. -/
theorem pullbackSeminorm_eq_sqrt_sum_inner_sq (x : E) :
    let p : Seminorm ℝ E :=
      Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
          (LinearMap.pi fun i ↦ (innerSL ℝ (a i)).toLinearMap))
    p x =
      Real.sqrt (∑ i : Fin m, (inner ℝ (a i) x) ^ 2) := sorry

-- Proof sketch: prove definiteness of the pullback seminorm from the spanning hypothesis
-- `span ℝ (range a) = ⊤`, identify
-- `∂ (fun x ↦ (ξ[Set.range a] x).toReal) (0)` with
-- `convexHull ℝ (Set.range fun i ↦ (InnerProductSpace.toDual ℝ E) (a i))`, and then derive the
-- two `Definition_7_7` dual-ball inclusions using the convex-combination estimate and the
-- zero-sum estimate from the textbook proof.
/-- Lemma 7.1: if the family `a` has full row rank, encoded by
`Submodule.span ℝ (Set.range a) = ⊤`, has at least two elements, and satisfies `∑ i, a i = 0`,
then the canonical pullback seminorm
`x ↦ (∑ i ⟪aᵢ, x⟫²)^(1/2)` is a norm and the subdifferential at `0` of the Chapter 3 support
function `x ↦ (ξ[Set.range a] x).toReal` satisfies the asphericity condition with `γ₁ = 1` and
`γ₀ = 1 / √(m (m - 1))`. -/
theorem supportFunction_range_toReal_norm_and_asphericity
    (hm : 2 ≤ m) (hfull_row_rank : Submodule.span ℝ (Set.range a) = ⊤)
    (hzero_sum : ∑ i : Fin m, a i = 0) :
    let p : Seminorm ℝ E :=
      Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
          (LinearMap.pi fun i ↦ (innerSL ℝ (a i)).toLinearMap))
    Seminorm.IsNorm p ∧
      SatisfiesAsphericityCondition
        (fun x ↦ (ξ[Set.range a] x).toReal)
        p
        (1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) 1 := sorry

end

/-! ### Proposition_7_1 (from Chap07) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E]

-- Proof sketch: use `0 ∈ interior (∂f(0))` to obtain a uniform lower bound
-- `f x ≥ ε * ‖x‖` from subgradients at `0`. Since the feasible set is closed and avoids `0`,
-- this gives a strictly positive lower bound for `f` on the feasible set. The same estimate
-- yields coercive growth, so the Chapter 3 proper-space minimizer-existence API gives a feasible
-- minimizer, whose attained objective value is therefore strictly positive.
/-- Proposition 7.1: for a conic unconstrained minimization problem, the optimal value
`min_{x ∈ Q₁} f(x)` is attained at a feasible point and that attained value is strictly positive.
-/
theorem positive_homogeneous_convex_minimizer_exists_and_pos
    (problem : ConicUnconstrainedMinimizationProblem E) :
    ∃ x ∈ problem.feasibleSet, IsMinOn problem problem.feasibleSet x ∧ 0 < problem x := sorry

/-! ### Theorem_7_1 (from Chap07) -/
noncomputable section

universe u v

/- Theorem 7.1 lies in the chapter's sublinear / asphericity domain.

Sampled owner-style declarations:
- project `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`
- project `SatisfiesAsphericityCondition` in `Definition_7_7`
- project
  `isGreatest_pairing_image_subdifferential_zero_of_convex_posHomogeneous`
  in `Chap03/Proposition_3_19`
- project `StrongConvexOn.norm_sub_le_two_mul_lipschitzOnWith_div_of_isMinOn_of_mem`
  in `Chap03/Proposition_3_41`

Best owner abstraction:
- source-facing: the consequences of the Chapter 7 asphericity sandwich for a convex positively
  homogeneous function
- core/canonical: `SatisfiesAsphericityCondition`
- bridge/view: the Chapter 3 max formula over `∂f(0)`, the Chapter 3 minimizer-distance owner,
  and, only for the sharper final clause, the explicit pullback of an inner-product norm along a
  linear isomorphism `A : E ≃ₗ[ℝ] F`

Primitive data:
- a real normed space `E`
- a seminorm `p : Seminorm ℝ E`
- a convex function `f : E → ℝ`
- the Chapter 3 positive-homogeneity owner `IsPositivelyHomogeneousOn 1 Set.univ f`
- radii `γ₀ ≤ γ₁` encoded canonically by `SatisfiesAsphericityCondition f p γ₀ γ₁`
- for the optimization companions: a set `Q₁`, a feasible `p`-minimizer `x₀ ∈ Q₁`, and a
  feasible `f`-minimizer `xStar ∈ Q₁`

Derived API:
- the pointwise comparison between `f` and `p`
- the `γ₁`-Lipschitz estimate for `f` with respect to `p`
- the optimal-value chain on `(.mk Q₁ f : SetConstrainedMinimizationProblem E)`, with the
  canonical lower factor `γ₀ / γ₁`
- the distance bounds between a `p`-minimizer and an `f`-minimizer
- the sharper factor-`1` distance estimate obtained separately when `p` is pulled back from an
  actual inner-product norm

Source/core/bridge triage:
- source-facing: the generic consequences of the asphericity sandwich
- core/canonical: `SatisfiesAsphericityCondition`
- bridge/view: the Chapter 3 max formula, the Chapter 3 minimizer-distance owner, and the
  separate inner-product pullback realization used for the sharper last bound

This file keeps the source-facing theorem family on the chapter's canonical asphericity owner.
The pointwise and Lipschitz consequences are organized around the existing Chapter 3
subdifferential/max-formula owner, and the distance estimate is aligned with the existing Chapter 3
minimizer-distance owner rather than introducing a parallel local comparison package. The generic
bounds are stated directly for the source-facing asphericity sandwich on a seminorm, while the
final sharper estimate is stated separately under the explicit inner-product pullback bridge
already exemplified by Lemma 7.1.
-/

section AsphericityConsequences

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Seminorm ℝ E} {f : E → ℝ} {γ₀ γ₁ : ℝ}

section

-- Proof sketch: apply the lower and upper dual-ball inclusions from
-- `h_asphericity` to the affine supports of the convex positively homogeneous function `f` at
-- the origin, then evaluate the resulting support inequalities at `x`.
/-- Theorem 7.1 (1): the asphericity sandwich implies the pointwise comparison
`γ₀ * p x ≤ f x ≤ γ₁ * p x`. -/
theorem SatisfiesAsphericityCondition.pointwise_bounds
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    (x : E) :
    γ₀ * p x ≤ f x ∧ f x ≤ γ₁ * p x := sorry

-- Proof sketch: combine the upper bound from `pointwise_bounds` with convexity and positive
-- homogeneity to control the increment `f x - f y` by the seminorm of `x - y`, then symmetrize.
/-- Theorem 7.1 (2): the asphericity sandwich implies the `γ₁`-Lipschitz estimate for `f` with
respect to `p`. -/
theorem SatisfiesAsphericityCondition.lipschitz
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    (x y : E) :
    |f x - f y| ≤ γ₁ * p (x - y) := sorry

-- Proof sketch: use the lower pointwise bound from `pointwise_bounds` together with the
-- `p`-minimality of the feasible point `x₀ ∈ Q₁` to compare every `f x` on `Q₁` to `f x₀`, and
-- then pass to the Chapter 1 owner optimal value.
/-- Theorem 7.1 (3): if `x₀` minimizes `p` on `Q₁`, then the asphericity sandwich yields the
lower optimal-value estimate
`((γ₀ / γ₁) * f x₀ : EReal) ≤ (.mk Q₁ f : SetConstrainedMinimizationProblem E).optimalValue`. -/
theorem SatisfiesAsphericityCondition.optimal_value_lower_bound
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    {Q₁ : Set E} {x₀ : E} (hx₀ : x₀ ∈ Q₁) (hx₀_min : IsMinOn p Q₁ x₀) :
    ((γ₀ / γ₁) * f x₀ : EReal) ≤ (.mk Q₁ f : SetConstrainedMinimizationProblem E).optimalValue :=
  sorry

/- Theorem 7.1 (4): every feasible point `x₀ ∈ Q₁` gives the standard Chapter 1 upper bound on
the constrained optimal value attached to `f` on `Q₁`; this is exactly
`SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet`. -/
recall SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet

-- Proof sketch: take the upper half of `pointwise_bounds` at the chosen point `x`.
/-- Theorem 7.1 (5): the upper half of the asphericity sandwich gives the pointwise estimate
`f x ≤ γ₁ * p x`, hence in particular at a `p`-minimizer. -/
theorem SatisfiesAsphericityCondition.pointwise_upper_bound
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    (x : E) :
    f x ≤ γ₁ * p x := sorry

-- Proof sketch: compare the minimizing points `x₀` and `xStar` through the convex positively
-- homogeneous estimates from `pointwise_bounds`, then combine the lower and upper comparisons in
-- the textbook way.
/-- Theorem 7.1 (6): any minimizer `xStar` of `f` on `Q₁` lies within `p`-distance at most
`(2 / γ₀) * f xStar` from a feasible `p`-minimizer `x₀ ∈ Q₁`, and the optimal values satisfy the
correctly oriented comparison `(2 / γ₁) * f x₀ ≤ (2 / γ₀) * f xStar`. -/
theorem SatisfiesAsphericityCondition.optimal_solution_distance
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    {Q₁ : Set E} {x₀ xStar : E}
    (hx₀ : x₀ ∈ Q₁) (hx₀_min : IsMinOn p Q₁ x₀)
    (hxStar : xStar ∈ Q₁) (hxStar_min : IsMinOn f Q₁ xStar) :
    p (x₀ - xStar) ≤ (2 / γ₀) * f xStar ∧
      (2 / γ₁) * f x₀ ≤ (2 / γ₀) * f xStar := sorry

end

end AsphericityConsequences

section InnerProductPullback

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : Seminorm ℝ E} {f : E → ℝ} {γ₀ γ₁ : ℝ}

section

-- Proof sketch: transport the `p`-minimizer `x₀` along the linear isomorphism `A` to a projection
-- point of `0` onto the convex image `A '' Q₁`, apply the Hilbert-space projection geometry from
-- `IsProjectionPointOn.pythagorean_ineq`, and then pull the resulting norm estimate back through
-- `hp_inner`.
/-- Theorem 7.1 (7): when `p` is the pullback of the norm on a real inner-product space along a
linear isomorphism `A`, the distance factor improves from `2` to `1`, and the optimal values
satisfy `(1 / γ₁) * f x₀ ≤ (1 / γ₀) * f xStar`. -/
theorem SatisfiesAsphericityCondition.optimal_solution_distance_of_inner_product
    (h_asphericity : SatisfiesAsphericityCondition f p γ₀ γ₁)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_hom : IsPositivelyHomogeneousOn 1 Set.univ f)
    {Q₁ : Set E} {x₀ xStar : E} {F : Type v}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (hQ₁_convex : Convex ℝ Q₁)
    (hx₀ : x₀ ∈ Q₁) (hx₀_min : IsMinOn p Q₁ x₀)
    (hxStar : xStar ∈ Q₁) (hxStar_min : IsMinOn f Q₁ xStar)
    (A : E ≃ₗ[ℝ] F)
    (hp_inner : ∀ x : E, p x = ‖A x‖) :
    p (x₀ - xStar) ≤ (1 / γ₀) * f xStar ∧
      (1 / γ₁) * f x₀ ≤ (1 / γ₀) * f xStar := sorry

end

end InnerProductPullback

end
