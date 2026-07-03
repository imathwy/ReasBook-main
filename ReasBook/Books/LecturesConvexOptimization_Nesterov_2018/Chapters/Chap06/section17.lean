import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_17 (from Chap06) -/
noncomputable section

open Module LinearMap

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Definition 6.17 lies in the affine variational-inequality / monotone affine-operator domain.

Sampled owner-style declarations:
- `AffineMap` in mathlib, the canonical owner of an affine operator together with its linear part;
- `LinearMap.BilinForm.IsNonneg` in mathlib, the canonical positivity owner for the bilinear form
  underlying a map `E →ₗ[ℝ] Dual ℝ E`;
- `PrimalConvexMinimizationProblem` in `Definition_6_4`, the chapter pattern of keeping only
  genuinely primitive feasible-set data public and deriving convenience API separately;
- `LinearEqualityConstrainedConvexProblem` in `Chap03/Definition_3_27`, the project pattern of
  extending an owner abstraction rather than restating equivalent lower-level data.

Best owner abstraction:
- source-facing: `AffineVariationalInequalityProblem E`;
- core/canonical: `AffineMap` for the operator and `BilinForm.IsNonneg` for the positivity of its
  linear part;
- bridge/view: the source-facing pointwise inequality `0 ≤ B.linear h h`, derived from the
  bilinear-form owner field.

Primitive data:
- the feasible set `Q` together with boundedness, closedness, and convexity;
- the affine operator `B : E →ᵃ[ℝ] E⋆`;
- nonnegativity of the bilinear form `B.linear`.

Derived API:
- coercion to the affine operator as a function;
- the source-facing pointwise monotonicity theorem `linear_nonnegative`;
- the solution predicate `IsSolution`.
-/

/-- Definition 6.17: an affine variational inequality problem consists of a bounded closed convex
set `Q ⊆ E` and an affine operator `B : E → E*` whose linear part satisfies
`⟪Bh, h⟫ ≥ 0` for every `h ∈ E`. The textbook item specializes this owner to finite-dimensional
real normed spaces. -/
structure AffineVariationalInequalityProblem (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] where
  /-- The feasible set `Q ⊆ E`. -/
  feasibleSet : Set E
  /-- The feasible set `Q` is bounded. -/
  feasibleSet_bounded : Bornology.IsBounded feasibleSet
  /-- The feasible set `Q` is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The feasible set `Q` is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The affine operator `B : E → E*`. -/
  operator : E →ᵃ[ℝ] Dual ℝ E
  /-- The bilinear form underlying the linear part of `B` is nonnegative. -/
  operator_linear_isNonneg : BilinForm.IsNonneg operator.linear

namespace AffineVariationalInequalityProblem

/-- An affine variational inequality problem can be evaluated as its canonical affine operator
`B : E → E*`. -/
instance : CoeFun (AffineVariationalInequalityProblem E) (fun _ ↦ E → Dual ℝ E) where
  coe problem := problem.operator

/-- Evaluating an affine variational inequality problem returns its affine operator value. -/
@[simp] theorem coe_apply
    (problem : AffineVariationalInequalityProblem E) (w : E) :
    problem w = problem.operator w :=
  rfl

/-- The linear part of the affine operator satisfies `⟪Bh, h⟫ ≥ 0` for every `h ∈ E`. -/
theorem linear_nonnegative
    (problem : AffineVariationalInequalityProblem E) (h : E) :
    0 ≤ problem.operator.linear h h :=
  problem.operator_linear_isNonneg.nonneg h

/-- A point `wStar` solves `VI(Q, B)` when it lies in `Q` and satisfies the defining variational
inequality against every `w ∈ Q`. -/
def IsSolution (problem : AffineVariationalInequalityProblem E) (wStar : E) : Prop :=
  wStar ∈ problem.feasibleSet ∧ ∀ w ∈ problem.feasibleSet, 0 ≤ problem wStar (w - wStar)

-- Proof sketch: unfold `IsSolution`; the conjunction is exactly feasibility together with the
-- displayed inequality against every feasible comparison point.
/-- A point solves `VI(Q, B)` exactly when it is feasible and satisfies the defining inequality
against every feasible comparison point. -/
theorem isSolution_iff (problem : AffineVariationalInequalityProblem E) (wStar : E) :
    problem.IsSolution wStar ↔
      wStar ∈ problem.feasibleSet ∧
        ∀ w ∈ problem.feasibleSet, 0 ≤ problem wStar (w - wStar) :=
  Iff.rfl

end AffineVariationalInequalityProblem

end

/-! ### Lemma_6_17 (from Chap06) -/
noncomputable section

open ConditionalGradientContraction

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Lemma 6.17 lies in the Chapter 6 dual-selection / Hölder-gradient domain.

Sampled owner-style declarations:
- `smoothedPrimalObjectiveMaximand` in `Definition_6_30`, the chapter owner for dual objectives of
  the form `u ↦ (A x) u - g(u) - μ d(u)`;
- `smoothedPrimalObjectiveArgmax` in `Definition_6_30`, the chapter owner for feasible
  maximizers of that dual maximand;
- `IsMaxRepresentationWithUniformlyConvexDualTerm` in `Definition_6_63`, the neighboring
  source-facing Chapter 6 owner that already records the same zero-smoothed geometry through
  `smoothedPrimalObjectiveArgmax`;
- `ConditionalGradientContraction.HolderGradientOn` in `Theorem_6_14`, the chapter owner for a
  chosen derivative field that is Hölder continuous on a feasible set.

Best owner abstraction:
- source-facing: Lemma 6.17's Hölder continuity statement for the gradient field attached to a
  maximizing selector `u`;
- core/canonical: the zero-smoothed argmax owner `smoothedPrimalObjectiveArgmax A Set.univ g 0 0`
  together with `ConditionalGradientContraction.HolderGradientOn` for the Hölder derivative
  field;
- bridge/view: the pointwise `fderiv` norm estimate below, recovered from the canonical owner
  using the assumed derivative identification `fderiv ℝ f x = A.flip (u x)`.

Primitive data:
- the dual pairing map `A`, the dual term `g`, the selector `u`, and the parameters `p`, `σg`;
- pointwise argmax membership of `u x` for the zero-smoothed chapter owner;
- differentiability of `g` through `gradg`;
- the `p`-uniform convexity inequality for `gradg`;
- the derivative identification `HasFDerivAt f (A.flip (u x)) x`.

Derived API:
- the canonical Hölder-gradient owner below;
- the source-facing pointwise derivative estimate.
-/

/-- Lemma 6.17 in the canonical Chapter 6 Hölder-gradient owner form: under the argmax-selection
and dual uniform-convexity hypotheses, the chosen derivative field `x ↦ A.flip (u x)`
defines `ConditionalGradientContraction.HolderGradientOn` on `Set.univ` with exponent
`v = 1 / (p - 1)` and constant `Gᵥ = (1 / σ_g)^v ‖A‖^(1 + v)`. -/
theorem holderGradientOn_of_argmax_selection_of_uniformly_convex_derivative
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {f : E₁ → ℝ} {g : E₂ → ℝ}
    {u : E₁ → E₂} {gradg : E₂ → StrongDual ℝ E₂} {p σg : ℝ}
    (hp : 2 ≤ p) (hσg : 0 < σg)
    (hu : ∀ x : E₁, u x ∈ smoothedPrimalObjectiveArgmax A Set.univ g 0 0 x)
    (hg : ∀ z : E₂, HasFDerivAt g (gradg z) z)
    (huniform :
      ∀ u₁ u₂ : E₂,
        σg * Real.rpow ‖u₁ - u₂‖ p ≤ (gradg u₁ - gradg u₂) (u₁ - u₂))
    (hf : ∀ x : E₁, HasFDerivAt f (A.flip (u x)) x) :
    HolderGradientOn
      (Real.toNNReal (1 / (p - 1)))
      (Real.toNNReal
        (Real.rpow (1 / σg) (1 / (p - 1)) * Real.rpow ‖A‖ (1 + 1 / (p - 1))))
      Set.univ f (fun x ↦ A.flip (u x)) := by
  sorry

-- Proof sketch: compare the first-order optimality conditions for the maximizers `u x₁` and
-- `u x₂`, use the assumed monotonicity inequality for `gradg` to bound `‖u x₁ - u x₂‖`, then
-- apply the operator-norm estimates for `A` and `A.flip` together with
-- `ContinuousLinearMap.opNorm_flip`, or equivalently reuse the canonical owner theorem above and
-- read off its pointwise Hölder bound.
/-- Lemma 6.17: if `u(x)` lies in the canonical argmax set of `u' ↦ A x u' - g(u')` for every
`x`, `g` has derivative selection `gradg` satisfying the uniform convexity inequality
`σ_g ‖u₁ - u₂‖^p ≤ (gradg u₁ - gradg u₂) (u₁ - u₂)` with `p ≥ 2` and `σ_g > 0`, and `f` has
derivative `A.flip (u x)` at every `x` (the Lean form of `A^* u(x)`), then `∇f` is Hölder
continuous of order `v = 1 / (p - 1)` with constant
`Gᵥ = (1 / σ_g)^v ‖A‖^(1 + v)`. -/
theorem gradient_holder_of_argmax_selection_of_uniformly_convex_derivative
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {f : E₁ → ℝ} {g : E₂ → ℝ}
    {u : E₁ → E₂} {gradg : E₂ → StrongDual ℝ E₂} {p σg : ℝ}
    (hp : 2 ≤ p) (hσg : 0 < σg)
    (hu : ∀ x : E₁, u x ∈ smoothedPrimalObjectiveArgmax A Set.univ g 0 0 x)
    (hg : ∀ z : E₂, HasFDerivAt g (gradg z) z)
    (huniform :
      ∀ u₁ u₂ : E₂,
        σg * Real.rpow ‖u₁ - u₂‖ p ≤ (gradg u₁ - gradg u₂) (u₁ - u₂))
    (hf : ∀ x : E₁, HasFDerivAt f (A.flip (u x)) x) (x₁ x₂ : E₁) :
    ‖fderiv ℝ f x₁ - fderiv ℝ f x₂‖ ≤
      (Real.rpow (1 / σg) (1 / (p - 1)) * Real.rpow ‖A‖ (1 + 1 / (p - 1))) *
        Real.rpow ‖x₁ - x₂‖ (1 / (p - 1)) := sorry

end

/-! ### Proposition_6_17 (from Chap06) -/
noncomputable section

open Metric
open scoped BigOperators SeminormOperatorNorm

universe u v

variable {ι : Type v}

/- Proposition 6.17 lies in the induced operator-norm domain for the weighted tuple geometry of
the continuous location model.

Sampled owner declarations:
* `Seminorm.primalDualOperatorNorm`, the chapter owner for induced norms between source and target
  seminorm geometries;
* `Seminorm.primalDualOperatorNorm_eq_sSup_dualPairing`, the owner-side source formula for the
  two-ball pairing supremum;
* `continuousLocationSmoothingMap`, the chapter owner for the weighted pairing
  `(x, u) ↦ ∑_j m_j ⟪u_j, x⟫`;
* `continuousLocationDualTupleNorm`, the source-facing weighted tuple norm on `ι → E`.

Best owner abstraction:
* source-facing: the textbook supremum of `∑_j m_j ⟪u_j, x⟫` over unit vectors `x` in the ambient
  real inner-product space `E` and weighted-dual unit tuples `u : ι → E`;
* core/canonical: `Seminorm.primalDualOperatorNorm` applied to the `PiLp`-transport of
  `continuousLocationSmoothingMap E weights` and the pullback seminorm
  `continuousLocationDualTupleSeminorm E weights`;
* bridge/view kept in this file: the weighted scaling map on `PiLp 2 (fun _ : ι ↦ E)` and the
  transported smoothing operator `continuousLocationSmoothingMapPiLp E weights`.

Primitive data:
* the population weights `weights`;
* the ambient real inner-product space `E`;
* the weighted tuple scaling linear map on `PiLp 2 (fun _ : ι ↦ E)`.

Derived API:
* the pairing map `continuousLocationSmoothingMap`;
* the transported pairing map `continuousLocationSmoothingMapPiLp`;
* the pullback seminorm owner `continuousLocationDualTupleSeminorm`;
* the canonical primal-dual operator norm of `continuousLocationSmoothingMap`;
* the source-facing sphere formula of Proposition 6.17 as a thin bridge.
-/

section Scale

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "E₂" => PiLp 2 fun _ : ι ↦ E

/-- The componentwise scaling `u_j ↦ √m_j • u_j` on the Hilbert product
`PiLp 2 (fun _ : ι ↦ E)` behind the weighted tuple geometry. -/
def continuousLocationDualTupleScale
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (weights : ContinuousLocationWeights ι) :
    PiLp 2 (fun _ : ι ↦ E) →L[ℝ] PiLp 2 (fun _ : ι ↦ E) :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ E)).symm.toContinuousLinearMap) :
      (ι → E) →L[ℝ] PiLp 2 (fun _ : ι ↦ E)).comp
    ((ContinuousLinearMap.pi fun j ↦
      Real.sqrt (weights j : ℝ) • PiLp.proj 2 (fun _ : ι ↦ E) j) :
      PiLp 2 (fun _ : ι ↦ E) →L[ℝ] (ι → E))

/-- The `j`-th coordinate of `continuousLocationDualTupleScale E weights u` is
`√m_j • u_j`. -/
theorem continuousLocationDualTupleScale_apply
    (weights : ContinuousLocationWeights ι) (u : E₂) (j : ι) :
    continuousLocationDualTupleScale E weights u j =
      Real.sqrt (weights j : ℝ) • u j := by
  simp [continuousLocationDualTupleScale]

end Scale

section Geometry

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fintype ι]

local notation "E₂" => PiLp 2 fun _ : ι ↦ E

/-- The weighted tuple geometry of Proposition 6.17, owned canonically as the pullback of the
ambient Hilbert norm on `PiLp 2 (fun _ : ι ↦ E)` along `continuousLocationDualTupleScale
E weights`. -/
def continuousLocationDualTupleSeminorm
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weights : ContinuousLocationWeights ι) : Seminorm ℝ (PiLp 2 fun _ : ι ↦ E) :=
  Seminorm.comp
    (normSeminorm ℝ (PiLp 2 fun _ : ι ↦ E))
    (continuousLocationDualTupleScale E weights).toLinearMap

/-- Evaluating `continuousLocationDualTupleSeminorm E weights` gives the ambient norm of the
weighted scaling of the tuple. -/
theorem continuousLocationDualTupleSeminorm_eq_norm_scale
    (weights : ContinuousLocationWeights ι) (u : E₂) :
    continuousLocationDualTupleSeminorm E weights u =
      ‖continuousLocationDualTupleScale E weights u‖ :=
  rfl

/-- The seminorm owner `continuousLocationDualTupleSeminorm E weights` recovers the textbook
weighted tuple norm `continuousLocationDualTupleNorm E weights` after identifying coordinate
tuples with the Hilbert product `PiLp 2 (fun _ : ι ↦ E)`. -/
theorem continuousLocationDualTupleSeminorm_apply
    (weights : ContinuousLocationWeights ι) (u : ι → E) :
    continuousLocationDualTupleSeminorm E weights (WithLp.toLp 2 u) =
      continuousLocationDualTupleNorm E weights u := by
  sorry

/-- Positive weights make the pullback seminorm `continuousLocationDualTupleSeminorm E weights`
nondegenerate, so the weighted tuple geometry is a genuine norm. -/
instance continuousLocationDualTupleSeminorm.isNorm
    (weights : ContinuousLocationWeights ι) :
    Seminorm.IsNorm (continuousLocationDualTupleSeminorm E weights : Seminorm ℝ E₂) := by
  sorry

/-- The canonical `PiLp` transport of `continuousLocationSmoothingMap E weights`, viewed in the
weighted tuple geometry on `PiLp 2 (fun _ : ι ↦ E)`. This is a thin bridge from the
source-facing coordinate-tuple owner to the Hilbert-product realization used by
`continuousLocationDualTupleSeminorm E weights`. -/
abbrev continuousLocationSmoothingMapPiLp
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weights : ContinuousLocationWeights ι) :=
  (ContinuousLinearMap.precomp ℝ
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ E)).toContinuousLinearMap).comp
    (continuousLocationSmoothingMap E weights)

/-- Evaluating the transported smoothing operator on a `PiLp` tuple recovers the same weighted
pairing formula as `continuousLocationSmoothingMap_apply`. -/
theorem continuousLocationSmoothingMapPiLp_apply
    (weights : ContinuousLocationWeights ι) (x : E) (u : E₂) :
    continuousLocationSmoothingMapPiLp E weights x u =
      ∑ j, (weights j : ℝ) * inner ℝ (u j) x := by
  simpa [continuousLocationSmoothingMapPiLp] using
    continuousLocationSmoothingMap_apply weights x
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ E)).toContinuousLinearMap u)

/-- Canonical owner form of Proposition 6.17: the induced norm of the continuous-location
smoothing map from the ambient norm on `E` to the weighted dual-tuple geometry is `√P`, where
`P = \sum_j m_j` is the total population weight. The `PiLp` realization is exposed through the
thin bridge `continuousLocationSmoothingMapPiLp E weights`, so the public theorem stays on
`Seminorm.primalDualOperatorNorm` without leaking the transport term. -/
theorem continuousLocationSmoothingMap_primalDualOperatorNorm_eq_sqrt_totalPopulation
    [FiniteDimensional ℝ E] [Nontrivial E] (weights : ContinuousLocationWeights ι) :
    ‖(continuousLocationSmoothingMapPiLp E weights).toLinearMap‖[
        normSeminorm ℝ E ⇀ continuousLocationDualTupleSeminorm E weights,*] =
      Real.sqrt (continuousLocationTotalPopulation weights) := by
  sorry

/-- Proposition 6.17: rewriting the canonical induced-norm statement through
`continuousLocationSmoothingMap_primalDualOperatorNorm_eq_sqrt_totalPopulation`,
`Seminorm.primalDualOperatorNorm_eq_sSup_dualPairing`, `continuousLocationSmoothingMap_apply`, and
`continuousLocationDualTupleSeminorm_apply`, and then transporting back along
`PiLp.continuousLinearEquiv`, gives the source-facing unit-sphere formula for the weighted
pairing. -/
theorem continuousLocation_sSup_pairing_unitSpheres_eq_sqrt_totalPopulation
    [FiniteDimensional ℝ E] [Nontrivial E] (weights : ContinuousLocationWeights ι) :
    sSup ((fun xu : E × (ι → E) ↦ ∑ j, (weights j : ℝ) * inner ℝ (xu.2 j) xu.1) ''
      Set.prod (sphere (0 : E) 1) {u | continuousLocationDualTupleNorm E weights u = 1}) =
      Real.sqrt (continuousLocationTotalPopulation weights) := by
  sorry

end Geometry

end
