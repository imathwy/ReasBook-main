import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_2_6 (from Chap04) -/
universe u

noncomputable section

open Module LinearMap

/- Definition 4.2.6 is a source-facing recall item in the induced-norm geometry of
positive-definite self-adjoint bilinear forms on real vector spaces.

Layer targeted by this refinement:
- source-facing recall of the Chapter 4 norm owners already defined on bilinear forms

Sampled owner-style declarations:
- `LinearMap.BilinForm.primalSeminorm` in `Definition_4_3_4`
- `LinearMap.BilinForm.dualNorm` in `Definition_4_3_4`
- `LinearMap.BilinForm.dualNorm_apply` in `Definition_4_3_4`
- `Seminorm.dualNorm` in `Definition_2_5`
- mathlib `StrongDual`

Best owner abstraction:
- the canonical bilinear-form owner `B : BilinForm ℝ E`, with derived norm API
  `LinearMap.BilinForm.primalSeminorm` and, in finite dimension,
  `LinearMap.BilinForm.dualNorm`

Primitive data:
- `B : BilinForm ℝ E`

Derived API:
- the primal seminorm owner `primalSeminorm B`
- in finite dimension, the dual norm `dualNorm B`
- the canonical inverse-pairing bridge `dualPreimage hPos`
- the support-function expansion `dualNorm_eq_sSup_primalUnitBall`
- under symmetry and positive-definiteness, the `B.toDual` inverse-pairing formula
  `dualNorm_apply`
- the continuous-dual bridge used by the nearby analytic statements

Source/core/bridge triage:
- source-facing: Definition 4.2.6's primal and dual norms attached to `B`
- core/canonical: the bilinear-form owner declarations in `Definition_4_3_4`
- bridge/view: the finite-dimensional `toDual` formula and its continuous-dual specialization
-/

/- The Chapter 4 primal seminorm owner is the canonical bilinear-form declaration from
`Definition_4_3_4`. -/
#check LinearMap.BilinForm.primalSeminorm

/- The bilinear-form dual norm owner is the corresponding support-function declaration from
`Definition_4_3_4`; as for the Chapter 2 owner `Seminorm.dualNorm`, the source-facing dual
surface is used in finite-dimensional settings where this support value is real-valued. -/

/- The pointwise primal seminorm expansion is recalled directly from the owner file. -/
#check LinearMap.BilinForm.primalSeminorm_apply

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/- The finite-dimensional bilinear-form dual norm owner is recalled directly from the owner file. -/
#check LinearMap.BilinForm.dualNorm

/- The finite-dimensional dual-norm support formula and its `B.toDual` bridge are recalled
directly from the owner file. -/
#check LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall
#check LinearMap.BilinForm.dualNorm_apply

end

namespace LinearMap.BilinForm

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-
Definition 4.2.6: for a positive-definite self-adjoint operator, the primal norm on `E` is
recalled through the canonical bilinear-form owner `LinearMap.BilinForm.primalSeminorm`, whose
value at `h` is `⟪Bh, h⟫^(1/2)` and whose owner surface depends only on `B.toQuadraticMap`.
-/
recall LinearMap.BilinForm.primalSeminorm (B : LinearMap.BilinForm ℝ E)
    (hPos : B.toQuadraticMap.PosDef) :
    Seminorm ℝ E

end

end LinearMap.BilinForm

namespace BInducedNorm

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

end

end BInducedNorm

open scoped BInducedNorm

namespace LinearMap.BilinForm

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In finite dimension, the `B`-dual norm on the continuous dual is computed by the same
`B.toDual` inverse-pairing formula after coercing a continuous functional to its underlying linear
map. -/
theorem dualNorm_apply_strongDual
    [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hSymm : B.IsSymm) (hPos : B.toQuadraticMap.PosDef)
    (s : StrongDual ℝ E) :
    B.dualNorm hPos s.toLinearMap = Real.sqrt (s (B.dualPreimage hPos s.toLinearMap)) := by
  simpa using B.dualNorm_apply hSymm hPos s.toLinearMap

/-- In finite dimension, the `B`-dual norm on the continuous dual is still the support function of
the primal `B`-unit ball after passing to the underlying linear functional. -/
theorem dualNorm_eq_sSup_primalUnitBall_strongDual
    [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hPos : B.toQuadraticMap.PosDef)
    (s : StrongDual ℝ E) :
    B.dualNorm hPos s.toLinearMap =
      sSup ((fun x : E ↦ s x) '' {x | B.primalSeminorm hPos x ≤ 1}) := by
  simpa using B.dualNorm_eq_sSup_primalUnitBall hPos s.toLinearMap

end

end LinearMap.BilinForm

/-! ### Lemma_4_2_6 (from Chap04) -/
open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {σ2 L τ : ℝ} {f : E → ℝ} {xStar : E}

/- Lemma 4.2.6 lies in the first-order nondegeneracy / strong-convexity-smoothness domain on
real Hilbert spaces.

Sampled owner declarations:
* `IsStrongConvexSmoothObjective` in `Chap02/Definition_2_17`, the chapter owner for positive
  strong convexity together with the `C¹` and Lipschitz-gradient data making `∇ f` genuinely
  first-order;
* `IsStrongConvexSmoothObjective.contDiff`, the canonical source of pointwise
  `HasGradientAt f (∇ f x) x`;
* `IsStrongConvexSmoothObjective.mu_le_L`, the owner comparison theorem showing that on
  nontrivial spaces the smoothness parameter dominates the strong-convexity parameter;
* `firstOrderNondegeneracyCoefficient` in `Definition_4_2_15`, the Chapter 4 owner of the
  normalized gradient/displacement coefficient;
* `IsFirstOrderNondegenerate` in `Definition_4_2_15`, the source-facing owner obtained by
  forgetting the explicit threshold formulas and retaining only the positive lower bound.

Best owner abstraction:
* source-facing: the explicit existence of a scalar `τ` with the displayed threshold and strict
  improvement properties;
* core/canonical: `IsStrongConvexSmoothObjective σ₂ L f`;
* bridge/view: the coefficient `firstOrderNondegeneracyCoefficient f xStar x` and the owner class
  `IsFirstOrderNondegenerate f xStar`.

Primitive data:
* `σ2`, `L`, the objective `f`, and the chosen minimizer `xStar`;
* the source-facing class membership hypothesis `f ∈ 𝓢[σ₂, L]¹¹`;
* the global minimizer witness `IsMinOn f Set.univ xStar`.

Derived API:
* the existence of a positive lower bound `τ`;
* the explicit threshold `2 * sqrt q[σ₂, L] / (1 + q[σ₂, L]) ≤ τ`;
* under the primitive scalar assumptions `0 < σ₂` and `σ₂ < L`, the strict improvement
  `sqrt q[σ₂, L] < τ`;
* the pointwise coefficient bound through `firstOrderNondegeneracyCoefficient`;
* the first-order owner bridge `HasGradientAt f (∇ f x) x` obtained from the smooth owner.

This refinement keeps the lemma source-facing while moving its assumptions to the chapter owner
that already packages the intended first-order meaning of `∇ f`. The coefficient and
nondegeneracy owner remain the downstream bridge/view layer. -/

-- Proof sketch: use the interpolation inequality for a `σ₂`-strongly convex function with
-- `L`-Lipschitz gradient to show that, for every `x ≠ xStar`,
-- `⟪∇ f x, x - xStar⟫` is bounded below by
-- `(2 * sqrt (σ₂ * L) / (σ₂ + L)) * ‖∇ f x‖ * ‖x - xStar‖`. Dividing by the product of the
-- norms gives a uniform lower bound for the coefficient, and the same scalar expression rewrites
-- as `2 * sqrt q[σ₂, L] / (1 + q[σ₂, L])`.
/-- Lemma 4.2.6 (1): if `f` lies in the strong-convex smooth class `𝓢^{1,1}_{σ₂,L}`, then
relative to any chosen global minimizer `xStar` there exists a uniform first-order
nondegeneracy lower bound `τ` whose size is at least the explicit threshold
`2 * sqrt q[σ₂, L] / (1 + q[σ₂, L])`. -/
theorem exists_firstOrderNondegeneracyLowerBound_of_mem_S11
    (hf : f ∈ 𝓢[σ2, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar) :
    ∃ τ : ℝ,
      2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L]) ≤ τ ∧
        IsFirstOrderNondegeneracyLowerBound f xStar τ := sorry

-- Proof sketch: apply the scalar inequality `2 * sqrt γ / (1 + γ) > sqrt γ` with
-- `γ = q[σ₂, L]`. The primitive scalar assumptions `0 < σ₂` and `σ₂ < L` give
-- `0 < q[σ₂, L] < 1`, so any `τ` above the explicit threshold automatically satisfies
-- `sqrt q[σ₂, L] < τ`.
/-- Lemma 4.2.6 (2): if `0 < σ₂` and `σ₂ < L`, then every lower bound `τ` dominating the explicit
threshold `2 * sqrt q[σ₂, L] / (1 + q[σ₂, L])` automatically satisfies the strict improvement
`sqrt q[σ₂, L] < τ`. -/
theorem sqrt_q_lt_of_firstOrderNondegeneracyThreshold_le
    (hσ2 : 0 < σ2)
    (hσL : σ2 < L)
    (hτ : 2 * Real.sqrt q[σ2, L] / (1 + q[σ2, L]) ≤ τ) :
    Real.sqrt q[σ2, L] < τ := sorry

/-- A global minimizer of a strongly convex smooth objective is first-order nondegenerate as soon
as Lemma 4.2.6 supplies the explicit positive lower bound on the coefficient. -/
-- Proof sketch: extract `τ` from Lemma 4.2.6 (1), use the `C¹` component of
-- `IsStrongConvexSmoothObjective` to obtain `HasGradientAt f (∇ f x) x` away from `xStar`, and
-- package these data into `IsFirstOrderNondegenerate f xStar`.
theorem isFirstOrderNondegenerate_of_mem_S11
    (hf : f ∈ 𝓢[σ2, L]¹¹)
    (hxStar : IsMinOn f Set.univ xStar) :
    IsFirstOrderNondegenerate f xStar := sorry

/-! ### Text_4_2_6 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

/- Text 4.2.6 lies in real inner-product-space norm-power calculus.

Layer targeted by this refinement:
- source-facing: the centered power-distance `x ↦ (1 / p) * ‖x - x₀‖^p`;
- core/canonical: mathlib's `hasFDerivAt_norm_rpow` and the chapter/mathlib owner
  `HasGradientAt`;
- bridge/view: the differentiability consequences below.

Sampled owner-style declarations:
- `HasGradientAt` in `Mathlib.Analysis.Calculus.Gradient.Basic`;
- `HasGradientAt.differentiableAt`;
- `hasFDerivAt_norm_rpow` in `Mathlib.Analysis.InnerProductSpace.NormPow`;
- `HasFDerivAt.hasGradientAt`.

Primitive data:
- the exponent `p : ℝ`;
- the center `x₀ : E`.

Derived API:
- the pointwise expansion of `powerDistance`;
- the gradient formula;
- differentiability at a point and on the whole space.

There is no earlier chapter owner for this centered Euclidean power function itself, so the
source-facing owner `powerDistance` stays public. The gradient theorem is refined to reuse the
canonical norm-power derivative owner instead of a parallel local wheel. -/

section Basic

variable {E : Type u} [NormedAddCommGroup E]

/-- The power-distance from a center `x₀`, namely `x ↦ (1 / p) * ‖x - x₀‖^p`. -/
def powerDistance (p : ℝ) (x0 : E) : E → ℝ :=
  fun x ↦ (1 / p) * ‖x - x0‖ ^ p

/-- Expanding `powerDistance p x₀` at `x` yields `(1 / p) * ‖x - x₀‖^p`. -/
theorem powerDistance_apply (p : ℝ) (x0 x : E) :
    powerDistance p x0 x = (1 / p) * ‖x - x0‖ ^ p :=
  rfl

end Basic

section Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- For `p > 1`, the centered power-distance has gradient
`‖x - x₀‖^(p - 2) • (x - x₀)` at `x`. -/
theorem hasGradientAt_powerDistance_of_one_lt
    {p : ℝ} (hp : 1 < p) (x0 x : E) :
    HasGradientAt (powerDistance p x0)
      (‖x - x0‖ ^ (p - 2) • (x - x0)) x := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp.le).ne'
  have htoDual_innerSL (z : E) : (InnerProductSpace.toDual ℝ E).symm ((innerSL ℝ) z) = z := by
    apply ext_inner_right ℝ
    intro y
    simp [InnerProductSpace.toDual_symm_apply]
  have hsub : HasFDerivAt (fun y : E ↦ y - x0) (1 : E →L[ℝ] E) x := by
    simpa using (hasFDerivAt_id x).sub_const x0
  have hnorm :
      HasFDerivAt (fun y : E ↦ ‖y - x0‖ ^ p)
        ((p * ‖x - x0‖ ^ (p - 2)) • innerSL ℝ (x - x0)) x := by
    simpa using (hasFDerivAt_norm_rpow (x - x0) hp).comp x hsub
  have hscaled :
      HasFDerivAt (fun y : E ↦ (1 / p) * ‖y - x0‖ ^ p)
        (((1 / p) * (p * ‖x - x0‖ ^ (p - 2))) • innerSL ℝ (x - x0)) x := by
    simpa [one_div, smul_smul, mul_assoc, mul_comm, mul_left_comm] using
      hnorm.const_smul (1 / p)
  have hgrad :
      HasGradientAt (fun y : E ↦ (1 / p) * ‖y - x0‖ ^ p)
        (‖x - x0‖ ^ (p - 2) • (x - x0)) x := by
    simpa [one_div, smul_smul, mul_assoc, mul_comm, mul_left_comm, hp0, sub_eq_add_neg,
      htoDual_innerSL] using hscaled.hasGradientAt
  change HasGradientAt (fun y : E ↦ (1 / p) * ‖y - x0‖ ^ p)
    (‖x - x0‖ ^ (p - 2) • (x - x0)) x
  exact hgrad

/-- Text 4.2.6: for `p ≥ 2`, the power-distance `x ↦ (1 / p) * ‖x - x₀‖^p` on a real
inner-product space has gradient `‖x - x₀‖^(p - 2) • (x - x₀)` at every point. In particular,
this applies to the finite-dimensional setting of the text. -/
theorem hasGradientAt_powerDistance
    {p : ℝ} (hp : 2 ≤ p) (x0 x : E) :
    HasGradientAt (powerDistance p x0)
      (‖x - x0‖ ^ (p - 2) • (x - x0)) x :=
  hasGradientAt_powerDistance_of_one_lt (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hp) x0 x

/-- The power-distance is differentiable at every point when `p ≥ 2`. -/
theorem differentiableAt_powerDistance
    {p : ℝ} (hp : 2 ≤ p) (x0 x : E) :
    DifferentiableAt ℝ (powerDistance p x0) x :=
  (hasGradientAt_powerDistance hp x0 x).differentiableAt

/-- The power-distance is differentiable on the whole space when `p ≥ 2`. -/
theorem differentiable_powerDistance
    {p : ℝ} (hp : 2 ≤ p) (x0 : E) :
    Differentiable ℝ (powerDistance p x0) :=
  fun x ↦ differentiableAt_powerDistance hp x0 x

end Gradient

/-! ### Definition_4_2_7 (from Chap04) -/
noncomputable section

universe u

open scoped Gradient

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition 4.2.7: a real-valued function has Lipschitz-continuous Hessian with constant `L₃`
when it is twice continuously differentiable and its second Fréchet derivative
`x ↦ fderiv ℝ (fderiv ℝ f) x` is globally `L₃`-Lipschitz in operator norm. On real Hilbert
spaces, the usual Hessian-operator surface is recovered by the derived theorem
`HasLipschitzContinuousHessian.lipschitz`. -/
class HasLipschitzContinuousHessian (L3 : NNReal) (f : E → ℝ) : Prop where
  /-- The function is twice continuously differentiable. -/
  contDiff : ContDiff ℝ 2 f
  /-- The second Fréchet derivative is globally `L₃`-Lipschitz in operator norm. -/
  sndFDeriv_lipschitz : LipschitzWith L3 (fun x ↦ fderiv ℝ (fderiv ℝ f) x)

/- The source-facing textbook surface for `HasLipschitzContinuousHessian M f` is the class
`C_M^{2,2}`. The owner file provides that notation directly so nearby theorem surfaces can use the
standard notation instead of a second downstream wrapper. -/
set_option quotPrecheck false in
notation "C22[" M "]" => {f | HasLipschitzContinuousHessian M f}

/-- The defining inequality for a Lipschitz-continuous Hessian is the operator-norm estimate
`‖D²f(x) - D²f(y)‖ ≤ L₃ ‖x - y‖` for the second Fréchet derivative. -/
theorem HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le
    {L3 : NNReal} {f : E → ℝ} (hf : f ∈ C22[L3]) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ (L3 : ℝ) * ‖x - y‖ := by
  simpa using hf.sndFDeriv_lipschitz.norm_sub_le x y

section Hilbert

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

namespace HasLipschitzContinuousHessian

private abbrev rieszToPrimal : StrongDual ℝ X →L[ℝ] X :=
  (InnerProductSpace.toDual ℝ X).symm.toContinuousLinearEquiv.toContinuousLinearMap

private theorem hessian_eq_riesz_sndFDeriv
    {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ 2 f x) :
    hessian f x = rieszToPrimal.comp (fderiv ℝ (fderiv ℝ f) x) := by
  let D : StrongDual ℝ X →L[ℝ] X := rieszToPrimal
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact hfderiv.differentiableAt one_ne_zero
  simpa [D, gradient, hessian] using fderiv_comp x D.differentiableAt hfdiff

/-- On a real Hilbert space, `f ∈ C22[L₃]` recovers the textbook global Hessian-Lipschitz bound
`LipschitzWith L₃ (hessian f)`. -/
theorem lipschitz
    {L3 : NNReal} {f : X → ℝ} (hf : f ∈ C22[L3]) :
    LipschitzWith L3 (hessian f) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  rw [hessian_eq_riesz_sndFDeriv (hf.contDiff.contDiffAt (x := x)),
    hessian_eq_riesz_sndFDeriv (hf.contDiff.contDiffAt (x := y))]
  calc
    ‖(rieszToPrimal.comp (fderiv ℝ (fderiv ℝ f) x)) -
        (rieszToPrimal.comp (fderiv ℝ (fderiv ℝ f) y))‖
        =
          ‖rieszToPrimal.comp
            (fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y)‖ := by
          rw [ContinuousLinearMap.comp_sub]
    _ = ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
          simpa using LinearIsometry.norm_toContinuousLinearMap_comp
            (InnerProductSpace.toDual ℝ X).symm.toLinearIsometry
            (g := fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y)
    _ ≤ (L3 : ℝ) * ‖x - y‖ :=
      HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le hf x y

/-- On a real Hilbert space, the defining inequality for `f ∈ C22[L₃]` is the operator-norm
estimate `‖∇² f(x) - ∇² f(y)‖ ≤ L₃ ‖x - y‖`. -/
theorem norm_sub_le
    {L3 : NNReal} {f : X → ℝ} (hf : f ∈ C22[L3]) (x y : X) :
    ‖hessian f x - hessian f y‖ ≤ (L3 : ℝ) * ‖x - y‖ := by
  simpa using HasLipschitzContinuousHessian.lipschitz hf |>.norm_sub_le x y

end HasLipschitzContinuousHessian

end Hilbert

/-! ### Lemma_4_2_7 (from Chap04) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

section RestartedAcceleratedCubicNewton

/- Lemma 4.2.7 lies in the restarted accelerated cubic-Newton / normed-distance contraction
domain.

Sampled owner-style declarations:
* `acceleratedCubicNewtonRestartPeriod` in `Algorithm_4_2_3`, the chapter owner of the least
  natural restart length above the source lower bound `((24 e) / (σ₃ / L₃))^(1/3)`;
* `acceleratedCubicNewtonRestartPeriod_lower_bound` in `Algorithm_4_2_3`, the canonical theorem
  that the owner block length dominates the source threshold;
* `lower_bound_at_minimizer_of_uniformConvexOn` in `Theorem_4_2_1`, a nearby chapter result whose
  public statement is already minimized to the normed-space layer for inequalities involving only
  `‖x - y‖`;
* mathlib `NormedAddCommGroup`, the owner abstraction supplying the primitive `E`-side operations
  used here: subtraction and the norm `‖x - y‖`.

Best owner abstraction:
* source-facing: the contraction estimate under a cubic growth lower bound and a restart-gap upper
  bound;
* core/canonical: `acceleratedCubicNewtonRestartPeriod sigma3 L3` for the least admissible
  restart block length;
* bridge/view: the source threshold
  `acceleratedCubicNewtonRestartThreshold sigma3 L3` together with
  `acceleratedCubicNewtonRestartPeriod_lower_bound`, which recovers the textbook real lower bound.

Primitive data:
* the objective `f`;
* the restart orbit `y`;
* the reference minimizer `xStar`;
* the cubic-growth modulus `sigma3`;
* the Hessian-Lipschitz constant `L3`;
* the chosen restart length `m`;
* the normed additive group structure on `E`.

Derived API:
* the canonical restart block length `acceleratedCubicNewtonRestartPeriod sigma3 L3`;
* the pointwise restart-gap estimate at step `k`;
* the one-step contraction estimates for the cubic distance and the objective gap.

This file keeps the cubic-growth hypothesis source-facing, since no upstream owner with the same
interface already packages exactly that content. The block-length hypothesis is nonetheless
refined to the chapter owner `acceleratedCubicNewtonRestartPeriod sigma3 L3 ≤ m`, rather than
keeping the equivalent real threshold inequality as primitive public data. On the ambient `E`-side,
the statements only use subtraction and `‖·‖`, so `NormedAddCommGroup E` is the correct owner
layer; there is no inner-product or scalar action on `E` in the public API. -/

variable {f : E → ℝ} {y : ℕ → E} {xStar : E} {sigma3 : ℝ} {L3 : NNReal} {m : ℕ}

variable
  (hsigma3 : 0 < sigma3)
  (hcubic_growth :
    ∀ x : E,
      f x - f xStar ≥ (sigma3 / 3 : ℝ) * ‖x - xStar‖ ^ (3 : ℕ))
  (hrestart_gap :
    ∀ k : ℕ,
      f (y (k + 1)) - f xStar ≤
        (((8 : ℝ) * (L3 : ℝ)) / ((m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2))) *
          ‖y k - xStar‖ ^ (3 : ℕ))
  (hm : acceleratedCubicNewtonRestartPeriod sigma3 L3 ≤ m)

-- Proof sketch: apply the cubic growth lower bound at `y (k + 1)` and combine it with the
-- restarted accelerated cubic-Newton estimate for `f (y (k + 1)) - f xStar`. The lower bound on
-- `m` supplied through `acceleratedCubicNewtonRestartPeriod sigma3 L3 ≤ m` and
-- `acceleratedCubicNewtonRestartPeriod_lower_bound` implies
-- `((8 : ℝ) * L3) / (m (m + 1) (m + 2)) ≤ sigma3 / (3 * e)`, so cancelling `sigma3 / 3 > 0`
-- yields the displayed contraction of the cubic distance.
/-- Lemma 4.2.7 (1): if `f` satisfies the global cubic growth bound
`f x - f xStar ≥ (sigma3 / 3) ‖x - xStar‖^3` with `sigma3 > 0`, if the restarted outer iterates
`y` satisfy
`f(y_{k+1}) - f(xStar) ≤ (8 L3 / (m (m + 1) (m + 2))) ‖y_k - xStar‖^3`,
and if `m` dominates the canonical restart period
`acceleratedCubicNewtonRestartPeriod sigma3 L3`, then each restart contracts the cubic distance to
`xStar` by the factor `e⁻¹`. -/
theorem restartedAcceleratedCubicNewton_normCube_succ_le_exp_neg_one_mul
    (k : ℕ) :
    ‖y (k + 1) - xStar‖ ^ (3 : ℕ) ≤
      (1 / Real.exp 1 : ℝ) * ‖y k - xStar‖ ^ (3 : ℕ) := sorry

-- Proof sketch: use the previous cubic-distance contraction together with the same cubic growth
-- lower bound applied at `y k` to rewrite `‖y k - xStar‖^3` in terms of the objective gap
-- `f (y k) - f xStar`. Substituting that bound into the upper estimate for
-- `f (y (k + 1)) - f xStar` gives the factor `1 / e`.
/-- Lemma 4.2.7 (2): under the same cubic growth, restart-gap, and canonical restart-period
hypotheses, the objective gaps along the restarted accelerated cubic-Newton iterates contract by
the factor `e⁻¹`. -/
theorem restartedAcceleratedCubicNewton_gap_succ_le_exp_neg_one_mul
    (k : ℕ) :
    f (y (k + 1)) - f xStar ≤
      (1 / Real.exp 1 : ℝ) * (f (y k) - f xStar) := sorry

end RestartedAcceleratedCubicNewton

/-! ### Text_4_2_7 (from Chap04) -/
noncomputable section

universe u

open scoped DegreeConditioning

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Text 4.2.7 lies in the Chapter 4 power-distance / degree-conditioning domain.

Sampled owner-style declarations:
* `powerDistance` in `Text_4_2_6`
* `HasIteratedFDerivLipschitzConstantOfDegree` in `Definition_4_2_11`
* `uniformConvexityParameterOfDegree` in `Definition_4_2_11`
* `conditionNumberOfDegree` in `Definition_4_2_11`

Best owner abstraction:
* source-facing: the exact degree-`2` and degree-`3` conditioning identities for the canonical
  power-distance
* core/canonical: the owner `powerDistance p x₀`
* bridge/view: the specialized values of `L[p](f)`, `σ[p](f)`, and `γ[p](f)` at `p = 2, 3`

Primitive data:
* the center `x₀`
* the canonical chapter owner `powerDistance p x₀`

Derived API:
* the finiteness instances needed to form `L[2](powerDistance (2 : ℝ) x₀)` and
  `L[3](powerDistance (3 : ℝ) x₀)`
* in the nontrivial case, the finite-parameter instances needed to form
  `σ[2](powerDistance (2 : ℝ) x₀)` and `σ[3](powerDistance (3 : ℝ) x₀)`
* in the nontrivial case, the positivity instances needed to form
  `γ[2](powerDistance (2 : ℝ) x₀)` and `γ[3](powerDistance (3 : ℝ) x₀)` as genuine real ratios
* the exact source-facing identities for `L`, `σ`, and `γ`

Ambient-level check:
* the owner layer for `powerDistance`, `L[p]`, `σ[p]`, and `γ[p]` does not require completeness;
  the public statements below therefore keep only the inner-product-space assumptions used by the
  `p = 2, 3` identities themselves;
* the sharp exact-value identities require `[Nontrivial E]`, since on the trivial space
  `powerDistance p x₀` is the zero function, so the textbook constants `1`, `2`, `1 / 2`, and
  `1 / 4` are no longer the actual values of `L[p]`, `σ[p]`, and `γ[p]`

The previous local declarations `quadraticPowerFunction` and `cubicPowerFunction` duplicated the
owner `powerDistance` from `Text_4_2_6`. This file now states Text 4.2.7 directly over that
owner instead of keeping parallel special-case wrappers. The support layer is kept minimal:
global instances record only the existence of finite `L[p]`, while the sharper `σ[p]` and `γ[p]`
owners are available only under `[Nontrivial E]`, where the textbook exact constants are
mathematically correct.
-/

section FiniteLipschitz

variable (x0 : E)

instance :
    HasIteratedFDerivLipschitzConstantOfDegree 2 (powerDistance (2 : ℝ) x0) := by
  refine ⟨?_⟩
  refine ⟨1, ?_⟩
  sorry

instance :
    HasIteratedFDerivLipschitzConstantOfDegree 3 (powerDistance (3 : ℝ) x0) := by
  refine ⟨?_⟩
  refine ⟨2, ?_⟩
  sorry

end FiniteLipschitz

section ExactValues

variable [Nontrivial E]
variable (x0 : E)

instance :
    HasUniformConvexityParameterOfDegree 2 (powerDistance (2 : ℝ) x0) := by
  refine ⟨?_, ?_⟩
  · refine ⟨1, by positivity, ?_⟩
    sorry
  · sorry

instance :
    HasUniformConvexityParameterOfDegree 3 (powerDistance (3 : ℝ) x0) := by
  refine ⟨?_, ?_⟩
  · refine ⟨1 / 2, by positivity, ?_⟩
    sorry
  · sorry

instance :
    HasPositiveIteratedFDerivLipschitzConstantOfDegree 2 (powerDistance (2 : ℝ) x0) := by
  refine ⟨?_⟩
  sorry

instance :
    HasPositiveIteratedFDerivLipschitzConstantOfDegree 3 (powerDistance (3 : ℝ) x0) := by
  refine ⟨?_⟩
  sorry

-- Proof sketch: identify the Hessian of `powerDistance (2 : ℝ) x₀` with the identity map, so the
-- derivative-Lipschitz constant from Definition 4.2.11 is exactly `1`.
/-- Text 4.2.7 (1): on a nontrivial real inner-product space, for
`d₂ = powerDistance (2 : ℝ) x₀`, the degree-`2` Lipschitz constant
satisfies `L₂(d₂) = 1`. -/
theorem powerDistance_two_lipschitzConstant :
    L[2](powerDistance (2 : ℝ) x0) = 1 := sorry

-- Proof sketch: compute the Bregman remainder of `powerDistance (2 : ℝ) x₀` exactly as
-- `(1 / 2) * ‖y - x‖²`, then compare with the definition of
-- `uniformConvexityParameterOfDegree`.
/-- Text 4.2.7 (2): on a nontrivial real inner-product space, for
`d₂ = powerDistance (2 : ℝ) x₀`, the degree-`2` uniform-convexity
parameter satisfies `σ₂(d₂) = 1`. -/
theorem powerDistance_two_uniformConvexityParameter :
    σ[2](powerDistance (2 : ℝ) x0) = 1 := sorry

-- Proof sketch: combine the previous two identities with the definition
-- `γ₂(d₂) = σ₂(d₂) / L₂(d₂)`.
/-- Text 4.2.7 (3): on a nontrivial real inner-product space, for
`d₂ = powerDistance (2 : ℝ) x₀`, the degree-`2` condition number
satisfies `γ₂(d₂) = 1`. -/
theorem powerDistance_two_conditionNumber :
    γ[2](powerDistance (2 : ℝ) x0) = 1 := sorry

-- Proof sketch: use the cubic Hessian estimate from Lemma 4.2.4, applied to the translated cubic
-- power function centered at `x₀`, to identify the optimal degree-`3` derivative-Lipschitz
-- constant as `2`.
/-- Text 4.2.7 (4): on a nontrivial real inner-product space, for
`d₃ = powerDistance (3 : ℝ) x₀`, the degree-`3` Lipschitz constant
satisfies `L₃(d₃) = 2`. -/
theorem powerDistance_three_lipschitzConstant :
    L[3](powerDistance (3 : ℝ) x0) = 2 := sorry

-- Proof sketch: apply the monotonicity estimate for the cubic power function from the preceding
-- chapter lemmas and translate it into the first-order lower support inequality defining
-- `uniformConvexityParameterOfDegree`.
/-- Text 4.2.7 (5): on a nontrivial real inner-product space, for
`d₃ = powerDistance (3 : ℝ) x₀`, the degree-`3` uniform-convexity
parameter satisfies `σ₃(d₃) = 1 / 2`. -/
theorem powerDistance_three_uniformConvexityParameter :
    σ[3](powerDistance (3 : ℝ) x0) = 1 / 2 := sorry

-- Proof sketch: combine the cubic values of `σ₃` and `L₃` with the definition
-- `γ₃(d₃) = σ₃(d₃) / L₃(d₃)`.
/-- Text 4.2.7 (6): on a nontrivial real inner-product space, for
`d₃ = powerDistance (3 : ℝ) x₀`, the degree-`3` condition number
satisfies `γ₃(d₃) = 1 / 4`. -/
theorem powerDistance_three_conditionNumber :
    γ[3](powerDistance (3 : ℝ) x0) = 1 / 4 := sorry

end ExactValues

/-! ### Definition_4_2_8 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.2.8 lies in uniformly convex differentiable analysis on real Hilbert spaces.

Sampled owner-style declarations:
* mathlib `UniformConvexOn`
* mathlib `StrongConvexOn`
* Chapter 2 `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt` in `Definition_2_2`
* Chapter 3 `Definition_3_2_2`, which recalls strong convexity by the canonical owner and keeps
  the source first-order presentation as companion API

Best owner abstraction:
* source-facing: the degree-`p` uniform-convexity inequality with remainder
  `(1 / p) * σp * ‖y - x‖^p`
* core/canonical: `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* bridge/view: the first-order lower-support inequality phrased with `gradientWithin d Q`

Primitive data:
* a feasible set `Q`
* a function `d`
* a degree `p`
* the canonical fixed-modulus owner predicate `UniformConvexOn`
* at a fixed feasible base point, an explicit within-set gradient witness
  `HasGradientWithinAt d g Q x`

Derived API:
* existence of a positive modulus `σp` witnessing degree-`p` uniform convexity
* convexity of `Q`, already packaged by `UniformConvexOn`
* the chapter's first-order lower-support inequality with the degree-`p` remainder term
* the `gradientWithin` corollary obtained from `DifferentiableWithinAt ℝ d Q x`

This file therefore removes the duplicate local owner predicates, keeps the source-facing
degree-indexed existential surface as the main entry, reuses mathlib's fixed-modulus owner
`UniformConvexOn` as the canonical companion, and treats the `gradientWithin` statement as a
pointwise differentiability corollary of the primitive `HasGradientWithinAt` bridge. -/

/-- The degree-`p` modulus `r ↦ (1 / p) * σp * r^p` used in Definition 4.2.8. -/
abbrev uniformConvexPowerModulus (σp p : ℝ) : ℝ → ℝ :=
  fun r ↦ (1 / p) * σp * Real.rpow r p

section

variable {Q : Set E} {p : ℝ} {d : E → ℝ}

/- Definition 4.2.8: for a differentiable function on `Q`, the source-facing notion of
degree-`p` uniform convexity is that `p ≥ 2` and some positive modulus `σp` makes the canonical
fixed-modulus owner `UniformConvexOn Q (uniformConvexPowerModulus σp p) d` hold. The
first-order lower-support inequality below is the differentiable bridge for that existential
owner. -/
#check (2 ≤ p ∧ ∃ σp > 0, UniformConvexOn Q (uniformConvexPowerModulus σp p) d)

/-- Fixed-modulus first-order lower-support companion for Definition 4.2.8. -/
theorem uniformConvexOn_iff_lower_tangent_power
    {σp : ℝ}
    (hQ : Convex ℝ Q) (hd : DifferentiableOn ℝ d Q) :
    UniformConvexOn Q (uniformConvexPowerModulus σp p) d ↔
      ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
        d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
          uniformConvexPowerModulus σp p ‖y - x‖ := sorry

/-- Source-facing differentiable characterization of degree-`p` uniform convexity from
Definition 4.2.8. -/
theorem exists_pos_uniformConvexOn_iff_forall_lower_tangent_power
    (hQ : Convex ℝ Q) (hd : DifferentiableOn ℝ d Q) :
    (2 ≤ p ∧ ∃ σp > 0, UniformConvexOn Q (uniformConvexPowerModulus σp p) d) ↔
      2 ≤ p ∧
        ∃ σp > 0,
          ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
            d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
              uniformConvexPowerModulus σp p ‖y - x‖ := by
  constructor
  · rintro ⟨hp, σp, hσp, huniform⟩
    have hiff :
        UniformConvexOn Q (uniformConvexPowerModulus σp p) d ↔
          ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
            d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
              uniformConvexPowerModulus σp p ‖y - x‖ :=
      uniformConvexOn_iff_lower_tangent_power hQ hd
    refine ⟨hp, σp, hσp, ?_⟩
    exact hiff.mp huniform
  · rintro ⟨hp, σp, hσp, hlower⟩
    have hiff :
        UniformConvexOn Q (uniformConvexPowerModulus σp p) d ↔
          ∀ ⦃x y : E⦄, x ∈ Q → y ∈ Q →
            d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
              uniformConvexPowerModulus σp p ‖y - x‖ :=
      uniformConvexOn_iff_lower_tangent_power hQ hd
    refine ⟨hp, σp, hσp, ?_⟩
    exact hiff.mpr hlower

namespace UniformConvexOn

/-- A degree-`p` uniformly convex function lies above every feasible tangent plane arising from an
explicit within-set gradient witness, with the power remainder term from Definition 4.2.8. -/
theorem lower_tangent_power_of_hasGradientWithinAt
    {σp : ℝ}
    (huniform : UniformConvexOn Q (uniformConvexPowerModulus σp p) d)
    (x : E) (hx : x ∈ Q) (g : E) (hgrad : HasGradientWithinAt d g Q x) (y : E) (hy : y ∈ Q) :
    d y ≥ d x + inner ℝ g (y - x) + uniformConvexPowerModulus σp p ‖y - x‖ := sorry

/-- A degree-`p` uniformly convex function lies above the tangent plane determined by its
within-set gradient at a feasible base point, with the power remainder term from Definition
4.2.8. -/
theorem lower_tangent_power
    {σp : ℝ}
    (huniform : UniformConvexOn Q (uniformConvexPowerModulus σp p) d)
    (x : E) (hx : x ∈ Q) (hdiff : DifferentiableWithinAt ℝ d Q x) (y : E) (hy : y ∈ Q) :
    d y ≥ d x + inner ℝ (gradientWithin d Q x) (y - x) +
      uniformConvexPowerModulus σp p ‖y - x‖ := by
  simpa using
    huniform.lower_tangent_power_of_hasGradientWithinAt
      x hx (gradientWithin d Q x) hdiff.hasGradientWithinAt y hy

end UniformConvexOn

end

/-! ### Text_4_2_8 (from Chap04) -/
open scoped Gradient CubicRegularizationModelNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {L3 : NNReal} {f : E → ℝ} {M : ℝ} {x T : E}

/- Text 4.2.8 lies in the cubic-regularization / second-order smooth optimization domain on real
Hilbert spaces.

Sampled owner-style declarations:
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner for the
  cubic model;
* `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation` in `Lemma_4_1_4`, the
  owner-level gradient estimate for cubic-model minimizers;
* `objective_sub_cubicRegularizationValue_ge_residual_cube` in `Lemma_4_1_5`, the owner-level
  lower bound on `f x - \bar f_M(x)`;
* `objective_cubicTrialPoint_le_cubicRegularizationValue_of_le_hessianLipschitz` in
  `Lemma_4_1_5`, the bridge comparing a minimizing trial point with `\bar f_M(x)`.

Best owner abstraction:
* the chapter cubic-model owner `m[f; M](x)`
* the owner theorem
  `gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation`
* the owner value `cubicRegularizationValue f M x`

Primitive data:
* for the recall item, no new primitive data beyond the imported owner theorem;
* for the new source-facing estimate, the cubic model
  `m[f; M](x)`, a global minimizer witness
  `hT : IsMinOn (m[f; M](x)) Set.univ T`, and the owner
  hypotheses `hf : f ∈ C22[L3]`, `hf_conv : ConvexOn ℝ Set.univ f`, and `hML : (L3 : ℝ) ≤ M`

Derived API:
* the direct recall of Text 4.2.8 (1) from `Lemma_4_1_4`
* the objective decrease estimate under convexity and `M ≥ L3`

Source/core/bridge triage:
* source-facing: Text 4.2.8 (2)
* core/canonical: `m[f; M](x)`, `cubicRegularizationValue`, and the owner theorem from
  `Lemma_4_1_4`
* bridge/view: specializing those owners to a global minimizer `T`

The previous version duplicated the Chapter 4 owner theorem
`gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation` and even strengthened its
assumptions from `0 ≤ M` to `0 < M`. This refinement removes that duplicate wheel: part (1) is a
pure recall, while part (2) remains the only fresh source-facing declaration in this file. -/

/- Text 4.2.8 (1) is the direct Chapter 4 recall of the owner theorem from `Lemma_4_1_4`; this
file keeps no parallel local theorem shell. -/
recall gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation

-- Proof sketch: compare `f T` with `m[f; M](x; T)` using the
-- Chapter 4 objective-versus-model upper bound from `Lemma_4_1_5`, use the minimizing property
-- against the competitor `x`, and then rewrite the resulting cubic-model gap using the
-- first-order optimality relation of the minimizer. Convexity keeps the Hessian quadratic term
-- nonnegative, leaving the factor `(M / 3) ‖x - T‖³`.
/-- If `f` is convex, `f ∈ C22[L3]`, and `M ≥ L₃`, then every cubic-step minimizer `T`
satisfies `f x - f T ≥ (M / 3) ‖x - T‖³`. -/
theorem convex_sub_ge_of_isMinOn_cubicRegularizationQuadraticApproximation
    (hf : f ∈ C22[L3]) (hf_conv : ConvexOn ℝ Set.univ f) (hML : (L3 : ℝ) ≤ M)
    (hT : IsMinOn (m[f; M](x)) Set.univ T) :
    f x - f T ≥ (M / 3 : ℝ) * ‖x - T‖ ^ (3 : ℕ) := sorry

end

/-! ### Definition_4_2_9 (from Chap04) -/
noncomputable section

universe u

open LinearMap (BilinForm)
open scoped BInducedNorm

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 4.2.9 is source-facing in the chapter's `B`-induced norm geometry.

Sampled owner-style declarations:
- `powerDistance` in `Text_4_2_6`
- `powerDistance_apply` in `Text_4_2_6`
- the notation layer `‖x‖[B]` from `Definition_4_3_4`

Best owner abstraction:
- source-facing: the degree-`p` power function centered at `x₀` in the `B`-induced geometry
- core/canonical: the public owner carrier `LinearMap.BilinForm.PrimalSpace B`, equipped with the
  norm and inner product induced by `B`
- bridge/view: the earlier chapter owner `powerDistance p x₀` on that intrinsic carrier

Primitive data:
- `B : BilinForm ℝ E`
- `p : ℝ`
- `x₀ : E`

Derived API:
- the intrinsic carrier `LinearMap.BilinForm.PrimalSpace B`
- the induced norm `‖x‖[B]`, now realized as the ambient norm on `PrimalSpace B`
- the source-facing owner `powerFunction B p x₀`
- the pointwise formula `x ↦ (1 / p) * ‖x - x₀‖[B]^p`

The public owner therefore stays the source-facing `B`-power function, but it now lives on the
intrinsic `B`-weighted carrier and reuses the earlier chapter owner `powerDistance` there instead
of rebuilding the `B`-normed-space structure privately.
-/
namespace LinearMap.BilinForm

/-- The carrier `E`, equipped with the norm induced by the symmetric positive-definite bilinear
form owner `B`. -/
abbrev PrimalSpace (_B : BilinForm ℝ E) := E

/-- The additive norm induced on the carrier `PrimalSpace B` by the primal seminorm of `B`. -/
def primalAddGroupNorm
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef] :
    AddGroupNorm (PrimalSpace B) :=
  let p : Seminorm ℝ E := B.primalSeminorm Fact.out
  { toFun := p
    map_zero' := map_zero p
    add_le' := map_add_le_add p
    neg' := map_neg_eq_map p
    eq_zero_of_map_eq_zero' := fun _ hx ↦
      let _ : Seminorm.IsNorm p := B.primalSeminorm_isNorm Fact.out
      Seminorm.IsNorm.eq_zero_of_map_eq_zero hx }

instance (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef] :
    NormedAddCommGroup (PrimalSpace B) :=
  AddGroupNorm.toNormedAddCommGroup (primalAddGroupNorm B)

instance (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef] :
    NormedSpace ℝ (PrimalSpace B) :=
  { norm_smul_le := fun a x ↦ by
      let p : Seminorm ℝ E := B.primalSeminorm Fact.out
      change p (a • x) ≤ ‖a‖ * p x
      exact le_of_eq (p.smul' a x) }

/-- On the intrinsic carrier `PrimalSpace B`, the ambient norm is exactly the chapter notation
`‖·‖[B]`. -/
@[simp] theorem primalSpace_norm_eq_bInducedNorm
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef] (x : PrimalSpace B) :
    ‖x‖ = B.primalSeminorm Fact.out x :=
  rfl

end LinearMap.BilinForm

/-- Definition 4.2.9: for a fixed center `x₀` and a positive-definite self-adjoint bilinear form
`B`, the degree-`p` power function is `x ↦ (1 / p) * ‖x - x₀‖[B]^p`. -/
def powerFunction (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef] (p : ℝ)
    (x0 : LinearMap.BilinForm.PrimalSpace B) : LinearMap.BilinForm.PrimalSpace B → ℝ :=
  powerDistance p x0

/-- Evaluating `powerFunction B p x₀` at `x` gives `(1 / p) * ‖x - x₀‖^p` in the intrinsic
`B`-weighted norm on `PrimalSpace B`. -/
theorem powerFunction_apply (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef] (p : ℝ)
    (x0 x : LinearMap.BilinForm.PrimalSpace B) :
    powerFunction B p x0 x = (1 / p) * Real.rpow ‖x - x0‖ p := by
  rfl

/-! ### Text_4_2_9 (from Chap04) -/
/- Text 4.2.9 is the subsection heading "Complexity of Non-degenerate Problems", so its primary
domain is the chapter's nondegenerate cubic-Newton complexity theory rather than the bilinear-form
`B`-geometry of `Definition_4_2_9`.

Mandatory domain-style sampling before refinement:
- `conditionNumberOfDegree` in `Definition_4_2_11`, the chapter owner of the conditioning ratio
  `γ[p](f) = σ[p](f) / L[p](f)`;
- `IsFirstOrderNondegenerate` in `Definition_4_2_15`, the source-facing owner for the
  nondegeneracy property itself;
- `cubic_newton_gap_le_linear_rate` in `Text_4_2_10`, the owner linear-rate estimate in this
  subsection;
- `cubic_newton_gap_le_of_iteration_count_bound` in `Text_4_2_10`, the owner iteration-complexity
  bound for the subsection.

Best owner abstraction:
- source-facing: Text 4.2.9 is a subsection-label item announcing the complexity theory for the
  nondegenerate regime;
- core/canonical: the subsection's complexity owner theorem
  `cubic_newton_gap_le_of_iteration_count_bound`;
- bridge/view: the one-step linear-rate estimate `cubic_newton_gap_le_linear_rate`, together with
  the conditioning owners `σ[p]`, `L[p]`, and `γ[p]`.

Primitive data:
- no new primitive mathematical data belong to this heading item itself.

Derived API:
- the subsection's canonical complexity theorem from `Text_4_2_10`.

This file therefore stays recall-only. The previous theorem about a linear-plus-cubic minimizer in
the `B`-induced geometry did not match the textbook semantics of 4.2.9 and duplicated an
unrelated owner layer. -/

/- Text 4.2.9 ("Complexity of Non-degenerate Problems"): the subsection's canonical complexity
surface is the cubic-Newton iteration bound stated in Text 4.2.10. -/
recall cubic_newton_gap_le_of_iteration_count_bound

/-! ### Definition_4_2_10 (from Chap04) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (p : ℕ) (f : E → ℝ) (s : Set E) (L : NNReal)

local notation "TaylorSeries" => E → FormalMultilinearSeries ℝ E ℝ

/- Definition 4.2.10 lies in the on-set higher-order Taylor-coefficient Lipschitz domain.

Sampled owner-style declarations:
* `taylorCoeffLipschitzClass`
* `HasFTaylorSeriesUpToOn`
* `HasFTaylorSeriesUpToOn.contDiffOn`
* `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`

Owner abstraction:
* the Chapter 1 source-facing owner `taylorCoeffLipschitzClass`
* this item is the self-order specialization `f ∈ 𝒞^{p - 1,p - 1}_{L}(s)`

Source/core/bridge triage:
* source-facing: `f ∈ 𝒞^{p - 1,p - 1}_{L}(s)`
* core/canonical: `HasFTaylorSeriesUpToOn (p - 1) f P s`
* bridge/view: the `iteratedFDerivWithin` formula recovered on `UniqueDiffOn ℝ s`

Primitive data:
* a Taylor witness `P`
* `HasFTaylorSeriesUpToOn (p - 1) f P s`
* `LipschitzOnWith L (fun x ↦ P x (p - 1)) s`

Derived API:
* `ContDiffOn ℝ (p - 1) f s`
* the source-style `iteratedFDerivWithin` norm estimate on `UniqueDiffOn ℝ s`

This file does not introduce a second owner around `iteratedFDerivWithin`; it reuses the
Chapter 1 owner and keeps the iterated-derivative formula only as a bridge.
-/

/- Definition 4.2.10: a nonnegative constant `L` is a Lipschitz constant for the `(p - 1)`-st
derivative of `f` on `s` exactly when `f` belongs to the Chapter 1 owner
`𝒞^{p - 1,p - 1}_{L}(s)`. The `iteratedFDerivWithin` presentation is a bridge view recovered
under `UniqueDiffOn ℝ s`, not the primitive owner.
-/
#check (f ∈ 𝒞^{p - 1,p - 1}_{L}(s))

namespace taylorCoeffLipschitzClass

theorem contDiffOn
    {p : ℕ} {f : E → ℝ} {s : Set E} {L : NNReal}
    (hf : f ∈ 𝒞^{p - 1,p - 1}_{L}(s)) :
    ContDiffOn ℝ (p - 1) f s := by
  rcases hf.2 with ⟨P, hP, _⟩
  exact hP.contDiffOn

/-- On a set with unique differentiability, membership in `𝒞^{p - 1,p - 1}_{L}(s)` recovers the
source-style pointwise Lipschitz estimate for `iteratedFDerivWithin ℝ (p - 1) f s`. -/
theorem norm_sub_le_iteratedFDerivWithin
    {p : ℕ} {f : E → ℝ} {s : Set E} {L : NNReal}
    (hf : f ∈ 𝒞^{p - 1,p - 1}_{L}(s)) (hs : UniqueDiffOn ℝ s)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖iteratedFDerivWithin ℝ (p - 1) f s x - iteratedFDerivWithin ℝ (p - 1) f s y‖ ≤
      (L : ℝ) * ‖x - y‖ := by
  rcases hf.2 with ⟨P, hP, hLip⟩
  simpa [hP.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hs hx,
    hP.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hs hy] using hLip.norm_sub_le hx hy

end taylorCoeffLipschitzClass

/-! ### Text_4_2_10 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.10 lies in the cubic-Newton linear-rate domain on a real Hilbert space.

Sampled owner-style declarations:
* `conditionNumberOfDegree` in `Definition_4_2_11`
* `uniformConvexityParameterOfDegree` in `Definition_4_2_11`
* `iteratedFDerivLipschitzConstantOfDegree` in `Definition_4_2_11`
* `cubicNewtonQuadraticDecreaseRegion` in `Text_4_2_11`, where the source threshold is rewritten
  in multiplication form to avoid division-by-zero artifacts
* `acceleratedCubicNewtonQuadraticConvergenceRegion` in `Text_4_2_22`, which uses the same
  multiplication-form threshold discipline for the local cubic region
* the positive-parameter owner style in `Lemma_4_4_8`, where `NNRealˣ` carries positivity in the
  public API instead of separate proof binders

Best owner abstraction:
* source-facing: the cubic-Newton rate bounds driven by arbitrary positive parameters `σ₃` and
  `L₃` satisfying the textbook gap and descent inequalities
* core/canonical: the chapter owner `γ[3](f)` for the degree-`3` condition number of a function
* bridge/view: the contraction factor `2 √L₃ / (2 √L₃ + √σ₃)`, equivalent to
  `(1 + (1 / 2) * sqrt (σ₃ / L₃))⁻¹`

Primitive data:
* a function `f`, a reference point `xStar`, and an iterate sequence `x`
* positive scalars `σ₃`, `L₃`, now owned canonically as `NNRealˣ`
* the two source hypotheses bounding the gap by `‖∇ f‖^(3/2)` and the one-step decrease by
  `‖∇ f‖^(3/2)`, stated in multiplication form rather than through `1 / sqrt σ₃` and
  `1 / sqrt L₃`

Derived API:
* the contraction factor `2 √L₃ / (2 √L₃ + √σ₃)` and its exponential companion
  `√σ₃ / (2 √L₃ + √σ₃)`

Semantic-priority note:
* the file remains source-facing over arbitrary `σ₃` and `L₃`; replacing them by the canonical
  owner `γ[3](f)` would change the theorem interface from textbook assumptions to a stronger
  function-level conditioning API.
* the refined statements keep those source parameters, but encode their positivity by `NNRealˣ`
  and rewrite the public inequalities in multiplication form, following the nearby chapter style
  that avoids division-by-zero and `Real.sqrt` artifacts in theorem surfaces.
-/

section CubicNewtonConditionNumberRate

variable {f : E → ℝ} {x : ℕ → E} {xStar : E} {σ₃ L₃ : NNRealˣ}

local notation "Δ" => fun k : ℕ ↦ f (x k) - f xStar
local notation "ρ" =>
  ((2 : ℝ) * Real.sqrt (L₃ : ℝ)) / ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))

-- Proof sketch: apply the global gap estimate at `x_{k+1}` to bound
-- `Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2)` from below, then substitute that lower bound into the
-- assumed one-step descent inequality. Writing the source bounds in multiplication form yields
-- `√σ₃ * Δ_{k+1} ≤ 2 √L₃ * (f(x_k) - f(x_{k+1}))`, which is equivalent to the textbook factor
-- `(1 / 2) * sqrt (σ₃ / L₃)` because `σ₃, L₃ > 0` are owned by `NNRealˣ`.
/-- Text 4.2.10 (1): if
`3 √σ₃ (f x - f xStar) ≤ 2 ‖∇ f x‖^(3/2)` for every `x`, and if the sequence `x`
satisfies
`‖∇ f(x_{k+1})‖^(3/2) ≤ 3 √L₃ (f(x_k) - f(x_{k+1}))`,
then each one-step decrease controls the next gap by
`√σ₃ (f(x_{k+1}) - f(xStar)) ≤ 2 √L₃ (f(x_k) - f(x_{k+1}))`, equivalently by the textbook
factor `(1 / 2) * sqrt (σ₃ / L₃)`. -/
theorem cubic_newton_objective_drop_ge_half_sqrt_conditionNumber_mul_next_gap
    (hgap :
      ∀ z : E,
        (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * (f z - f xStar) ≤
          (2 : ℝ) * Real.rpow ‖∇ f z‖ (3 / 2 : ℝ))
    (hdescent :
      ∀ k : ℕ,
        Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2 : ℝ) ≤
          (3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))
    (k : ℕ) :
    Real.sqrt (σ₃ : ℝ) * Δ (k + 1) ≤
      (2 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))) := sorry

-- Proof sketch: apply the one-step estimate from
-- `cubic_newton_objective_drop_ge_half_sqrt_conditionNumber_mul_next_gap` to the gaps
-- `Δ_k = f (x k) - f xStar`, rewrite it as
-- `Δ_{k+1} ≤ ρ * Δ_k` with `ρ = 2 √L₃ / (2 √L₃ + √σ₃)`, and iterate this scalar recurrence from
-- `1` to `k - 1`.
/-- Text 4.2.10 (2): under the same assumptions, the objective gaps along `x` decay at the linear
rate
`ρ^(k-1)` with `ρ = 2 √L₃ / (2 √L₃ + √σ₃) =
(1 + (1 / 2) * sqrt (σ₃ / L₃))⁻¹` for every `k ≥ 1`. -/
theorem cubic_newton_gap_le_linear_rate
    (hgap :
      ∀ z : E,
        (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * (f z - f xStar) ≤
          (2 : ℝ) * Real.rpow ‖∇ f z‖ (3 / 2 : ℝ))
    (hdescent :
      ∀ k : ℕ,
        Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2 : ℝ) ≤
          (3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))
    {k : ℕ} (hk : 1 ≤ k) :
    Δ k ≤ ρ ^ (k - 1) * Δ 1 := sorry

-- Proof sketch: combine `cubic_newton_gap_le_linear_rate` with the initial cubic upper bound on
-- `f (x 1) - f xStar`, then use
-- `ρ ≤ exp (-√σ₃ / (2 √L₃ + √σ₃))` to bound the geometric factor by the displayed exponential
-- term.
/-- Text 4.2.10 (3): if in addition the first gap satisfies
`3 (f(x₁) - f(xStar)) ≤ L₃ ‖x₀ - xStar‖³`, then for every `k ≥ 1` the gap is bounded by the
displayed exponential expression, written with the equivalent rate coefficient
`√σ₃ / (2 √L₃ + √σ₃)`. -/
theorem cubic_newton_gap_le_exponential_rate
    (hgap :
      ∀ z : E,
        (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * (f z - f xStar) ≤
          (2 : ℝ) * Real.rpow ‖∇ f z‖ (3 / 2 : ℝ))
    (hdescent :
      ∀ k : ℕ,
        Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2 : ℝ) ≤
          (3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))
    (hinit :
      (3 : ℝ) * (f (x 1) - f xStar) ≤ (L₃ : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ))
    {k : ℕ} (hk : 1 ≤ k) :
    Δ k ≤
      Real.exp
          (-(Real.sqrt (σ₃ : ℝ) * (k - 1 : ℝ)) /
            ((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ))) *
        (((L₃ : ℝ) / 3 : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ)) := sorry

-- Proof sketch: start from `cubic_newton_gap_le_exponential_rate`, replace `‖x 0 - xStar‖` by
-- the bound `D`, and solve the resulting exponential inequality for `k` in terms of `ε` by
-- taking logarithms. The lower bound on `k` is written in multiplication form to avoid the
-- surface factor `(2 √L₃ + √σ₃) / √σ₃`.
/-- Text 4.2.10 (4): if `‖x₀ - xStar‖ ≤ D`, then the target accuracy `f(x_k) - f(xStar) ≤ ε` is
guaranteed once `k` satisfies the explicit logarithmic lower bound corresponding to the textbook
`O((√L₃ / √σ₃) * log (L₃ D^3 / ε))` estimate, stated in multiplication form. -/
theorem cubic_newton_gap_le_of_iteration_count_bound
    (hgap :
      ∀ z : E,
        (3 : ℝ) * Real.sqrt (σ₃ : ℝ) * (f z - f xStar) ≤
          (2 : ℝ) * Real.rpow ‖∇ f z‖ (3 / 2 : ℝ))
    (hdescent :
      ∀ k : ℕ,
        Real.rpow ‖∇ f (x (k + 1))‖ (3 / 2 : ℝ) ≤
          (3 : ℝ) * Real.sqrt (L₃ : ℝ) * (f (x k) - f (x (k + 1))))
    (hinit :
      (3 : ℝ) * (f (x 1) - f xStar) ≤ (L₃ : ℝ) * ‖x 0 - xStar‖ ^ (3 : ℕ))
    {D ε : ℝ}
    (hD : ‖x 0 - xStar‖ ≤ D)
    (hε : 0 < ε)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hk_bound :
      (((2 : ℝ) * Real.sqrt (L₃ : ℝ) + Real.sqrt (σ₃ : ℝ)) *
          Real.log ((((L₃ : ℝ) / 3 : ℝ) * D ^ (3 : ℕ)) / ε) ≤
        (k - 1 : ℝ) * Real.sqrt (σ₃ : ℝ))) :
    Δ k ≤ ε := sorry

end CubicNewtonConditionNumberRate

/-! ### Definition_4_2_11 (from Chap04) -/
noncomputable section

universe u

/- Definition 4.2.11 lies in Chapter 4's higher-order conditioning domain.

Sampled owner-style declarations:
* project `f ∈ 𝒞^{p - 1,p - 1}_{L}(s)` in `Definition_4_2_10`
* project `uniformConvexPowerModulus` in `Definition_4_2_8`
* mathlib `LipschitzWith`
* mathlib `UniformConvexOn`

Best owner abstraction:
* source-facing: the global quantities `σ_p(f)`, `L_p(f)`, and `γ_p(f)`
* core/canonical: `f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)` together with
  `UniformConvexOn Set.univ (uniformConvexPowerModulus σ p) f`
* source-facing finiteness owner: `HasIteratedFDerivLipschitzConstantOfDegree p f`
* bridge/view: the source-style whole-space iterated-derivative norm estimate recovered from the
  `Set.univ` owner in `Definition_4_2_10`

Primitive data:
* whole-space degree-`p` uniform convexity, already owned by `UniformConvexOn`
* whole-space degree-`p` iterated-derivative Lipschitz control, already owned upstream by the
  `Set.univ` specialization `f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)` with `L : NNReal`
* finiteness of that control, recorded directly by the owner class
  `HasIteratedFDerivLipschitzConstantOfDegree p f`
* finiteness of the degree-`p` uniform-convexity parameter, recorded by the owner class
  `HasUniformConvexityParameterOfDegree p f`
* positivity of the canonical degree-`p` Lipschitz constant when the source ratio `γ_p(f)` is
  used as an honest real quotient, recorded by
  `HasPositiveIteratedFDerivLipschitzConstantOfDegree p f`

Derived API:
* the source-style whole-space norm estimate for `iteratedFDeriv ℝ (p - 1) f`
* the canonical infimum `L_p(f)` once `f` admits a finite degree-`p` derivative Lipschitz
  constant
* the canonical supremum `σ_p(f)` once the degree-`p` uniform-convexity witnesses are known to be
  nonempty and bounded above
* the quotient `γ_p(f) = σ_p(f) / L_p(f)` once `L_p(f)` is known to be strictly positive

This file therefore keeps the Chapter 4 quantities as the public source-facing owners and reduces
the whole-space derivative-Lipschitz layer to the upstream `Set.univ` owner
`f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)` instead of duplicating it through a real-valued wrapper
predicate. It also makes explicit the owner hypotheses needed for the real-valued source
parameters: `L_p(f)` keeps its canonical infimum definition on the finite-Lipschitz owner,
`σ_p(f)` is only formed when the source witness set is nonempty and bounded above, and `γ_p(f)`
is only formed when the canonical denominator `L_p(f)` is strictly positive. -/

section Smoothness

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function admits a finite degree-`p` Lipschitz constant when some nonnegative constant
witnesses the whole-space owner predicate from Definition 4.2.10. -/
class HasIteratedFDerivLipschitzConstantOfDegree (p : ℕ) (f : E → ℝ) : Prop where
  /-- Existence of a global degree-`p` Lipschitz constant for the `(p - 1)`st derivative of `f`.
  -/
  exists_mem : ∃ L : NNReal, f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)

namespace HasIteratedFDerivLipschitzConstantOfDegree

/-- A concrete degree-`p` Lipschitz constant yields the finiteness owner. -/
theorem of_constant
    {L : NNReal} {p : ℕ} {f : E → ℝ}
    (hL : f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)) :
    HasIteratedFDerivLipschitzConstantOfDegree p f :=
  ⟨⟨L, hL⟩⟩

/-- An existential degree-`p` Lipschitz witness yields the finiteness owner. -/
theorem of_exists
    {p : ℕ} {f : E → ℝ}
    (h : ∃ L : NNReal, f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)) :
    HasIteratedFDerivLipschitzConstantOfDegree p f :=
  ⟨h⟩

/-- Finite degree-`p` Lipschitz control of the `(p - 1)`st derivative implies
`C^(p - 1)` regularity. -/
theorem contDiff
    {p : ℕ} {f : E → ℝ}
    [hf : HasIteratedFDerivLipschitzConstantOfDegree p f] :
    ContDiff ℝ (p - 1 : ℕ) f := by
  rcases hf.exists_mem with ⟨L, hL⟩
  exact contDiffOn_univ.mp <| taylorCoeffLipschitzClass.contDiffOn hL

/-- The upstream owner recovers the source-style global norm estimate for the `(p - 1)`st
iterated derivative. -/
theorem norm_sub_le
    {L : NNReal} {p : ℕ} {f : E → ℝ}
    (hL : f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ))
    (x y : E) :
    ‖iteratedFDeriv ℝ (p - 1) f x - iteratedFDeriv ℝ (p - 1) f y‖ ≤ (L : ℝ) * ‖x - y‖ := by
  simpa [iteratedFDerivWithin_univ] using
    taylorCoeffLipschitzClass.norm_sub_le_iteratedFDerivWithin hL
      (uniqueDiffOn_univ : UniqueDiffOn ℝ (Set.univ : Set E)) (by simp) (by simp)

end HasIteratedFDerivLipschitzConstantOfDegree

/-- The canonical degree-`p` Lipschitz constant `L_p(f)`, defined as the infimum of all global
Lipschitz constants for the `(p - 1)`st derivative of `f` once `f` admits such a constant. -/
def iteratedFDerivLipschitzConstantOfDegree
    (f : E → ℝ) (p : ℕ) [HasIteratedFDerivLipschitzConstantOfDegree p f] : NNReal :=
  sInf {L : NNReal | f ∈ 𝒞^{p - 1,p - 1}_{L}(Set.univ)}

/-- The canonical degree-`p` Lipschitz constant is strictly positive. This owner is the domain on
which the source ratio `γ_p(f)` is a genuine real quotient rather than a totalized zero-division
artifact. -/
class HasPositiveIteratedFDerivLipschitzConstantOfDegree
    (p : ℕ) (f : E → ℝ) [HasIteratedFDerivLipschitzConstantOfDegree p f] : Prop where
  /-- Positivity of the canonical infimum `L_p(f)`. -/
  pos : 0 < (iteratedFDerivLipschitzConstantOfDegree f p : ℝ)

namespace HasPositiveIteratedFDerivLipschitzConstantOfDegree

theorem lipschitzConstant_pos
    {p : ℕ} {f : E → ℝ}
    [HasIteratedFDerivLipschitzConstantOfDegree p f]
    [hf : HasPositiveIteratedFDerivLipschitzConstantOfDegree p f] :
    0 < (iteratedFDerivLipschitzConstantOfDegree f p : ℝ) :=
  hf.pos

end HasPositiveIteratedFDerivLipschitzConstantOfDegree

end Smoothness

section Conditioning

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function admits a finite degree-`p` uniform-convexity parameter when the positive whole-space
degree-`p` uniform-convexity witnesses form a nonempty set that is bounded above in `ℝ`. This is
exactly the domain on which the source supremum `σ_p(f)` is a genuine real parameter. -/
class HasUniformConvexityParameterOfDegree (p : ℕ) (f : E → ℝ) : Prop where
  /-- Existence of a positive whole-space degree-`p` uniform-convexity witness. -/
  exists_mem : ∃ σ > 0,
    UniformConvexOn Set.univ (uniformConvexPowerModulus σ (p : ℝ)) f
  /-- The positive witness set defining `σ_p(f)` is bounded above in `ℝ`. -/
  bddAbove : BddAbove
    {σ : ℝ | 0 < σ ∧ UniformConvexOn Set.univ (uniformConvexPowerModulus σ (p : ℝ)) f}

namespace HasUniformConvexityParameterOfDegree

theorem nonempty
    {p : ℕ} {f : E → ℝ}
    [hf : HasUniformConvexityParameterOfDegree p f] :
    Set.Nonempty
      {σ : ℝ | 0 < σ ∧ UniformConvexOn Set.univ (uniformConvexPowerModulus σ (p : ℝ)) f} := by
  rcases hf.exists_mem with ⟨σ, hσ, huniform⟩
  exact ⟨σ, hσ, huniform⟩

end HasUniformConvexityParameterOfDegree

/-- The canonical degree-`p` uniform-convexity parameter `σ_p(f)`, defined as the supremum of all
positive constants whose degree-`p` power modulus witnesses the canonical owner predicate
`UniformConvexOn Set.univ`. This source quantity is formed only on the owner
`HasUniformConvexityParameterOfDegree p f`, which records that the defining witness set is
nonempty and bounded above. -/
def uniformConvexityParameterOfDegree
    (f : E → ℝ) (p : ℕ) [HasUniformConvexityParameterOfDegree p f] : ℝ :=
  sSup
    {σ : ℝ |
      0 < σ ∧ UniformConvexOn Set.univ (uniformConvexPowerModulus σ (p : ℝ)) f}

namespace HasUniformConvexityParameterOfDegree

theorem le_uniformConvexityParameterOfDegree
    {p : ℕ} {f : E → ℝ} [hf : HasUniformConvexityParameterOfDegree p f]
    {σ : ℝ}
    (hσ : 0 < σ)
    (huniform : UniformConvexOn Set.univ (uniformConvexPowerModulus σ (p : ℝ)) f) :
    σ ≤ uniformConvexityParameterOfDegree f p :=
  le_csSup hf.bddAbove ⟨hσ, huniform⟩

theorem uniformConvexityParameterOfDegree_pos
    {p : ℕ} {f : E → ℝ} [hf : HasUniformConvexityParameterOfDegree p f] :
    0 < uniformConvexityParameterOfDegree f p := by
  rcases hf.exists_mem with ⟨σ, hσ, huniform⟩
  exact lt_of_lt_of_le hσ <| le_uniformConvexityParameterOfDegree hσ huniform

end HasUniformConvexityParameterOfDegree

/-- Definition 4.2.11: for a function `f` and degree `p`, the degree-`p` condition number
`γ_p(f)` is the ratio `σ_p(f) / L_p(f)` of its degree-`p` uniform-convexity parameter and its
degree-`p` Lipschitz constant for the `(p - 1)`st derivative. This is defined only when `σ_p(f)`
is a genuine real parameter and the canonical denominator `L_p(f)` is strictly positive. -/
def conditionNumberOfDegree
    (f : E → ℝ) (p : ℕ)
    [HasUniformConvexityParameterOfDegree p f]
    [HasIteratedFDerivLipschitzConstantOfDegree p f]
    [HasPositiveIteratedFDerivLipschitzConstantOfDegree p f] : ℝ :=
  uniformConvexityParameterOfDegree f p / iteratedFDerivLipschitzConstantOfDegree f p

end Conditioning

namespace DegreeConditioning

scoped notation:max "L[" p "](" f ")" => iteratedFDerivLipschitzConstantOfDegree f p
scoped notation:max "σ[" p "](" f ")" => uniformConvexityParameterOfDegree f p
scoped notation:max "γ[" p "](" f ")" => conditionNumberOfDegree f p

end DegreeConditioning

open scoped DegreeConditioning

/-- Expanding `γ[p](f)` recovers the quotient `σ[p](f) / L[p](f)`. -/
theorem conditionNumberOfDegree_eq_ratio
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (p : ℕ)
    [HasUniformConvexityParameterOfDegree p f]
    [HasIteratedFDerivLipschitzConstantOfDegree p f]
    [HasPositiveIteratedFDerivLipschitzConstantOfDegree p f] :
    γ[p](f) = σ[p](f) / L[p](f) :=
  rfl
