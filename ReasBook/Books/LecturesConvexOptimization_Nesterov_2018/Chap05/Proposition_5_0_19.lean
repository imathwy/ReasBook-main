import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_3_3
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_4_16
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin Gradient
open ContinuousLinearMap

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}

/- Proposition 5.0.19 lies in the chapter's partial-minimization / second-order calculus domain.

Sampled owner-style declarations:
- `partialInfProjection` in `Chap03/Theorem_3_1_2_3`, the chapter owner for constrained
  fiberwise infima;
- `extendedRealRealPart_partialInfProjection_eq_sInf_image` in `Chap05/Definition_5_0_18`, the
  real-valued bridge for that owner on finite fibers;
- `hessian` in `Chap01/Definition_1_4_16`, the canonical frozen-slice owner for the `yy`
  second-derivative block;
- `hessian` in `Chap01/Definition_1_4_16`, the intrinsic second-order owner on a real
  inner-product space, here used on the canonical `L²` product lift `Z = WithLp 2 (E₁ × E₂)`.

Best owner abstraction:
- source-facing: `extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))`;
- core/canonical: `partialInfProjection Q (Real.toEReal ∘ Φ)`,
  `extendedRealRealPart`, and the frozen-slice Hessian
  `hessian (Φ ∘ Prod.mk x) y`;
- bridge/view: the `x`-slice gradient and the ambient Hessian block formulas obtained by
  composing `hessian (Φ ∘ WithLp.ofLp) (WithLp.toLp 2 (x, y))` with
  `WithLp.fstL`/`WithLp.sndL` and the canonical product-coordinate inclusions.

Primitive data:
- the feasible set `Q : Set (E₁ × E₂)`;
- the objective `Φ : E₁ × E₂ → ℝ`;
- the selected minimizing branch `y : E₁ → E₂`.

Derived API:
- the `x`-slice gradient `∇ (fun x' ↦ Φ (x', y)) x`;
- the inverse-Hessian-based implicit-derivative and Schur-complement operators
  `partialMinimizerImplicitFDeriv` and `partialMinimizationSchurHessian`.

Source/core/bridge triage:
- source-facing: Proposition 5.0.19 and its envelope / implicit-function / Schur-complement
  conclusions for the real surface of the canonical infimal projection;
- core/canonical: `partialInfProjection`, `extendedRealRealPart`,
  the frozen-slice Hessian `hessian (Φ ∘ Prod.mk x) y`, and `hessian` on the intrinsic
  product lift `Z`;
- bridge/view: the displayed `x`-slice gradient and the inverse-`yy` / Schur-complement
  constructions below, written directly from the ambient Hessian with internal mixed-block
  helpers.

This refinement keeps the proposition on the chapter's canonical infimal-projection owner,
uses the canonical frozen-slice Hessian for the `yy` second-order data directly, and packages the
remaining mixed-block formulas into the minimal derived operator API needed by the proposition.
-/

section Value

variable [TopologicalSpace E₁]

/-- Proposition 5.0.19 (1): on any neighborhood where `y` realizes the fiberwise minima of `Φ`
over `Q`, the canonical real surface of the partial infimal projection agrees with the minimizing
branch `u ↦ Φ (u, y u)`. -/
-- Proof sketch: for each nearby `u`, the hypothesis `hy_argmin` identifies `y u` as the canonical
-- fiber minimizer over `{z | (u, z) ∈ Q}`. The
-- canonical Chapter 5 bridge from `extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘
-- Φ)) u` to the fiber infimum therefore evaluates to `Φ (u, y u)`, yielding eventual equality.
theorem partialMinimizationObjective_eventuallyEq_of_eventually_argmin
    (Q : Set (E₁ × E₂)) (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₁ → E₂)
    (hy_argmin : ∀ᶠ u in nhds x,
      y u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u)) :
    extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ)) =ᶠ[nhds x]
      fun u ↦ Φ (u, y u) := sorry

end Value

section FirstOrder

variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

variable {Q : Set (E₁ × E₂)} {Φ : E₁ × E₂ → ℝ} {x : E₁} {y : E₁ → E₂}

local notation "f" => extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))

section

variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Helper: if `Φ` is `C¹` at `(x, y x)`, the minimizing branch `y` is differentiable at `x`,
the point `(x, y x)` lies in `interior Q`, and `y x` realizes the fiberwise minimum of `Φ` over
the `x`-fiber of `Q`, then the branch `u ↦ Φ (u, y u)` has the envelope gradient
`∇ (fun u' ↦ Φ (u', y x)) x` at `x`. -/
theorem partialMinimizationBranch_hasGradientAt_xGradient_of_mem_argmin
    (hΦ : ContDiffAt ℝ 1 Φ (x, y x))
    (hy : DifferentiableAt ℝ y x)
    (hxy_mem_interior : (x, y x) ∈ interior Q)
    (hy_argmin :
      y x ∈ argmin[(Prod.mk x) ⁻¹' Q] (Φ ∘ Prod.mk x)) :
    HasGradientAt (fun u ↦ Φ (u, y u)) (∇ (fun u' ↦ Φ (u', y x)) x) x := sorry

/-- Proposition 5.0.19 (1): if `Φ` is `C¹` at `(x, y x)`, the minimizing branch `y` is
differentiable at `x`, the base point `(x, y x)` lies in `interior Q`, and `y` realizes the
fiberwise minima of `Φ` near `x`, then the partial-minimization objective has gradient
`∇ (fun u' ↦ Φ (u', y x)) x` at `x`. -/
theorem partialMinimizationObjective_hasGradientAt_of_eventually_argmin
    (hΦ : ContDiffAt ℝ 1 Φ (x, y x))
    (hy : DifferentiableAt ℝ y x)
    (hxy_mem_interior : (x, y x) ∈ interior Q)
    (hy_argmin : ∀ᶠ u in nhds x,
      y u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u)) :
    HasGradientAt f (∇ (fun u' ↦ Φ (u', y x)) x) x := by
  exact
    (partialMinimizationBranch_hasGradientAt_xGradient_of_mem_argmin
      hΦ hy hxy_mem_interior hy_argmin.self_of_nhds).congr_of_eventuallyEq
      (partialMinimizationObjective_eventuallyEq_of_eventually_argmin Q Φ x y hy_argmin)

/-- Proposition 5.0.19 (1), pointwise form: if `Φ` is `C¹` at `(x, y x)`, the minimizing branch
`y` is differentiable at `x`, the base point `(x, y x)` lies in `interior Q`, and `y` realizes the
fiberwise minima of `Φ` near `x`, then the gradient of the partial-minimization objective is the
`x`-gradient of `Φ` with `y` frozen at `y x`. -/
theorem partialMinimizationObjective_gradient_eq_xGradient_of_eventually_argmin
    (hΦ : ContDiffAt ℝ 1 Φ (x, y x))
    (hy : DifferentiableAt ℝ y x)
    (hxy_mem_interior : (x, y x) ∈ interior Q)
    (hy_argmin : ∀ᶠ u in nhds x,
      y u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u)) :
    ∇ f x = ∇ (fun u' ↦ Φ (u', y x)) x := by
  exact
    (partialMinimizationObjective_hasGradientAt_of_eventually_argmin
      hΦ hy hxy_mem_interior hy_argmin).gradient

end

end FirstOrder

section SecondOrder

variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

local notation "Z" => WithLp 2 (E₁ × E₂)

private abbrev partialMinimizationLift (Φ : E₁ × E₂ → ℝ) : Z → ℝ :=
  Φ ∘ (WithLp.ofLp : Z → E₁ × E₂)

private abbrev partialMinimizationAmbientHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂) : E₁ × E₂ →L[ℝ] Z :=
  hessian (partialMinimizationLift Φ) (WithLp.toLp 2 (x, y)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm.toContinuousLinearMap

private abbrev partialMinimizationXXHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂) : E₁ →L[ℝ] E₁ :=
  WithLp.fstL 2 ℝ E₁ E₂ ∘L partialMinimizationAmbientHessian Φ x y ∘L inl ℝ E₁ E₂

private abbrev partialMinimizationXYHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂) : E₂ →L[ℝ] E₁ :=
  WithLp.fstL 2 ℝ E₁ E₂ ∘L partialMinimizationAmbientHessian Φ x y ∘L inr ℝ E₁ E₂

private abbrev partialMinimizationYXHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂) : E₁ →L[ℝ] E₂ :=
  WithLp.sndL 2 ℝ E₁ E₂ ∘L partialMinimizationAmbientHessian Φ x y ∘L inl ℝ E₁ E₂

variable {Φ : E₁ × E₂ → ℝ} {x : E₁} {y : E₁ → E₂}

/-- The formal implicit-function linear map attached to a critical minimizing branch. When the
frozen-slice `yy` Hessian is invertible, Proposition 5.0.19 (2) identifies this operator with the
Fréchet derivative of the minimizing branch. -/
def partialMinimizerImplicitFDeriv
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂) : E₁ →L[ℝ] E₂ :=
  -((hessian (Φ ∘ Prod.mk x) y).inverse.comp
    (partialMinimizationYXHessian Φ x y))

/-- The formal Schur-complement operator governing the Hessian of the partial-minimization
objective along a critical minimizing branch. Under an invertible frozen-slice `yy` Hessian,
Proposition 5.0.19 (3) identifies the Hessian of the partial-minimization objective with this
operator. -/
def partialMinimizationSchurHessian
    (Φ : E₁ × E₂ → ℝ) (x : E₁) (y : E₂) : E₁ →L[ℝ] E₁ :=
  partialMinimizationXXHessian Φ x y +
    (partialMinimizationXYHessian Φ x y).comp
      (partialMinimizerImplicitFDeriv Φ x y)

variable {Q : Set (E₁ × E₂)}

local notation "f" => extendedRealRealPart (partialInfProjection Q (Real.toEReal ∘ Φ))

/-- Proposition 5.0.19 (2): if the frozen-slice `yy` Hessian
`hessian (Φ ∘ Prod.mk x) (y x)` is invertible and the branch `u ↦ y u` stays on the locally
unique fiberwise minimizer branch of `Φ` through interior points of `Q` near `(x, y x)`, then `y`
is Fréchet differentiable at `x` with derivative given by the implicit-equation formula. -/
-- Proof sketch: the minimizing-branch hypotheses identify `u ↦ y u` with the local implicit
-- minimizer branch near `(x, y x)`. The interior hypothesis turns these constrained fiberwise
-- minimizers into unconstrained local minimizers of the `y`-slice, so the branch satisfies the
-- `y`-gradient equation near `x`. Apply the implicit function theorem to that critical-point
-- equation and solve the `yy`-block linear equation using the inverse Hessian hypothesis.
theorem partialMinimizer_hasFDerivAt_of_isInvertible_yyHessian
    (hPhi : ContDiffAt ℝ 2 Φ (x, y x))
    (hy_tendsto : Filter.Tendsto y (nhds x) (nhds (y x)))
    (hy_mem_interior : ∀ᶠ u in nhds x, (u, y u) ∈ interior Q)
    (hy_argmin : ∀ᶠ u in nhds x,
      y u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u))
    (hy_unique : ∀ᶠ u in nhds x,
      ∀ z : E₂, z ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) → z = y u)
    (hyy_inv : (hessian (Φ ∘ Prod.mk x) (y x)).IsInvertible) :
    HasFDerivAt y (partialMinimizerImplicitFDeriv Φ x (y x)) x := sorry

/-- Proposition 5.0.19 (2), linewise companion: the Fréchet derivative formula for the critical
branch yields the directional derivative of every line `t ↦ y (x + t • h)` through `x`. -/
theorem partialMinimizer_hasDerivAt_line_of_isInvertible_yyHessian
    (hPhi : ContDiffAt ℝ 2 Φ (x, y x))
    (hy_tendsto : Filter.Tendsto y (nhds x) (nhds (y x)))
    (hy_mem_interior : ∀ᶠ u in nhds x, (u, y u) ∈ interior Q)
    (hy_argmin : ∀ᶠ u in nhds x,
      y u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u))
    (hy_unique : ∀ᶠ u in nhds x,
      ∀ z : E₂, z ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) → z = y u)
    (hyy_inv : (hessian (Φ ∘ Prod.mk x) (y x)).IsInvertible)
    (h : E₁) :
    HasDerivAt (fun t : ℝ ↦ y (x + t • h))
      ((partialMinimizerImplicitFDeriv Φ x (y x)) h) 0 := sorry

/-- Proposition 5.0.19 (3): under the same local interior minimizer-branch and invertibility
hypotheses, the Hessian of the partial-minimization objective at `x` is the Schur complement of
the ambient Hessian of `Φ` at `(x, y x)`. -/
-- Proof sketch: first use the minimizing-branch hypotheses to identify the partial-minimization
-- objective with the canonical minimizing branch near `x`. The preceding differentiability formula
-- for `y`, together with the first-order envelope identity `∇ f(x) = ∇ₓ Φ(x, y(x))`, then yields
-- the Schur complement formula on the canonical Hessian owner `hessian`.
theorem partialMinimizationObjective_hessian_eq_schur_of_isInvertible_yyHessian
    (hPhi : ContDiffAt ℝ 2 Φ (x, y x))
    (hy_tendsto : Filter.Tendsto y (nhds x) (nhds (y x)))
    (hy_mem_interior : ∀ᶠ u in nhds x, (u, y u) ∈ interior Q)
    (hy_argmin : ∀ᶠ u in nhds x,
      y u ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u))
    (hy_unique : ∀ᶠ u in nhds x,
      ∀ z : E₂, z ∈ argmin[(Prod.mk u) ⁻¹' Q] (Φ ∘ Prod.mk u) → z = y u)
    (hyy_inv : (hessian (Φ ∘ Prod.mk x) (y x)).IsInvertible) :
    hessian f x = partialMinimizationSchurHessian Φ x (y x) := sorry

end SecondOrder

end
