import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_5_0_19 (from Chap05) -/
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

/-! ### Definition_5_0_20 (from Chap05) -/
open InnerProductSpace
open Module LinearMap
open scoped BInducedNorm Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 5.0.20 lies in the local Hessian-metric / dual-norm domain.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the canonical Hessian operator owner;
* `LinearMap.BilinForm.dualNorm` and `dualNorm_apply_strongDual` in `Chap04/Definition_4_2_6`,
  the canonical dual norm attached to a symmetric positive-definite bilinear form;
* `ContinuousLinearMap.IsInvertible` and `ContinuousLinearMap.inverse` in mathlib, the canonical
  owner and inverse bridge for a nondegenerate Hessian operator;
* `HasPositiveDefiniteHessianOn` together with
  `HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem` and
  `HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem` in `Definition_5_0_23`, the
  domain-level owner and its canonical bridge to the local Hessian data needed here.

Best owner abstraction:
* source-facing: the Hessian-metric dual local norm of a covector at `x`;
* core/canonical: the bilinear-form owner `‖g‖[hessianBilin f x,*]`;
* bridge/view: the canonical inverse `((hessian f x).inverse : E →L[ℝ] E)`.

Primitive data:
* a function `f`;
* a base point `x`;
* positivity of the Hessian operator at `x`;
* an invertibility witness for that Hessian;
* a covector `g`.

Derived API:
* the source-facing notation `‖g‖*[f; x | hPos; hInv]`;
* the determinant bridge `HessianDualLocalNorm.ofDetNeZero`;
* the domain-level bridge `HessianDualLocalNorm.ofPosDefMem`;
* the inverse-Hessian pairing formula for that dual norm;
* nonnegative scalar homogeneity of the dual local norm.

This file keeps the textbook dual local norm as the source-facing owner, but refines it to the
canonical Chapter 4 dual norm attached to the positive-definite Hessian bilinear form rather than
to a determinant-based witness. Determinant nonvanishing remains only as a thin bridge to the
canonical owner `ContinuousLinearMap.IsInvertible`. -/

/-- The bilinear form on `E` induced by the Hessian operator of `f` at `x`. -/
private def hessianBilin (f : E → ℝ) (x : E) : LinearMap.BilinForm ℝ E :=
  ((innerSL ℝ).comp (hessian f x)).toBilinForm

/-- Evaluating `hessianBilin f x` on `u` and `v` pairs `v` with the Hessian of `f` at `x`
applied to `u`. -/
private theorem hessianBilin_apply (f : E → ℝ) (x u v : E) :
    hessianBilin f x u v = inner ℝ (hessian f x u) v :=
  rfl

/-- A positive Hessian operator induces a symmetric Hessian bilinear form. -/
private theorem hessianBilin_isSymm_of_isPositive {f : E → ℝ} {x : E}
    (hPos : (hessian f x).IsPositive) : (hessianBilin f x).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro u v
  change inner ℝ (hessian f x u) v = inner ℝ (hessian f x v) u
  simpa [real_inner_comm] using hPos.isSymmetric u v

/-- A positive invertible Hessian operator induces a positive-definite Hessian bilinear form. -/
private theorem hessianBilin_posDef_of_isPositive_of_isInvertible {f : E → ℝ} {x : E}
    (hPos : (hessian f x).IsPositive) (hInv : (hessian f x).IsInvertible) :
    (hessianBilin f x).toQuadraticMap.PosDef := by
  rw [QuadraticMap.posDef_iff_nonneg]
  refine ⟨?_, ?_⟩
  · intro u
    change 0 ≤ inner ℝ (hessian f x u) u
    simpa [real_inner_comm] using hPos.inner_nonneg_right u
  · intro u hu
    change inner ℝ (hessian f x u) u = 0 at hu
    have hHu : hessian f x u = 0 := by
      obtain ⟨m, w, hA⟩ := (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).mp hPos
      rw [hA] at hu ⊢
      have hsum : ∑ j : Fin m, (inner ℝ (w j) u) ^ (2 : ℕ) = 0 := by
        simpa [Finset.sum_apply, InnerProductSpace.rankOne_apply, sum_inner, real_inner_smul_left,
          pow_two] using hu
      have hw : ∀ i : Fin m, inner ℝ (w i) u = 0 := by
        intro i
        exact sq_eq_zero_iff.mp <|
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun j _ ↦ sq_nonneg (inner ℝ (w j) u))).mp hsum i (by simp)
      simp [Finset.sum_apply, InnerProductSpace.rankOne_apply, hw]
    apply hInv.injective
    simpa using hHu

/-- A Hessian with nonzero determinant is canonically invertible as a continuous linear map. -/
theorem hessian_isInvertible_of_det_ne_zero {f : E → ℝ} {x : E}
    (hH : (hessian f x).det ≠ 0) : (hessian f x).IsInvertible :=
  ⟨(hessian f x).toContinuousLinearEquivOfDetNeZero hH, rfl⟩

-- Internal bridge used to specialize the Chapter 4 `B.toDual` inverse-pairing formula to the
-- Hessian bilinear form. Keeping it private avoids exposing bridge data as public theorem-statement
-- scaffolding.
private theorem hessianBilin_dualPreimage_eq_inverse {f : E → ℝ} {x : E}
    (hPos : (hessian f x).IsPositive) (hInv : (hessian f x).IsInvertible)
    (g : StrongDual ℝ E) :
    (hessianBilin f x).dualPreimage
        (hessianBilin_posDef_of_isPositive_of_isInvertible hPos hInv) g.toLinearMap =
      (hessian f x).inverse ((toDual ℝ E).symm g) := by
  let B := hessianBilin f x
  let hBPos : B.toQuadraticMap.PosDef :=
    hessianBilin_posDef_of_isPositive_of_isInvertible hPos hInv
  let hnd : (hessianBilin f x).Nondegenerate :=
    B.nondegenerate_of_posDef hBPos
  apply (B.toDual hnd).injective
  ext u
  calc
    B (B.dualPreimage hBPos g.toLinearMap) u =
        g u := by
      exact B.dualPreimage_apply hBPos g.toLinearMap u
    _ =
        ((B.toDual hnd) ((hessian f x).inverse ((toDual ℝ E).symm g))) u := by
      have hinv :
          (hessian f x) ((hessian f x).inverse ((toDual ℝ E).symm g)) =
            (toDual ℝ E).symm g :=
        hInv.self_apply_inverse ((toDual ℝ E).symm g)
      let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
      rw [LinearMap.BilinForm.toDual_def, hessianBilin_apply, hinv]
      simp

/-- Definition 5.0.20: when the Hessian of `f` at `x` is positive and invertible, the dual
local norm of a covector `g` is the Chapter 4 dual norm attached to the Hessian bilinear form. -/
abbrev dualLocalNorm (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hInv : (hessian f x).IsInvertible) (g : StrongDual ℝ E) : ℝ :=
  let _ : Fact (hessianBilin f x).IsSymm := ⟨hessianBilin_isSymm_of_isPositive hPos⟩
  let _ : Fact (hessianBilin f x).toQuadraticMap.PosDef :=
    ⟨hessianBilin_posDef_of_isPositive_of_isInvertible hPos hInv⟩
  (hessianBilin f x).dualNorm Fact.out g.toLinearMap

namespace HessianDualLocalNorm

/-- Source-facing notation for the Hessian-metric dual local norm of `g` at `x`. -/
scoped notation:max "‖" g "‖*[" f "; " x " | " hPos "; " hInv "]" =>
  dualLocalNorm f x hPos hInv g

/-- When the Hessian is given to be positive and determinant-nondegenerate, the dual local norm is
obtained by passing through the canonical invertibility owner. -/
abbrev ofDetNeZero (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hH : (hessian f x).det ≠ 0) (g : StrongDual ℝ E) : ℝ :=
  dualLocalNorm f x hPos (hessian_isInvertible_of_det_ne_zero hH) g

/-- When `f` has positive-definite Hessian on `dom`, the dual local norm at `x ∈ dom` is obtained
from the canonical positivity and invertibility bridges supplied by that owner. -/
abbrev ofPosDefMem (f : E → ℝ) {dom : Set E} {x : E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) (g : StrongDual ℝ E) : ℝ :=
  dualLocalNorm f x
    (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx)
    (hessian_isInvertible_of_det_ne_zero
      (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx)) g

/-- Under the standing qualitative self-concordant hypotheses, the dual local norm at `x ∈ dom`
is still the canonical owner `ofPosDefMem`, read through the positive-definite-Hessian bridge from
`IsSelfConcordantOn.hasPositiveDefiniteHessianOn_of_no_affine_line`. -/
abbrev ofSelfConcordantMem
    {dom : Set E} (Mf : NNReal) (f : E → ℝ)
    [IsSelfConcordantOnWith dom Mf f]
    (hclosed : IsClosed (constrainedEpigraph dom (fun y ↦ (f y : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom)
    {x : E} (hx : x ∈ dom) (g : StrongDual ℝ E) : ℝ :=
  let hself : IsSelfConcordantOn dom f := ⟨Mf, inferInstance⟩
  let _ : HasPositiveDefiniteHessianOn dom f :=
    hself.hasPositiveDefiniteHessianOn_of_no_affine_line hclosed hnoAffineLine
  ofPosDefMem f hx g

/-- Thin vector-view bridge for `ofSelfConcordantMem`: under the standing self-concordant
hypotheses, evaluate the dual local norm on the covector corresponding to `u` under the Riesz
identification. This is a bridge/view API, not a second owner. -/
abbrev ofSelfConcordantMemVec
    {dom : Set E} (Mf : NNReal) (f : E → ℝ)
    [IsSelfConcordantOnWith dom Mf f]
    (hclosed : IsClosed (constrainedEpigraph dom (fun y ↦ (f y : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom)
    (x : E) (hx : x ∈ dom) (u : E) : ℝ :=
  ofSelfConcordantMem Mf f hclosed hnoAffineLine hx ((toDual ℝ E) u)

/-- Source-facing notation for the Hessian-metric dual local norm of a vector `u` at a
self-concordant domain point `x ∈ dom`, read through the canonical self-concordant bridge. The
self-concordance parameter `M_f` remains explicit because it is not recoverable from the point
data alone. -/
scoped notation:max "‖" u "‖*[" f "; " x " | " Mf "; " hx "; " hclosed "; " hnoAffineLine "]" =>
  ofSelfConcordantMemVec Mf f hclosed hnoAffineLine x hx u

end HessianDualLocalNorm

open scoped HessianDualLocalNorm

-- Proof sketch: specialize the Chapter 4 `B`-dual norm formula to the Hessian bilinear form, then
-- identify the `B.toDual` inverse image with the inverse Hessian applied to the Riesz vector.
/-- Expanding `‖g‖*[f; x | hPos; hInv]` gives the square root of the inverse-Hessian pairing of the
covector `g` with itself at `x`. -/
theorem dualLocalNorm_def (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hInv : (hessian f x).IsInvertible) (g : StrongDual ℝ E) :
    ‖g‖*[f; x | hPos; hInv] =
      Real.sqrt (g ((hessian f x).inverse ((toDual ℝ E).symm g))) := by
  let hSymm : (hessianBilin f x).IsSymm := hessianBilin_isSymm_of_isPositive hPos
  let hBPos : (hessianBilin f x).toQuadraticMap.PosDef :=
    hessianBilin_posDef_of_isPositive_of_isInvertible hPos hInv
  calc
    ‖g‖*[f; x | hPos; hInv] =
        Real.sqrt (g ((hessianBilin f x).dualPreimage hBPos g.toLinearMap)) := by
      simpa [dualLocalNorm, hSymm, hBPos] using
        (LinearMap.BilinForm.dualNorm_apply_strongDual (hessianBilin f x) hSymm hBPos g)
    _ =
        Real.sqrt (g ((hessian f x).inverse ((toDual ℝ E).symm g))) := by
      congr 1
      simpa using congrArg g (hessianBilin_dualPreimage_eq_inverse hPos hInv g)

/-- The Hessian-metric dual local norm is always nonnegative. -/
theorem dualLocalNorm_nonneg (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hInv : (hessian f x).IsInvertible) (g : StrongDual ℝ E) :
    0 ≤ ‖g‖*[f; x | hPos; hInv] := by
  rw [dualLocalNorm_def]
  exact Real.sqrt_nonneg _

/-- The Hessian-metric dual local norm is positively homogeneous for nonnegative scalar multiples
of covectors. -/
theorem dualLocalNorm_smul_nonneg (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hInv : (hessian f x).IsInvertible) (g : StrongDual ℝ E) {a : ℝ} (ha : 0 ≤ a) :
    ‖a • g‖*[f; x | hPos; hInv] = a * ‖g‖*[f; x | hPos; hInv] := by
  let B := hessianBilin f x
  let hSymm : B.IsSymm := hessianBilin_isSymm_of_isPositive hPos
  let hBPos : B.toQuadraticMap.PosDef :=
    hessianBilin_posDef_of_isPositive_of_isInvertible hPos hInv
  let z := B.dualPreimage hBPos g.toLinearMap
  have hz : 0 ≤ B z z := hBPos.nonneg z
  have hz' : 0 ≤ g z := by
    simpa [z] using hz
  calc
    ‖a • g‖*[f; x | hPos; hInv] =
        Real.sqrt ((a • g) (B.dualPreimage hBPos ((a • g : StrongDual ℝ E).toLinearMap))) := by
      simpa [dualLocalNorm, B, hSymm, hBPos] using
        (LinearMap.BilinForm.dualNorm_apply_strongDual B hSymm hBPos (a • g : StrongDual ℝ E))
    _ = Real.sqrt ((a * a) * g z) := by
      simp [LinearMap.BilinForm.dualPreimage, z, map_smul, smul_eq_mul]
      ring_nf
    _ = Real.sqrt (a * a) * Real.sqrt (g z) := by
      rw [Real.sqrt_mul (mul_nonneg ha ha) (g z)]
    _ = a * Real.sqrt (g z) := by
      rw [Real.sqrt_mul_self ha]
    _ = a * ‖g‖*[f; x | hPos; hInv] := by
      congr 1
      symm
      simpa [dualLocalNorm, B, hSymm, hBPos, z] using
        (LinearMap.BilinForm.dualNorm_apply_strongDual B hSymm hBPos g)

namespace HessianDualLocalNorm

/-- Expanding `HessianDualLocalNorm.ofDetNeZero f x hPos hH g` recovers the inverse-Hessian
pairing formula through the determinant-to-invertibility bridge. -/
@[simp] theorem ofDetNeZero_def (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hH : (hessian f x).det ≠ 0) (g : StrongDual ℝ E) :
    ofDetNeZero f x hPos hH g =
      Real.sqrt
        (g ((hessian f x).inverse ((toDual ℝ E).symm g))) := by
  simp [ofDetNeZero, dualLocalNorm_def]

/-- Expanding `HessianDualLocalNorm.ofPosDefMem f hx g` recovers the inverse-Hessian pairing
formula with the local Hessian data derived from positive definiteness on `dom`. -/
@[simp] theorem ofPosDefMem_def (f : E → ℝ) {dom : Set E} {x : E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) (g : StrongDual ℝ E) :
    ofPosDefMem f hx g =
      Real.sqrt
        (g ((hessian f x).inverse ((toDual ℝ E).symm g))) := by
  simp [ofPosDefMem, dualLocalNorm_def]

/-- Expanding `HessianDualLocalNorm.ofSelfConcordantMem Mf f hclosed hnoAffineLine hx g`
recovers the same inverse-Hessian pairing formula through the canonical self-concordant-to-
positive-definite bridge. -/
@[simp] theorem ofSelfConcordantMem_def
    {dom : Set E} (Mf : NNReal) (f : E → ℝ)
    [IsSelfConcordantOnWith dom Mf f]
    (hclosed : IsClosed (constrainedEpigraph dom (fun y ↦ (f y : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom)
    {x : E} (hx : x ∈ dom) (g : StrongDual ℝ E) :
    ofSelfConcordantMem Mf f hclosed hnoAffineLine hx g =
      Real.sqrt
        (g ((hessian f x).inverse ((toDual ℝ E).symm g))) := by
  simp [ofSelfConcordantMem]

end HessianDualLocalNorm

end

/-! ### Definition_5_0_21 (from Chap05) -/
noncomputable section

/- Definition 5.0.21 lies in the Chapter 5 one-variable self-concordant auxiliary-function
domain.

Sampled owner-style declarations:
* `HasDerivAt` / `HasStrictDerivAt` in mathlib, the standard one-variable calculus owners behind
  the explicit derivative formulas used downstream;
* `Set.Ioi` and `Set.Iio`, the canonical interval owners for the natural domains `(-1, ∞)` and
  `(-∞, 1)`;
* `Function.invFun` in mathlib, the canonical inverse-function owner later reused for `ω` in
  `Theorem_5_2_4`;
* the adjacent chapter files `Lemma_5_1_4` and `Lemma_5_1_5`, which already treat `ω`, `ω_*`,
  `ω'`, and `ω'_*` as the owner-level Chapter 5 vocabulary.

Source/core/bridge triage:
* source-facing: the four Chapter 5 auxiliary scalar functions `ω`, `ω_*`, `ω'`, and `ω'_*`;
* core/canonical: those owners as maps on their intrinsic interval domains;
* bridge/view: the canonical subtype arguments `selfConcordantOmegaArg`,
  `selfConcordantOmegaStarArg`, and the owner-level evaluation lemmas.

Primitive data:
* the owner functions `ω` and `ω_*`.

Derived API:
* the derivative/inverse branches `ω'` and `ω'_*`;
* the canonical scaled-domain arguments for evaluating `ω` and `ω_*`;
* owner-level `[simp]` evaluation lemmas on the actual subtype domains.

This refinement keeps the Chapter 5 owners unchanged and trims only the duplicate scalar
specializations that were recoverable from the subtype-level evaluation lemmas by ordinary
elaboration. -/

/-- Definition 5.0.21 (1): the auxiliary function `ω(t) = t - log (1 + t)` on `(-1, ∞)`. -/
def selfConcordantOmega : Set.Ioi (-1 : ℝ) → ℝ :=
  fun t ↦ t - Real.log (1 + t)

/-- Definition 5.0.21 (2): the auxiliary function `ω_*(τ) = -τ - log (1 - τ)` on `(-∞, 1)`. -/
def selfConcordantOmegaStar : Set.Iio (1 : ℝ) → ℝ :=
  fun τ ↦ -τ - Real.log (1 - τ)

/-- The derivative branch `ω'(t) = t / (1 + t)` of `ω`, defined on its natural domain
`(-1, ∞)`. -/
def selfConcordantOmegaDeriv : Set.Ioi (-1 : ℝ) → ℝ :=
  fun t ↦ t / (1 + t)

/-- The inverse branch `ω'_*(τ) = τ / (1 - τ)` associated with `ω` and `ω_*`, defined on its
natural domain `(-∞, 1)`. -/
def selfConcordantOmegaPrimeStar : Set.Iio (1 : ℝ) → ℝ :=
  fun τ ↦ τ / (1 - τ)

namespace SelfConcordantAuxiliaryFunction

scoped notation:max "ω" => selfConcordantOmega
scoped notation:max "ω_*" => selfConcordantOmegaStar
scoped notation:max "ω'" => selfConcordantOmegaDeriv
scoped notation:max "ω'_*" => selfConcordantOmegaPrimeStar

end SelfConcordantAuxiliaryFunction

open scoped SelfConcordantAuxiliaryFunction

/-- If `r < 1 / M_f`, then the scaled quantity `M_f r` lies in the natural domain of `ω_*`. -/
theorem mf_mul_lt_one_of_lt_inv {Mf : NNReal} {r : ℝ} (hr : r < 1 / (Mf : ℝ)) :
    (Mf : ℝ) * r < 1 := by
  by_cases hMf : Mf = 0
  · simp [hMf]
  · have hMf_pos : 0 < Mf := lt_of_le_of_ne Mf.2 (Ne.symm hMf)
    have hMf' : 0 < (Mf : ℝ) := by
      exact_mod_cast hMf_pos
    have hlt :
        (Mf : ℝ) * r < (Mf : ℝ) * (1 / (Mf : ℝ)) := by
      exact mul_lt_mul_of_pos_left hr hMf'
    have hunit : (Mf : ℝ) * (1 / (Mf : ℝ)) = 1 := by
      field_simp [ne_of_gt hMf']
    calc
      (Mf : ℝ) * r < (Mf : ℝ) * (1 / (Mf : ℝ)) := hlt
      _ = 1 := hunit

/-- If `r ≥ 0`, then the scaled quantity `M_f r` lies in the natural domain of `ω`. -/
theorem neg_one_lt_mf_mul_of_nonneg {Mf : NNReal} {r : ℝ} (hr : 0 ≤ r) :
    -1 < (Mf : ℝ) * r := by
  have hMf : 0 ≤ (Mf : ℝ) := by
    exact_mod_cast Mf.2
  nlinarith

/-- The canonical `ω` argument attached to a scalar `r` whose scaled value lies in the natural
domain of `ω`. -/
def selfConcordantOmegaArg (Mf : NNReal) (r : ℝ) (hr : -1 < (Mf : ℝ) * r) : Set.Ioi (-1 : ℝ) :=
  ⟨(Mf : ℝ) * r, hr⟩

/-- Coercing `selfConcordantOmegaArg Mf r hr` back to `ℝ` recovers `M_f r`. -/
@[simp] theorem coe_selfConcordantOmegaArg
    (Mf : NNReal) (r : ℝ) (hr : -1 < (Mf : ℝ) * r) :
    ↑(selfConcordantOmegaArg Mf r hr) = (Mf : ℝ) * r :=
  rfl

/-- The textbook point `1 / 2` in the natural domain `(-1, ∞)` of `ω`. -/
def selfConcordantOmegaOneHalfArg : Set.Ioi (-1 : ℝ) :=
  ⟨1 / 2, by norm_num⟩

/-- Coercing `selfConcordantOmegaOneHalfArg` back to `ℝ` recovers `1 / 2`. -/
@[simp] theorem coe_selfConcordantOmegaOneHalfArg :
    ↑selfConcordantOmegaOneHalfArg = (1 / 2 : ℝ) :=
  rfl

/-- The Chapter 5 textbook constant `ω(1 / 2)`. -/
def selfConcordantOmegaAtOneHalf : ℝ :=
  ω selfConcordantOmegaOneHalfArg

/-- The canonical `ω_*` argument attached to a scalar `r` satisfying `(Mf : ℝ) * r < 1`. -/
def selfConcordantOmegaStarArg (Mf : NNReal) (r : ℝ) (hr : (Mf : ℝ) * r < 1) :
    Set.Iio (1 : ℝ) :=
  ⟨(Mf : ℝ) * r, hr⟩

/-- Coercing `selfConcordantOmegaStarArg Mf r hr` back to `ℝ` recovers `M_f r`. -/
@[simp] theorem coe_selfConcordantOmegaStarArg
    (Mf : NNReal) (r : ℝ) (hr : (Mf : ℝ) * r < 1) :
    ↑(selfConcordantOmegaStarArg Mf r hr) = (Mf : ℝ) * r :=
  rfl

/-- Evaluating `ω` at a point of `(-1, ∞)` recovers the explicit formula
`t - log (1 + t)`. -/
@[simp] theorem selfConcordantOmega_apply (t : Set.Ioi (-1 : ℝ)) :
    ω t = t - Real.log (1 + t) :=
  rfl

/-- Evaluating `ω_*` at a point of `(-∞, 1)` recovers the textbook
formula `-τ - log (1 - τ)`. -/
@[simp] theorem selfConcordantOmegaStar_apply (τ : Set.Iio (1 : ℝ)) :
    ω_* τ = -τ - Real.log (1 - τ) :=
  rfl

/-- Evaluating `ω'` at a point of `(-1, ∞)` recovers the explicit derivative formula
`t / (1 + t)`. -/
@[simp] theorem selfConcordantOmegaDeriv_apply (t : Set.Ioi (-1 : ℝ)) :
    ω' t = t / (1 + t) :=
  rfl

/-- Evaluating `ω'_*` at a point of `(-∞, 1)` recovers the explicit inverse-branch formula
`τ / (1 - τ)`. -/
@[simp] theorem selfConcordantOmegaPrimeStar_apply (τ : Set.Iio (1 : ℝ)) :
    ω'_* τ = τ / (1 - τ) :=
  rfl

end

/-! ### Proposition_5_0_21 (from Chap05) -/
noncomputable section

universe u

open LinearMap
open scoped LinearMap.BilinForm.BInducedNorm

/- Proposition 5.0.21 lies in the bilinear-form / induced-norm duality domain.

Sampled owner-style declarations:
* `LinearMap.BilinForm.primalSeminorm` in `Chap04/Definition_4_3_4`, the canonical primal
  seminorm induced by a symmetric positive-definite bilinear form;
* `LinearMap.BilinForm.dualNorm` in `Chap04/Definition_4_3_4`, the corresponding dual norm on
  `Module.Dual ℝ E`;
* `Seminorm.inner_le_dualNorm_mul` in `Chap02/Definition_2_5`, the owner-level dual-pairing
  estimate for a separated seminorm and its dual norm;
* the notation layer `‖·‖[B]` / `‖·‖[B,*]` in `Chap04/Definition_4_3_4`, together with the direct
  owner call `B.dualNorm Fact.out` on `Module.Dual ℝ E`;
* `LinearMap.BilinForm.dualNorm_apply` in `Chap04/Definition_4_3_4`, the `B.toDual` bridge for
  the dual norm.

Best owner abstraction:
* core/canonical: the bilinear-form owners `B.primalSeminorm` and `B.dualNorm`.

Primitive data:
* a bilinear form `B`;
* symmetry and positive-definiteness of `B.toQuadraticMap`.

Derived API:
* the induced primal seminorm and dual norm;
* the pairing estimate of Proposition 5.0.21.
* as a source-facing bridge, positive-definiteness from nonnegativity plus nondegeneracy.

The local Chapter 5 wrappers `localNormOfBilin` and `dualLocalNormOfBilin` were duplicate wheel
definitions: they carried no mathematics beyond the Chapter 4 bilinear-form owners. This file now
uses the owner abstraction directly and keeps only the source-faithful bridge from the proposition's
semidefinite plus nondegenerate hypotheses to that owner layer. -/

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

namespace LinearMap.BilinForm

/-- A symmetric nonnegative bilinear form is positive definite as soon as it is nondegenerate. -/
theorem posDef_of_nonneg_of_nondegenerate (B : LinearMap.BilinForm ℝ E)
    (hB_nonneg : ∀ v : E, 0 ≤ B v v) (hB_symm : B.IsSymm) (hB_nondeg : B.Nondegenerate) :
    B.toQuadraticMap.PosDef := by
  let hLinearSymm : LinearMap.IsSymm B := LinearMap.BilinForm.isSymm_iff.1 hB_symm
  have hB_pos : ∀ v : E, v ≠ 0 → 0 < B v v :=
    (LinearMap.BilinForm.nondegenerate_iff' B hB_nonneg hLinearSymm).1 hB_nondeg
  exact hB_pos

end LinearMap.BilinForm

variable [FiniteDimensional ℝ E]

private theorem abs_apply_le_dualNorm_mul_primalSeminorm_of_posDef
    (B : LinearMap.BilinForm ℝ E) (hB_symm : B.IsSymm) (hPos : B.toQuadraticMap.PosDef)
    (g : Module.Dual ℝ E) (h : E) :
    |g h| ≤ ‖g‖*[B | hPos] * ‖h‖[B | hPos] := by
  let v := B.dualPreimage hPos g
  let hLinearSymm : LinearMap.IsSymm B := LinearMap.BilinForm.isSymm_iff.1 hB_symm
  have hsq : (B v h) ^ 2 ≤ (B v v) * (B h h) :=
    B.apply_sq_le_of_symm hPos.nonneg hLinearSymm v h
  have habs_sq : |B v h| ^ 2 ≤ (Real.sqrt (B v v) * Real.sqrt (B h h)) ^ 2 := by
    have hv_sq : (Real.sqrt (B v v)) ^ 2 = B v v := by
      simpa [BilinMap.toQuadraticMap_apply] using Real.sq_sqrt (hPos.nonneg v)
    have hh_sq : (Real.sqrt (B h h)) ^ 2 = B h h := by
      simpa [BilinMap.toQuadraticMap_apply] using Real.sq_sqrt (hPos.nonneg h)
    calc
      |B v h| ^ 2 = (B v h) ^ 2 := by rw [sq_abs]
      _ ≤ (B v v) * (B h h) := hsq
      _ = (Real.sqrt (B v v) * Real.sqrt (B h h)) ^ 2 := by
        calc
          (B v v) * (B h h) = (Real.sqrt (B v v)) ^ 2 * (Real.sqrt (B h h)) ^ 2 := by
            rw [hv_sq, hh_sq]
          _ = (Real.sqrt (B v v) * Real.sqrt (B h h)) ^ 2 := by ring
  have habs : |B v h| ≤ Real.sqrt (B v v) * Real.sqrt (B h h) := by
    exact le_of_sq_le_sq habs_sq (by positivity)
  have hv : B v v = g v := by
    simp [v]
  calc
    |g h| = |B v h| := by
      simp [v]
    _ ≤ Real.sqrt (B v v) * Real.sqrt (B h h) := habs
    _ = Real.sqrt (g v) * ‖h‖[B | hPos] := by
      rw [hv, B.primalSeminorm_apply]
    _ = ‖g‖*[B | hPos] * ‖h‖[B | hPos] := by
      simpa [v] using
        congrArg (fun t : ℝ ↦ t * ‖h‖[B | hPos]) (B.dualNorm_apply hB_symm hPos g).symm

/-- Proposition 5.0.21: if `B` is symmetric, nonnegative on diagonal values, and nondegenerate,
then the pairing between a covector and a vector is bounded by the `B`-dual norm of the covector
times the `B`-primal norm of the vector. The positive-definite owner data are obtained canonically
from these textbook hypotheses. -/
theorem abs_apply_le_dualNorm_mul_primalSeminorm (B : LinearMap.BilinForm ℝ E)
    (hB_nonneg : ∀ v : E, 0 ≤ B v v) (hB_symm : B.IsSymm) (hB_nondeg : B.Nondegenerate)
    (g : Module.Dual ℝ E) (h : E) :
    let hPos := B.posDef_of_nonneg_of_nondegenerate hB_nonneg hB_symm hB_nondeg
    |g h| ≤ ‖g‖*[B | hPos] * ‖h‖[B | hPos] := by
  let hPos : B.toQuadraticMap.PosDef :=
    B.posDef_of_nonneg_of_nondegenerate hB_nonneg hB_symm hB_nondeg
  simpa [hPos] using abs_apply_le_dualNorm_mul_primalSeminorm_of_posDef B hB_symm hPos g h

/-! ### Proposition_5_0_22 (from Chap05) -/
open scoped SelfConcordantAuxiliaryFunction

noncomputable section

/-
Proposition 5.0.22 lies in the Chapter 5 one-variable convexity / auxiliary-function domain.

Sampled owner-style declarations:
* `selfConcordantOmega` and `selfConcordantOmegaStar` in `Definition_5_0_21`, the chapter owners
  for `ω` and `ω_*`;
* `selfConcordantOmega_apply` and `selfConcordantOmegaStar_apply`, the canonical owner-level
  evaluation lemmas recovering the textbook scalar formulas from those owners;
* `convexOn_of_deriv2_nonneg` in mathlib, the standard one-variable convexity owner for proving
  interval convexity from nonnegative second derivative;
* `convex_Ioi` and `convex_Iio`, the canonical interval-convexity owners for the two domains.

Source/core/bridge triage:
* source-facing: the convexity of the Chapter 5 auxiliary functions on their natural intervals;
* core/canonical: the chapter owners `ω` and `ω_*` together with mathlib's `ConvexOn`;
* bridge/view: the canonical ambient real-valued extensions
  `Function.extend Subtype.val ω 0` and `Function.extend Subtype.val ω_* 0`, used only because
  `ConvexOn` is stated for total functions on `ℝ`.

Primitive data:
* the source-facing owners `ω : Set.Ioi (-1) → ℝ` and `ω_* : Set.Iio 1 → ℝ`.

Derived API:
* their canonical ambient extensions via `Function.extend Subtype.val ... 0`, which agree with
  the owners on the relevant convex domains and are mathematically irrelevant off those domains.

This refinement removes the duplicate raw-formula surface from the proposition statements and
reuses the chapter owners directly. -/

-- Proof sketch: compute the second derivatives of the two scalar functions,
-- `ω''(t) = (1 + t)⁻²` on `(-1, ∞)` and `ω_*''(τ) = (1 - τ)⁻²` on `(-∞, 1)`,
-- and apply the standard one-variable criterion that nonnegative second derivative
-- on a convex interval implies convexity.
/-- Proposition 5.0.22 (1): the ambient real-function view of the Chapter 5 owner `ω` is convex
on `(-1, ∞)`. -/
theorem selfConcordantOmega_convexOn :
    ConvexOn ℝ (Set.Ioi (-1 : ℝ))
      (Function.extend Subtype.val ω 0) := by
  sorry

/-- Proposition 5.0.22 (2): the ambient real-function view of the Chapter 5 owner `ω_*` is convex
on `(-∞, 1)`. -/
theorem selfConcordantOmegaStar_convexOn :
    ConvexOn ℝ (Set.Iio (1 : ℝ))
      (Function.extend Subtype.val ω_* 0) := by
  sorry

end

/-! ### Definition_5_0_23 (from Chap05) -/
noncomputable section

universe u

/- Definition 5.0.23 lies in the chapter's self-concordant minimization domain.

Sampled owner declarations:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued objective;
* `IsSelfConcordantOnWith` and `IsSelfConcordantOn` in `Chap05/Definition_5_1_1`, the chapter
  owners for quantitative and existential self-concordance on a domain;
* `ContinuousLinearMap.IsPositive` in mathlib, the canonical pointwise positivity owner for
  symmetric continuous linear operators on real inner-product spaces;
* `hessian` in `Chap01/Definition_1_4_16`, reused upstream by the self-concordance owner as the
  canonical Hessian operator.

Best owner abstraction:
* source-facing: `UnconstrainedSelfConcordantMinimizationProblem E`;
* core/canonical ambient owner: `SetConstrainedMinimizationProblem E`;
* core/canonical regularity owner:
  `IsSelfConcordantOnWith feasibleSet selfConcordanceConstant objective`;
* auxiliary reusable property: `HasPositiveDefiniteHessianOn feasibleSet objective`.

Primitive data:
* the feasible set and objective, owned by `SetConstrainedMinimizationProblem E`;
* a self-concordance constant for the objective on the feasible set;
* quantitative self-concordance of the objective on the feasible set;
* pointwise positivity and strict positive definiteness of the Hessian on the feasible set.

Derived API:
* openness and convexity of the feasible set, recovered from self-concordance;
* the qualitative self-concordance view `IsSelfConcordantOn feasibleSet objective`;
* the coercion to the ambient objective function;
* the inherited ambient owner projection `toSetConstrainedMinimizationProblem`.

Source/core/bridge triage:
* source-facing: `UnconstrainedSelfConcordantMinimizationProblem E`;
* core/canonical:
  `SetConstrainedMinimizationProblem E`,
  `IsSelfConcordantOnWith feasibleSet selfConcordanceConstant objective`;
* bridge/view: the inherited parent projection when only the ambient minimization owner is
  needed. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Hessian of `f` is positive definite on `dom` when, at each point of the domain, the
Hessian operator is positive in the canonical mathlib sense and every nonzero direction has
strictly positive Hessian quadratic form. -/
class HasPositiveDefiniteHessianOn (dom : Set E) (f : E → ℝ) : Prop where
  /-- At each point of the domain, the Hessian operator is positive. -/
  isPositive {x : E} (hx : x ∈ dom) :
    (hessian f x).IsPositive
  /-- Every nonzero direction has strictly positive Hessian quadratic form on the domain. -/
  posdef {x : E} (hx : x ∈ dom) {u : E} (hu : u ≠ 0) :
    0 < inner ℝ u (hessian f x u)

namespace HasPositiveDefiniteHessianOn

/-- Positive definiteness of the Hessian on `dom` canonically supplies Hessian positivity at each
point of the domain. -/
theorem hessian_isPositive_of_mem {dom : Set E} {f : E → ℝ}
    [h : HasPositiveDefiniteHessianOn dom f] {x : E} (hx : x ∈ dom) :
    (hessian f x).IsPositive :=
  h.isPositive hx

/-- Positive definiteness of the Hessian on `dom` forces Hessian nondegeneracy at every point of
the domain. -/
theorem hessian_det_ne_zero_of_mem {dom : Set E} {f : E → ℝ}
    [FiniteDimensional ℝ E] [h : HasPositiveDefiniteHessianOn dom f] {x : E} (hx : x ∈ dom) :
    (hessian f x).det ≠ 0 := by
  rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot]
  intro hker
  obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hu_zero : hessian f x u = 0 := hu_mem
  have : ¬ 0 < (0 : ℝ) := not_lt_of_ge le_rfl
  exact this <| by
    simpa [hu_zero] using h.posdef hx hu_ne

end HasPositiveDefiniteHessianOn

/-- Definition 5.0.23, generalized from the textbook Euclidean setting: an unconstrained
self-concordant minimization problem consists of a domain and an objective to be minimized over
that domain, where the objective is self-concordant on the domain and has positive definite
Hessian there. The ambient problem data are owned canonically by
`SetConstrainedMinimizationProblem`, while self-concordance is expressed through the chapter owner
`IsSelfConcordantOnWith`. -/
structure UnconstrainedSelfConcordantMinimizationProblem (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    extends SetConstrainedMinimizationProblem E where
  /-- The self-concordance constant of the objective on the feasible set. -/
  selfConcordanceConstant : NNReal
  /-- The problem canonically supplies the quantitative self-concordance owner for its objective
  on its feasible set. -/
  toIsSelfConcordantOnWith :
    IsSelfConcordantOnWith feasibleSet selfConcordanceConstant objective
  /-- The problem canonically supplies positive-definite Hessian data for its objective on its
  feasible set. -/
  toHasPositiveDefiniteHessianOn : HasPositiveDefiniteHessianOn feasibleSet objective

attribute [instance] UnconstrainedSelfConcordantMinimizationProblem.toIsSelfConcordantOnWith
attribute [instance] UnconstrainedSelfConcordantMinimizationProblem.toHasPositiveDefiniteHessianOn

namespace UnconstrainedSelfConcordantMinimizationProblem

/-- The objective of an unconstrained self-concordant minimization problem is self-concordant on
its feasible set. -/
theorem isSelfConcordantOn
    (problem : UnconstrainedSelfConcordantMinimizationProblem E) :
    IsSelfConcordantOn problem.feasibleSet problem.objective :=
  ⟨problem.selfConcordanceConstant, problem.toIsSelfConcordantOnWith⟩

/-- The feasible set of an unconstrained self-concordant minimization problem is open. -/
theorem feasibleSet_open (problem : UnconstrainedSelfConcordantMinimizationProblem E) :
    IsOpen problem.feasibleSet :=
  problem.toIsSelfConcordantOnWith.isOpen_domain

/-- The feasible set of an unconstrained self-concordant minimization problem is convex. -/
theorem feasibleSet_convex (problem : UnconstrainedSelfConcordantMinimizationProblem E) :
    Convex ℝ problem.feasibleSet :=
  problem.toIsSelfConcordantOnWith.convex_domain

/-- An unconstrained self-concordant minimization problem can be used as its objective function.
-/
instance : CoeFun (UnconstrainedSelfConcordantMinimizationProblem E) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating an unconstrained self-concordant minimization problem returns its objective value.
-/
@[simp] theorem coe_apply
    (problem : UnconstrainedSelfConcordantMinimizationProblem E) (x : E) :
    problem x = problem.objective x :=
  rfl

end UnconstrainedSelfConcordantMinimizationProblem

end

/-! ### Definition_5_0_24 (from Chap05) -/
open InnerProductSpace
open scoped Gradient HessianDualLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/- Definition 5.0.24 lies in the Newton-decrement / Hessian-dual-norm domain.

Sampled owner declarations:
* `dualLocalNorm` and `‖g‖*[f; x | hPos; hInv]` in `Definition_5_0_20`, the chapter owner for the
  Hessian-metric dual norm of a covector;
* `ContinuousLinearMap.IsInvertible` and `ContinuousLinearMap.inverse` in mathlib, the canonical
  owner abstraction for an invertible Hessian operator;
* `InnerProductSpace.toDual_apply_apply` in mathlib, the canonical Riesz-evaluation bridge from a
  covector formula back to the intrinsic inner-product pairing.

Best owner abstraction:
* source-facing: the Newton decrement of `f` at `x`;
* core/canonical: the dual local norm of the gradient covector;
* bridge/view: the inverse-Hessian gradient-pairing formula.

Primitive data:
* a function `f`;
* a base point `x`;
* Hessian positivity and invertibility at `x`.

Derived API:
* the source-facing notation `λ[f; x | hPos; hInv]`;
* the source-facing self-concordant-domain notation `ndec(f, x, Mf, hx, hH)`;
* the determinant bridge `NewtonDecrement.ofDetNeZero`;
* the positive-definite-domain bridge `NewtonDecrement.ofPosDefMem`;
* the bridge theorem `newtonDecrement_def`.

This file keeps `newtonDecrement` as the source-facing owner, reusing the upstream dual-local-norm
owner directly. Determinant nonvanishing survives only in the explicit bridge
`NewtonDecrement.ofDetNeZero`; the main public surface uses the intrinsic invertibility witness
and the canonical inverse operator. The stronger `CompleteSpace` layer is localized below to the
self-concordant and positive-definite bridge declarations whose owner classes require it. -/

/-- Definition 5.0.24: when the Hessian of `f` at `x` is positive and invertible, the Newton
decrement is the dual local norm of the gradient at `x`. -/
abbrev newtonDecrement (f : E → ℝ) (x : E)
    (hPos : (hessian f x).IsPositive) (hInv : (hessian f x).IsInvertible) : ℝ :=
  ‖(toDual ℝ E) (∇ f x)‖*[f; x | hPos; hInv]

namespace NewtonDecrement

/-- Source-facing notation for the Newton decrement of `f` at `x`. -/
scoped notation:max "λ[" f "; " x " | " hPos "; " hInv "]" =>
  newtonDecrement f x hPos hInv

section CompleteSpaceBridge

variable [CompleteSpace E]

/-- When `f` is self-concordant on `dom` and the Hessian is nondegenerate at `x ∈ dom`, the
Newton decrement is defined using the Hessian positivity canonically supplied by
self-concordance. -/
abbrev ofDetNeZero (Mf : NNReal) (f : E → ℝ) {dom : Set E} {x : E}
    [IsSelfConcordantOnWith dom Mf f] (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) : ℝ :=
  HessianDualLocalNorm.ofDetNeZero f x
    (IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx)
    hH ((toDual ℝ E) (∇ f x))

/-- Source-facing notation for the Newton decrement at a self-concordant domain point `x ∈ dom`
with Hessian nondegeneracy witness `hH`. The self-concordance parameter `M_f` remains explicit in
this surface because it is not inferable from the point data alone. -/
scoped notation:max "ndec(" f:arg ", " x:arg ", " Mf:arg ", " hx:arg ", " hH:arg ")" =>
  (fun _ ↦ ofDetNeZero Mf f hx hH) x

/-- The Newton decrement supplied by self-concordance is nonnegative. -/
@[simp] theorem ofDetNeZero_nonneg
    (Mf : NNReal) (f : E → ℝ) {dom : Set E} {x : E}
    [IsSelfConcordantOnWith dom Mf f] (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    0 ≤ ndec(f, x, Mf, hx, hH) := by
  simpa [ofDetNeZero, HessianDualLocalNorm.ofDetNeZero] using
    dualLocalNorm_nonneg f x
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx)
      (hessian_isInvertible_of_det_ne_zero hH)
      ((toDual ℝ E) (∇ f x))

/-- The canonical `ω` argument attached to `NewtonDecrement.ofDetNeZero Mf f hx hH`. -/
  abbrev omegaArgOfDetNeZero
    (Mf : NNReal) (f : E → ℝ) {dom : Set E} {x : E}
    [IsSelfConcordantOnWith dom Mf f] (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    Set.Ioi (-1 : ℝ) :=
  selfConcordantOmegaArg Mf (ofDetNeZero Mf f hx hH)
    (neg_one_lt_mf_mul_of_nonneg (ofDetNeZero_nonneg Mf f hx hH))

/-- Coercing `omegaArgOfDetNeZero` back to `ℝ` recovers `M_f λ_f(x)`. -/
@[simp] theorem coe_omegaArgOfDetNeZero
    (Mf : NNReal) (f : E → ℝ) {dom : Set E} {x : E}
    [IsSelfConcordantOnWith dom Mf f] (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    ↑(omegaArgOfDetNeZero Mf f hx hH) = (Mf : ℝ) * ndec(f, x, Mf, hx, hH) := by
  rfl

/-- When `f` has positive-definite Hessian on `dom`, the Newton decrement at `x ∈ dom` uses only
the domain membership witness; Hessian positivity and invertibility are derived canonically from
that owner hypothesis. -/
abbrev ofPosDefMem (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) : ℝ :=
  HessianDualLocalNorm.ofPosDefMem f hx ((toDual ℝ E) (∇ f x))

/-- Source-facing notation for the Newton decrement at a domain point `x ∈ dom` in the
positive-definite-Hessian regime. -/
scoped notation:max "λ[" f "; " x " | " hx "]" =>
  ofPosDefMem f x hx

end CompleteSpaceBridge

end NewtonDecrement

open scoped NewtonDecrement

-- Proof sketch: unfold `newtonDecrement` and then expand `dualLocalNorm` at the gradient covector
-- corresponding to `∇ f x` under the Riesz identification.
/-- Expanding `λ[f; x | hPos; hInv]` gives the square root of the inverse-Hessian pairing
of the gradient with itself, i.e. the local dual norm of `∇ f x`. -/
@[simp]
theorem newtonDecrement_def (f : E → ℝ) (x : E) (hPos : (hessian f x).IsPositive)
    (hInv : (hessian f x).IsInvertible) :
    λ[f; x | hPos; hInv] =
      Real.sqrt (inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x))) := by
  simpa [newtonDecrement, InnerProductSpace.toDual_apply_apply] using
    dualLocalNorm_def f x hPos hInv ((toDual ℝ E) (∇ f x))

namespace NewtonDecrement

section CompleteSpaceBridge

variable [CompleteSpace E]

/-- Expanding `NewtonDecrement.ofDetNeZero Mf f hx hH` recovers the inverse-Hessian gradient
pairing formula with the Hessian positivity supplied by self-concordance. -/
@[simp] theorem ofDetNeZero_def (Mf : NNReal) (f : E → ℝ) {dom : Set E} {x : E}
    [IsSelfConcordantOnWith dom Mf f] (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    ndec(f, x, Mf, hx, hH) =
      Real.sqrt (inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x))) := by
  change newtonDecrement f x
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx)
      (hessian_isInvertible_of_det_ne_zero hH) =
    Real.sqrt (inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x)))
  exact newtonDecrement_def f x
    (IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx)
    (hessian_isInvertible_of_det_ne_zero hH)

/-- Expanding `NewtonDecrement.ofPosDefMem f x hx` recovers the inverse-Hessian gradient pairing
formula with the Hessian witnesses derived from positive definiteness on `dom`. -/
@[simp] theorem ofPosDefMem_def (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) :
    λ[f; x | hx] =
      Real.sqrt (inner ℝ (∇ f x) ((hessian f x).inverse (∇ f x))) := by
  simp [ofPosDefMem]

/-- The positive-definite-domain Newton decrement is nonnegative. -/
@[simp] theorem ofPosDefMem_nonneg (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) :
    0 ≤ λ[f; x | hx] := by
  rw [ofPosDefMem_def]
  exact Real.sqrt_nonneg _

/-- The canonical `ω` argument attached to `λ[f; x | hx]`. -/
abbrev omegaArgOfPosDefMem
    (Mf : NNReal) (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) :
    Set.Ioi (-1 : ℝ) :=
  selfConcordantOmegaArg Mf (λ[f; x | hx])
    (neg_one_lt_mf_mul_of_nonneg (ofPosDefMem_nonneg f x hx))

/-- Coercing `omegaArgOfPosDefMem Mf f x hx` back to `ℝ` recovers `M_f λ_f(x)`. -/
@[simp] theorem coe_omegaArgOfPosDefMem
    (Mf : NNReal) (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom) :
    ↑(omegaArgOfPosDefMem Mf f x hx) = (Mf : ℝ) * (λ[f; x | hx]) := by
  rfl

/-- The canonical `ω_*` argument attached to `λ[f; x | hx]` under the small-decrement
hypothesis. -/
abbrev omegaStarArgOfPosDefMem
    (Mf : NNReal) (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom)
    (hlt : ofPosDefMem f x hx < 1 / (Mf : ℝ)) :
    Set.Iio (1 : ℝ) :=
  selfConcordantOmegaStarArg Mf (ofPosDefMem f x hx) (mf_mul_lt_one_of_lt_inv hlt)

/-- Coercing `omegaStarArgOfPosDefMem Mf f x hx hlt` back to `ℝ` recovers `M_f λ_f(x)`. -/
@[simp] theorem coe_omegaStarArgOfPosDefMem
    (Mf : NNReal) (f : E → ℝ) (x : E) {dom : Set E}
    [HasPositiveDefiniteHessianOn dom f] (hx : x ∈ dom)
    (hlt : ofPosDefMem f x hx < 1 / (Mf : ℝ)) :
    ↑(omegaStarArgOfPosDefMem Mf f x hx hlt) = (Mf : ℝ) * ofPosDefMem f x hx := by
  rfl

end CompleteSpaceBridge

end NewtonDecrement

end

/-! ### Theorem_5_0_25 (from Chap05) -/
universe u

open scoped LevelSetNotation

/- Theorem 5.0.25 lies in the chapter's convex recession-direction domain.

Sampled owner declarations:
* `BddBelow (Set.range f)` from mathlib, the canonical function-level owner for "bounded below";
* `𝓛[f](a)` and `mem_levelSet_iff` from `Chap01/Definition_1_4_8`, the chapter owner for lower
  sublevel sets, retained here only for the horizontal-ray geometric companions.
* `Set.MapsTo` from mathlib, the canonical owner for the horizontal-ray bridge into a level set.

Best owner abstraction:
* source-facing: a function with a negative-slope recession ray is not bounded below;
* core/canonical: `¬ BddBelow (Set.range f)`;
* bridge/view: the horizontal-slope sublevel-set consequences for `𝓛[f](f x)`.

Primitive data:
* the objective `f : E → ℝ`;
* a base point `x` and a recession direction `d`;
* a scalar recession slope `σ < 0` together with the ray estimate
  `f (x + t • d) ≤ f x + t * σ`.

Derived API:
* the owner-level conclusion `¬ BddBelow (Set.range f)`;
* the horizontal-slope bridge `Set.MapsTo (fun t ↦ x + t • d) (Set.Ici 0) (𝓛[f](f x))`;
* the geometric corollaries `¬ Bornology.IsBounded (𝓛[f](f x))` and
  `Set.Infinite (𝓛[f](f x))`.

Source/core/bridge triage:
* source-facing: the function-level unbounded-below conclusion for the objective;
* core/canonical: `¬ BddBelow (Set.range f)`;
* bridge/view: the level-set containment and unboundedness lemmas for the special horizontal case
  `σ = 0`.

The previous revision promoted only the horizontal-ray geometric bridge
`¬ Bornology.IsBounded (𝓛[f](f x))`. This file restores the source-facing owner conclusion on
`Set.range f` and demotes the level-set statements to companions. -/

section RangeBoundedness

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {f : E → ℝ}

/-- Theorem 5.0.25: if an objective admits a recession ray from `x` whose values are bounded
above by an affine function with negative slope `σ`, then the objective is not bounded below on
the whole space. The owner-level conclusion is the canonical range statement
`¬ BddBelow (Set.range f)`. -/
theorem not_bddBelow_range_of_negative_recession_ray
    {x d : E} {σ : ℝ} (hσ : σ < 0)
    (hray : ∀ t : ℝ, 0 ≤ t → f (x + t • d) ≤ f x + t * σ) :
    ¬ BddBelow (Set.range f) := by
  intro hbelow
  rcases hbelow with ⟨m, hm⟩
  let t : ℝ := (|f x - m| + 1) / (-σ)
  have ht_nonneg : 0 ≤ t := by
    have : 0 < -σ := by linarith
    dsimp [t]
    positivity
  have hm_t : m ≤ f (x + t • d) :=
    hm ⟨x + t • d, rfl⟩
  have hltm : f x + t * σ < m := by
    have habs : f x - m ≤ |f x - m| := le_abs_self _
    have hσ_ne : σ ≠ 0 := ne_of_lt hσ
    have ht_eval : t * σ = -(|f x - m| + 1) := by
      dsimp [t]
      field_simp [hσ_ne]
    linarith
  exact (not_lt_of_ge hm_t) (lt_of_le_of_lt (hray t ht_nonneg) hltm)

end RangeBoundedness

section HorizontalLevelSetBridge

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {f : E → ℝ} {x d : E}

/-- In the horizontal recession case `σ = 0`, the forward ray from `x` in direction `d` stays
inside the lower sublevel set `𝓛[f](f x)`. This is a bridge/view statement for the later geometric
companions, not the main owner conclusion of Theorem 5.0.25. -/
theorem ray_mapsTo_levelSet_of_nonincreasing_ray
    (hray : ∀ t : ℝ, 0 ≤ t → f (x + t • d) ≤ f x) :
    Set.MapsTo (fun t : ℝ ↦ x + t • d) (Set.Ici (0 : ℝ)) (𝓛[f]((f x))) := by
  intro t ht
  exact hray t ht

end HorizontalLevelSetBridge

section HorizontalLevelSetGeometry

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → ℝ} {x d : E}

/-- A nonzero horizontal recession ray forces the sublevel set through `x` to be unbounded. This
is the geometric bridge companion to Theorem 5.0.25, corresponding to the special slope `σ = 0`
case. -/
theorem levelSet_not_bounded_of_nonzero_horizontal_recession_ray
    (hd : d ≠ 0)
    (hray : ∀ t : ℝ, 0 ≤ t → f (x + t • d) ≤ f x) :
    ¬ Bornology.IsBounded (𝓛[f]((f x)) : Set E) := by
  intro hbounded
  let ray : ℝ → E := fun t ↦ x + t • d
  have hray_mapsTo : Set.MapsTo ray (Set.Ici (0 : ℝ)) (𝓛[f]((f x))) :=
    ray_mapsTo_levelSet_of_nonincreasing_ray hray
  have himage_bounded : Bornology.IsBounded (ray '' Set.Ici (0 : ℝ)) :=
    hbounded.subset hray_mapsTo.image_subset
  obtain ⟨R, hR⟩ := himage_bounded.exists_norm_le
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hR_nonneg : 0 ≤ R := by
    have hzero_mem : ray 0 ∈ ray '' Set.Ici (0 : ℝ) := ⟨0, by simp, rfl⟩
    exact le_trans (norm_nonneg _) (hR _ hzero_mem)
  let t : ℝ := (R + ‖x‖ + 1) / ‖d‖
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_mem : ray t ∈ ray '' Set.Ici (0 : ℝ) := ⟨t, ht_nonneg, rfl⟩
  have hRt : ‖ray t‖ ≤ R := hR _ ht_mem
  have htd : t * ‖d‖ ≤ R + ‖x‖ := by
    have hsub : ‖t • d‖ ≤ ‖ray t‖ + ‖x‖ := by
      simpa [ray, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        norm_sub_le (x + t • d) x
    calc
      t * ‖d‖ = ‖t • d‖ := by
        rw [norm_smul, Real.norm_of_nonneg ht_nonneg]
      _ ≤ ‖ray t‖ + ‖x‖ := hsub
      _ ≤ R + ‖x‖ := add_le_add hRt le_rfl
  have ht_eval : t * ‖d‖ = R + ‖x‖ + 1 := by
    dsimp [t]
    field_simp [hdnorm.ne']
  linarith

/-- A nonzero horizontal recession ray produces infinitely many points in the sublevel set through
`x`. This remains a corollary of the geometric bridge theorem, not the main owner content of
Theorem 5.0.25. -/
theorem levelSet_infinite_of_nonzero_horizontal_recession_ray
    (hd : d ≠ 0)
    (hray : ∀ t : ℝ, 0 ≤ t → f (x + t • d) ≤ f x) :
    Set.Infinite (𝓛[f]((f x)) : Set E) := by
  intro hfinite
  exact levelSet_not_bounded_of_nonzero_horizontal_recession_ray hd hray hfinite.isBounded

end HorizontalLevelSetGeometry

/-! ### Definition_5_0_27 (from Chap05) -/
noncomputable section

universe u

open scoped ConvexAnalysis WithTopConvexAnalysis

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 5.0.27 lies in the chapter's Fenchel-conjugacy domain.

Sampled owner-style declarations:
- `extendedRealEffectiveDomain` / `dom` in `Chap03/Definition_3_1_1_2`, the chapter owner for the
  effective domain of an `EReal`-valued function;
- `fenchelDual` in `Chap03/Definition_3_1_2_1`, the source-facing owner for the Fenchel conjugate
  of a `WithTop ℝ`-valued function on a real inner-product space;
- `fenchelDual_apply_eq_sSup_image_dom` in `Chap03/Definition_3_8`, the canonical bridge that
  restricts the defining supremum to `dom f`;
- `fenchelConjugate` in `Chap06/Definition_6_1`, the core dual-space owner underlying
  `fenchelDual`.

Best owner abstraction:
- source-facing: `fenchelDual`, written on the theorem surface as `f⋆`;
- core/canonical: `fenchelConjugate`;
- bridge/view: the `dom`-restricted supremum formula and the finite real part `withTopRealPart`.

Primitive data:
- `f : E → WithTop ℝ`.

Derived API:
- the recalled owner `f⋆`;
- the recalled dual effective domain `dom (f⋆)`;
- the recalled `dom`-restricted supremum formula `fenchelDual_apply_eq_sSup_image_dom`;
- the textbook bounded-below characterization of `dom (f⋆)` under `dom f` nonempty.

Source/core/bridge triage:
- source-facing: Definition 5.0.27, the Fenchel conjugate and its textbook dual domain on `ℝⁿ`;
- core/canonical: `fenchelConjugate`;
- bridge/view: the Euclidean specialization via `innerₗ E`.

This file is recall-first for the conjugate itself: the Chapter 3 owner already supplies the exact
source-facing Fenchel-dual construction and the canonical `dom`-restricted supremum formula, so
the previous local duplicate definitions are deleted. The dual effective domain is likewise
recalled directly as `dom (f⋆)`; only the textbook bounded-below condition remains as a companion
bridge theorem, because it is not the owner and it needs a nonempty-domain hypothesis to match the
canonical effective domain.
-/

/- Definition 5.0.27 recalls the source-facing Fenchel-dual owner on `ℝⁿ`. -/
recall fenchelDual

section

variable (f : E → WithTop ℝ)

/- Definition 5.0.27 also recalls the canonical dual effective domain surface `dom (f⋆)`. -/
#check dom (f⋆)

end

section

variable (f : E → WithTop ℝ) (s : E)

/- Restricting the recalled Fenchel-dual supremum to `dom f` gives the textbook formula. -/
#check fenchelDual_apply_eq_sSup_image_dom f s

end

section

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- On a real inner-product space, under the nonempty-domain hypothesis needed to exclude the
empty-image edge case, membership in the canonical dual effective domain `dom (f⋆)` is equivalent
to the textbook condition that `x ↦ f(x) - ⟪s, x⟫` is bounded below on `dom f`. -/
-- Proof sketch: rewrite `(f⋆) s` with `fenchelDual_apply_eq_sSup_image_dom`; under
-- `(dom f).Nonempty`, the displayed image set is nonempty and consists of finite real values, so
-- finiteness of the supremum is equivalent to boundedness above of
-- `x ↦ inner ℝ s x - withTopRealPart f x`, equivalently to boundedness below of
-- `x ↦ withTopRealPart f x - inner ℝ s x`.
theorem mem_dom_fenchelDual_iff {f : F → WithTop ℝ} (hdom : (dom f).Nonempty) {s : F} :
    s ∈ dom (f⋆) ↔
      BddBelow ((fun x : F ↦ withTopRealPart f x - inner ℝ s x) '' dom f) := sorry

end

end
