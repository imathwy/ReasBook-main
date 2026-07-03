import Mathlib
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_1_4 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

/-
Definition 4.1.4 lies in the cubic-regularization local-optimality domain on finite-dimensional
real inner-product spaces.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`;
* the `Gradient`-scope notation `∇` from mathlib;
* `spectrum ℝ (hessian f x)`, the canonical spectral owner for the intrinsic Hessian operator;
* `sInf` and `max` on `ℝ`, the canonical owners for the least spectral value and the textbook
  “take the larger defect” construction.

Source/core/bridge triage:
* source-facing: `cubicRegularizationLocalOptimalityMeasure`;
* core/canonical: `‖∇ f x‖` and `sInf (spectrum ℝ (hessian f x))`;
* bridge/view: the Euclidean specialization `E = EuclideanSpace ℝ (Fin n)` used downstream when
  the Hessian is later displayed as a matrix and its least spectral value is written as
  `λ_min(∇² f x)`.

Primitive data:
* an ambient space `E`;
* an objective `f : E → ℝ`;
* scalars `L` and `M`;
* a point `x`.

Derived API:
* the defining formula for the source-facing local optimality measure;
* the owner notation `μ[f; L; M](x)`, with the textbook shorthand `μ[M](x)` recovered locally
  downstream once `f` and `L` are fixed.

This keeps the source-facing owner from the text but moves it to the same intrinsic ambient layer
as the chapter's Hessian owner, while using the primitive canonical spectral term directly instead
of depending on the later local alias for the least Hessian eigenvalue. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Definition 4.1.4: the local optimality measure `μ_M(x)` for cubic regularization is the
maximum of the square root of the scaled gradient norm term and the scaled negative least Hessian
eigenvalue term. -/
def cubicRegularizationLocalOptimalityMeasure (f : E → ℝ) (L M : ℝ) (x : E) : ℝ :=
  max (Real.sqrt ((2 / (L + M)) * ‖∇ f x‖))
    (-(2 / (2 * L + M)) * sInf (spectrum ℝ (hessian f x)))

namespace CubicRegularizationLocalOptimalityMeasure

scoped notation:max "μ[" f ";" L ";" M "](" x ")" =>
  cubicRegularizationLocalOptimalityMeasure f L M x

end CubicRegularizationLocalOptimalityMeasure

open scoped CubicRegularizationLocalOptimalityMeasure

-- Proof sketch: this is the defining expansion of
-- `cubicRegularizationLocalOptimalityMeasure`.
/-- The local optimality measure `μ[f; L; M](x)` is given by the textbook maximum formula. -/
@[simp] theorem cubicRegularizationLocalOptimalityMeasure_eq_max
    (f : E → ℝ) (L M : ℝ) (x : E) :
    μ[f; L; M](x) =
      max (Real.sqrt ((2 / (L + M)) * ‖∇ f x‖))
        (-(2 / (2 * L + M)) * sInf (spectrum ℝ (hessian f x))) :=
  rfl

-- Proof sketch: rewrite `μ[f; L; M](x)` using
-- `cubicRegularizationLocalOptimalityMeasure_eq_max`; the claim is then `le_max_left`.
/-- The scaled gradient term is bounded above by the local optimality measure. -/
theorem sqrt_scaledGradientNorm_le_cubicRegularizationLocalOptimalityMeasure
    (f : E → ℝ) (L M : ℝ) (x : E) :
    Real.sqrt ((2 / (L + M)) * ‖∇ f x‖) ≤ μ[f; L; M](x) := by
  rw [cubicRegularizationLocalOptimalityMeasure_eq_max]
  exact le_max_left _ _

-- Proof sketch: rewrite `μ[f; L; M](x)` using
-- `cubicRegularizationLocalOptimalityMeasure_eq_max`; the claim is then `le_max_right`.
/-- The scaled negative least-Hessian-eigenvalue term is bounded above by the local optimality
measure. -/
theorem scaledNegLeastHessianEigenvalue_le_cubicRegularizationLocalOptimalityMeasure
    (f : E → ℝ) (L M : ℝ) (x : E) :
    -(2 / (2 * L + M)) * sInf (spectrum ℝ (hessian f x)) ≤ μ[f; L; M](x) := by
  rw [cubicRegularizationLocalOptimalityMeasure_eq_max]
  exact le_max_right _ _

end

/-! ### Lemma_4_1_4 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 4.1.4 lies in the Chapter 4 cubic-regularization / Hessian-Lipschitz domain on
complete real inner-product spaces.

Sampled owner declarations:
* `HessianLipschitzOn` in `Definition_4_1_2`, the chapter owner for local `C²` Hessian-
  Lipschitz control on an open convex set;
* `HessianLipschitzOn.gradient_deviation_le` in `Lemma_4_1_1`, the localized gradient Taylor
  remainder bound supplied by that owner;
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner of the
  cubic model centered at `x`;
* `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y`, the canonical global
  minimizer interface for the cubic model.

Source/core/bridge triage:
* source-facing: the gradient bound for a cubic-model minimizer `T_M(x)`;
* core/canonical: `HessianLipschitzOn L 𝓕 f` together with
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y`;
* bridge/view: downstream specialization from the owner-level minimizer statement to a chosen
  step map `y = T_M(x)`.

Owner abstraction:
* keep the cubic-model minimizer relation as the public owner abstraction on the intrinsic ambient
  space `E`;
* derive the estimate from the localized gradient-deviation owner
  `HessianLipschitzOn.gradient_deviation_le`, rather than through a downstream residual wrapper.

Primitive data:
* the objective `f : E → ℝ`;
* the regularization parameter `M`;
* the base point `x`;
* the minimizer `y`;
* the owner hypotheses
  `HessianLipschitzOn L 𝓕 f` and
  `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y`.

Derived API:
* the norm bound for `∇ f y`;
* downstream step-map reformulations obtained by instantiating the same `IsMinOn` owner at a
  chosen trial-point map.

This removes the conflicting local owner `cubicRegularizationTrialPoint`, reuses the existing
cubic-model minimizer interface from `Definition_4_1_3` directly, and depends only on the direct
upstream gradient-remainder ingredient `Lemma_4_1_1` instead of reaching it through the
downstream residual file `Lemma_4_1_5`. -/

-- Proof sketch: use the first-order optimality equation satisfied by a global minimizer `y` of
-- `cubicRegularizationQuadraticApproximation f M x` to rewrite the linearized gradient at `y`,
-- then combine that identity with the gradient Taylor remainder estimate on `𝓕`; only the
-- nonnegativity `0 ≤ M` of the cubic coefficient is needed in the final estimate.
/-- Helper for Lemma 4.1.4: restricting the cubic model to an affine line through a global
minimizer preserves local minimality at the line parameter `0`. -/
private theorem cubic_model_line_isLocalMin_at_zero
    {f : E → ℝ} {M : ℝ} {x y : E}
    (hy : IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y)
    (v : E) :
    IsLocalMin
      (fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (y + t • v))
      0 := by
  have huniv : Set.univ ∈ nhds y := by
    simp
  have hlocal : IsLocalMin (cubicRegularizationQuadraticApproximation f M x) y :=
    hy.isLocalMin huniv
  have hlocal0 :
      IsLocalMin (cubicRegularizationQuadraticApproximation f M x) (y + (0 : ℝ) • v) := by
    simpa using hlocal
  have hline : ContinuousAt (fun t : ℝ ↦ y + t • v) 0 := by
    -- The affine line through `y` is smooth, hence continuous at the minimizing parameter.
    simpa [one_smul] using
      (HasDerivAt.const_add y ((hasDerivAt_id (0 : ℝ)).smul_const v)).continuousAt
  -- Compose ambient local minimality with the affine line parametrization.
  change IsLocalMin
    ((cubicRegularizationQuadraticApproximation f M x) ∘ fun t : ℝ ↦ y + t • v) 0
  exact hlocal0.comp_continuous (g := fun t : ℝ ↦ y + t • v) (b := 0) hline

/-- Helper for Lemma 4.1.4: along an affine line through `y`, the quadratic Taylor model centered
at `x` has derivative `⟪∇ f x + ∇² f(x)(y - x), v⟫` at the line parameter `0`. -/
private theorem quadratic_model_line_hasDerivAt_zero
    {f : E → ℝ} {x y v : E}
    (hf2 : ContDiffAt ℝ 2 f x) :
    HasDerivAt
      (fun t : ℝ ↦ secondOrderTaylorModelAt f x (y + t • v))
      (inner ℝ (∇ f x + hessian f x (y - x)) v)
      0 := by
  let a : E := y - x
  let T : E →L[ℝ] E := hessian f x
  let g : E := ∇ f x
  let A : ℝ := inner ℝ g v + inner ℝ (T a) v
  let B : ℝ := inner ℝ (T v) v
  have hsymm : T.IsSymmetric := by
    simpa [T] using fderiv_gradient_isSymmetric_of_contDiffAt hf2
  have hcross : inner ℝ (T v) a = inner ℝ (T a) v := by
    -- Symmetry of the Hessian identifies the two mixed terms in the quadratic expansion.
    calc
      inner ℝ (T v) a = inner ℝ v (T a) := hsymm v a
      _ = inner ℝ (T a) v := by
          rw [real_inner_comm]
  have hpoly :
      (fun t : ℝ ↦ secondOrderTaylorModelAt f x (y + t • v)) =
        fun t : ℝ ↦ secondOrderTaylorModelAt f x y + A * t + (B / 2 : ℝ) * t ^ (2 : ℕ) := by
    -- Expand the quadratic model along the line and collect the scalar polynomial terms.
    funext t
    have hdisp : y + t • v - x = a + t • v := by
      simp [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [secondOrderTaylorModelAt_apply, secondOrderTaylorModelAt_apply, hdisp]
    simp [A, B, T, g, a, hcross, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, pow_two]
    ring
  rw [hpoly]
  have hlin : HasDerivAt (fun s : ℝ ↦ A * s) A 0 := by
    simpa using (HasDerivAt.const_mul A (hasDerivAt_id (0 : ℝ)))
  have hquad : HasDerivAt (fun s : ℝ ↦ (B / 2 : ℝ) * s ^ (2 : ℕ)) 0 0 := by
    -- The quadratic correction has zero derivative at the base parameter.
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      (HasDerivAt.const_mul (B / 2 : ℝ) ((hasDerivAt_id (0 : ℝ)).pow 2))
  -- Differentiate the scalar polynomial description at `0`.
  simpa [A, B, T, g, a, inner_add_left, add_assoc, add_left_comm, add_comm] using
    (HasDerivAt.const_add (secondOrderTaylorModelAt f x y) (hlin.add hquad))

/-- Helper for Lemma 4.1.4: along an affine line through `y`, the cubic penalty contributes the
directional derivative `((M / 2) * ‖y - x‖) * ⟪y - x, v⟫` at the base parameter `0`. -/
private theorem cubic_penalty_line_hasDerivAt_zero
    {M : ℝ} {x y v : E} :
    HasDerivAt
      (fun t : ℝ ↦ (M / 6 : ℝ) * ‖(y + t • v) - x‖ ^ (3 : ℕ))
      ((((M / 2 : ℝ) * ‖y - x‖) * inner ℝ (y - x) v))
      0 := by
  have hthree : 1 < (3 : ℝ) := by
    norm_num
  have hexp : ((3 : ℝ) - 2) = 1 := by
    norm_num
  have hline : HasDerivAt (fun t : ℝ ↦ (y - x) + t • v) v 0 := by
    -- The norm-power derivative is composed with the affine line `t ↦ (y - x) + t v`.
    simpa [one_smul] using
      (HasDerivAt.const_add (y - x) ((hasDerivAt_id (0 : ℝ)).smul_const v))
  have hnorm :
      HasFDerivAt (fun z : E ↦ ‖z‖ ^ (3 : ℝ))
        ((3 * ‖y - x‖ ^ ((3 : ℝ) - 2)) • innerSL ℝ (y - x))
        ((y - x) + (0 : ℝ) • v) := by
    simpa [one_smul] using
      (hasFDerivAt_norm_rpow (y - x) hthree)
  have hraw :
      HasDerivAt (fun t : ℝ ↦ ‖(y - x) + t • v‖ ^ (3 : ℝ))
        (((3 : ℝ) * ‖y - x‖ ^ ((3 : ℝ) - 2)) * inner ℝ y v -
          (((3 : ℝ) * ‖y - x‖ ^ ((3 : ℝ) - 2)) * inner ℝ x v))
        0 := by
    simpa [Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      innerSL_apply_apply] using
      HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hnorm hline
  have hbase :
      HasDerivAt (fun t : ℝ ↦ ‖(y - x) + t • v‖ ^ (3 : ℝ))
        ((((3 : ℝ) * ‖y - x‖ ^ ((3 : ℝ) - 2))) * inner ℝ (y - x) v)
        0 := by
    -- Rewrite the raw scalar derivative through `inner (y - x) v`.
    convert hraw using 1
    rw [inner_sub_left]
    ring
  have hscaled :
      HasDerivAt (fun t : ℝ ↦ (M / 6 : ℝ) * ‖(y - x) + t • v‖ ^ (3 : ℝ))
        ((M / 6 : ℝ) * ((((3 : ℝ) * ‖y - x‖ ^ ((3 : ℝ) - 2))) * inner ℝ (y - x) v))
        0 := by
    -- Scale the norm-power derivative by the cubic coefficient `M / 6`.
    simpa [mul_comm] using (HasDerivAt.const_mul (M / 6 : ℝ) hbase)
  convert hscaled using 1
  · ext t
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · rw [hexp, Real.rpow_one]
    ring

/-- Helper for Lemma 4.1.4: first-order optimality of a global minimizer of the cubic model
rewrites the linearized gradient as the negative cubic-penalty vector. -/
private theorem linearized_gradient_eq_neg_cubic_penalty_of_isMinOn
    {f : E → ℝ} {𝓕 : Set E} {L : NNReal} {M : ℝ} {x y : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hy : IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y)
    (hx : x ∈ 𝓕) :
    ∇ f x + hessian f x (y - x) = -((((M / 2 : ℝ) * ‖y - x‖) • (y - x))) := by
  apply ext_inner_right ℝ
  intro v
  have hlineMin :
      IsLocalMin
        (fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (y + t • v))
        0 :=
    cubic_model_line_isLocalMin_at_zero hy v
  have hquad :
      HasDerivAt
        (fun t : ℝ ↦ secondOrderTaylorModelAt f x (y + t • v))
        (inner ℝ (∇ f x + hessian f x (y - x)) v)
        0 :=
    quadratic_model_line_hasDerivAt_zero (hf.contDiffAt hx)
  have hpen :
      HasDerivAt
        (fun t : ℝ ↦ (M / 6 : ℝ) * ‖(y + t • v) - x‖ ^ (3 : ℕ))
        ((((M / 2 : ℝ) * ‖y - x‖) * inner ℝ (y - x) v))
        0 :=
    cubic_penalty_line_hasDerivAt_zero (M := M)
  have hmodel :
      HasDerivAt
        (fun t : ℝ ↦ cubicRegularizationQuadraticApproximation f M x (y + t • v))
        (inner ℝ (∇ f x + hessian f x (y - x)) v +
          (((M / 2 : ℝ) * ‖y - x‖) * inner ℝ (y - x) v))
        0 := by
    -- Differentiate the quadratic Taylor part and the cubic penalty separately on the line.
    simpa [cubicRegularizationQuadraticApproximation, inner_add_left] using hquad.add hpen
  have hzero :
      inner ℝ (∇ f x + hessian f x (y - x)) v +
        (((M / 2 : ℝ) * ‖y - x‖) * inner ℝ (y - x) v) = 0 :=
    hlineMin.hasDerivAt_eq_zero hmodel
  have hinner :
      inner ℝ (∇ f x + hessian f x (y - x)) v =
        -((((M / 2 : ℝ) * ‖y - x‖) * inner ℝ (y - x) v)) := by
    -- Fermat stationarity on the line slice gives the scalar optimality equation.
    rw [eq_neg_iff_add_eq_zero]
    exact hzero
  simpa [inner_smul_left] using hinner

/-- Lemma 4.1.4: if `f` has `L`-Lipschitz Hessian on `𝓕`, and `y` globally minimizes the cubic
model centered at `x` with parameter `M`, then `‖∇ f y‖ ≤ ((L + M) / 2) ‖y - x‖²`. -/
theorem gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation
    {f : E → ℝ} {𝓕 : Set E} {L : NNReal} {M : ℝ} {x y : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hM : 0 ≤ M)
    (hy :
      IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y)
    (hx : x ∈ 𝓕)
    (hy𝓕 : y ∈ 𝓕) :
    ‖∇ f y‖ ≤ (((L : ℝ) + M) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  let d : E := y - x
  let cubicVector : E := (((M / 2 : ℝ) * ‖d‖) • d)
  have hlinearized :
      ∇ f x + hessian f x d = -cubicVector := by
    -- The minimizer stationarity identity is obtained from the line-slice derivative formula.
    simpa [d, cubicVector] using
      linearized_gradient_eq_neg_cubic_penalty_of_isMinOn hf hy hx
  have hdeviation :
      ‖∇ f y - ∇ f x - hessian f x d‖ ≤ ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
    -- This is exactly the localized gradient Taylor remainder from Lemma 4.1.1.
    simpa [d] using hf.gradient_deviation_le x y hx hy𝓕
  have hMhalf_nonneg : 0 ≤ (M / 2 : ℝ) := by
    linarith
  have hcubic_nonneg : 0 ≤ ((M / 2 : ℝ) * ‖d‖) := by
    exact mul_nonneg hMhalf_nonneg (norm_nonneg d)
  have hcubic_norm : ‖cubicVector‖ = (M / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) := by
    -- The cubic penalty vector has norm `(M / 2) * ‖d‖²` because `M ≥ 0`.
    calc
      ‖cubicVector‖ = ‖((M / 2 : ℝ) * ‖d‖)‖ * ‖d‖ := by
        simp [cubicVector, norm_smul]
      _ = ((M / 2 : ℝ) * ‖d‖) * ‖d‖ := by
        rw [Real.norm_of_nonneg hcubic_nonneg]
      _ = (M / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) := by
        ring
  have hrepack :
      ∇ f y = (∇ f y - ∇ f x - hessian f x d) - cubicVector := by
    -- Substitute the stationarity identity into the gradient at `y`.
    calc
      ∇ f y = (∇ f y - (∇ f x + hessian f x d)) - cubicVector := by
        rw [hlinearized]
        abel_nf
      _ = (∇ f y - ∇ f x - hessian f x d) - cubicVector := by
        abel_nf
  -- Apply the triangle inequality after isolating the Taylor remainder and cubic vector terms.
  calc
    ‖∇ f y‖ = ‖(∇ f y - ∇ f x - hessian f x d) - cubicVector‖ := by
      rw [← hrepack]
    _ ≤ ‖∇ f y - ∇ f x - hessian f x d‖ + ‖cubicVector‖ := norm_sub_le _ _
    _ ≤ ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) + ‖cubicVector‖ := by
      exact add_le_add hdeviation le_rfl
    _ = ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) + (M / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) := by
      rw [hcubic_norm]
    _ = (((L : ℝ) + M) / 2) * ‖d‖ ^ (2 : ℕ) := by
      ring

/-! ### Proposition_4_1_4 (from Chap04) -/
open scoped Gradient StrongConvex
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace StrongConvexOn

/- Proposition 4.1.4 lies in the whole-space strong-convexity / Polyak-inequality domain on
real Hilbert spaces.

Sampled owner-style declarations:
- project `f ∈ 𝓛^1[μ]` and `mem_strongConvexClass_iff` in `Chap02/Definition_2_14`;
- mathlib `StrongConvexOn`;
- project `StrongConvexOn.quadratic_growth_of_isMinOn` in `Chap02/Theorem_2_30`;
- project `ConvexOn.lower_tangent_plane` in `Chap02/Definition_2_2`;
- mathlib `IsMinOn`.

Best owner abstraction:
- source-facing: the whole-space strong-convexity class input `f ∈ 𝓛^1[μ]`;
- core/canonical: `StrongConvexOn Set.univ μ f`;
- bridge/view: `mem_strongConvexClass_iff`, together with rewriting the squared norm as
  `Real.rpow ‖∇ f x‖ (2 : ℝ)`.

Primitive data:
- the source-facing owner witness `hf : f ∈ 𝓛^1[μ]`;
- the differentiability needed to form `∇ f`.

Derived API:
- the internal bridge `0 < μ ∧ StrongConvexOn Set.univ μ f`;
- the source-facing owner `GradientDominatedOn 2 Set.univ f`;
- the pointwise Polyak bound at any point of `argmin[Set.univ] f`;
- the degree-two `Real.rpow` pointwise bound with textbook constant `(2 * μ)⁻¹`.

This refinement removes the parallel global wrappers `strongConvexOn_...`, restores the chapter's
source-facing strong-convexity owner `𝓛^1[μ]` on the public theorem surface, and uses
`StrongConvexOn Set.univ μ f` only through the internal bridge
`mem_strongConvexClass_iff`. It still exposes gradient domination through the chapter owner
`GradientDominatedOn` rather than through a parallel unbundled witness interface.
-/

/-- Helper for Proposition 4.1.4: a differentiable whole-space `μ`-strongly convex function has
objective values bounded below on `Set.univ`. -/
lemma objective_image_bddBelow_of_mem_strongConvexClass
    {μ : ℝ} {f : E → ℝ}
    (hf : f ∈ 𝓛^1[μ]) (hf_diff : Differentiable ℝ f) :
    BddBelow (f '' Set.univ) := by
  rcases mem_strongConvexClass_iff.mp hf with ⟨hμ, hstrong⟩
  let g0 : E := ∇ f 0
  let c : ℝ := f 0 - ‖g0‖ ^ (2 : ℕ) / (2 * μ)
  refine ⟨c, ?_⟩
  rintro _ ⟨x, -, rfl⟩
  have hgrad0 : HasGradientAt f g0 0 := by
    -- Differentiability identifies the canonical gradient at the base point.
    simpa [g0] using (hf_diff 0).hasGradientAt
  have htangent :
      f x ≥ f 0 + inner ℝ g0 (x - 0) + (μ / 2) * ‖x - 0‖ ^ (2 : ℕ) := by
    -- Strong convexity gives a quadratic lower tangent model at the base point.
    simpa using
      StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
        hstrong (by simp) (by simp) hgrad0
  have hquad :
      -(‖g0‖ ^ (2 : ℕ)) / (2 * μ) ≤
        inner ℝ g0 (x - 0) + (μ / 2) * ‖x - 0‖ ^ (2 : ℕ) :=
    SmoothMinimaxProblem.inner_add_quadratic_lower_bound μ hμ _ _
  have hraw :
      f 0 - ‖g0‖ ^ (2 : ℕ) / (2 * μ) ≤
        f 0 + (inner ℝ g0 (x - 0) + (μ / 2) * ‖x - 0‖ ^ (2 : ℕ)) := by
    -- Completing the square turns the tangent inequality into a uniform lower bound.
    simpa [neg_div, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hquad (f 0)
  have hraw' :
      c ≤ f 0 + inner ℝ g0 (x - 0) + (μ / 2) * ‖x - 0‖ ^ (2 : ℕ) := by
    simpa [c, add_assoc, add_left_comm, add_comm] using hraw
  exact le_trans hraw' htangent

/-- Helper for Proposition 4.1.4: a differentiable whole-space `μ`-strongly convex function
attains its minimum on `Set.univ`. -/
lemma exists_mem_argmin_of_mem_strongConvexClass
    {μ : ℝ} {f : E → ℝ}
    (hf : f ∈ 𝓛^1[μ]) (hf_diff : Differentiable ℝ f) :
    ∃ xStar, xStar ∈ argmin[Set.univ] f := by
  rcases mem_strongConvexClass_iff.mp hf with ⟨hμ, hstrong⟩
  rcases
      SmoothMinimaxProblem.exists_isMinOn_of_isClosed_of_complete_of_bddBelow
        (Q := Set.univ) (f := f) (μ := μ)
        isClosed_univ ⟨0, by simp⟩
        hf_diff.continuous.continuousOn hstrong hμ
        (objective_image_bddBelow_of_mem_strongConvexClass hf hf_diff)
    with ⟨xStar, -, hxStar_min⟩
  -- Repackage the attained minimum as canonical `argmin` membership.
  exact ⟨xStar, mem_constrainedArgmin_iff.mpr ⟨by simp, hxStar_min⟩⟩

/-- Helper for Proposition 4.1.4: the textbook trial point
`x - (1 / μ) • ∇ f x` satisfies the one-step lower bound obtained from strong convexity. -/
lemma gradient_step_lower_bound
    {μ : ℝ} {f : E → ℝ}
    (hf : f ∈ 𝓛^1[μ]) (hf_diff : Differentiable ℝ f) (x : E) :
    f (x - (1 / μ) • ∇ f x) ≥ f x - (1 / (2 * μ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
  rcases mem_strongConvexClass_iff.mp hf with ⟨hμ, hstrong⟩
  let g : E := ∇ f x
  let trialPoint : E := x - (1 / μ) • g
  have hgrad : HasGradientAt f g x := by
    -- Differentiability identifies the gradient used by the tangent inequality.
    simpa [g] using (hf_diff x).hasGradientAt
  have htangent :
      f trialPoint ≥ f x + inner ℝ g (trialPoint - x) + (μ / 2) * ‖trialPoint - x‖ ^ (2 : ℕ) := by
    -- Apply strong convexity at the pair `(x, x - μ⁻¹ ∇ f x)`.
    simpa using
      StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
        (Q := Set.univ) (x := x) (y := trialPoint) (g := g)
        hstrong (by simp) (by simp [trialPoint]) hgrad
  have hquad :
      -(‖g‖ ^ (2 : ℕ)) / (2 * μ) ≤
        inner ℝ g (trialPoint - x) + (μ / 2) * ‖trialPoint - x‖ ^ (2 : ℕ) :=
    SmoothMinimaxProblem.inner_add_quadratic_lower_bound μ hμ g (trialPoint - x)
  have hraw :
      f x - ‖g‖ ^ (2 : ℕ) / (2 * μ) ≤
        f x + (inner ℝ g (trialPoint - x) + (μ / 2) * ‖trialPoint - x‖ ^ (2 : ℕ)) := by
    -- Completing the square gives the desired lower bound for the trial-point model value.
    simpa [neg_div, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hquad (f x)
  have hlower : f x - ‖g‖ ^ (2 : ℕ) / (2 * μ) ≤ f trialPoint := by
    have htangent' :
        f x + (inner ℝ g (trialPoint - x) + (μ / 2) * ‖trialPoint - x‖ ^ (2 : ℕ)) ≤
          f trialPoint := by
      simpa [add_assoc, add_left_comm, add_comm] using htangent
    exact le_trans hraw htangent'
  have hgoal_div : f trialPoint ≥ f x - ‖g‖ ^ (2 : ℕ) / (2 * μ) := hlower
  simpa [trialPoint, g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hgoal_div

/-- Proposition 4.1.4: a positive strongly convex objective on a real Hilbert space is gradient
dominated of degree `2`. -/
-- Proof sketch: choose any global minimizer `xStar`, apply strong convexity at the pair `x` and
-- `x - (1 / μ) • ∇ f x`, using `mem_strongConvexClass_iff` to extract the internal
-- `StrongConvexOn Set.univ μ f` bridge and positivity of `μ`, and rewrite the resulting Polyak
-- inequality as the degree-two gradient-domination bound with constant `(2 * μ)⁻¹`.
theorem gradientDominatedOn_two
    {μ : ℝ} {f : E → ℝ}
    (hf : f ∈ 𝓛^1[μ]) (hf_diff : Differentiable ℝ f) :
    GradientDominatedOn 2 Set.univ f := by
  rcases mem_strongConvexClass_iff.mp hf with ⟨hμ, -⟩
  rcases exists_mem_argmin_of_mem_strongConvexClass hf hf_diff with ⟨xStar, hxStar⟩
  refine ⟨hf_diff.differentiableOn, by norm_num, ?_⟩
  refine ⟨xStar, 1 / (2 * μ), ?_⟩
  refine ⟨uniqueDiffOn_univ, hxStar, ?_, ?_⟩
  · -- The Polyak constant is positive because `μ` is positive.
    positivity
  · intro x hx
    rcases mem_constrainedArgmin_iff.mp hxStar with ⟨-, hxStar_min⟩
    have hgrad : HasGradientAt f (∇ f x) x := by
      -- Differentiability identifies the canonical gradient at `x`.
      simpa using (hf_diff x).hasGradientAt
    have htangent :
        f xStar ≥ f x + inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ) := by
      -- Evaluate strong convexity directly at the minimizer `xStar`.
      simpa using
        StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
          (mem_strongConvexClass_iff.mp hf).2 (by simp) (by simp) hgrad
    have hquad :
        -(‖∇ f x‖ ^ (2 : ℕ)) / (2 * μ) ≤
          inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ) :=
      SmoothMinimaxProblem.inner_add_quadratic_lower_bound
        μ hμ (∇ f x) (xStar - x)
    have hraw :
        f x - ‖∇ f x‖ ^ (2 : ℕ) / (2 * μ) ≤
          f x + (inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ)) := by
      -- Completing the square on the tangent model produces the Polyak bound.
      simpa [neg_div, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        add_le_add_left hquad (f x)
    have htangent' :
        f x + (inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ)) ≤ f xStar := by
      simpa [add_assoc, add_left_comm, add_comm] using htangent
    have hbound_sq :
        f x - f xStar ≤ (1 / (2 * μ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
      have hlower : f x - ‖∇ f x‖ ^ (2 : ℕ) / (2 * μ) ≤ f xStar := le_trans hraw htangent'
      have hbound_div :
          f x - f xStar ≤ ‖∇ f x‖ ^ (2 : ℕ) / (2 * μ) := by
        linarith
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbound_div
    -- On `Set.univ`, the within-gradient agrees with the ambient gradient.
    simpa [gradientWithin, gradient, fderivWithin_univ, Real.rpow_natCast] using hbound_sq

/-- Companion `Real.rpow` form of Proposition 4.1.4's Polyak inequality. -/
-- Proof sketch: obtain the owner witness `GradientDominatedOn 2 Set.univ f` from
-- `gradientDominatedOn_two`, transport it to the chosen minimizer with
-- `GradientDominatedOn.exists_usesConstant_of_mem_argmin`, and then apply the resulting
-- pointwise bound with textbook constant `(2 * μ)⁻¹`.
theorem sub_le_inv_two_mul_rpow_norm_gradient_two_of_isMinOn
    {μ : ℝ} {f : E → ℝ}
    (hf : f ∈ 𝓛^1[μ]) (hf_diff : Differentiable ℝ f)
    {xStar x : E} (hxStar : xStar ∈ argmin[Set.univ] f) :
    f x - f xStar ≤ (1 / (2 * μ)) * Real.rpow ‖∇ f x‖ (2 : ℝ) := by
  rcases mem_strongConvexClass_iff.mp hf with ⟨hμ, hstrong⟩
  let _ := hxStar
  have hgrad : HasGradientAt f (∇ f x) x := by
    -- Differentiability identifies the canonical gradient at `x`.
    simpa using (hf_diff x).hasGradientAt
  have htangent :
      f xStar ≥ f x + inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ) := by
    -- Evaluate strong convexity at the minimizer `xStar`.
    simpa using
      StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
        hstrong (by simp) (by simp) hgrad
  have hquad :
      -(‖∇ f x‖ ^ (2 : ℕ)) / (2 * μ) ≤
        inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ) :=
    SmoothMinimaxProblem.inner_add_quadratic_lower_bound
      μ hμ (∇ f x) (xStar - x)
  have hraw :
      f x - ‖∇ f x‖ ^ (2 : ℕ) / (2 * μ) ≤
        f x + (inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ)) := by
    -- Completing the square on the lower tangent model isolates the gradient norm term.
    simpa [neg_div, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hquad (f x)
  have htangent' :
      f x + (inner ℝ (∇ f x) (xStar - x) + (μ / 2) * ‖xStar - x‖ ^ (2 : ℕ)) ≤ f xStar := by
    simpa [add_assoc, add_left_comm, add_comm] using htangent
  have hbound_sq :
      f x - f xStar ≤ (1 / (2 * μ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
    have hlower : f x - ‖∇ f x‖ ^ (2 : ℕ) / (2 * μ) ≤ f xStar := le_trans hraw htangent'
    have hbound_div :
        f x - f xStar ≤ ‖∇ f x‖ ^ (2 : ℕ) / (2 * μ) := by
      linarith
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbound_div
  -- Rewrite the square as a degree-two real power.
  simpa [Real.rpow_natCast] using hbound_sq

/-- Companion squared-norm form of Proposition 4.1.4's Polyak inequality. -/
-- Proof sketch: apply `sub_le_inv_two_mul_rpow_norm_gradient_two_of_isMinOn` and rewrite
-- `Real.rpow ‖∇ f x‖ (2 : ℝ)` as `‖∇ f x‖ ^ (2 : ℕ)`.
theorem sub_le_inv_two_mul_norm_gradient_sq_of_isMinOn
    {μ : ℝ} {f : E → ℝ}
    (hf : f ∈ 𝓛^1[μ]) (hf_diff : Differentiable ℝ f)
    {xStar x : E} (hxStar : xStar ∈ argmin[Set.univ] f) :
    f x - f xStar ≤ (1 / (2 * μ)) * ‖∇ f x‖ ^ (2 : ℕ) := by
  -- This is the same estimate with the exponent written as a square.
  simpa [Real.rpow_natCast] using
    sub_le_inv_two_mul_rpow_norm_gradient_two_of_isMinOn hf hf_diff hxStar

end StrongConvexOn

/-! ### Theorem_4_1_4 (from Chap04) -/
open scoped ConstrainedArgmin

noncomputable section

universe u

/- Theorem 4.1.4 lies in the star-convex / cubic-regularization rate domain.

Sampled owner declarations:
* mathlib `StarConvex` and `starConvex_iff_segment_subset` for the ambient segment geometry;
* `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner
  for feasible minimizers on a comparison set;
* mathlib `Bornology.IsBounded`, `Metric.diam`, and `Metric.dist_le_diam_of_mem` for the
  feasible-set diameter bound owner;
* project `cubicallyRegularizedObjective` in `Definition_4_2_16` for the cubic perturbation owner.

Source/core/bridge triage:
* source-facing: `StarConvexWithRespectToOn f xStar 𝓕`, the textbook function-level
  star-convexity inequality relative to a chosen feasible reference point on a feasible set;
* core/canonical: `argmin[𝓕] f`, `argmin[segment ℝ x0 xStar] ...`, and
  `cubicallyRegularizedObjective`;
* bridge/view: the projection lemma `StarConvexWithRespectToOn.mem`.

Primitive data:
* an objective `f`;
* a feasible set `𝓕` with a distinguished optimizer `xStar ∈ argmin[𝓕] f`;
* a boundedness witness and diameter bound for `𝓕`;
* the fixed-center star-convexity inequality from `xStar` to feasible points.

Derived API:
* feasibility and optimality of `xStar` from `xStar ∈ argmin[𝓕] f`;
* feasibility of the star center from `StarConvexWithRespectToOn.mem`;
* the two rate theorems below, phrased directly over the canonical cubic perturbation owner. -/

section StarConvexOwner

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- `StarConvexWithRespectToOn f xStar 𝓕` is the textbook star-convexity inequality for `f`
with respect to the reference point `xStar` on the feasible set `𝓕`. -/
def StarConvexWithRespectToOn
    (f : E → ℝ) (xStar : E) (𝓕 : Set E) : Prop :=
  xStar ∈ 𝓕 ∧
    ∀ ⦃x : E⦄, x ∈ 𝓕 → ∀ ⦃α : ℝ⦄, α ∈ Set.Icc (0 : ℝ) 1 →
      f (α • xStar + (1 - α) • x) ≤ (1 - α) * f x + α * f xStar

/-- A star center with respect to `𝓕` is itself feasible. -/
theorem StarConvexWithRespectToOn.mem
    {f : E → ℝ} {xStar : E} {𝓕 : Set E}
    (hstar : StarConvexWithRespectToOn f xStar 𝓕) :
    xStar ∈ 𝓕 :=
  hstar.1

end StarConvexOwner

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

section StarConvexCubicRate

variable {f : E → ℝ} {𝓕 : Set E} {xStar : E} {L D : ℝ}

/-- Helper for Theorem 4.1.4: every feasible point has nonnegative objective gap above the
constrained minimizer `xStar`. -/
lemma objective_gap_nonneg_of_mem_argmin
    {x : E}
    (hxStar : xStar ∈ argmin[𝓕] f)
    (hx : x ∈ 𝓕) :
    0 ≤ f x - f xStar := by
  rcases (mem_constrainedArgmin_iff.mp hxStar) with ⟨_, hxStar_min⟩
  rw [isMinOn_iff] at hxStar_min
  -- Compare the feasible point directly against the constrained minimizer `xStar`.
  have hxStar_le : f xStar ≤ f x := hxStar_min x hx
  linarith

/-- Helper for Theorem 4.1.4: a cubic step along the segment to `xStar` satisfies the textbook
one-step scalar gap recurrence. -/
lemma cubic_segment_one_step_gap_le
    {xk y : E}
    (hF_bounded : Bornology.IsBounded 𝓕)
    (hdiam : Metric.diam 𝓕 ≤ D)
    (hstar : StarConvexWithRespectToOn f xStar 𝓕)
    (hxk : xk ∈ 𝓕)
    (hL : 0 < L)
    (hy :
      y ∈ argmin[segment ℝ xk xStar]
        (cubicallyRegularizedObjective f ((3 / 2 : ℝ) * L) xk))
    {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    f y - f xStar ≤
      (1 - α) * (f xk - f xStar) + (L / 2 : ℝ) * α ^ (3 : ℕ) * D ^ (3 : ℕ) := by
  rcases (mem_constrainedArgmin_iff.mp hy) with ⟨_, hy_min⟩
  rw [isMinOn_iff] at hy_min
  let z : E := AffineMap.lineMap xk xStar α
  have hz_mem : z ∈ segment ℝ xk xStar := by
    -- The comparison point is the canonical segment point with parameter `α`.
    rw [segment_eq_image_lineMap]
    exact ⟨α, hα, rfl⟩
  have hy_le :
      cubicallyRegularizedObjective f ((3 / 2 : ℝ) * L) xk y ≤
        cubicallyRegularizedObjective f ((3 / 2 : ℝ) * L) xk z :=
    hy_min z hz_mem
  have hcoeff : (3 / 2 : ℝ) * L / 3 = L / 2 := by
    ring
  have hy_le' :
      f y + (L / 2 : ℝ) * ‖y - xk‖ ^ (3 : ℕ) ≤
        f z + (L / 2 : ℝ) * ‖z - xk‖ ^ (3 : ℕ) := by
    rw [cubicallyRegularizedObjective_apply, cubicallyRegularizedObjective_apply] at hy_le
    simpa [hcoeff] using hy_le
  have hz_obj :
      f z ≤ (1 - α) * f xk + α * f xStar := by
    -- Star-convexity controls the objective value on the comparison segment.
    simpa [z, AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
      hstar.2 hxk hα
  have hD_nonneg : 0 ≤ D := le_trans Metric.diam_nonneg hdiam
  have hbase_norm_le : ‖xStar - xk‖ ≤ D := by
    have hdist_le : dist xStar xk ≤ D :=
      (Metric.dist_le_diam_of_mem hF_bounded hstar.mem hxk).trans hdiam
    simpa [dist_eq_norm] using hdist_le
  have hz_norm_eq : ‖z - xk‖ = α * ‖xStar - xk‖ := by
    -- The comparison point differs from `xk` by the scalar displacement `α • (xStar - xk)`.
    rw [show z = α • (xStar - xk) + xk by
      simpa [z] using (AffineMap.lineMap_apply xk xStar α)]
    simp [norm_smul_of_nonneg, hα.1]
  have hz_norm_le : ‖z - xk‖ ≤ α * D := by
    rw [hz_norm_eq]
    exact mul_le_mul_of_nonneg_left hbase_norm_le hα.1
  have hcube_le :
      (L / 2 : ℝ) * ‖z - xk‖ ^ (3 : ℕ) ≤
        (L / 2 : ℝ) * α ^ (3 : ℕ) * D ^ (3 : ℕ) := by
    -- The cubic penalty is bounded by the feasible-set diameter.
    have hpow :
        ‖z - xk‖ ^ (3 : ℕ) ≤ (α * D) ^ (3 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hz_norm_le 3
    have hcoef_nonneg : 0 ≤ L / 2 := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hpow hcoef_nonneg
    simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hy_pen_nonneg : 0 ≤ (L / 2 : ℝ) * ‖y - xk‖ ^ (3 : ℕ) := by
    positivity
  -- Drop the nonnegative penalty at `y`, then insert the star-convex and diameter bounds.
  nlinarith [hy_le', hz_obj, hy_pen_nonneg, hcube_le]

/-- Helper for Theorem 4.1.4: if the feasible-set diameter is nonpositive, every feasible point
coincides with the optimizer `xStar`, hence its objective gap vanishes. -/
lemma gap_eq_zero_of_diam_nonpos
    {x : E}
    (hF_bounded : Bornology.IsBounded 𝓕)
    (hdiam_nonpos : Metric.diam 𝓕 ≤ 0)
    (hxStar : xStar ∈ argmin[𝓕] f)
    (hx : x ∈ 𝓕) :
    f x - f xStar = 0 := by
  rcases (mem_constrainedArgmin_iff.mp hxStar) with ⟨hxStar_mem, _⟩
  -- A nonpositive diameter forces every feasible point to lie at zero distance from `xStar`.
  have hdist_le_zero : dist x xStar ≤ 0 :=
    (Metric.dist_le_diam_of_mem hF_bounded hx hxStar_mem).trans hdiam_nonpos
  have hdist_zero : dist x xStar = 0 := le_antisymm hdist_le_zero dist_nonneg
  have hx_eq : x = xStar := dist_eq_zero.mp hdist_zero
  simp [hx_eq]

/-- Helper for Theorem 4.1.4: the normalized square-root parameter of the scalar cubic recurrence
either vanishes or gains at least `1 / 3` in reciprocal value. -/
lemma reciprocal_alpha_growth_of_cubic_step
    {c α Δnext : ℝ}
    (hc : 0 < c)
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hΔnext_nonneg : 0 ≤ Δnext)
    (hstep : Δnext ≤ c * (α ^ (2 : ℕ) - (2 / 3 : ℝ) * α ^ (3 : ℕ))) :
    let αnext := Real.sqrt (Δnext / c)
    αnext ∈ Set.Icc (0 : ℝ) α ∧
      (Δnext = 0 ∨ 1 / αnext ≥ 1 / α + 1 / 3) := by
  dsimp
  have hcontract : Real.sqrt (Δnext / c) ≤ α * (1 - α / 3) := by
    -- Rewrite the cubic recurrence as a contraction for the normalized square-root parameter.
    apply (Real.sqrt_le_iff).2
    constructor
    · nlinarith [hα.1, hα.2]
    · have hquot : Δnext / c ≤ α ^ (2 : ℕ) - (2 / 3 : ℝ) * α ^ (3 : ℕ) := by
        exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using hstep)
      nlinarith [hquot]
  have hαnext_nonneg : 0 ≤ Real.sqrt (Δnext / c) := Real.sqrt_nonneg _
  have hαnext_le_α : Real.sqrt (Δnext / c) ≤ α := by
    nlinarith [hcontract, hα.1, hα.2]
  refine ⟨⟨hαnext_nonneg, hαnext_le_α⟩, ?_⟩
  by_cases hΔnext_zero : Δnext = 0
  · exact Or.inl hΔnext_zero
  · right
    have hΔnext_pos : 0 < Δnext :=
      lt_of_le_of_ne hΔnext_nonneg (Ne.symm hΔnext_zero)
    have hα_pos : 0 < α := by
      by_contra hα_nonpos
      have hα_zero : α = 0 := by
        nlinarith [hα.1]
      rw [hα_zero] at hstep
      have : Δnext ≤ 0 := by
        simpa using hstep
      linarith
    have hsqrt_pos : 0 < Real.sqrt (Δnext / c) := by
      apply Real.sqrt_pos.2
      exact div_pos hΔnext_pos hc
    have hrecip :
        1 / (α * (1 - α / 3)) ≤ 1 / Real.sqrt (Δnext / c) := by
      exact one_div_le_one_div_of_le hsqrt_pos hcontract
    have hexpand : 1 / α + 1 / 3 ≤ 1 / (α * (1 - α / 3)) := by
      have hthree_sub_pos : 0 < 3 - α := by
        nlinarith
      have hα_ne : α ≠ 0 := ne_of_gt hα_pos
      have hthree_sub_ne : 3 - α ≠ 0 := ne_of_gt hthree_sub_pos
      have hsplit :
          1 / (α * (1 - α / 3)) = 1 / α + 1 / (3 - α) := by
        field_simp [hα_ne, hthree_sub_ne]
        ring
      rw [hsplit]
      have hbound : 1 / 3 ≤ 1 / (3 - α) := by
        refine one_div_le_one_div_of_le ?_ ?_
        · positivity
        · nlinarith
      linarith
    linarith

-- Proof sketch: evaluate the one-step segment minimization rule against the competitor `xStar`,
-- use that `xStar` is a feasible optimizer together with star-convexity at `xStar` to control
-- the objective term along the segment from `x0` to `xStar`, and bound the cubic penalty by the
-- feasible-set diameter bound `D`.
/-- Theorem 4.1.4 (1): if the initial objective gap is at least `(3 / 2) L D^3`, then one cubic
segment-minimization step reduces it to at most `(1 / 2) L D^3`. -/
theorem starConvex_cubicSegment_first_gap_le_half_LD_cube
    {x0 x1 : E}
    (hF_bounded : Bornology.IsBounded 𝓕)
    (hdiam : Metric.diam 𝓕 ≤ D)
    (hxStar : xStar ∈ argmin[𝓕] f)
    (hstar : StarConvexWithRespectToOn f xStar 𝓕)
    (hx0 : x0 ∈ 𝓕)
    (hL : 0 < L)
    (hx1 :
      x1 ∈ argmin[segment ℝ x0 xStar]
        (cubicallyRegularizedObjective f ((3 / 2 : ℝ) * L) x0))
    (hgap0 : f x0 - f xStar ≥ (3 / 2 : ℝ) * L * D ^ (3 : ℕ)) :
    f x1 - f xStar ≤ (1 / 2 : ℝ) * L * D ^ (3 : ℕ) := by
  -- Compare the step directly with the endpoint competitor `xStar`, i.e. with `α = 1`.
  have hstep_one :=
    cubic_segment_one_step_gap_le hF_bounded hdiam hstar hx0 hL hx1
      (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  nlinarith [hstep_one]

-- Proof sketch: derive the one-step recurrence
-- `Δ_{k+1} ≤ min_{α ∈ [0,1]} ((1 - α) Δ_k + (L / 2) α^3 D^3)` from the segment minimization rule,
-- using that `xStar` is the chosen optimizer and star center. Then optimize it at
-- `α_k = sqrt (2 Δ_k / (3 L D^3))`, and telescope the reciprocal estimate
-- `1 / α_{k+1} - 1 / α_k ≥ 1 / 3` to obtain the inverse-square rate.
/-- Theorem 4.1.4 (2): if the initial objective gap is at most `(3 / 2) L D^3`, then every
iterate satisfies the inverse-square decay bound
`f(x_k) - f(xStar) ≤ 3 L D^3 / (2 (1 + k / 3)^2)`. -/
theorem starConvex_cubicSegment_gap_le_inverse_square_rate
    {x : ℕ → E}
    (hF_bounded : Bornology.IsBounded 𝓕)
    (hdiam : Metric.diam 𝓕 ≤ D)
    (hxStar : xStar ∈ argmin[𝓕] f)
    (hstar : StarConvexWithRespectToOn f xStar 𝓕)
    (hiterates : ∀ k : ℕ, x k ∈ 𝓕)
    (hL : 0 < L)
    (hstep :
      ∀ k : ℕ,
        x (k + 1) ∈ argmin[segment ℝ (x k) xStar]
          (cubicallyRegularizedObjective f ((3 / 2 : ℝ) * L) (x k)))
    (hgap0 : f (x 0) - f xStar ≤ (3 / 2 : ℝ) * L * D ^ (3 : ℕ)) :
    ∀ k : ℕ,
      f (x k) - f xStar ≤
        (3 * L * D ^ (3 : ℕ)) / (2 * (1 + (k : ℝ) / 3) ^ (2 : ℕ)) := by
  have hD_nonneg : 0 ≤ D := le_trans Metric.diam_nonneg hdiam
  by_cases hD_zero : D = 0
  · intro k
    have hdiam_nonpos : Metric.diam 𝓕 ≤ 0 := by
      simpa [hD_zero] using hdiam
    -- In the zero-diameter branch, every feasible iterate equals the optimizer.
    have hgap_eq :
        f (x k) - f xStar = 0 :=
      gap_eq_zero_of_diam_nonpos hF_bounded hdiam_nonpos hxStar (hiterates k)
    simpa [hD_zero] using hgap_eq.le
  · have hD_pos : 0 < D := lt_of_le_of_ne hD_nonneg (Ne.symm hD_zero)
    set c : ℝ := (3 / 2 : ℝ) * L * D ^ (3 : ℕ) with hcdef
    have hc : 0 < c := by
      rw [hcdef]
      positivity
    let Δ : ℕ → ℝ := fun k ↦ f (x k) - f xStar
    let α : ℕ → ℝ := fun k ↦ Real.sqrt (Δ k / c)
    have hΔ_nonneg : ∀ k : ℕ, 0 ≤ Δ k := by
      intro k
      simpa [Δ] using objective_gap_nonneg_of_mem_argmin hxStar (hiterates k)
    have hΔ_le_c : ∀ k : ℕ, Δ k ≤ c := by
      intro k
      induction k with
      | zero =>
          simpa [Δ, hcdef] using hgap0
      | succ k hk =>
          have hstep_one :
              Δ (k + 1) ≤ (L / 2 : ℝ) * D ^ (3 : ℕ) := by
            simpa [Δ, α] using
              cubic_segment_one_step_gap_le hF_bounded hdiam hstar
                (hiterates k) hL (hstep k)
                (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
          have hhalf_le_c : (L / 2 : ℝ) * D ^ (3 : ℕ) ≤ c := by
            rw [hcdef]
            nlinarith
          exact hstep_one.trans hhalf_le_c
    have hα_mem : ∀ k : ℕ, α k ∈ Set.Icc (0 : ℝ) 1 := by
      intro k
      refine ⟨?_, ?_⟩
      · simpa [α] using Real.sqrt_nonneg (Δ k / c)
      · have hsqrt_le_one : Real.sqrt (Δ k / c) ≤ 1 := by
          apply (Real.sqrt_le_iff).2
          constructor
          · norm_num
          · exact (div_le_iff₀ hc).2 (by simpa [hcdef] using hΔ_le_c k)
        simpa [α] using hsqrt_le_one
    have hΔ_eq : ∀ k : ℕ, Δ k = c * α k ^ (2 : ℕ) := by
      intro k
      have hsq : α k ^ (2 : ℕ) = Δ k / c := by
        simp [α, Real.sq_sqrt, div_nonneg (hΔ_nonneg k) hc.le]
      have hmul := congrArg (fun t : ℝ ↦ c * t) hsq
      field_simp [hc.ne'] at hmul
      nlinarith [hmul]
    have hstep_gap :
        ∀ k : ℕ,
          Δ (k + 1) ≤
            (1 - α k) * Δ k + (L / 2 : ℝ) * α k ^ (3 : ℕ) * D ^ (3 : ℕ) := by
      intro k
      simpa [Δ, α] using
        cubic_segment_one_step_gap_le hF_bounded hdiam hstar
          (hiterates k) hL (hstep k) (hα_mem k)
    have hrecurrence :
        ∀ k : ℕ,
          Δ (k + 1) ≤ c * (α k ^ (2 : ℕ) - (2 / 3 : ℝ) * α k ^ (3 : ℕ)) := by
      intro k
      have hstepk := hstep_gap k
      have hgapk := hΔ_eq k
      have hcubic :
          (L / 2 : ℝ) * α k ^ (3 : ℕ) * D ^ (3 : ℕ) =
            c * ((1 / 3 : ℝ) * α k ^ (3 : ℕ)) := by
        rw [hcdef]
        ring
      rw [hgapk, hcubic] at hstepk
      nlinarith
    have hreciprocal_or_zero :
        ∀ k : ℕ, Δ k = 0 ∨ 1 / α k ≥ 1 + (k : ℝ) / 3 := by
      intro k
      induction k with
      | zero =>
          by_cases hΔ0 : Δ 0 = 0
          · exact Or.inl hΔ0
          · have hα0_nonneg : 0 ≤ α 0 := (hα_mem 0).1
            have hα0_ne : α 0 ≠ 0 := by
              intro hα0_zero
              have : Δ 0 = 0 := by
                rw [hΔ_eq 0, hα0_zero]
                ring
              exact hΔ0 this
            have hα0_pos : 0 < α 0 := lt_of_le_of_ne hα0_nonneg (Ne.symm hα0_ne)
            have hone : 1 ≤ 1 / α 0 := by
              simpa using one_div_le_one_div_of_le hα0_pos (hα_mem 0).2
            exact Or.inr (by nlinarith)
      | succ k hk =>
          rcases hk with hΔk_zero | hk_recip
          · have hαk_zero : α k = 0 := by
              rw [hΔ_eq k] at hΔk_zero
              have hsq_zero : α k ^ (2 : ℕ) = 0 := by
                nlinarith [hΔk_zero, hc]
              nlinarith [sq_nonneg (α k), hsq_zero]
            have hnext_le_zero : Δ (k + 1) ≤ 0 := by
              have hrec := hrecurrence k
              rw [hαk_zero] at hrec
              simpa using hrec
            exact Or.inl (le_antisymm hnext_le_zero (hΔ_nonneg (k + 1)))
          · have hgrowth :
                α (k + 1) ∈ Set.Icc (0 : ℝ) (α k) ∧
                  (Δ (k + 1) = 0 ∨ 1 / α (k + 1) ≥ 1 / α k + 1 / 3) := by
              simpa [α] using
                reciprocal_alpha_growth_of_cubic_step hc (hα_mem k)
                  (hΔ_nonneg (k + 1)) (hrecurrence k)
            rcases hgrowth with ⟨_, hgrowth⟩
            rcases hgrowth with hΔnext_zero | hnext_recip
            · exact Or.inl hΔnext_zero
            · have hsum : 1 / α (k + 1) ≥ 1 + ((k + 1 : ℕ) : ℝ) / 3 := by
                have hsum' : 1 / α (k + 1) ≥ (1 + (k : ℝ) / 3) + 1 / 3 := by
                  nlinarith [hk_recip, hnext_recip]
                have hcast :
                    (1 + (k : ℝ) / 3) + 1 / 3 = 1 + ((k + 1 : ℕ) : ℝ) / 3 := by
                  rw [Nat.cast_add]
                  ring
                rw [← hcast]
                exact hsum'
              exact Or.inr hsum
    intro k
    change Δ k ≤ (3 * L * D ^ (3 : ℕ)) / (2 * (1 + (k : ℝ) / 3) ^ (2 : ℕ))
    rcases hreciprocal_or_zero k with hΔk_zero | hk_recip
    · simpa [hΔk_zero] using
        (show
          0 ≤ (3 * L * D ^ (3 : ℕ)) / (2 * (1 + (k : ℝ) / 3) ^ (2 : ℕ)) by
          positivity)
    · have hαk_nonneg : 0 ≤ α k := (hα_mem k).1
      have hαk_ne : α k ≠ 0 := by
        intro hαk_zero
        have hkfalse : ¬((0 : ℝ) ≥ 1 + (k : ℝ) / 3) := by
          have : (0 : ℝ) < 1 + (k : ℝ) / 3 := by
            positivity
          linarith
        have : (0 : ℝ) ≥ 1 + (k : ℝ) / 3 := by
          simpa [hαk_zero] using hk_recip
        exact hkfalse this
      have hαk_pos : 0 < α k := lt_of_le_of_ne hαk_nonneg (Ne.symm hαk_ne)
      have hs_pos : 0 < 1 + (k : ℝ) / 3 := by
        positivity
      have hsα : (1 + (k : ℝ) / 3) * α k ≤ 1 := by
        exact (le_div_iff₀ hαk_pos).1 (by simpa using hk_recip)
      have hαk_le : α k ≤ 1 / (1 + (k : ℝ) / 3) := by
        exact (le_div_iff₀ hs_pos).2 (by simpa [mul_comm] using hsα)
      have hsq_le :
          α k ^ (2 : ℕ) ≤ (1 / (1 + (k : ℝ) / 3)) ^ (2 : ℕ) :=
        pow_le_pow_left₀ hαk_nonneg hαk_le 2
      calc
        Δ k = c * α k ^ (2 : ℕ) := hΔ_eq k
        _ ≤ c * (1 / (1 + (k : ℝ) / 3)) ^ (2 : ℕ) := by
          gcongr
        _ = (3 * L * D ^ (3 : ℕ)) / (2 * (1 + (k : ℝ) / 3) ^ (2 : ℕ)) := by
          rw [hcdef]
          have hs_ne : (1 + (k : ℝ) / 3) ≠ 0 := by positivity
          field_simp [hs_ne]

end StarConvexCubicRate

/-! ### Definition_4_1_5 (from Chap04) -/
universe u

variable {X : Type u}

/- Definition 4.1.5 lies in the regularized-Newton trajectory domain.

Sampled owner declarations:
* `Set.Ioc` in mathlib, the canonical owner for the admissible interval condition `M_k ∈ (0, 2L]`;
* `RegularizedNewton.acceptingParameters` in `Definition_4_1_16`, the later fixed-iterate
  acceptance owner that deliberately builds on top of, rather than inside, the weaker trajectory
  object defined here;
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the stronger Chapter 4 owner that adds
  accepted-step data and then forgets to the present relaxed iteration.

Source/core/bridge triage:
* source-facing: the relaxed trajectory data `x_k`, `M_k`, and `x_{k+1} = T_{M_k}(x_k)`;
* core/canonical: the iterate sequence, regularization sequence, and the interval owner
  `Set.Ioc 0 (2 * L)`;
* bridge/view: the coercion to the underlying trajectory `ℕ → X`.

Primitive data:
* the iterate sequence `x`;
* the regularization sequence `M_k`;
* the admissible-interval condition `M_k ∈ (0, 2L]`;
* the update law `x_{k+1} = T_{M_k}(x_k)`.

Derived API:
* the coercion to the iterate sequence;
* positivity of each `M_k`;
* the upper bound `M_k ≤ 2L`;
* positivity of `L`, derived from any admissible `M_k`.

The owner abstraction is therefore already the right one for this file: later chapter APIs add
acceptance or minimization data on top of this trajectory object, rather than replacing it by a
parallel wrapper. -/
/-- Definition 4.1.5: a relaxed regularized Newton iteration for a trial map `T_M` and constant
`L` consists of an iterate sequence `x_k` and regularization parameters `M_k` such that each
`M_k` lies in `(0, 2L]` and the update `x_{k+1} = T_{M_k}(x_k)` holds for every `k ≥ 0`. These
interval conditions force `L > 0`, recovered below as derived API. -/
structure RelaxedRegularizedNewtonIteration
    (stepMap : ℝ → X → X) (L : ℝ) where
  /-- The iterate sequence `x₀, x₁, x₂, ...`. -/
  x : ℕ → X
  /-- The regularization parameters `M₀, M₁, M₂, ...`. -/
  regularization : ℕ → ℝ
  /-- Every parameter `M_k` lies in the admissible interval `(0, 2L]`. -/
  regularization_mem_Ioc (k : ℕ) : regularization k ∈ Set.Ioc 0 (2 * L)
  /-- The next iterate is obtained by applying `T_{M_k}` to the current iterate `x_k`. -/
  x_succ (k : ℕ) : x (k + 1) = stepMap (regularization k) (x k)

namespace RelaxedRegularizedNewtonIteration

variable {stepMap : ℝ → X → X} {L : ℝ}

/-- A relaxed regularized Newton iteration can be used as its underlying iterate sequence `x_k`. -/
instance :
    CoeFun (RelaxedRegularizedNewtonIteration stepMap L) (fun _ ↦ ℕ → X) where
  coe method := method.x

/-- Every regularization parameter in a relaxed regularized Newton iteration is positive. -/
theorem regularization_pos
    (method : RelaxedRegularizedNewtonIteration stepMap L) (k : ℕ) :
    0 < method.regularization k :=
  (method.regularization_mem_Ioc k).1

/-- Every regularization parameter in a relaxed regularized Newton iteration is bounded above by
`2L`. -/
theorem regularization_le_two_mul_L
    (method : RelaxedRegularizedNewtonIteration stepMap L) (k : ℕ) :
    method.regularization k ≤ 2 * L :=
  (method.regularization_mem_Ioc k).2

/-- The regularization scale `L` is positive. -/
theorem L_pos
    (method : RelaxedRegularizedNewtonIteration stepMap L) :
    0 < L := by
  have h0 : 0 < method.regularization 0 :=
    method.regularization_pos 0
  have hL : method.regularization 0 ≤ 2 * L :=
    method.regularization_le_two_mul_L 0
  linarith

end RelaxedRegularizedNewtonIteration

/-! ### Lemma_4_1_5 (from Chap04) -/
open scoped ConstrainedArgmin CubicRegularizationModelNotation Gradient

noncomputable section

universe u

section CubicRegularizationModel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped CubicRegularizationResidual

/- Lemma 4.1.5 lies in the chapter cubic-regularization model-value domain on complete real
inner-product spaces.

Sampled owner declarations:
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`
* `IsMinOn (cubicRegularizationQuadraticApproximation f M x) Set.univ y` in
  `Definition_4_1_3`
* `cubicRegularizationProblem`, `Φ[f; M](x)`, and `f̄[f; M](x)` in `Definition_4_1_3`
* `HessianLipschitzOn.secondOrderTaylorModel_error_le` in `Lemma_4_1_1`

Source/core/bridge triage:
* source-facing: the feasible-comparison and descent consequences of Lemma 4.1.5
* core/canonical: the whole-space owner `Φ[f; M](x)` and its real-valued surface `f̄[f; M](x)`
* bridge/view: realizing `f̄[f; M](x)` at the current minimizing trial point `trialPoint` from
  `IsMinOn (m[f; M](x)) Set.univ trialPoint`

Primitive data:
* the objective `f`
* the regularization parameter `M`
* the current minimizing trial point `trialPoint`
* the owner hypotheses `IsMinOn (m[f; M](x)) Set.univ trialPoint` and
  `HessianLipschitzOn L 𝓕 f`

Derived API:
* the pointwise residual `r[trialPoint] x`, which specializes to the textbook `r_M(x)` after
  choosing the minimizing trial point `trialPoint = T_M(x)`
* the pointwise feasible-comparison upper bound for `f̄[f; M](x)`
* the source-facing minimum corollary of that pointwise comparison
* the residual-cube decrease estimate
* the local upper bound `f y ≤ m_x^M(y)` on feasible points when `M ≥ L`
* objective control of a minimizing trial point once that trial point is known to lie in `𝓕`

The previous local wrapper `cubicRegularizedModelValue` duplicated the canonical owner
`Φ[f; M](x)`; this file now states the source-facing lemmas directly on that owner and leaves
realization at a chosen minimizing trial point to
`cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn`. -/

variable {trialPoint : E}

/-- Helper for Lemma 4.1.5: restricting the cubic model to the affine line
`t ↦ x + t • (trialPoint - x)` preserves local minimality at the minimizing parameter `t = 1`. -/
private theorem cubic_model_line_isLocalMin_at_one
    {f : E → ℝ} {M : ℝ} {x : E}
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint) :
    IsLocalMin
      (fun t : ℝ ↦ (m[f; M](x)) (x + t • (trialPoint - x)))
      1 := by
  have hlocal : IsLocalMin (m[f; M](x)) trialPoint :=
    hstep.isLocalMin (by simp)
  have hlocal1 :
      IsLocalMin (m[f; M](x)) (x + (1 : ℝ) • (trialPoint - x)) := by
    -- The affine slice hits the minimizing trial point exactly at the parameter `1`.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlocal
  have hline :
      ContinuousAt (fun t : ℝ ↦ x + t • (trialPoint - x)) 1 := by
    -- The affine line through `x` and `trialPoint` is smooth, hence continuous at `1`.
    simpa [one_smul] using
      (HasDerivAt.const_add x
        ((hasDerivAt_id (1 : ℝ)).smul_const (trialPoint - x))).continuousAt
  -- Compose ambient local minimality with the affine line parametrization.
  change IsLocalMin
    ((m[f; M](x)) ∘ fun t : ℝ ↦ x + t • (trialPoint - x))
    1
  exact hlocal1.comp_continuous (g := fun t : ℝ ↦ x + t • (trialPoint - x)) (b := 1) hline

/-- Helper for Lemma 4.1.5: comparing the minimizing trial point with its reflection across `x`
shows that the gradient pairing with the trial displacement is nonpositive. -/
private theorem cubic_model_gradient_pairing_nonpos_of_reflection
    {f : E → ℝ} {M : ℝ} {x : E}
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint) :
    inner ℝ (∇ f x) (trialPoint - x) ≤ 0 := by
  let d : E := trialPoint - x
  have hmin :
      m[f; M](x; trialPoint) ≤ (m[f; M](x)) (x - d) :=
    hstep (by simp)
  have htrial :
      m[f; M](x; trialPoint) =
        f x + inner ℝ (∇ f x) d +
          (1 / 2 : ℝ) * inner ℝ (hessian f x d) d +
          (M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    -- Expand the model at the minimizing trial point in terms of the displacement `d`.
    simp [cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply, d]
  have hreflect :
      (m[f; M](x)) (x - d) =
        f x - inner ℝ (∇ f x) d +
          (1 / 2 : ℝ) * inner ℝ (hessian f x d) d +
          (M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    -- At the reflected point, the linear term changes sign while the quadratic and cubic terms
    -- stay unchanged.
    have hreflect : x - d = x + (-1 : ℝ) • d := by
      simp [sub_eq_add_neg]
    rw [hreflect, cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply]
    simp
    ring
  rw [htrial, hreflect] at hmin
  linarith

/-- Helper for Lemma 4.1.5: the scalar line slice through
`t ↦ x + t • (trialPoint - x)` satisfies the textbook stationarity identity at the minimizing
parameter `t = 1`. -/
private theorem cubic_model_directional_stationarity_at_trialPoint
    {f : E → ℝ} {M : ℝ} {x : E}
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint) :
    inner ℝ (∇ f x) (trialPoint - x) +
      inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
      (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) = 0 := by
  let d : E := trialPoint - x
  have hlineMin :
      IsLocalMin (fun t : ℝ ↦ (m[f; M](x)) (x + t • d)) 1 := by
    -- Recenter the source optimality condition on the scalar parameter `t = 1`.
    simpa [d] using cubic_model_line_isLocalMin_at_one (trialPoint := trialPoint) hstep
  have hmodel :
      HasDerivAt
        (fun t : ℝ ↦ (m[f; M](x)) (x + t • d))
        (inner ℝ (∇ f x) d + inner ℝ (hessian f x d) d +
          (M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ))
        1 := by
    have hslice :
        (fun t : ℝ ↦ (m[f; M](x)) (x + t • d)) =
          fun t : ℝ ↦
            f x +
              inner ℝ (∇ f x) d * t +
              ((inner ℝ (hessian f x d) d) / 2 : ℝ) * t ^ (2 : ℕ) +
              (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * |t| ^ (3 : ℕ) := by
      -- Expanding the model on the affine line produces a scalar cubic polynomial with an
      -- absolute-value cubic penalty.
      funext t
      rw [cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply]
      have hdisp : x + t • d - x = t • d := by
        simp [sub_eq_add_neg, add_assoc]
      rw [hdisp, norm_smul, mul_pow]
      simp [inner_smul_right, inner_smul_left, mul_assoc]
      ring
    rw [hslice]
    have hlin :
        HasDerivAt (fun t : ℝ ↦ inner ℝ (∇ f x) d * t) (inner ℝ (∇ f x) d) 1 := by
      -- The linear Taylor term differentiates to the gradient pairing.
      simpa using (HasDerivAt.const_mul (inner ℝ (∇ f x) d) (hasDerivAt_id (1 : ℝ)))
    have hquad :
        HasDerivAt
          (fun t : ℝ ↦ ((inner ℝ (hessian f x d) d) / 2 : ℝ) * t ^ (2 : ℕ))
          (inner ℝ (hessian f x d) d)
          1 := by
      -- The quadratic Taylor term differentiates to the Hessian quadratic form at `t = 1`.
      have hquadBase :
          HasDerivAt
            (fun t : ℝ ↦ ((inner ℝ (hessian f x d) d) / 2 : ℝ) * t ^ (2 : ℕ))
            ((((inner ℝ (hessian f x d) d) / 2 : ℝ) * (2 * 1)) : ℝ)
            1 := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
          (HasDerivAt.const_mul (((inner ℝ (hessian f x d) d) / 2 : ℝ))
            ((hasDerivAt_id (1 : ℝ)).pow 2))
      convert hquadBase using 1
      ring
    have habsCube :
        HasDerivAt (fun t : ℝ ↦ |t| ^ (3 : ℕ)) (3 : ℝ) 1 := by
      -- Near the positive point `1`, the cubic penalty behaves like the ordinary cubic.
      convert
        (hasDerivAt_abs_rpow (1 : ℝ) (by norm_num) :
          HasDerivAt (fun t : ℝ ↦ |t| ^ (3 : ℝ)) _ 1) using 1
      · ext t
        rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
      · norm_num
    have hcubic :
        HasDerivAt
          (fun t : ℝ ↦ (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * |t| ^ (3 : ℕ))
          ((M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ))
          1 := by
      -- Differentiate the absolute-value cubic penalty and simplify the scalar coefficient.
      have hbase :
          HasDerivAt
            (fun t : ℝ ↦ (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * |t| ^ (3 : ℕ))
            ((((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * 3)
            1 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (HasDerivAt.const_mul (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) habsCube)
      convert hbase using 1
      ring
    -- Summing the derivatives of the constant, linear, quadratic, and cubic pieces gives the
    -- scalar stationarity identity along the line slice.
    simpa [add_assoc, add_left_comm, add_comm] using
      (HasDerivAt.const_add (f x) (hlin.add hquad |>.add hcubic))
  exact hlineMin.hasDerivAt_eq_zero hmodel

-- Proof sketch: use the second-order Taylor remainder estimate from Lemma 4.1.1 to bound the
-- cubic model at each feasible `y`, then apply global minimality of `trialPoint` for the cubic
-- model.
/-- Lemma 4.1.5 (1), pointwise form: for `x ∈ 𝓕` and every feasible `y`, the cubic model value
`\bar f_M(x)` is bounded above by the comparison quantity
`f(y) + ((L + M) / 6) ‖y - x‖³`. -/
theorem cubicRegularizationValue_le_feasibleComparison_of_mem
    {𝓕 : Set E} {f : E → ℝ} {L : NNReal} {M : ℝ} {x y : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint)
    (hx : x ∈ 𝓕)
    (hy : y ∈ 𝓕) :
    f̄[f; M](x) ≤
      f y + (((L : ℝ) + M) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := by
  have hvalue :
      f̄[f; M](x) = m[f; M](x; trialPoint) :=
    cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn hstep
  have hmin :
      m[f; M](x; trialPoint) ≤ m[f; M](x; y) :=
    hstep (by simp)
  have hmodel_le :
      m[f; M](x; y) ≤
        f y + (((L : ℝ) + M) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := by
    -- The minimizing model value at `y` is controlled by the lower side of the Taylor remainder.
    rw [cubicRegularizationQuadraticApproximation_apply]
    have herror := hf.secondOrderTaylorModel_error_le x y hx hy
    linarith [(abs_le.mp herror).1]
  -- Realize `f̄[f; M](x)` at `trialPoint`, then compare it with the feasible point `y`.
  calc
    f̄[f; M](x) = m[f; M](x; trialPoint) := hvalue
    _ ≤ m[f; M](x; y) := hmin
    _ ≤ f y + (((L : ℝ) + M) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := hmodel_le

-- Lemma 4.1.5 (1) in the textbook minimum language is the immediate corollary of the stronger
-- pointwise feasible-comparison theorem above.
/-- Lemma 4.1.5 (1): for `x ∈ 𝓕`, the cubic model value `\bar f_M(x)` is bounded above by the
minimum of the feasible comparison quantity `f(y) + ((L + M) / 6) ‖y - x‖³`. -/
theorem cubicRegularizationValue_le_feasibleComparisonMinimum
    {𝓕 : Set E} {f : E → ℝ} {L : NNReal} {M : ℝ} {x yMin : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint)
    (hx : x ∈ 𝓕)
    (hyMin :
      yMin ∈ argmin[𝓕]
        (fun y ↦ f y + (((L : ℝ) + M) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ))) :
    f̄[f; M](x) ≤
      f yMin + (((L : ℝ) + M) / 6 : ℝ) * ‖yMin - x‖ ^ (3 : ℕ) :=
  cubicRegularizationValue_le_feasibleComparison_of_mem hf hstep hx
    (mem_constrainedArgmin_iff.mp hyMin).1

-- Proof sketch: write `\bar f_M(x)` as the cubic model value at `T_M(x)`, use the first-order
-- optimality relation for the global cubic minimizer together with the nonnegativity of the
-- descent term `⟪∇ f(x), x - T_M(x)⟫`, and simplify the remaining terms to obtain the explicit
-- `(M / 12) r_M(x)^3` lower bound.
/-- Lemma 4.1.5 (2): the gap `f(x) - \bar f_M(x)` dominates
`(M / 12) * r[trialPoint] x ^ 3`; when `trialPoint = T_M(x)`, this is the textbook bound
`(M / 12) r_M(x)^3`. -/
theorem objective_sub_cubicRegularizationValue_ge_residual_cube
    {f : E → ℝ} {M : ℝ} {x : E}
    (hM : 0 ≤ M)
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint) :
    f x - f̄[f; M](x) ≥
      (M / 12 : ℝ) * r[trialPoint] x ^ (3 : ℕ) := by
  let d : E := trialPoint - x
  have hcoeff_nonneg : 0 ≤ (M / 12 : ℝ) := by
    linarith
  have hvalue :
      f̄[f; M](x) = m[f; M](x; trialPoint) :=
    cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn hstep
  have hpair_nonpos :
      inner ℝ (∇ f x) d ≤ 0 := by
    -- Comparing the minimizer with its reflected point supplies the sign of the linear term.
    simpa [d] using
      cubic_model_gradient_pairing_nonpos_of_reflection (trialPoint := trialPoint) hstep
  have hstationary :
      inner ℝ (∇ f x) (trialPoint - x) +
        inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) +
        (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) = 0 :=
    cubic_model_directional_stationarity_at_trialPoint (trialPoint := trialPoint) hstep
  have hrewrite :
      f x - f̄[f; M](x) =
        -inner ℝ (∇ f x) (trialPoint - x) -
          (1 / 2 : ℝ) * inner ℝ (hessian f x (trialPoint - x)) (trialPoint - x) -
          (M / 6 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) := by
    -- Realizing `f̄[f; M](x)` at `trialPoint` leaves only the explicit model terms.
    rw [hvalue, cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply]
    ring
  have hgap :
      f x - f̄[f; M](x) =
        -(1 / 2 : ℝ) * inner ℝ (∇ f x) d +
          (M / 12 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    -- Eliminate the Hessian quadratic term using the stationarity identity.
    rw [hrewrite]
    simp [d]
    have hstationary' :
        inner ℝ (∇ f x) (trialPoint - x) +
          inner ℝ ((hessian f x) trialPoint - (hessian f x) x) (trialPoint - x) +
          (M / 2 : ℝ) * ‖trialPoint - x‖ ^ (3 : ℕ) = 0 := by
      simpa [map_sub] using hstationary
    linarith
  have hmain :
      f x - f̄[f; M](x) ≥
        (M / 12 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    rw [hgap]
    have hlin_nonneg : 0 ≤ -(1 / 2 : ℝ) * inner ℝ (∇ f x) d := by
      nlinarith
    nlinarith [hcoeff_nonneg]
  -- Rewrite the residual owner back to the norm `‖x - trialPoint‖`.
  simpa [d, cubicRegularizationResidual_eq_norm_sub, norm_sub_rev] using hmain

-- Proof sketch: apply the local Taylor upper bound from
-- `HessianLipschitzOn.secondOrderTaylorModel_error_le` at the feasible pair `x, y ∈ 𝓕`, then
-- absorb the cubic remainder using `M ≥ L` to compare the objective directly with the cubic
-- model at `y`.
/-- Lemma 4.1.5 (3): if `x, y ∈ 𝓕` and `M ≥ L`, then the objective value at `y` is bounded above
by the cubic model centered at `x`. -/
theorem objective_le_cubicRegularizationQuadraticApproximation_of_mem_of_le_hessianLipschitz
    {𝓕 : Set E} {f : E → ℝ} {L : NNReal} {M : ℝ} {x y : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hx : x ∈ 𝓕)
    (hy : y ∈ 𝓕)
    (hLM : (L : ℝ) ≤ M) :
    f y ≤ m[f; M](x; y) := by
  have hupper :
      f y ≤ secondOrderTaylorModelAt f x y + ((L : ℝ) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := by
    -- The upper side of the Taylor remainder controls the objective by the quadratic model.
    have herror := hf.secondOrderTaylorModel_error_le x y hx hy
    linarith [(abs_le.mp herror).2]
  have hcubic :
      ((L : ℝ) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) ≤
        (M / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := by
    -- The larger regularization parameter `M` absorbs the Hessian-Lipschitz cubic remainder.
    have hpow_nonneg : 0 ≤ ‖y - x‖ ^ (3 : ℕ) := by
      positivity
    have hcoeff : ((L : ℝ) / 6 : ℝ) ≤ (M / 6 : ℝ) := by
      linarith
    exact mul_le_mul_of_nonneg_right hcoeff hpow_nonneg
  -- Combine the Taylor upper bound with the coefficient comparison and fold back to `m[f; M](x; y)`.
  calc
    f y ≤ secondOrderTaylorModelAt f x y + ((L : ℝ) / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := hupper
    _ ≤ secondOrderTaylorModelAt f x y + (M / 6 : ℝ) * ‖y - x‖ ^ (3 : ℕ) := by
      gcongr
    _ = m[f; M](x; y) := by rw [cubicRegularizationQuadraticApproximation_apply]

-- Proof sketch: first apply
-- `objective_le_cubicRegularizationQuadraticApproximation_of_mem_of_le_hessianLipschitz` at the
-- feasible minimizing trial point `trialPoint`, then rewrite the cubic model value there as the
-- canonical owner `f̄[f; M](x)` using
-- `cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn hstep`.
/-- Lemma 4.1.5 (4): if `M ≥ L` and a minimizing cubic trial point lies in `𝓕`, then its
objective value is bounded above by the model value `\bar f_M(x)`. -/
theorem objective_cubicTrialPoint_le_cubicRegularizationValue_of_le_hessianLipschitz
    {𝓕 : Set E} {f : E → ℝ} {L : NNReal} {M : ℝ} {x : E}
    (hf : HessianLipschitzOn L 𝓕 f)
    (hstep : IsMinOn (m[f; M](x)) Set.univ trialPoint)
    (hx : x ∈ 𝓕)
    (htrialPoint : trialPoint ∈ 𝓕)
    (hLM : (L : ℝ) ≤ M) :
    f trialPoint ≤ f̄[f; M](x) := by
  have htrial : f trialPoint ≤ m[f; M](x; trialPoint) :=
    objective_le_cubicRegularizationQuadraticApproximation_of_mem_of_le_hessianLipschitz
      hf hx htrialPoint hLM
  simpa [cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn hstep] using htrial

end CubicRegularizationModel
