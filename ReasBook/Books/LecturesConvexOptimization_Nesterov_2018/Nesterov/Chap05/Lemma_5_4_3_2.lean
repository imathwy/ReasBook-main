import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_23
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_3_3
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 5.4.3.2 lies in the Chapter 5 logarithmic-homogeneity / self-concordant-barrier domain.

Sampled owner declarations in this domain:
* `IsLogarithmicallyHomogeneousOnWith` in `Definition_5_4_3_3`, the source-facing owner for the
  logarithmic scaling law on a cone interior;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for `ν`-self-
  concordant barriers on a domain;
* mathlib `ConvexCone.Salient`, the canonical owner for the source's "no straight lines" / no
  nontrivial lineality condition on a cone;
* `HasPositiveDefiniteHessianOn` and
  `HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem` in `Definition_5_0_23`, the canonical
  Chapter 5 owner and bridge for pointwise Hessian nondegeneracy on a domain;
* `hessian` in `Chap01/Definition_1_4_16` and `ContinuousLinearMap.inverse`, the canonical
  operator-level Hessian and inverse-Hessian surface.

Best owner abstraction:
* source-facing: the six logarithmic-homogeneity identities and their barrier consequence under
  the full logarithmic-homogeneity / barrier / salience hypotheses;
* core/canonical: `HasPositiveDefiniteHessianOn (interior (K : Set E)) F` together with the
  operator owner `hessian F x`, and the cone owner `K.Salient`;
* bridge/view: the textbook "no straight lines" phrasing
  `∀ u, u ∈ K → -u ∈ K → u = 0`, the determinant-nonzero consequence, and the inverse-Hessian
  pairing formula.

Primitive data:
* a cone owner `K : ConvexCone ℝ E`;
* logarithmic homogeneity of `F` on `K`;
* a self-concordant barrier hypothesis on `interior K`;
* the salience condition on `K`.

Derived API:
* pointwise positive-definite Hessian on `interior K` under the full barrier hypotheses;
* Hessian nondegeneracy at each interior point;
* the canonical inverse-Hessian expression `((hessian F x).inverse ...)`.

This refinement keeps the textbook source-facing statements, deletes the unused local salience
repackaging, and keeps the supporting Hessian-nondegeneracy bridge on the chapter owner
`HasPositiveDefiniteHessianOn`. The bridge now carries the closed logarithmic-homogeneity
hypothesis actually needed to match the cone geometry used later in the file, while the main
gradient/Hessian identities continue to use the canonical cone owner `K.Salient` together with the
canonical `hessian` / inverse surface instead of raw `fderiv` terms. -/

section BarrierCone

variable {K : ConvexCone ℝ E} {ν : NNReal} {F : E → ℝ}

variable [CompleteSpace E]

-- Proof sketch: use the closed logarithmically-homogeneous cone data carried by `hFlog`
-- together with salience to rule out the flat directions that obstruct strict Hessian
-- positivity, and read the result on `interior K` through the owner
-- `HasPositiveDefiniteHessianOn (interior K) F`.
/-- A logarithmically homogeneous self-concordant barrier on the interior of a salient cone has
positive-definite Hessian on that interior domain. -/
theorem hasPositiveDefiniteHessianOn_of_logHomogeneousBarrier_of_salient
    (hFlog : IsLogarithmicallyHomogeneousOnWith K (ν : ℝ) F)
    (hbarrier : IsSelfConcordantBarrierOnWith (interior (K : Set E)) ν F)
    (hK : K.Salient) :
    HasPositiveDefiniteHessianOn (interior (K : Set E)) F := by
  sorry

end BarrierCone

section BarrierCone

variable [FiniteDimensional ℝ E]
variable {K : ConvexCone ℝ E} {ν : NNReal} {F : E → ℝ}

local instance barrierConeFiniteDimensionalComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

-- Proof sketch: apply the owner bridge
-- `HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem` to the positive-definite Hessian
-- owner supplied by `hasPositiveDefiniteHessianOn_of_logHomogeneousBarrier_of_salient`.
/-- A logarithmically homogeneous self-concordant barrier on the interior of a salient cone has
nondegenerate Hessian at every interior point. -/
theorem hessian_det_ne_zero_of_logHomogeneousBarrier_of_salient
    (hFlog : IsLogarithmicallyHomogeneousOnWith K (ν : ℝ) F)
    (hbarrier : IsSelfConcordantBarrierOnWith (interior (K : Set E)) ν F)
    (hK : K.Salient)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    (hessian F x).det ≠ 0 := by
  letI : HasPositiveDefiniteHessianOn (interior (K : Set E)) F :=
    hasPositiveDefiniteHessianOn_of_logHomogeneousBarrier_of_salient hFlog hbarrier hK
  exact HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx

end BarrierCone

section LogarithmicHomogeneity

variable [CompleteSpace E]
variable {K : ConvexCone ℝ E} {ν : ℝ} {F : E → ℝ}

-- Proof sketch: differentiate the logarithmic scaling identity
-- `F (τ • x) = F x - ν log τ` with respect to `x`; the chain rule contributes the factor `τ` on
-- the left, and rearranging gives the `τ⁻¹` scaling of the gradient.
/-- Lemma 5.4.3.2 (1): logarithmic homogeneity rescales the gradient by `τ⁻¹`. -/
theorem gradient_pos_smul_eq_inv_smul
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) {τ : ℝ} (hτ : 0 < τ) :
    ∇ F (τ • x) = (1 / τ) • ∇ F x := sorry

-- Proof sketch: differentiate the gradient scaling identity once more with respect to `x`; the
-- chain rule introduces a second factor of `τ`, yielding the `τ⁻²` scaling of the Hessian map.
/-- Lemma 5.4.3.2 (2): logarithmic homogeneity rescales the Hessian by `τ⁻²`. -/
theorem hessian_pos_smul_eq_inv_sq_smul
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) {τ : ℝ} (hτ : 0 < τ) :
    hessian F (τ • x) = (1 / τ ^ (2 : ℕ)) • hessian F x := sorry

-- Proof sketch: differentiate the logarithmic scaling identity with respect to the scalar `τ`
-- along the ray `τ ↦ τ • x`, and then evaluate at `τ = 1`.
/-- Lemma 5.4.3.2 (3): the gradient pairing with the base point equals `-ν`. -/
theorem inner_gradient_self_eq_neg_parameter
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    inner ℝ (∇ F x) x = -ν := sorry

-- Proof sketch: differentiate the scalar identity `⟪∇ F(x), x⟫ = -ν` in an arbitrary direction
-- `h`; symmetry of the Hessian then identifies the resulting linear functional with
-- `h ↦ ⟪h, ∇²F(x) x + ∇F(x)⟫`.
/-- Lemma 5.4.3.2 (4): applying the Hessian at `x` to `x` gives `-∇ F(x)`. -/
theorem hessian_apply_self_eq_neg_gradient
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    hessian F x x = -∇ F x := sorry

-- Proof sketch: pair the identity `∇²F(x) x = -∇F(x)` with `x`, then substitute
-- `⟪∇ F(x), x⟫ = -ν`.
/-- Lemma 5.4.3.2 (5): the Hessian quadratic form of `x` at `x` equals `ν`. -/
theorem inner_hessian_apply_self_self_eq_parameter
    (hFlog : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    inner ℝ (hessian F x x) x = ν := sorry

end LogarithmicHomogeneity

section InverseHessian

variable [FiniteDimensional ℝ E]
variable {K : ConvexCone ℝ E} {ν : NNReal} {F : E → ℝ}

local instance inverseHessianFiniteDimensionalComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

-- Proof sketch: the logarithmically homogeneous salient-cone barrier hypothesis gives the owner
-- `HasPositiveDefiniteHessianOn (interior K) F`, so the Hessian at `x` has its canonical inverse
-- `(hessian F x).inverse`. Solve `∇²F(x) x = -∇F(x)` for `x` using that inverse, then substitute
-- the result into `⟪∇ F(x), x⟫ = -ν`.
/-- Lemma 5.4.3.2 (6): the inverse-Hessian pairing of the gradient with itself equals `ν`. -/
theorem inner_gradient_inverseHessian_gradient_eq_parameter
    (hFlog : IsLogarithmicallyHomogeneousOnWith K (ν : ℝ) F)
    (hbarrier : IsSelfConcordantBarrierOnWith (interior (K : Set E)) ν F)
    (hK : K.Salient)
    {x : E} (hx : x ∈ interior (K : Set E)) :
    inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) = (ν : ℝ) := sorry

end InverseHessian

end
