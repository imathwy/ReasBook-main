import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_4_16
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "PosMat" => {A : Mat // Matrix.PosDef A}

/- Proposition 1.8.6 is a bridge/view statement in weighted differential calculus.

Source/core/bridge triage:
* source-facing: the formulas expressing the gradient and Hessian in the inner product induced by a
  positive-definite matrix `A`
* core/canonical: the intrinsic owners `gradient` and `hessian` for the weighted inner-product
  structure determined by `A`
* bridge/view: the Euclidean carrier owners `weightedGradient A` and `weightedHessian A`, which
  make the metric parameter explicit and record the weighted owners through Euclidean formulas

Primary domain:
* weighted first- and second-order differential calculus on finite-dimensional real inner-product
  spaces

Sampled owner-style declarations:
* `Matrix.PosDef.WeightedSpace` from Definition 1.8.3
* `HasWeightedGradientSecondOrderExpansionAt.iff_hasGradientAt_and_hasFDerivAt_gradient` from
  Definition 1.8.4
* `gradient` from mathlib's gradient API
* `hessian` from Definition 1.4.16

Best owner abstraction:
* the weighted-space `gradient`/`hessian` pair as core owners
* the coordinate transport `EuclideanSpace.equiv (Fin n) ℝ`, used only as a bridge from the
  weighted coordinate model to the Euclidean formulas

Primitive data:
* `A : PosMat`
* `f : Matrix.PosDef.WeightedSpace A → ℝ`
* `x : E`

Derived API:
* the transported weighted gradient `e.symm (∇ f (e x))`
* the transported weighted Hessian
  `(e.symm : _ →L[ℝ] _).comp (hessian f (e x)).comp (e : _ →L[ℝ] _)`
* the Euclidean formulas identifying those intrinsic weighted owners with `A⁻¹` applied to the
  Euclidean gradient/Hessian of the transported function

The proposition therefore stays at the `bridge/view` layer: it keeps the chapter's canonical
weighted `gradient`/`hessian` owners central, and records only their coordinate transport to the
Euclidean formulas. -/

namespace Matrix.PosDef

section
variable (A : PosMat)

/-- Proposition 1.8.6 (1): after transporting the intrinsic weighted gradient on
`Matrix.PosDef.WeightedSpace A` to Euclidean coordinates, one obtains `A⁻¹` applied to the
Euclidean gradient of the transported function. -/
theorem gradient_eq_inverse_gradient (f : WeightedSpace A → ℝ) (x : E) :
    let e : E ≃L[ℝ] WeightedSpace A :=
      (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toContinuousLinearEquiv
    e.symm (∇ f (e x)) = (A.1⁻¹).toEuclideanLin (∇ (f ∘ e) x) := by
  sorry

/-- Proposition 1.8.6 (2): after transporting the intrinsic weighted Hessian on
`Matrix.PosDef.WeightedSpace A` to Euclidean coordinates, one obtains the inverse metric composed
with the Euclidean Hessian of the transported function. -/
theorem hessian_eq_inverse_comp_hessian (f : WeightedSpace A → ℝ) (x : E) :
    let e : E ≃L[ℝ] WeightedSpace A :=
      (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toContinuousLinearEquiv
    let K : WeightedSpace A →L[ℝ] WeightedSpace A := hessian f (e x)
    let H₀ : WeightedSpace A →L[ℝ] E := (e.symm : WeightedSpace A →L[ℝ] E).comp K
    let H : E →L[ℝ] E :=
      H₀.comp (e : E →L[ℝ] WeightedSpace A)
    H =
      (A.1⁻¹).toEuclideanLin.toContinuousLinearMap.comp (hessian (f ∘ e) x) := by
  sorry

end

end Matrix.PosDef

end
