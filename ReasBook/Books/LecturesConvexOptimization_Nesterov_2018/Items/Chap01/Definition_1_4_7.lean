import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_4_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u v

/-
Definition 1.4.7 is a source-facing bridge in first-order differential calculus on Euclidean
space.

Source/core/bridge triage:
* source-facing: the coordinate formula for the gradient in the standard Euclidean basis
* core/canonical: mathlib's `gradient`
* bridge/view: identify each coordinate with the Fréchet derivative on the corresponding basis
  vector

Primary domain:
* first-order differential calculus on finite-dimensional Euclidean spaces

Relevant owner-style declarations sampled before refining:
* `gradient` from `Mathlib.Analysis.Calculus.Gradient.Basic`
* `inner_gradient_left`, which identifies `fderiv ℝ f xBar` with pairing against `∇ f xBar`
* `EuclideanSpace.inner_basisFun_real`, which recovers standard coordinates from the Euclidean
  basis
* `gradient_eq_pi_fderiv_stdBasis` from `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_4_7.lean`, the exact
  chapter-level source-facing bridge for this item

Owner abstraction:
* the gradient vector `∇ f xBar`

Primitive data:
* a function `f`
* a point `xBar`

Derived API:
* the directional derivative along the `i`th standard basis vector
* the coordinate formula `gradient_eq_pi_fderiv_stdBasis` under differentiability at `xBar`

The exact source-facing bridge already exists in the chapter owner file, so this item is refined
to a recall surface instead of reintroducing a parallel local theorem.
-/
recall gradient {𝕜 : Type u} {F : Type v} [RCLike 𝕜] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] (f : F → 𝕜) (x : F) : F

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

/- Definition 1.4.7: at a differentiability point `xBar`, the `i`th coordinate of `∇ f xBar`
in the standard Euclidean basis is the directional derivative of `f` along the `i`th basis
vector. -/
recall gradient_eq_pi_fderiv_stdBasis
    (f : E → ℝ) (xBar : E) (hf : DifferentiableAt ℝ f xBar) :
    ∇ f xBar = fun i ↦ fderiv ℝ f xBar (e i)
