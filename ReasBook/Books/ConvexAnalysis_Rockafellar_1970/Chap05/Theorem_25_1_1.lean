import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [T2Space (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 25.1.1 says that if a scalar-valued function is differentiable at `x`,
  then the Rockafellar directional derivative `f'(x; y)` exists in every direction `y`.
- `core/canonical`: the primitive owner layer is `Function.HasDirectionalDerivativeAt` /
  `Function.directionalDerivativeAt`, where differentiability first produces the Fréchet-derivative
  value `fderiv 𝕜 f x y` over a plain normed space.
- `bridge/view`: the gradient pairing `⟪∇ f x, y⟫` is a Euclidean specialization of that
  primitive owner formula, recalled from the upstream Chapter 23 theorem.
- `bridge/view`: mathlib's `lineDeriv` is only a comparison view for the same first-order datum,
  so any `lineDeriv` statement here must remain a thin companion rather than a second owner.

Domain-style sampling used here:
- `Function.HasDirectionalDerivativeAt`;
- `Function.directionalDerivativeAt`;
- `Function.hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt`;
- `Function.directionalDerivativeAt_toWithTopBot_eq_fderiv_apply_of_hasFDerivAt`;
- `DifferentiableAt.lineDeriv_eq_fderiv`;

Upstream Euclidean bridge sampling:
- `Function.hasDirectionalDerivativeAt_toWithTopBot_of_hasGradientAt`;
- `Function.directionalDerivativeAt_toWithTopBot_eq_inner_gradient`;

Primitive data vs derived API:
- primitive source input: a differentiable scalar-valued function `f` at `x`;
- primitive owner outputs: the Chapter 23 existence/value statements on `f.toWithBotTop` with
  value `fderiv 𝕜 f x y`;
- derived API: Euclidean gradient pairing formulas and the comparison identity with mathlib's
  scalar-valued `lineDeriv`.

Layer target:
- `Function.hasDirectionalDerivativeAt_toWithBotTop_of_differentiableAt`: `core/canonical`;
- `Function.directionalDerivativeAt_toWithBotTop_eq_fderiv_apply`: `core/canonical`;
- `Function.lineDeriv_toWithBotTop_eq_directionalDerivativeAt`: `core/canonical`;
- `Function.directionalDerivativeAt_toWithTopBot_eq_inner_gradient`: recalled
  `bridge/view` value theorem from Chapter 23.

Ambient-assumption minimization:
- the imported Chapter 23 derivative owners used here are available at the Hausdorff codomain
  layer, so theorem surfaces stay at `[T2Space (WithBotTop 𝕜)]` rather than requiring the stronger
  `[OrderTopology (WithBotTop 𝕜)]`.
-/

namespace Function

/-- Theorem 25.1.1, canonical owner form at the primitive derivative layer: differentiability at
`x` gives the Chapter 23 directional-derivative owner for `f.toWithBotTop`, with value
`fderiv 𝕜 f x y`. -/
theorem hasDirectionalDerivativeAt_toWithBotTop_of_differentiableAt
    {f : E → 𝕜} {x y : E} (hf : DifferentiableAt 𝕜 f x) :
    HasDirectionalDerivativeAt f.toWithBotTop x y (fderiv 𝕜 f x y : WithBotTop 𝕜) := by
  simpa using hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt hf.hasFDerivAt

-- Proof sketch: specialize the Chapter 23 Fréchet-derivative value theorem using
-- `DifferentiableAt.hasFDerivAt`.
/-- Theorem 25.1.1, value form at the primitive derivative layer: for a differentiable
scalar-valued function, the Chapter 23 directional derivative of `f.toWithBotTop` is exactly the
Fréchet derivative evaluation `fderiv 𝕜 f x y`. -/
theorem directionalDerivativeAt_toWithBotTop_eq_fderiv_apply
    {f : E → 𝕜} {x y : E} (hf : DifferentiableAt 𝕜 f x) :
    directionalDerivativeAt f.toWithBotTop x y = (fderiv 𝕜 f x y : WithBotTop 𝕜) := by
  simpa using directionalDerivativeAt_toWithTopBot_eq_fderiv_apply_of_hasFDerivAt hf.hasFDerivAt

-- Proof sketch: compare `lineDeriv` with `fderiv`, then use the Chapter 23 owner-value theorem
-- at the Fréchet derivative layer.
/-- Canonical comparison owner for Theorem 25.1.1: for a differentiable scalar-valued function,
mathlib's `lineDeriv` agrees (after coercion to `WithBotTop 𝕜`) with the Chapter 23 owner
`Function.directionalDerivativeAt` on `f.toWithBotTop`. -/
theorem lineDeriv_toWithBotTop_eq_directionalDerivativeAt
    {f : E → 𝕜} {x y : E} (hf : DifferentiableAt 𝕜 f x) :
    (↑(lineDeriv 𝕜 f x y) : WithBotTop 𝕜) = directionalDerivativeAt f.toWithBotTop x y := by
  calc
    (↑(lineDeriv 𝕜 f x y) : WithBotTop 𝕜) = (↑(fderiv 𝕜 f x y) : WithBotTop 𝕜) := by
      rw [hf.lineDeriv_eq_fderiv]
    _ = directionalDerivativeAt f.toWithBotTop x y := by
      simpa using
        (directionalDerivativeAt_toWithBotTop_eq_fderiv_apply (f := f) (x := x) (y := y) hf).symm

end Function

end

/- Theorem 25.1.1 is already owned upstream by the exact Chapter 23 value theorem for
`Function.directionalDerivativeAt` on `f.toWithBotTop`. -/
recall Function.directionalDerivativeAt_toWithTopBot_eq_inner_gradient

end
