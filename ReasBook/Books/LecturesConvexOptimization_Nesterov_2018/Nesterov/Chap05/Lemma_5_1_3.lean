import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped HessianLocalNorm

noncomputable section

universe u

/- Lemma 5.1.3 lies in the chapter's self-concordance / line-derivative domain.

Sampled owner declarations in this domain:
* `thirdDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for the cubic
  directional derivative;
* `directionalSlice` from `Definition_5_0_10`, the chapter owner for affine-line restriction;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `associatedUnivariateFunction` from `Definition_5_0_12`, the source-facing reciprocal
  local-norm slice owner on the positivity domain;
* `associatedUnivariateFunctionDomain` from `Definition_5_0_12`, the source-facing owner for the
  natural positivity domain of that slice;
* nearby Chapter 5 line-derivative statements such as `Corollary_5_1_1` and `Theorem_5_1_4`,
  which already work over arbitrary complete real inner-product spaces.

Source/core/bridge triage:
* source-facing: the associated univariate reciprocal local-norm function and its natural domain
  along the affine line `t ↦ x + t • h`;
* core/canonical: `directionalSlice`, `thirdDirectionalDerivative f (x + t • h) h`, and
  `‖h‖[f; x + t • h]`;
* bridge/view: the ambient representative
  `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h` of
  `associatedUnivariateFunction dom f x h` on `associatedUnivariateFunctionDomain dom f x h`.

Primitive data:
* the objective `f`;
* the line data `x` and `h`;
* the open domain carrying `C³` regularity;
* the single point `t` of `associatedUnivariateFunctionDomain dom f x h`.

Derived API:
* the source-facing derivative bound for the reciprocal local-norm slice in terms of the chapter
  owners `thirdDirectionalDerivative` and `hessianLocalNorm`;
* the explicit derivative formula for the canonical affine-line bridge
  `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h` on
  `associatedUnivariateFunctionDomain dom f x h`.

This file therefore keeps `associatedUnivariateFunction` as the source-facing owner from
`Definition_5_0_12`, and its main public entry is the source-facing derivative bound for that
reciprocal local-norm slice. The explicit `HasDerivWithinAt` formula is only a bridge/view
statement because the one-variable calculus owner lives on ambient functions. Both statements use
the canonical ambient bridge `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h` on the natural domain
`associatedUnivariateFunctionDomain dom f x h`, not an ad hoc zero-extension. The Chapter 5
differential-calculus API used here already lives over complete real inner-product spaces, so
finite dimensionality is not part of the canonical statement. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {dom : Set E} {f : E → ℝ} {x h : E}

section AssociatedUnivariateFunctionBridge

local notation "sliceDomain" => associatedUnivariateFunctionDomain dom f x h
local notation "reciprocalLocalNormSlice" =>
  directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h

-- Proof sketch: differentiate the reciprocal local-norm slice on its natural domain using the
-- explicit `HasDerivWithinAt` bridge below; the uniform quotient hypothesis bounds the resulting
-- derivative formula by `M_f` at the chosen point.
/-- Lemma 5.1.3: if `f` is `C³` on an open set `dom` and the quotient
`|D³f(x + t h)[h,h,h]| / (2 ‖h‖[f; x + t • h]^3)` is bounded by `M_f` throughout the natural
domain of the associated univariate function, then the derivative within that domain of the
canonical ambient representative `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h`, equivalently
`associatedUnivariateFunction dom f x h`, has absolute value at most `M_f` at every
`t ∈ associatedUnivariateFunctionDomain dom f x h`. -/
theorem abs_derivWithin_associatedUnivariateFunction_le
    {Mf : NNReal} {t : ℝ}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (ht : t ∈ sliceDomain)
    (hbound :
      ∀ {s : ℝ}, s ∈ sliceDomain →
        |thirdDirectionalDerivative f (x + s • h) h| /
            (2 * ‖h‖[f; x + s • h] ^ (3 : ℕ)) ≤ (Mf : ℝ)) :
    |derivWithin
        reciprocalLocalNormSlice
        sliceDomain
        t| ≤ (Mf : ℝ) := sorry

-- Proof sketch: let `g(t) = hessianLocalNorm f (x + t • h) h ^ 2`, so `g` is the Hessian
-- quadratic form along the line. Differentiate `g` using the `C³` regularity of `f` on the open
-- set containing the line, identify `g'` with `thirdDirectionalDerivative f (x + t • h) h`, and
-- then apply the chain rule to `g ↦ g^(-1/2)` rewritten as the reciprocal local norm.
/-- Bridge form of Lemma 5.1.3: at each `t ∈ associatedUnivariateFunctionDomain dom f x h` the
canonical ambient representative `directionalSlice (fun y ↦ 1 / ‖h‖[f; y]) x h`, equivalently
`associatedUnivariateFunction dom f x h` on its natural domain, has derivative within that domain
`-D³f(x + t h)[h,h,h] / (2 ‖h‖[f; x + t • h]^3)`. -/
theorem associatedUnivariateFunction_hasDerivWithinAt
    {t : ℝ}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (ht : t ∈ sliceDomain) :
    HasDerivWithinAt
      reciprocalLocalNormSlice
      (-(thirdDirectionalDerivative f (x + t • h) h /
          (2 * ‖h‖[f; x + t • h] ^ (3 : ℕ))))
      sliceDomain
      t := sorry

end AssociatedUnivariateFunctionBridge

end
