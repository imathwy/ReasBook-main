import Mathlib
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_2_1 (from Chap05) -/
open scoped Gradient
open NewtonDecrement

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Definition 5.2.1 lies in the Chapter 5 self-concordant Newton-iteration domain.

Sampled owner declarations:
* `NewtonDecrement.ofDetNeZero` in `Definition_5_0_24`, the chapter owner for the Newton
  decrement on a self-concordant domain;
* `DampedNewton.step` in Chapter 1, the canonical one-step Newton-update owner;
* `DampedNewton.Method` in Chapter 1, the recursive damped-Newton owner on the Hessian-
  nondegenerate admissible domain.

Best owner abstraction:
* source-facing: the variant-dependent step-size rule and the self-concordant Newton method on
  `dom`;
* core/canonical: `DampedNewton.step`, `DampedNewton.Method`,
  `DampedNewton.Method.IsSelfConcordant`, and `NewtonDecrement.ofDetNeZero`;
* bridge/view: the explicit inverse-Hessian update formula recovered from
  `DampedNewton.step_def`.

Primitive data:
* the Chapter 1 damped-Newton method in the admissible Hessian-nondegenerate domain.

Derived API:
* membership of its iterates in `dom`;
* the fact that its step-size schedule is the self-concordant one prescribed by the chosen
  variant;
* the canonical one-step update `selfConcordantNewtonNextPoint f Mf variant x hx hH`;
* iterate-wise Hessian nondegeneracy, inherited from `DampedNewton.Method`;
* the self-concordant recursion `xₖ₊₁ = selfConcordantNewtonNextPoint ...`.

This file keeps the source-facing Chapter 5 method as a property of the canonical Chapter 1 owner
`DampedNewton.Method`, rather than duplicating that method structure with extra
proof-bookkeeping fields. -/

/-- The three damping choices used in the local-convergence variants of Newton's method. -/
inductive SelfConcordantNewtonVariant
  /-- The standard Newton method with no damping shift. -/
  | standard
  /-- The damped Newton method with shift `M_f λ`. -/
  | damped
  /-- The intermediate Newton method with shift `M_f^2 λ^2 / (1 + M_f λ)`. -/
  | intermediate
deriving DecidableEq

/-- The damping shift `ξ` attached to a Newton variant for self-concordance parameter `M_f` and
Newton decrement `λ`. -/
def selfConcordantNewtonShift
    (variant : SelfConcordantNewtonVariant) (Mf : NNReal) (decrement : ℝ) : ℝ :=
  match variant with
  | .standard => 0
  | .damped => (Mf : ℝ) * decrement
  | .intermediate =>
      ((Mf : ℝ) ^ (2 : ℕ) * decrement ^ (2 : ℕ)) / (1 + (Mf : ℝ) * decrement)

/-- The self-concordant Newton step size attached to `variant` at `x`. -/
def selfConcordantNewtonStepSize
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (variant : SelfConcordantNewtonVariant) (x : E) (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) : ℝ :=
  1 / (1 + selfConcordantNewtonShift variant Mf (ofDetNeZero Mf f hx hH))

theorem selfConcordantNewtonShift_nonneg
    (variant : SelfConcordantNewtonVariant) (Mf : NNReal) {decrement : ℝ}
    (hdecrement : 0 ≤ decrement) :
    0 ≤ selfConcordantNewtonShift variant Mf decrement := by
  have hMf : 0 ≤ (Mf : ℝ) := Mf.2
  cases variant with
  | standard =>
      simp [selfConcordantNewtonShift]
  | damped =>
      simpa [selfConcordantNewtonShift] using mul_nonneg hMf hdecrement
  | intermediate =>
      have hnum : 0 ≤ (Mf : ℝ) ^ (2 : ℕ) * decrement ^ (2 : ℕ) := by positivity
      have hden : 0 ≤ 1 + (Mf : ℝ) * decrement := by
        nlinarith [mul_nonneg hMf hdecrement]
      exact div_nonneg hnum hden

/-- The self-concordant Newton step size is always positive. -/
theorem selfConcordantNewtonStepSize_pos
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (variant : SelfConcordantNewtonVariant) (x : E) (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) :
    0 < selfConcordantNewtonStepSize f Mf variant x hx hH := by
  have hshift :
      0 ≤
        selfConcordantNewtonShift variant Mf
          (ofDetNeZero Mf f hx hH) :=
    selfConcordantNewtonShift_nonneg variant Mf
      (ofDetNeZero_nonneg Mf f hx hH)
  have hdenom :
      0 <
        1 + selfConcordantNewtonShift variant Mf
          (ofDetNeZero Mf f hx hH) := by
    linarith
  simpa [selfConcordantNewtonStepSize] using one_div_pos.mpr hdenom

/-- The one-step self-concordant Newton update of variant `variant` from the point `x`. -/
def selfConcordantNewtonNextPoint
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (variant : SelfConcordantNewtonVariant) (x : E) (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) : E :=
  DampedNewton.step f ⟨x, hH⟩
    (selfConcordantNewtonStepSize f Mf variant x hx hH)

-- Proof sketch: unfold `selfConcordantNewtonNextPoint`; this is exactly the update formula from
-- Definition 5.2.1 with the variant-dependent shift `ξ = selfConcordantNewtonShift variant Mf
-- λ_f(x)`.
/-- Expanding `selfConcordantNewtonNextPoint f Mf variant x hx hH` gives the textbook one-step
self-concordant Newton update
`x - (1 + ξ)⁻¹ [∇² f(x)]⁻¹ ∇ f(x)`. -/
@[simp]
theorem selfConcordantNewtonNextPoint_def
    {dom : Set E} (f : E → ℝ) (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (variant : SelfConcordantNewtonVariant) (x : E) (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) :
    selfConcordantNewtonNextPoint f Mf variant x hx hH =
      x -
        (1 /
          (1 + selfConcordantNewtonShift variant Mf
            (ofDetNeZero Mf f hx hH))) •
          (hessian f x).inverse (∇ f x) := by
  have happly :
      (hessian f x).inverse (∇ f x) =
        ((hessian f x).toContinuousLinearEquivOfDetNeZero hH).symm (∇ f x) := by
    simpa using
      congrArg (fun T : E →L[ℝ] E ↦ T (∇ f x))
        (ContinuousLinearMap.inverse_equiv
          ((hessian f x).toContinuousLinearEquivOfDetNeZero hH))
  rw [selfConcordantNewtonNextPoint, DampedNewton.step_def]
  simp [selfConcordantNewtonStepSize, happly, hessian]

/-- Definition 5.2.1: a self-concordant Newton method of variant `variant` for `f` on `dom`
with parameter `M_f` is a Chapter 1 damped Newton method whose iterates stay in `dom` and whose
step-size schedule is the canonical self-concordant one
`(1 + ξ_k)⁻¹`, where
(A) `ξ_k = 0` for the standard Newton method,
(B) `ξ_k = M_f λ_f(x_k)` for the damped Newton method,
(C) `ξ_k = M_f^2 λ_f(x_k)^2 / (1 + M_f λ_f(x_k))` for the intermediate Newton method. -/
structure DampedNewton.Method.IsSelfConcordant
    (dom : Set E) {f : E → ℝ} (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (variant : SelfConcordantNewtonVariant) {x0 : E} (method : DampedNewton.Method f x0) :
    Prop where
  /-- Every iterate belongs to `dom`. -/
  iterates_mem : ∀ k : ℕ, method k ∈ dom
  /-- The Chapter 1 damping factors are exactly the canonical self-concordant step sizes from
  Definition 5.2.1. -/
  stepSize_eq : ∀ k : ℕ,
    method.stepSize k =
      selfConcordantNewtonStepSize f Mf variant (method k) (iterates_mem k)
        (method.hessian_nondegenerate k)

namespace DampedNewton.Method.IsSelfConcordant

/-- The Newton decrement of a self-concordant Newton method at step `k`. -/
def decrement
    {dom : Set E} {f : E → ℝ} {Mf : NNReal}
    [IsSelfConcordantOnWith dom Mf f] {variant : SelfConcordantNewtonVariant} {x0 : E}
    {method : DampedNewton.Method f x0}
    (hmethod : method.IsSelfConcordant dom Mf variant) (k : ℕ) : ℝ :=
  NewtonDecrement.ofDetNeZero Mf f (hmethod.iterates_mem k)
    (method.hessian_nondegenerate k)

/-- Expanding `hmethod.decrement k` recovers the canonical Newton decrement of the `k`th
self-concordant iterate. -/
@[simp] theorem decrement_def
    {dom : Set E} {f : E → ℝ} {Mf : NNReal}
    [IsSelfConcordantOnWith dom Mf f] {variant : SelfConcordantNewtonVariant} {x0 : E}
    {method : DampedNewton.Method f x0}
    (hmethod : method.IsSelfConcordant dom Mf variant) (k : ℕ) :
    hmethod.decrement k =
      NewtonDecrement.ofDetNeZero Mf f (hmethod.iterates_mem k)
        (method.hessian_nondegenerate k) :=
  rfl

/-- Each successor iterate of a self-concordant Newton method is the canonical self-concordant
Newton update of the previous one. -/
theorem succ_eq_nextPoint
    {dom : Set E} {f : E → ℝ} {Mf : NNReal}
    [IsSelfConcordantOnWith dom Mf f] {variant : SelfConcordantNewtonVariant} {x0 : E}
    {method : DampedNewton.Method f x0}
    (hmethod : method.IsSelfConcordant dom Mf variant) (k : ℕ) :
    method (k + 1) =
      selfConcordantNewtonNextPoint f Mf variant (method k) (hmethod.iterates_mem k)
        (method.hessian_nondegenerate k) := by
  have hx :
      (⟨method k, method.hessian_nondegenerate k⟩ : NewtonSystem.AdmissiblePoint (∇ f)) =
        method.x k := by
    ext
    rfl
  rw [selfConcordantNewtonNextPoint]
  simpa [hx, hmethod.stepSize_eq k] using method.step_eq k

end DampedNewton.Method.IsSelfConcordant

end

/-! ### Lemma_5_2_1 (from Chap05) -/
open scoped Gradient NewtonDecrement
open SelfConcordantNewtonVariant

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 5.2.1 lies in the Chapter 5 self-concordant intermediate-Newton domain.

Sampled owner declarations:
* `selfConcordantNewtonNextPoint` in `Definition_5_2_1`, the Chapter 5 owner for one-step
  self-concordant Newton updates;
* `NewtonDecrement.ofDetNeZero` in `Definition_5_0_24`, the Chapter 5 owner for the Newton
  decrement at a domain point with nondegenerate Hessian;
* `DampedNewton.Method.IsSelfConcordant` in `Definition_5_2_1`, the Chapter 5 refinement of the
  recursive damped Newton iterate sequence;
* `selfConcordant_dampedNewtonStep_value_decrease` in `Theorem_5_1_15`, the nearby one-step
  value-decrease owner for the damped variant.

Best owner abstraction:
* source-facing: the value drop along the intermediate Newton iterates;
* core/canonical: the one-step update `selfConcordantNewtonNextPoint` together with
  `NewtonDecrement.ofDetNeZero`;
* bridge/view: the recursive method step `x_{k+1}` obtained from the method package.

Primitive data:
* a self-concordant function `f` on `dom` with parameter `Mf`;
* a point `x ∈ dom`;
* Hessian nondegeneracy at `x`.

Derived API:
* the one-step intermediate update
  `selfConcordantNewtonNextPoint f Mf .intermediate x hx hH`;
* the Newton decrement `NewtonDecrement.ofDetNeZero Mf f hx hH`;
* the method-level successor `method (k + 1)`, recovered from the canonical one-step owner.

This refinement keeps the iterate-level textbook lemma, but no longer treats the recursive method
package as primitive data for the inequality itself. The file now centers the one-step owner
surface and derives the method statement from it. -/

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f]

-- Proof sketch: apply the self-concordant upper Taylor bound to the intermediate Newton update
-- `x_{k+1} = x_k - (1 + ξ_k)⁻¹ [∇²f(x_k)]⁻¹ ∇f(x_k)` with
-- `ξ_k = M_f² λ_k² / (1 + M_f λ_k)`, then rewrite the resulting `ω_*` term using the rational
-- lower bound from Lemma 5.1.5 and simplify the scalar expression exactly as in the textbook.
-- No positivity hypothesis on `M_f` is needed: at `M_f = 0`, the intermediate shift is `0` and
-- the displayed lower bound collapses to `δ² / 2`.
/-- The intermediate self-concordant Newton step decreases the objective by at least the explicit
rational function of the Newton decrement. -/
theorem selfConcordant_intermediateNewtonStep_value_drop_lower_bound
    (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f] {x : E}
    (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    let δ := NewtonDecrement.ofDetNeZero Mf f hx hH
    let xPlus := selfConcordantNewtonNextPoint f Mf .intermediate x hx hH
    f x - f xPlus ≥
      δ ^ 2 / (2 * (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ 2 * δ ^ 2)) +
        (Mf : ℝ) * δ ^ 3 / (2 * (1 + (Mf : ℝ) * δ) * (3 + 2 * (Mf : ℝ) * δ)) := sorry

-- Proof sketch: specialize `selfConcordant_intermediateNewtonStep_value_drop_lower_bound` to the
-- iterate `x_k`, then rewrite the successor `x_{k+1}` through the canonical one-step owner
-- `selfConcordantNewtonNextPoint`. As above, no separate positivity hypothesis on `M_f` is part
-- of the mathematical data.
/-- Lemma 5.2.1: along the intermediate self-concordant Newton method `(5.2.1)C`, the objective
drop from `x_k` to `x_{k+1}` is bounded below by the explicit rational function of the Newton
decrement `λ_k`. This is the textbook inequality `(5.2.2)`. -/
lemma intermediateNewton_value_drop_lower_bound
    {x0 : E}
    (method : DampedNewton.Method f x0)
    (hmethod : method.IsSelfConcordant dom Mf .intermediate)
    (k : ℕ) :
    let δ :=
      NewtonDecrement.ofDetNeZero Mf f (hmethod.iterates_mem k) (method.hessian_nondegenerate k)
    f (method k) - f (method (k + 1)) ≥
      δ ^ 2 / (2 * (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ 2 * δ ^ 2)) +
        (Mf : ℝ) * δ ^ 3 / (2 * (1 + (Mf : ℝ) * δ) * (3 + 2 * (Mf : ℝ) * δ)) := by
  simpa [hmethod.succ_eq_nextPoint k] using
    (selfConcordant_intermediateNewtonStep_value_drop_lower_bound
      Mf (hmethod.iterates_mem k) (method.hessian_nondegenerate k))

end

/-! ### Proposition_5_2_1 (from Chap05) -/
open scoped Gradient NewtonDecrement

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 5.2.1 lies in the Chapter 5 self-concordant Newton local-convergence domain.

Sampled owner declarations:
* `HasPositiveDefiniteHessianOn` in `Definition_5_0_23`, the Chapter 5 owner for the
  positive-definite-Hessian regime used throughout the local-convergence theory;
* `NewtonDecrement.ofPosDefMem` in `Definition_5_0_24`, the Chapter 5 owner for evaluating the
  Newton
  decrement from ordinary domain membership in that regime;
* `NewtonDecrement.ofPosDefMem_def` in `Definition_5_0_24`, the canonical expansion of that owner
  into
  the inverse-Hessian pairing formula.

Best owner abstraction:
* source-facing: the intermediate Newton quadratic-convergence region;
* core/canonical: `NewtonDecrement.ofPosDefMem`;
* bridge/view: the region-membership theorem specialized at a point `x ∈ dom`.

Primitive data:
* a point `x ∈ dom`;
* a positive parameter `Mf`;
* the ambient owner assumption `HasPositiveDefiniteHessianOn dom f`.

Derived API:
* the Newton decrement `NewtonDecrement.ofPosDefMem f x hx`;
* the Hessian nondegeneracy supplied canonically from `HasPositiveDefiniteHessianOn dom f`;
* the inverse-Hessian pairing expansion from `NewtonDecrement.ofPosDefMem_def`.

This proposition remains source-facing as the quadratic-convergence region, but it no longer
packages Hessian witness bookkeeping into the public theorem surface: that data is already owned
canonically by the Chapter 5 Newton-decrement API, while self-concordance hypotheses belong only
to downstream convergence results that actually use them. -/

/-- Proposition 5.2.1: the region of quadratic convergence for the self-concordant Newton method
`(5.2.1) C` is the subset `𝒟_f = {x ∈ dom f | λ_f(x) < 1 / (2 M_f)}`. -/
def intermediateNewtonQuadraticConvergenceRegion
    (dom : Set E) (f : E → ℝ) (Mf : NNRealˣ)
    [HasPositiveDefiniteHessianOn dom f] : Set E :=
  {x | ∃ hx : x ∈ dom, λ[f; x | hx] < 1 / (2 * (Mf : ℝ))}

/-- Source-facing notation for the intermediate Newton quadratic-convergence region `𝒟_f`. -/
scoped[IntermediateNewtonQuadraticConvergenceRegion] notation:max "𝒟[" f " | " dom ", " Mf "]" =>
  intermediateNewtonQuadraticConvergenceRegion dom f Mf

open scoped IntermediateNewtonQuadraticConvergenceRegion

section

variable {dom : Set E} {f : E → ℝ} {Mf : NNRealˣ}
variable [HasPositiveDefiniteHessianOn dom f]

-- Proof sketch: unfold `intermediateNewtonQuadraticConvergenceRegion`; with `hx : x ∈ dom`
-- fixed as ordinary public data, membership is exactly the smallness inequality for the canonical
-- domain-level Newton decrement owner `NewtonDecrement.ofPosDefMem f x hx`.
/-- Any point of `𝒟[f | dom, Mf]` lies in `dom`. -/
theorem mem_dom_of_mem_intermediateNewtonQuadraticConvergenceRegion
    {x : E} (hxD : x ∈ 𝒟[f | dom, Mf]) : x ∈ dom := by
  rcases hxD with ⟨hx, _⟩
  exact hx

/-- For a fixed domain point `x ∈ dom`, membership in `𝒟[f | dom, Mf]` is equivalent to the
bound `λ_f(x) < 1 / (2 M_f)` expressed through the canonical domain-level owner
`NewtonDecrement.ofPosDefMem`. -/
theorem mem_intermediateNewtonQuadraticConvergenceRegion_iff
    {x : E} (hx : x ∈ dom) :
    x ∈ 𝒟[f | dom, Mf] ↔
      λ[f; x | hx] < 1 / (2 * (Mf : ℝ)) := by
  constructor
  · rintro ⟨hx', hDec⟩
    simpa using hDec
  · intro hDec
    exact ⟨hx, hDec⟩

end

end

/-! ### Remark_5_2_1 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: unfold `satisfies_approximate_centering_condition` and then expand
-- `dualLocalNorm` via `dualLocalNorm_def`. Writing `s = ∇ f y`, the shifted covector becomes
-- `s - t ∇ f(y₀)`, so the condition is exactly the inverse-Hessian quadratic-neighborhood bound
-- around the straight line `t ↦ t ∇ f(y₀)` in dual coordinates.
/-- Remark 5.2.1: in dual coordinates `s = ∇ f(y)`, the central path is the straight line
`s(t) = t ∇ f(y₀)`, and the approximate centering condition `(5.2.13)` is exactly the statement
that `s` lies in the inverse-Hessian quadratic neighborhood of that line with radius `β / M_f`.
This is the project's library-facing form of the textbook dual interpretation using
`∇² f_* (s)`. -/
theorem approximateCenteringCondition_iff_dualCentralPathNeighborhood
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) (y : E) (hy : y ∈ dom) (Mf : NNRealˣ) (β : ℝ) :
    satisfies_approximate_centering_condition f y0 t y hy Mf β ↔
      let s := ∇ f y
      Real.sqrt
          (inner ℝ (s - (t : ℝ) • ∇ f (y0 : E))
            ((hessian f y).inverse (s - (t : ℝ) • ∇ f (y0 : E)))) ≤
        β / (Mf : ℝ) := sorry

end

/-! ### Theorem_5_2_1 (from Chap05) -/
open scoped Gradient HessianLocalNorm NewtonDecrement SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.2.1 lies in the Chapter 5 self-concordant minimization / Newton-decrement domain.

Sampled owner declarations:
* `HasPositiveDefiniteHessianOn` in `Definition_5_0_23`, the chapter owner for the
  positive-definite-Hessian regime in which the Newton decrement is evaluated from domain
  membership alone;
* `newtonDecrement`, the notation `λ[f; x | hx]`, and
  `NewtonDecrement.omegaArgOfPosDefMem` in `Definition_5_0_24`, the chapter owner for the Newton
  decrement, its positive-definite-domain theorem surface, and the canonical `ω` argument;
* `hessianLocalNorm` and `hessianLocalNorm_nonneg` in `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `existsUnique_isMinOn_with_suboptimality_bound_of_newtonDecrement_lt_inv` in `Theorem_5_1_13`,
  the chapter minimizer / Newton-decrement owner for the upper `ω_*` bound.

Best owner abstraction:
* source-facing: the minimizer-distance and suboptimality bounds of Theorem 5.2.1;
* core/canonical: `newtonDecrement`, `HasPositiveDefiniteHessianOn`, `hessianLocalNorm`, and the
  chapter self-concordant auxiliary functions;
* bridge/view: the domain-point notation `λ[f; x | hx]` together with the `ω'` / `ω'_*` scalar
  reparameterizations of the same canonical `ω` and `ω_*` arguments.

Primitive data:
* a self-concordant function `f` on `dom` with parameter `Mf`;
* a point `x ∈ dom` and a feasible minimizer `xStar : dom`.
* for the Newton-decrement clauses only, positive definiteness of the Hessian of `f` on `dom`.

Derived API:
* the domain-level Newton decrement `λ[f; x | hx]`;
* the canonical `ω` argument `NewtonDecrement.omegaArgOfPosDefMem Mf f x hx`;
* the canonical `ω_*` argument obtained from the small-decrement hypothesis;
* the local minimizer distance `‖x - xStar‖[f; x]`.

This file stays source-facing. Its Newton-decrement clauses live in the finite-dimensional
positive-definite-Hessian owner layer, while the minimizer-distance clause stays on the weaker
self-concordant/local-norm layer. The refinement removes the file-local duplicate witnesses for
Hessian nondegeneracy from the theorem surface, reusing the Chapter 5 positive-definite-Hessian
owner and the domain-level Newton-decrement bridge directly instead of keeping a parallel
determinant-witness surface. -/

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f]

section NewtonDecrementBounds

variable [FiniteDimensional ℝ E]
variable [HasPositiveDefiniteHessianOn dom f]

-- Proof sketch: apply the lower and upper self-concordant value bounds at the minimizer `xStar`.
-- The lower bound comes from Theorem 5.1.12, while the upper bound is the minimizer estimate from
-- Theorem 5.1.13 specialized to the Newton decrement at `x`.
/-- Theorem 5.2.1: if `xStar` minimizes a self-concordant function `f` on `dom` and the Newton
decrement at `x` is smaller than `1 / M_f`, then the scaled suboptimality
`M_f^2 (f x - f xStar)` lies between `ω(M_f λ_f(x))` and `ω_*(M_f λ_f(x))`. This is the textbook
inequality `(5.2.3)`. -/
theorem selfConcordant_suboptimality_bounds_of_newtonDecrement_lt_inv
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    let tω := NewtonDecrement.omegaArgOfPosDefMem Mf f x hx
    let τω := NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda
    ω tω ≤ (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) ∧
      (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ ω_* τω := sorry

-- Proof sketch: combine the gradient-pairing comparison from Theorem 5.1.8 with the Hessian
-- transport estimate from Corollary 5.1.5 to compare the minimizer distance
-- `‖x - xStar‖_x` to the Newton decrement `λ_f(x)`, then rewrite the resulting scalar bounds in
-- terms of `ω'` and `ω'_*`.
/-- The local minimizer distance `‖x - xStar‖_x` satisfies the textbook two-sided estimate
`(5.2.4)` in terms of the Newton decrement `λ_f(x)`. -/
theorem selfConcordant_minimizerDistance_bounds_of_newtonDecrement_lt_inv
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hlambda : λ[f; x | hx] < 1 / (Mf : ℝ)) :
    let tω := NewtonDecrement.omegaArgOfPosDefMem Mf f x hx
    let τω := NewtonDecrement.omegaStarArgOfPosDefMem Mf f x hx hlambda
    ω' tω ≤ (Mf : ℝ) * ‖x - xStar‖[f; x] ∧
      (Mf : ℝ) * ‖x - xStar‖[f; x] ≤ ω'_* τω := sorry

end NewtonDecrementBounds

-- Proof sketch: apply the lower and upper self-concordant value bounds with `y = xStar`, using
-- the local distance `r_*(x) = ‖x - xStar‖_x` as the step size. The admissibility hypothesis
-- `r_*(x) < 1 / M_f` supplies the upper `ω_*` estimate.
/-- If the local distance from `x` to a minimizer `xStar` is smaller than `1 / M_f`, then the
scaled suboptimality is bounded between `ω(M_f r_*(x))` and `ω_*(M_f r_*(x))`, which is the
textbook inequality `(5.2.5)`. -/
theorem selfConcordant_suboptimality_bounds_of_minimizerDistance_lt_inv
    {x : E} (xStar : dom) (hx : x ∈ dom) (hmin : IsMinOn f dom (xStar : E))
    (hr : ‖x - xStar‖[f; x] < 1 / (Mf : ℝ)) :
    let r := ‖x - xStar‖[f; x]
    let tω := selfConcordantOmegaArg Mf r (by
      exact neg_one_lt_mf_mul_of_nonneg (by
        simpa [r] using hessianLocalNorm_nonneg f x (x - xStar)))
    let τω := selfConcordantOmegaStarArg Mf r (mf_mul_lt_one_of_lt_inv hr)
    ω tω ≤ (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) ∧
      (Mf : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ ω_* τω := sorry

end

end

/-! ### Definition_5_2_2 (from Chap05) -/
noncomputable section

/- Definition 5.2.2 lies in the Chapter 5 self-concordant Newton-strategy domain.

Sampled owner declarations:
* `SelfConcordantNewtonVariant` in `Definition_5_2_1`, the chapter owner for the textbook Newton
  variants;
* `selfConcordantNewtonNextPoint` in `Theorem_5_2_2`, the downstream one-step owner specialized by
  a Newton variant.

Best owner abstraction:
* source-facing: the two-stage strategy choosing between the textbook damped and intermediate
  variants;
* core/canonical: `SelfConcordantNewtonVariant`;
* bridge/view: the threshold test `1 / (2 M_f) ≤ λ` selecting one of those two canonical
  variants.

Primitive data:
* the positive self-concordance parameter `M_f`;
* the current Newton decrement `λ`.

Derived API:
* the chosen canonical variant `selfConcordantTwoStageStrategy Mf decrement`;
* the branch characterizations for `.damped` and `.intermediate`.

This file keeps the source-facing two-stage choice, reuses the chapter owner
`SelfConcordantNewtonVariant`, and deletes the one-off threshold wrapper in favor of the direct
textbook inequality `1 / (2 M_f) ≤ λ` on the canonical positive-parameter surface `Mf : NNRealˣ`.
-/

/-- Definition 5.2.2: the two-stage strategy for self-concordant minimization chooses the damped
Newton method when the current Newton decrement is at least `1 / (2 M_f)`, and otherwise chooses
the intermediate method from Definition 5.2.1(C), viewed as the canonical Newton variant. -/
def selfConcordantTwoStageStrategy
    (Mf : NNRealˣ) (decrement : ℝ) : SelfConcordantNewtonVariant :=
  if 1 / (2 * (Mf : ℝ)) ≤ decrement then
    .damped
  else
    .intermediate

-- Proof sketch: unfold `selfConcordantTwoStageStrategy`; the result is definitionally the
-- displayed `if` expression selecting between the two canonical variants.
/-- Expanding `selfConcordantTwoStageStrategy Mf decrement` gives the textbook two-stage
branching rule. -/
@[simp] theorem selfConcordantTwoStageStrategy_def
    (Mf : NNRealˣ) (decrement : ℝ) :
    selfConcordantTwoStageStrategy Mf decrement =
      if 1 / (2 * (Mf : ℝ)) ≤ decrement then
        .damped
      else
        .intermediate := rfl

-- Proof sketch: split on the threshold inequality defining
-- `selfConcordantTwoStageStrategy`; in the two branches the strategy is definitionally
-- `.damped` or `.intermediate`.
/-- The two-stage strategy always returns one of the two textbook stages: the damped or the
intermediate Newton variant. -/
theorem selfConcordantTwoStageStrategy_spec
    (Mf : NNRealˣ) (decrement : ℝ) :
    selfConcordantTwoStageStrategy Mf decrement = .damped ∨
      selfConcordantTwoStageStrategy Mf decrement = .intermediate := by
  unfold selfConcordantTwoStageStrategy
  split_ifs <;> simp

-- Proof sketch: unfold `selfConcordantTwoStageStrategy`; the `if` branch is exactly the
-- first-stage condition `1 / (2 M_f) ≤ λ`.
/-- The two-stage strategy selects the damped Newton method exactly on the first-stage branch
`1 / (2 M_f) ≤ λ`. -/
@[simp] theorem selfConcordantTwoStageStrategy_eq_damped_iff
    (Mf : NNRealˣ) (decrement : ℝ) :
    selfConcordantTwoStageStrategy Mf decrement = .damped ↔
      1 / (2 * (Mf : ℝ)) ≤ decrement := by
  unfold selfConcordantTwoStageStrategy
  split_ifs with h
  · constructor
    · intro _
      exact h
    · intro _
      rfl
  · constructor
    · intro hs
      cases hs
    · intro hs
      exact (h hs).elim

-- Proof sketch: unfold `selfConcordantTwoStageStrategy`; the negated `if` branch is
-- equivalent to the second-stage inequality `λ < 1 / (2 M_f)`.
/-- The two-stage strategy selects the intermediate method exactly on the second-stage
branch `λ < 1 / (2 M_f)`. -/
@[simp] theorem selfConcordantTwoStageStrategy_eq_intermediate_iff
    (Mf : NNRealˣ) (decrement : ℝ) :
    selfConcordantTwoStageStrategy Mf decrement = .intermediate ↔
      decrement < 1 / (2 * (Mf : ℝ)) := by
  unfold selfConcordantTwoStageStrategy
  split_ifs with h
  · constructor
    · intro hs
      cases hs
    · intro hs
      exact (not_lt.mpr h hs).elim
  · constructor
    · intro _
      exact lt_of_not_ge h
    · intro _
      rfl

-- Proof sketch: unfold `selfConcordantTwoStageStrategy`; both branches are either `.damped`
-- or `.intermediate`, so the output cannot be `.standard`.
/-- The two-stage strategy never selects the standard Newton variant. -/
@[simp] theorem selfConcordantTwoStageStrategy_ne_standard
    (Mf : NNRealˣ) (decrement : ℝ) :
    selfConcordantTwoStageStrategy Mf decrement ≠ .standard := by
  unfold selfConcordantTwoStageStrategy
  split_ifs <;> decide

end

/-! ### Lemma_5_2_2 (from Chap05) -/
open InnerProductSpace
open scoped Gradient NewtonDecrement AuxiliaryCentralPathNewtonDecrement

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A linear tilt preserves the positive-definite-Hessian owner on `dom`. -/
instance auxiliaryCentralPathObjective_hasPositiveDefiniteHessianOn
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) :
    HasPositiveDefiniteHessianOn dom (auxiliaryCentralPathObjective f y0 t) where
  isPositive {x} hx := by
    simpa [auxiliaryCentralPathObjective_hessian_eq] using
      (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem hx : (hessian f x).IsPositive)
  posdef {x} hx {u} hu := by
    simpa [auxiliaryCentralPathObjective_hessian_eq] using
      (HasPositiveDefiniteHessianOn.posdef hx hu : 0 < inner ℝ u (hessian f x u))

/-- The Hessian of the tilted objective `ψ(t; ·)` is nondegenerate at every domain point once the
ambient objective carries the chapter's positive-definite-Hessian owner. -/
theorem auxiliaryCentralPathObjective_hessian_det_ne_zero
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) {y : E} (hy : y ∈ dom) :
    (hessian (auxiliaryCentralPathObjective f y0 t) y).det ≠ 0 := by
  have hdet : (hessian f y).det ≠ 0 := HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hy
  simpa [auxiliaryCentralPathObjective_hessian_eq] using hdet

/-- The approximate centering condition for the tilted objective `ψ(t; ·)` at `y`, expressed as
the bound `λ_{ψ(t; ·)}(y) ≤ β / M_f` on the canonical domain-membership Newton-decrement surface
for the tilted objective, with the positive self-concordance parameter carried on the canonical
`NNRealˣ` surface. -/
def satisfies_approximate_centering_condition
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) (y : E) (hy : y ∈ dom) (Mf : NNRealˣ)
    (β : ℝ) : Prop :=
  λ[auxiliaryCentralPathObjective f y0 t; y | hy] ≤ β / (Mf : ℝ)

-- Proof sketch: unfold `satisfies_approximate_centering_condition`.
/-- Expanding `satisfies_approximate_centering_condition` recovers the inequality
`λ_{ψ(t; ·)}(y) ≤ β / M_f`. -/
theorem satisfies_approximate_centering_condition_iff
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : ℝ) (y : E) (hy : y ∈ dom) (Mf : NNRealˣ) (β : ℝ) :
    satisfies_approximate_centering_condition f y0 t y hy Mf β ↔
      λ[auxiliaryCentralPathObjective f y0 t; y | hy] ≤ β / (Mf : ℝ) := Iff.rfl

variable {dom : Set E} {f : E → ℝ} {Mf : NNRealˣ}

/-- A linear tilt preserves the Chapter 5 self-concordance owner, so the updated path parameter
`t₊` determines a canonical intermediate Newton step for `ψ(t₊; ·)` on the same domain. -/
theorem auxiliaryCentralPathObjective_isSelfConcordantOnWith
    (f : E → ℝ) (Mf : NNReal) [IsSelfConcordantOnWith dom Mf f]
    (y0 : dom) (t : ℝ) :
    IsSelfConcordantOnWith dom Mf (auxiliaryCentralPathObjective f y0 t) := by
  let hf : IsSelfConcordantOnWith dom Mf f := inferInstance
  simpa [auxiliaryCentralPathObjective, quadraticAffineObjective, sub_eq_add_neg,
    inner_smul_left, add_assoc, add_left_comm, add_comm] using
    hf.add_quadraticAffineObjective 0 (-(t : ℝ) • ∇ f (y0 : E))
      (0 : E →L[ℝ] E) ContinuousLinearMap.isPositive_zero

private instance pathFollowingUpdate_auxiliaryCentralPathObjective_isSelfConcordantOnWith
    (y0 : dom) (t : ℝ) [IsSelfConcordantOnWith dom (Mf : NNReal) f] :
    IsSelfConcordantOnWith dom (Mf : NNReal) (auxiliaryCentralPathObjective f y0 t) :=
  auxiliaryCentralPathObjective_isSelfConcordantOnWith f (Mf : NNReal) y0 t

private abbrev pathFollowingObjectiveNorm
    {dom : Set E} (f : E → ℝ) [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (y : E) (hy : y ∈ dom) : ℝ :=
  HessianDualLocalNorm.ofPosDefMem f hy
    ((toDual ℝ E) (∇ f (y0 : E)))

/-- The path-following map sending `(t, y)` to the intermediate Newton update `(t₊, y₊)` for the
tilted objective based at `y₀` and path increment parameter `γ`, defined on the canonical
positive-definite-Hessian owner over `dom`. The scalar update is the ordinary expression
`t₊ = t - γ / (M_f ‖∇ f(y₀)‖*_y)`, so the denominator positivity is kept explicit as part of the
input data. The vector update is the canonical intermediate Newton next point for the tilted
objective at the updated parameter `t₊`. -/
def pathFollowingUpdate
    {dom : Set E} (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) (y : E) (hy : y ∈ dom)
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (gamma : ℝ) : ℝ × E :=
  let hMf : 0 < (Mf : ℝ) := by
    have hMfNNReal : 0 < (Mf : NNReal) := by
      exact pos_iff_ne_zero.mpr (Units.ne_zero Mf)
    exact_mod_cast hMfNNReal
  let denominator : Set.Ioi (0 : ℝ) :=
    ⟨(Mf : ℝ) * pathFollowingObjectiveNorm f y0 y hy, mul_pos hMf hObjectiveNorm⟩
  let tPlus :=
    (t : ℝ) - gamma / (denominator : ℝ)
  (tPlus,
    selfConcordantNewtonNextPoint
      (auxiliaryCentralPathObjective f y0 tPlus)
      (Mf : NNReal) .intermediate y hy
      (auxiliaryCentralPathObjective_hessian_det_ne_zero f y0 tPlus hy))

namespace PathFollowingUpdate

/-- Source-facing notation for the path-following map `𝒫_γ`, with the ambient objective data
kept explicit because they are not inferable from `(t, y)` alone. -/
scoped notation:max
  "𝒫[" f "; " Mf "; " y0 " | " hy "; " hObjectiveNorm "; " gamma "](" t ", " y ")" =>
  pathFollowingUpdate f Mf y0 t y hy hObjectiveNorm gamma

end PathFollowingUpdate

open scoped PathFollowingUpdate

-- Proof sketch: unfold `pathFollowingUpdate`.
/-- The first coordinate of `pathFollowingUpdate` is the scalar update
`t₊ = t - γ / (M_f ‖∇ f(y₀)‖*_y)`. -/
theorem pathFollowingUpdate_fst
    (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) (y : E) (hy : y ∈ dom)
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (gamma : ℝ) :
    (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1 =
      (t : ℝ) - gamma / ((Mf : ℝ) *
        HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E)))) := by
  simp [pathFollowingUpdate, pathFollowingObjectiveNorm]

/-- The second coordinate of `pathFollowingUpdate` is the canonical intermediate Newton next
point for the tilted objective at the updated parameter `t₊`. -/
theorem pathFollowingUpdate_snd
    (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) (y : E) (hy : y ∈ dom)
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (gamma : ℝ) :
    (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).2 =
      selfConcordantNewtonNextPoint
        (auxiliaryCentralPathObjective f y0
          (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1)
        (Mf : NNReal) .intermediate y hy
        (auxiliaryCentralPathObjective_hessian_det_ne_zero f y0
          (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1 hy) := by
  simp only [pathFollowingUpdate, pathFollowingObjectiveNorm]

/-- The centering threshold `β = τ² (1 + τ + τ / (1 + τ + τ²))` used in the path-following
small-step estimate. -/
def pathFollowingCenteringBeta (τ : ℝ) : ℝ :=
  τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ)))

-- Proof sketch: unfold `pathFollowingCenteringBeta`.
/-- Expanding `pathFollowingCenteringBeta τ` recovers the textbook formula
`τ² (1 + τ + τ / (1 + τ + τ²))`. -/
theorem pathFollowingCenteringBeta_def (τ : ℝ) :
    pathFollowingCenteringBeta τ =
      τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) := rfl

/-- The admissible path-parameter increment bound
`τ - τ² (1 + τ + τ / (1 + τ + τ²))` from `(5.2.15)`. -/
def pathFollowingGammaRadius (τ : ℝ) : ℝ :=
  τ - pathFollowingCenteringBeta τ

-- Proof sketch: unfold `pathFollowingGammaRadius` and then rewrite with
-- `pathFollowingCenteringBeta_def`.
/-- Expanding `pathFollowingGammaRadius τ` gives the bound from `(5.2.15)`. -/
theorem pathFollowingGammaRadius_def (τ : ℝ) :
    pathFollowingGammaRadius τ =
      τ - τ ^ (2 : ℕ) * (1 + τ + τ / (1 + τ + τ ^ (2 : ℕ))) := by
  simp [pathFollowingGammaRadius, pathFollowingCenteringBeta]

/-- Under the hypotheses of Lemma 5.2.2, the updated point produced by `pathFollowingUpdate`
belongs to `dom`; this is derived from the canonical intermediate Newton step for
`ψ(t₊; ·)`, not taken as primitive path-following data. -/
theorem pathFollowingUpdate_snd_mem
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) {y : E} (hy : y ∈ dom) {τ gamma : ℝ}
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (htau : τ ≤ 1 / 2)
    (hcenter : satisfies_approximate_centering_condition f y0 t y hy Mf
      (pathFollowingCenteringBeta τ))
    (hgamma : |gamma| ≤ pathFollowingGammaRadius τ) :
    (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).2 ∈ dom := by
  sorry

-- Proof sketch: let `λ = ‖∇f(y) - t ∇f(y₀)‖*_y`, `λ₁ = ‖∇f(y) - t₊ ∇f(y₀)‖*_y`, and
-- `λ₊ = ‖∇f(y₊) - t₊ ∇f(y₀)‖*_{y₊}`. The assumption `hcenter` gives
-- `λ ≤ pathFollowingCenteringBeta τ / M_f`, while the path-parameter update and the bound on
-- `|γ|` imply `λ₁ ≤ τ / M_f`. Applying the intermediate-step decrement estimate `(5.2.8)` to the
-- tilted objective then yields
-- `λ₊ ≤ pathFollowingCenteringBeta τ / M_f`, which is exactly the same approximate-centering
-- condition at `(t₊, y₊)`.
/-- Lemma 5.2.2: if `(t, y)` satisfies the approximate centering condition `(5.2.13)` with
`β = τ² (1 + τ + τ / (1 + τ + τ²))` and `τ ≤ 1 / 2`, then the path-following update
`𝒫_γ(t, y)` also satisfies the same centering condition whenever its computed first coordinate
lies in `[0, 1]` and `|γ| ≤ τ - τ² (1 + τ + τ / (1 + τ + τ²))`. The updated point is read
through the canonical intermediate Newton owner for the tilted objective `ψ(t₊; ·)`, so its
domain membership is derived rather than assumed separately. -/
theorem pathFollowingUpdate_preserves_approximate_centering_condition
    [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (t : Set.Icc (0 : ℝ) 1) {y : E} (hy : y ∈ dom) {τ gamma : ℝ}
    (hObjectiveNorm :
      0 < HessianDualLocalNorm.ofPosDefMem f hy ((toDual ℝ E) (∇ f (y0 : E))))
    (htau : τ ≤ 1 / 2)
    (hcenter : satisfies_approximate_centering_condition f y0 t y hy Mf
      (pathFollowingCenteringBeta τ))
    (hgamma : |gamma| ≤ pathFollowingGammaRadius τ) :
    satisfies_approximate_centering_condition f y0
      (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).1
      (𝒫[f; Mf; y0 | hy; hObjectiveNorm; gamma](t, y)).2
      (pathFollowingUpdate_snd_mem y0 t hy hObjectiveNorm htau hcenter hgamma) Mf
      (pathFollowingCenteringBeta τ) := by
  sorry

end

/-! ### Proposition_5_2_2 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open scoped NewtonDecrement
open scoped SelfConcordantAuxiliaryFunction

/- Proposition 5.2.2 lies in the Chapter 5 self-concordant two-stage-strategy domain.

Sampled owner declarations:
* `DampedNewton.Method.IsSelfConcordant` in `Definition_5_2_1`, the Chapter 5 refinement of the
  recursive damped Newton owner;
* `NewtonDecrement.ofDetNeZero` and the source-facing notation
  `ndec(f, x, Mf, hx, hH)` in `Definition_5_0_24`, the canonical Newton-decrement owner at a
  domain point with nondegenerate Hessian;
* `selfConcordantTwoStageStrategy` and `selfConcordantTwoStageStrategy_eq_damped_iff` in
  `Definition_5_2_2`, the source-facing two-stage owner and its threshold bridge;
* `IsMinOn` in mathlib, the canonical minimizer owner reused throughout Chapter 5.

Best owner abstraction:
* source-facing: the assertion that the first `N` iterates of the damped Newton method remain in
  Stage 1 of the two-stage strategy;
* core/canonical: `DampedNewton.Method.IsSelfConcordant`, `ndec(f, x, Mf, hx, hH)`,
  `selfConcordantTwoStageStrategy`, and `IsMinOn f dom xStar`;
* bridge/view: the threshold inequality
  `1 / (2 M_f) ≤ NewtonDecrement.ofDetNeZero ...`.

Primitive data:
* the damped self-concordant Newton method;
* the objective `f` and domain `dom`;
* the positive self-concordance parameter `Mf`;
* the canonical Newton decrement at each iterate, read through the chapter notation
  `ndec(f, method k, Mf, hmethod.iterates_mem k, method.hessian_nondegenerate k)`;
* the Stage-1 membership condition for the first `N` iterates;
* the canonical minimizer owner `IsMinOn f dom xStar`.

Derived API:
* the pointwise threshold characterization of Stage 1 from
  `selfConcordantTwoStageStrategy_eq_damped_iff`;
* the lower bound `f xStar ≤ f (method k)` obtained by applying `IsMinOn` to any iterate in `dom`;
* the Stage-1 damped-step decrease estimate obtained at each iterate from the canonical one-step
  damped Newton owner.

This file stays source-facing at the level of the Stage-1 segment length, but removes the parallel
free decrement sequence and instead reads Stage 1 directly from the canonical Newton decrement
along the damped self-concordant Newton method. -/

namespace DampedNewton.Method.IsSelfConcordant

section

variable {dom : Set E} {f : E → ℝ} {Mf : NNRealˣ}
variable [IsSelfConcordantOnWith dom (Mf : NNReal) f]
variable {x0 : E}

-- Proof sketch: record Stage 1 directly through the canonical Newton decrement of the damped
-- method and then use `selfConcordantTwoStageStrategy_eq_damped_iff`.
/-- `method.IsStageOneUpTo N` means that the first `N` iterates of the damped self-concordant
Newton method remain in Stage 1 of the two-stage strategy from Definition 5.2.2. -/
def IsStageOneUpTo
    {method : DampedNewton.Method f x0}
    (hmethod : method.IsSelfConcordant dom (Mf : NNReal) SelfConcordantNewtonVariant.damped)
    (N : ℕ) : Prop :=
  ∀ k : ℕ, k < N →
    selfConcordantTwoStageStrategy Mf
        (ndec(
          f, (method k), (Mf : NNReal), (hmethod.iterates_mem k),
          (method.hessian_nondegenerate k))) =
      .damped

-- Proof sketch: unfold `DampedNewton.Method.IsSelfConcordant.IsStageOneUpTo` and apply
-- `selfConcordantTwoStageStrategy_eq_damped_iff` at each iterate.
/-- Expanding `method.IsStageOneUpTo N` says that every index `k < N` satisfies the Stage 1
threshold inequality `1 / (2 M_f) ≤ λ_f(x_k)` for the canonical Newton decrement of `method`. -/
theorem isStageOneUpTo_iff
    {method : DampedNewton.Method f x0}
    (hmethod : method.IsSelfConcordant dom (Mf : NNReal) SelfConcordantNewtonVariant.damped)
    {N : ℕ} :
    hmethod.IsStageOneUpTo N ↔
      ∀ k : ℕ, k < N →
        1 / (2 * (Mf : ℝ)) ≤
          ndec(
            f, (method k), (Mf : NNReal), (hmethod.iterates_mem k),
            (method.hessian_nondegenerate k)) := by
  constructor
  · intro h k hk
    exact
      (selfConcordantTwoStageStrategy_eq_damped_iff Mf
        (ndec(
          f, (method k), (Mf : NNReal), (hmethod.iterates_mem k),
          (method.hessian_nondegenerate k)))).1
        (h k hk)
  · intro h k hk
    exact
      (selfConcordantTwoStageStrategy_eq_damped_iff Mf
        (ndec(
          f, (method k), (Mf : NNReal), (hmethod.iterates_mem k),
          (method.hessian_nondegenerate k)))).2
        (h k hk)

end

end DampedNewton.Method.IsSelfConcordant

-- Proof sketch: use the Stage 1 hypothesis to justify the uniform decrease estimate
-- `f(x_{k + 1}) ≤ f(x_k) - M_f⁻² ω(M_f λ_f(x_k))` for every `k < N`. The Stage 1 hypothesis gives
-- `1 / 2 ≤ M_f λ_f(x_k)`, so monotonicity of `ω` yields the uniform lower bound
-- `M_f⁻² ω(1 / 2)`. Summing these `N` inequalities gives
-- `f(x_N) ≤ f(x_0) - N * M_f⁻² ω(1 / 2)`. Since `xStar` minimizes `f` on `dom` and the method
-- stays in `dom`, we have `f xStar ≤ f(x_N)`, and rearranging yields the stated estimate.
/-- Proposition 5.2.2: if the first `N` iterates of the damped segment of the two-stage
self-concordant Newton method remain in Stage 1, then
`N ≤ M_f^2 (f(x_0) - f(x_f^*)) / ω(1 / 2)`, where `x_f^*` minimizes `f` on the domain. -/
theorem selfConcordantTwoStage_stageOneLength_le
    {dom : Set E} {f : E → ℝ} {Mf : NNRealˣ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    {x0 : E}
    (method : DampedNewton.Method f x0)
    (hmethod : method.IsSelfConcordant dom (Mf : NNReal) SelfConcordantNewtonVariant.damped)
    {xStar : E} {N : ℕ}
    (hmin : IsMinOn f dom xStar)
    (hstage : hmethod.IsStageOneUpTo N) :
    (N : ℝ) ≤
      (Mf : ℝ) ^ (2 : ℕ) * (f x0 - f xStar) /
        selfConcordantOmegaAtOneHalf := sorry

end

/-! ### Theorem_5_2_2 (from Chap05) -/
open scoped Gradient NewtonDecrement

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.2.2 lies in the Chapter 5 self-concordant Newton local-convergence domain.

Sampled owner declarations:
* `selfConcordantNewtonNextPoint`, `DampedNewton.Method.IsSelfConcordant`, and
  `selfConcordantNewtonShift` in `Definition_5_2_1`, the source-facing one-step / recursive
  Newton owners and their variant-dependent scalar shift;
* `selfConcordantTwoStageStrategy` in `Definition_5_2_2`, which already places the damped /
  intermediate branch choice on the positive owner surface `Mf : NNRealˣ`;
* `newtonDecrement`, the notation `ndec(f, x, Mf, hx, hH)`, and `NewtonDecrement.ofDetNeZero` in
  `Definition_5_0_24`, the Chapter 5 Newton-decrement owner and its self-concordant-domain
  theorem surface;
* `selfConcordant_dampedNewtonStep_value_decrease` in `Theorem_5_1_15`, the nearby one-step
  value-decrease theorem phrased directly in terms of the Chapter 5 one-step owner.

Best owner abstraction:
* source-facing: the one-step self-concordant Newton update and its decrement bounds;
* core/canonical: `selfConcordantNewtonShift`, `selfConcordantNewtonNextPoint`, and
  `NewtonDecrement.ofDetNeZero`, with the positive `NNRealˣ` owner surface for the damped and
  intermediate variants;
* bridge/view: the later recursive method step obtained by specializing
  `DampedNewton.Method.IsSelfConcordant.succ_eq_nextPoint`.

Primitive data:
* a self-concordant function `f` on `dom` with parameter `Mf`;
* a point `x ∈ dom`;
* Hessian nondegeneracy at `x`;
* a Newton variant, with `Mf : NNRealˣ` on the positive damped / intermediate branch.

Derived API:
* the canonical next point `selfConcordantNewtonNextPoint f Mf variant x hx hH`;
* the source-facing self-concordant-domain decrement notation `ndec(f, x, Mf, hx, hH)`;
* the direct one-step decrement bounds for the three textbook variants.

This file reuses the Chapter 5 one-step update owner from `Definition_5_2_1` and the Chapter 5
decrement owner directly. The theorem surface stays on the local one-step layer `x ∈ dom` plus
Hessian nondegeneracy, uses the source-facing decrement notation `ndec(f, x, Mf, hx, hH)`, and
derives each next-point membership witness from the corresponding membership clause instead of
carrying it as primitive decrement-bound data. The standard variant remains valid for arbitrary
`Mf : NNReal`, while the damped and intermediate variants are refined to the canonical positive
owner surface `Mf : NNRealˣ` already used by the Chapter 5 two-stage strategy. -/

section StandardVariant

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom Mf f]

-- Proof sketch: set `λ = λ_f(x)` and `x₊ = selfConcordantNewtonNextPoint f Mf .standard x hx hH`.
-- The standard step has `ξ = 0`, so the local step norm is `‖x₊ - x‖_x = λ`. The assumption
-- `λ < 1 / M_f` lets Theorem 5.1.5 place `x₊` back in `dom`, and the matrix argument from the
-- proof of Theorem 5.2.2 bounds the new decrement by
-- `M_f λ^2 / (1 - M_f λ)^2`.
/-- Theorem 5.2.2 (1): if the Newton decrement at `x` is smaller than `1 / M_f`, then the
variant `A` self-concordant Newton step stays in `dom`. -/
theorem selfConcordantNewtonNextPoint_standard_mem
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hlambda :
      let δ := ndec(f, x, Mf, hx, hH)
      δ < 1 / (Mf : ℝ))
    :
    let xPlus := selfConcordantNewtonNextPoint f Mf .standard x hx hH
    xPlus ∈ dom := sorry

/-- Theorem 5.2.2 (2): at the canonical variant `A` self-concordant Newton next point, the new
Newton decrement is at most `M_f λ_f(x)^2 / (1 - M_f λ_f(x))^2`. -/
theorem selfConcordantNewtonDecrement_standard_step_bound
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hlambda :
      let δ := ndec(f, x, Mf, hx, hH)
      δ < 1 / (Mf : ℝ))
    (hHPlus :
      let xPlus := selfConcordantNewtonNextPoint f Mf .standard x hx hH
      (hessian f xPlus).det ≠ 0)
    :
    let δ := ndec(f, x, Mf, hx, hH)
    let xPlus := selfConcordantNewtonNextPoint f Mf .standard x hx hH
    let hxPlus := selfConcordantNewtonNextPoint_standard_mem hx hH hlambda
    ndec(f, xPlus, Mf, hxPlus, hHPlus) ≤
      ((Mf : ℝ) * δ ^ (2 : ℕ)) / (1 - (Mf : ℝ) * δ) ^ (2 : ℕ) := sorry

end StandardVariant

section PositiveVariants

variable {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom (Mf : NNReal) f]

-- Proof sketch: set `λ = λ_f(x)` and `x₊ = selfConcordantNewtonNextPoint f Mf .damped x hx hH`.
-- For variant `B`, the shift is `ξ = M_f λ`, so the local step norm is
-- `λ / (1 + M_f λ) < 1 / M_f`. Theorem 5.1.5 again yields `x₊ ∈ dom`, and the comparison
-- argument in Theorem 5.2.2 gives the displayed quadratic bound for `λ_f(x₊)`.
/-- Theorem 5.2.2 (3): for positive self-concordance parameter `M_f`, the variant `B`
self-concordant Newton step stays in `dom`. -/
theorem selfConcordantNewtonNextPoint_damped_mem
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    :
    let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .damped x hx hH
    xPlus ∈ dom := sorry

/-- Theorem 5.2.2 (4): at the canonical variant `B` self-concordant Newton next point, the new
Newton decrement is bounded by
`M_f λ_f(x)^2 (1 + (1 + M_f λ_f(x))⁻¹)` when `M_f > 0`. -/
theorem selfConcordantNewtonDecrement_damped_step_bound
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hHPlus :
      let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .damped x hx hH
      (hessian f xPlus).det ≠ 0)
    :
    let δ := ndec(f, x, (Mf : NNReal), hx, hH)
    let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .damped x hx hH
    let hxPlus := selfConcordantNewtonNextPoint_damped_mem hx hH
    ndec(f, xPlus, (Mf : NNReal), hxPlus, hHPlus) ≤
      ((Mf : ℝ) * δ ^ (2 : ℕ)) * (1 + 1 / (1 + (Mf : ℝ) * δ)) := sorry

-- Proof sketch: set `λ = λ_f(x)` and let `x₊` be the variant `C` step. The hypothesis
-- `M_f λ + M_f^2 λ^2 + M_f^3 λ^3 ≤ 1` implies the corresponding step norm is smaller than
-- `1 / M_f`, so Theorem 5.1.5 yields `x₊ ∈ dom`. The matrix comparison from the proof of
-- Theorem 5.2.2 then gives the explicit bound
-- `M_f λ^2 (1 + M_f λ + (M_f λ) / (1 + M_f λ + M_f^2 λ^2))`.
/-- Theorem 5.2.2 (5): under the cubic smallness condition
`M_f λ_f(x) + M_f^2 λ_f(x)^2 + M_f^3 λ_f(x)^3 ≤ 1`, the variant `C` self-concordant Newton step
stays in `dom` for positive self-concordance parameter `M_f`. -/
theorem selfConcordantNewtonNextPoint_intermediate_mem
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hsmall :
      let δ := ndec(f, x, (Mf : NNReal), hx, hH)
      (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) +
        (Mf : ℝ) ^ (3 : ℕ) * δ ^ (3 : ℕ) ≤
      1)
    :
    let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .intermediate x hx hH
    xPlus ∈ dom := sorry

/-- Theorem 5.2.2 (6): under the cubic smallness condition, the Newton decrement at the canonical
variant `C` next point is bounded by the explicit rational expression in `λ_f(x)` from `(5.2.8)`
when `M_f > 0`. -/
theorem selfConcordantNewtonDecrement_intermediate_step_explicit_bound
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hsmall :
      let δ := ndec(f, x, (Mf : NNReal), hx, hH)
      (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) +
        (Mf : ℝ) ^ (3 : ℕ) * δ ^ (3 : ℕ) ≤
      1)
    (hHPlus :
      let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .intermediate x hx hH
      (hessian f xPlus).det ≠ 0)
    :
    let δ := ndec(f, x, (Mf : NNReal), hx, hH)
    let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .intermediate x hx hH
    let hxPlus := selfConcordantNewtonNextPoint_intermediate_mem hx hH hsmall
    ndec(f, xPlus, (Mf : NNReal), hxPlus, hHPlus) ≤
      ((Mf : ℝ) * δ ^ (2 : ℕ)) *
        (1 + (Mf : ℝ) * δ +
          ((Mf : ℝ) * δ) / (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ))) := sorry

-- Proof sketch: combine the explicit variant `C` estimate from the previous clause with the
-- elementary scalar inequality
-- `(M_f λ) / (1 + M_f λ + M_f^2 λ^2) ≤ M_f λ`, which turns the bracketed term into
-- `1 + 2 M_f λ`.
/-- Theorem 5.2.2 (7): under the same cubic smallness condition as in the variant `C` case, the
new Newton decrement at the canonical variant `C` next point also satisfies the simpler bound
`M_f λ_f(x)^2 (1 + 2 M_f λ_f(x))` when `M_f > 0`. -/
theorem selfConcordantNewtonDecrement_intermediate_step_simplified_bound
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hsmall :
      let δ := ndec(f, x, (Mf : NNReal), hx, hH)
      (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) +
        (Mf : ℝ) ^ (3 : ℕ) * δ ^ (3 : ℕ) ≤
      1)
    (hHPlus :
      let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .intermediate x hx hH
      (hessian f xPlus).det ≠ 0)
    :
    let δ := ndec(f, x, (Mf : NNReal), hx, hH)
    let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) .intermediate x hx hH
    let hxPlus := selfConcordantNewtonNextPoint_intermediate_mem hx hH hsmall
    ndec(f, xPlus, (Mf : NNReal), hxPlus, hHPlus) ≤
      ((Mf : ℝ) * δ ^ (2 : ℕ)) * (1 + 2 * (Mf : ℝ) * δ) := sorry

end PositiveVariants

end

/-! ### Definition_5_2_3 (from Chap05) -/
open scoped Gradient
open scoped ConstrainedArgmin

noncomputable section

universe u

/- Definition 5.2.3 lies in the chapter's constrained-minimization / auxiliary-central-path
domain.

Sampled owner declarations:
* `IsMinOn` in mathlib, the canonical minimizer predicate on a feasible set;
* `constrainedArgmin` and the scoped notation `argmin[Q]` in `Chap01/Definition_1_3_3`, the
  project owner for minimizer sets on a fixed feasible set;
* `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the bridge decomposing canonical
  argmin membership into feasibility and minimality;
* the later Chapter 5 owner `IsCentralPath` in `Definition_5_3_6_1`, whose pointwise minimizer
  interface confirms that central-path data should be expressed through minimizers rather than a
  separate chosen-witness wrapper.

Best owner abstraction:
* source-facing: the auxiliary tilted objective and the corresponding path of its minimizers on
  `t ∈ [0, 1]`;
* core/canonical: the dependent family `∀ t, {y : E // y ∈ argmin[dom] ...}`;
* bridge/view: `mem_constrainedArgmin_iff`, which yields the textbook facts that each path point
  lies in `dom` and minimizes the tilted objective there.

Primitive data:
* the domain `dom : Set E`;
* the objective `f : E → ℝ`;
* the base point `y0 : dom`.

Derived API:
* the tilted objective `auxiliaryCentralPathObjective f y0 t`;
* the canonical argmin subtype at each parameter `t`;
* the feasibility and `IsMinOn` facts for any auxiliary central path.

Source/core/bridge triage:
* source-facing: the auxiliary central path from Definition 5.2.3;
* core/canonical: `argmin[dom] (auxiliaryCentralPathObjective f y0 t)`;
* bridge/view: coercion from the argmin subtype to `E` together with
  `mem_constrainedArgmin_iff`.

This refinement removes the public `Classical.choose` trajectory. The source-facing path is kept
as a function into the canonical argmin subtype, so the pointwise minimizer and domain facts are
derived rather than stored as primitive chosen-witness data. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The tilted objective `ψ(t; y) = f(y) - t ⟪∇ f(y₀), y⟫` whose minimizers define the
auxiliary central path. -/
def auxiliaryCentralPathObjective
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) : E → ℝ :=
  fun y ↦ f y - (t : ℝ) * inner ℝ (∇ f (y0 : E)) y

/-- Evaluating `auxiliaryCentralPathObjective f y₀ t` recovers the textbook formula
`f(y) - t ⟪∇ f(y₀), y⟫`. -/
@[simp] theorem auxiliaryCentralPathObjective_apply
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E) :
    auxiliaryCentralPathObjective f y0 t y =
      f y - (t : ℝ) * inner ℝ (∇ f (y0 : E)) y :=
  rfl

section

variable {dom : Set E} (f : E → ℝ) (y0 : dom)

/- Definition 5.2.3: the auxiliary central path of `f` based at `y₀ ∈ dom` is a trajectory on
`t ∈ [0, 1]` whose value at each parameter is a point of the canonical minimizer set of the
tilted objective `y ↦ f(y) - t ⟪∇ f(y₀), y⟫` on `dom`. -/
set_option linter.hashCommand false in
#check
  (∀ t : Set.Icc (0 : ℝ) 1,
    {y : E // y ∈ argmin[dom] (auxiliaryCentralPathObjective f y0 t)})

end

section

variable {dom : Set E} {f : E → ℝ} {y0 : dom}
variable
  (yStar :
    ∀ t : Set.Icc (0 : ℝ) 1,
      {y : E // y ∈ argmin[dom] (auxiliaryCentralPathObjective f y0 t)})

/-- Evaluating an auxiliary central path at time `t` yields a point of `dom` that minimizes the
tilted objective over `dom`. -/
theorem auxiliaryCentralPath_spec (t : Set.Icc (0 : ℝ) 1) :
    (yStar t : E) ∈ dom ∧
      IsMinOn (auxiliaryCentralPathObjective f y0 t) dom (yStar t : E) :=
  mem_constrainedArgmin_iff.mp (yStar t).2

/-- The value of an auxiliary central path at time `t` minimizes the tilted objective over
`dom`. -/
theorem auxiliaryCentralPath_isMinOn (t : Set.Icc (0 : ℝ) 1) :
    IsMinOn (auxiliaryCentralPathObjective f y0 t) dom (yStar t : E) :=
  (auxiliaryCentralPath_spec yStar t).2

/-- Every point on an auxiliary central path belongs to the domain on which the tilted problem is
posed. -/
theorem auxiliaryCentralPath_mem_domain (t : Set.Icc (0 : ℝ) 1) :
    (yStar t : E) ∈ dom :=
  (auxiliaryCentralPath_spec yStar t).1

end

/-! ### Proposition_5_2_3 (from Chap05) -/
noncomputable section

universe u

/- Proposition 5.2.3 lies in the Chapter 5 strongly-convex quadratic-regime entry-time domain on
real normed spaces.

Primary mathematical domain:
* strongly convex objectives together with the canonical strong-convexity specialization of the
  Chapter 4 global rate estimate, and the resulting Chapter 5 quadratic region
  `𝒬[f | f(x*), M_f]`

Sampled owner-style declarations:
* `selfConcordantQuadraticRegion` and the notation `𝒬[f | f*, M_f]` in `Definition_5_2_9`, the
  Chapter 5 source-facing quadratic-region owner;
* `strongConvexSelfConcordanceConstant` in `Definition_5_2_8`, the chapter owner for the
  canonical strong-convexity-induced self-concordance constant
  `M_f = L₃ / (2 σ₂^(3 / 2))`;
* `mem_selfConcordantQuadraticRegion_iff_mem_cubicNewtonQuadraticDecreaseRegion` in
  `Definition_5_2_9`, the canonical bridge to the older Chapter 4 comparison region;
* `cubicNewton_gap_le_inverse_square_rate_of_bounded_sublevel` in `Chap04/Theorem_4_2_2`, the
  nearby chapter theorem whose strong-convexity specialization produces the canonical
  coefficient `2^(5/2) c M_f (f(x₀) - f(x*))^(3/2) / k^p`;
* `StrongConvexOn.quadratic_growth_of_isMinOn` in `Chap02/Theorem_2_30`, the canonical
  quadratic-growth owner behind that specialization;
* `stronglyConvexHalfGapIndex` in `Definition_5_2_10`, the downstream owner showing that the
  natural strong-convexity scaling parameter is `Δ = M_f * √gap`, not a local wrapper.

Best owner abstraction:
* source-facing: the first index where the iterate enters the Chapter 5 region
  `𝒬[f | f(x*), M_f]`;
* core/canonical: the Chapter 5 region owner together with the canonical strong-convexity
  specialization of the Chapter 4 inverse-square rate;
* bridge/view: the comparison between the Chapter 5 threshold `1 / (8 M_f^2)`, the Chapter 4
  multiplication-form region `cubicNewtonQuadraticDecreaseRegion`, and the scaled gap
  `Δ = M_f * √gap`.

Primitive data:
* the strong-convexity parameter sign `0 < σ₂`;
* the iterate family `x`;
* the minimizer `x*` together with the canonical owner witness `IsMinOn f Set.univ x*`;
* the global-rate constants `c`, `p`;
* the canonical strong-convexity-specialized rate bound `hrate`;
* the least-entry witness `hN`.

Derived API:
* the Chapter 5 quadratic-region owner `𝒬[f | f(x*), M_f]`;
* the strong-convexity scaling `Δ M_f gap`.

This refinement keeps Proposition 5.2.3 source-facing while removing the noncanonical free radius
parameter `D`. The theorem surface now uses the canonical strong-convexity-specialized rate
coefficient that one obtains from the Chapter 4 inverse-square estimate via
`StrongConvexOn.quadratic_growth_of_isMinOn`, so the public statement no longer pretends that an
arbitrary bounded-sublevel witness is itself controlled by strong convexity. The entry condition
stays phrased directly with the Chapter 5 owner `𝒬[f | f(x*), M_f]` rather than the older
Chapter 4 comparison region. -/

/-- The strong-convex scaled gap `Δ = M_f * √gap` used in the textbook complexity estimate for
entering the quadratic-convergence region. In source-facing applications the gap is the
suboptimality `f(x) - f(x*)`, whose nonnegativity is supplied by `IsMinOn`. -/
def stronglyConvexScaledGap (Mf gap : ℝ) : ℝ :=
  Mf * Real.sqrt gap

/- Source-facing Lean notation for the textbook strongly-convex scaled gap owner `Δ`. -/
scoped[StronglyConvexScaledGap] notation:max "Δ" => stronglyConvexScaledGap

open scoped SelfConcordantQuadraticRegion StronglyConvexScaledGap

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

section

variable {σ2 : ℝ} {L3 : NNReal}

-- Proof sketch: start from the canonical strong-convexity specialization of the Chapter 4 rate
-- bound,
-- `f(x_k) - f(x*) ≤ 2^(5/2) c M_f (f(x₀) - f(x*))^(3/2) / k^p`
-- with `M_f = L₃ / (2 * σ₂^(3 / 2))`, compare it to the defining threshold
-- `f(x) - f(x*) ≤ 1 / (8 M_f^2)` of `𝒬[f | f(x*), M_f]`, and choose the first positive integer
-- above the scalar root. Converting that natural-number rounding into a real inequality yields
-- the final `1 + ...` bound on the least entry index.
/-- Proposition 5.2.3: assume the iterate sequence `x_k` satisfies the global rate
`f(x_k) - f(x*) ≤ (2^(5/2) c M_f / k^p) * (f(x₀) - f(x*))^(3/2)`, where `x*` is a global
minimizer of `f`,
`M_f = L₃ / (2 * σ₂^(3 / 2))`, then `N` is bounded by the corresponding constant multiple of
`Δ_f(x₀)^(3 / p)`, with the natural-number rounding written as
`1 + (2^(11/2) c Δ_f(x₀)^3)^(1 / p)`. Here `N` is the least index for which `x_N` enters the
Chapter 5 quadratic region `𝒬[f | f(x*), M_f]`. Under `L₃ > 0`, the Chapter 5 threshold
`f(x_N) - f(x*) ≤ 1 / (8 M_f^2)` is equivalent to the older Chapter 4 comparison-region
condition `2 L₃² (f(x_N) - f(x*)) ≤ σ₂³`. -/
theorem stronglyConvex_firstSourceQuadraticConvergenceRegionEntryIndex_le
    {f : E → ℝ}
    (x : ℕ → E) (xStar : E) {c p : ℝ}
    (hσ2 : 0 < σ2)
    (hmin : IsMinOn f Set.univ xStar)
    (hc : 0 < c) (hp : 0 < p)
    (hrate :
      ∀ k : ℕ, 0 < k →
        f (x k) - f xStar ≤
          (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c *
            (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) *
            Real.rpow (f (x 0) - f xStar) (3 / 2 : ℝ)) /
            Real.rpow (k : ℝ) p)
    {N : ℕ}
    (hN :
      IsLeast
        {n : ℕ | x n ∈ 𝒬[f | f xStar, strongConvexSelfConcordanceConstant σ2 L3]}
        N) :
    (N : ℝ) ≤
      1 +
      Real.rpow
        (Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c *
          (Δ (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) (f (x 0) - f xStar)) ^ (3 : ℕ))
        (1 / p) := sorry

end

/-! ### Theorem_5_2_3 (from Chap05) -/
open InnerProductSpace
open scoped Gradient NewtonDecrement AuxiliaryCentralPathNewtonDecrement PathFollowingUpdate

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The coefficient
`κ(τ) = ((τ - 3β(τ)) (1 + β(τ))) / (2 (1 + β(τ) + β(τ)^2))`
appearing in the path-following decay estimate. -/
def pathFollowingKappa (τ : ℝ) : ℝ :=
  ((τ - 3 * pathFollowingCenteringBeta τ) * (1 + pathFollowingCenteringBeta τ)) /
    (2 * (1 + pathFollowingCenteringBeta τ + (pathFollowingCenteringBeta τ) ^ (2 : ℕ)))

-- Proof sketch: unfold `pathFollowingKappa`.
/-- Expanding `pathFollowingKappa τ` gives the textbook formula for `κ(τ)`. -/
theorem pathFollowingKappa_def (τ : ℝ) :
    pathFollowingKappa τ =
      ((τ - 3 * pathFollowingCenteringBeta τ) * (1 + pathFollowingCenteringBeta τ)) /
        (2 * (1 + pathFollowingCenteringBeta τ + (pathFollowingCenteringBeta τ) ^ (2 : ℕ))) := sorry

/-- A path-following process for the tilted objective based at `y₀`, started from `t₀ = 1` and
generated by repeated application of `𝒫_γ` with `γ = τ - β(τ)`. -/
structure SelfConcordantPathFollowingProcess
    {dom : Set E} (f : E → ℝ) (Mf : NNRealˣ) [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    (y0 : dom) (τ : ℝ) where
  /-- The path parameters `t_k`, constrained to lie in `[0, 1]`. -/
  t : ℕ → Set.Icc (0 : ℝ) 1
  /-- The path-following iterates `y_k`. -/
  y : ℕ → E
  /-- Every iterate belongs to the domain of the objective. -/
  mem_domain : ∀ k : ℕ, y k ∈ dom
  /-- At each iterate, the denominator `M_f ‖∇ f(y₀)‖*_{y_k}` in the scalar path update is
  strictly positive, so the textbook update formula for `t_{k+1}` is mathematically defined. -/
  objectiveNorm_pos :
    ∀ k : ℕ,
      0 <
        HessianDualLocalNorm.ofPosDefMem f (mem_domain k)
          ((toDual ℝ E) (∇ f (y0 : E)))
  /-- The initial path parameter is `t₀ = 1`. -/
  t_zero : (t 0 : ℝ) = 1
  /-- The initial iterate is the prescribed base point `y₀`. -/
  y_zero : y 0 = y0
  /-- Each successive pair `(t_{k+1}, y_{k+1})` is obtained from the path-following map
  `𝒫_γ(t_k, y_k)` with `γ = τ - β(τ)`. -/
  step_eq :
    ∀ k : ℕ,
      ((t (k + 1) : ℝ), y (k + 1)) =
        pathFollowingUpdate f Mf y0 (t k) (y k) (mem_domain k) (objectiveNorm_pos k)
          (pathFollowingGammaRadius τ)

-- Proof sketch: use `process.t_zero` and `process.y_zero` to obtain vanishing of the
-- shifted-gradient dual local norm at the initial pair `(1, y₀)`, then iterate
-- `pathFollowingUpdate_preserves_approximate_centering_condition` to propagate the uniform bound
-- `λ_k ≤ β(τ) / M_f`. For the decay of `t_N`, combine the one-step decrease estimate for
-- `f(y_k) - f(y_{k+1})` with the lower bound `1 / (2 M_f) ≤ λ_f(y_k)` for `k ≤ N`, and sum the
-- resulting reciprocal estimate using the scalar minimum `(N + 1)^2`.
/-- Theorem 5.2.3: for the path-following process `(t_k, y_k)` generated by `𝒫_γ` with
`γ = τ - β(τ)` and `τ ≤ 0.23`, the shifted Newton decrement remains bounded by `β(τ) / M_f` at
every iterate. If, in addition, the ordinary Newton decrement satisfies
`1 / (2 M_f) ≤ λ_f(y_k)` for all `k = 0, ..., N`, then the path parameter obeys the exponential
bound `t_N ≤ exp (-(γ κ(τ) N^2) / Δ_f(x₀))`, represented here by the scalar
`initialScaledGap = Δ_f(x₀)`. -/
theorem selfConcordantPathFollowing_parameter_exponential_decay
    {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ} [IsSelfConcordantOnWith dom (Mf : NNReal) f]
    [HasPositiveDefiniteHessianOn dom f]
    {τ : ℝ} (htau : τ ≤ 0.23) (y0 : dom)
    (process : SelfConcordantPathFollowingProcess f Mf y0 τ)
    (initialScaledGap : ℝ) :
    (∀ k : ℕ,
      satisfies_approximate_centering_condition f y0 (process.t k) (process.y k)
        (process.mem_domain k) Mf (pathFollowingCenteringBeta τ)) ∧
      ∀ N : ℕ,
        (∀ k : ℕ, k ≤ N →
          1 / (2 * (Mf : ℝ)) ≤ λ[f; process.y k | process.mem_domain k]) →
        (process.t N : ℝ) ≤
          Real.exp
            (-(pathFollowingGammaRadius τ * pathFollowingKappa τ * (N : ℝ) ^ (2 : ℕ) /
                initialScaledGap)) := sorry

end
