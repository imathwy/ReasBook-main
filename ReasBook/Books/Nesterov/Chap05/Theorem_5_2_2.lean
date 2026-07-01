import Mathlib
import Nesterov.Chap05.Definition_5_1_1
import Nesterov.Chap05.Definition_5_2_1

-- Declarations for this item will be appended below by the statement pipeline.

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
