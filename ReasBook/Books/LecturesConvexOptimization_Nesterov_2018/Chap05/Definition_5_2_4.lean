import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_0_24
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_2_3

open InnerProductSpace
open scoped Gradient NewtonDecrement

noncomputable section

/- Definition 5.2.4 lies in the Chapter 5 self-concordant path-following / tilted-objective
Newton-decrement domain.

Source/core/bridge triage:
* source-facing: the shifted-objective decrement `λ_{ψ(t; ·)}(y)`
* core/canonical: `newtonDecrement (auxiliaryCentralPathObjective f y₀ t) y`
* bridge/view: the shifted-gradient/Hessian identities and the determinant-based Hessian
  invertibility bridge

Mandatory domain-style sampling before refinement:
* `auxiliaryCentralPathObjective` in `Chap05/Definition_5_2_3`, the chapter owner for the tilted
  objective `ψ(t; ·)`
* `newtonDecrement` in `Chap05/Definition_5_0_24`, the chapter owner for Newton decrements
* `newtonDecrement_def` in `Chap05/Definition_5_0_24`, the canonical inverse-Hessian pairing
  expansion of the Newton-decrement owner
* `HessianDualLocalNorm.ofDetNeZero` / `HessianDualLocalNorm.ofDetNeZero_def` in
  `Chap05/Definition_5_0_20`, the determinant bridge for the shifted gradient covector

Best owner abstraction:
* source-facing: the Newton decrement of the tilted objective `ψ(t; ·)`
* core/canonical: `newtonDecrement` applied to `auxiliaryCentralPathObjective f y₀ t`
* bridge/view: the shifted-gradient formula and the determinant-nondegeneracy specialization

Primitive data:
* a function `f`
* a base point `y₀`
* a path parameter `t`
* an evaluation point `y`
* Hessian positivity and nondegeneracy at `y`

Derived API:
* the source-facing notation `λψ[f; y₀; t; y](hPos; hHy)`
* the bridge to `newtonDecrement (auxiliaryCentralPathObjective f y₀ t) y`
* the shifted-gradient and Hessian identities for the tilted objective
* the inverse-Hessian pairing formula and determinant-dual-norm specialization

This refinement makes the mathematical owner explicit: Definition 5.2.4 is a specialization of
the Chapter 5 Newton-decrement owner to the tilted objective `ψ(t; ·)`. The determinant witness
survives only in the thin bridge layer that supplies the tilted objective's Hessian
invertibility from the unchanged Hessian of `f`. -/

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section

/- Definition 5.2.4 recalls the Chapter 5 Newton-decrement owner specialized to the tilted
objective `auxiliaryCentralPathObjective f y₀ t`. -/
recall newtonDecrement

/-- The gradient of the tilted objective `ψ(t; ·)` is the shifted gradient
`∇ f(y) - t ∇ f(y₀)`. -/
theorem auxiliaryCentralPathObjective_gradient_eq
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E) :
    ∇ (auxiliaryCentralPathObjective f y0 t) y =
      ∇ f y - (t : ℝ) • ∇ f (y0 : E) := sorry

/-- The linear tilt in `ψ(t; ·)` does not change the Hessian. -/
theorem auxiliaryCentralPathObjective_hessian_eq
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E) :
    hessian (auxiliaryCentralPathObjective f y0 t) y = hessian f y := sorry

/-- Hessian positivity for `f` at `y` transfers directly to the tilted objective `ψ(t; ·)` at
the same point. -/
theorem auxiliaryCentralPathObjective_hessian_isPositive
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E)
    (hPos : (hessian f y).IsPositive) :
    (hessian (auxiliaryCentralPathObjective f y0 t) y).IsPositive := by
  simpa [auxiliaryCentralPathObjective_hessian_eq] using hPos

/-- Hessian nondegeneracy for `f` at `y` canonically yields Hessian invertibility for the tilted
objective `ψ(t; ·)` at `y`. -/
theorem auxiliaryCentralPathObjective_hessian_isInvertible
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ) (y : E)
    (hHy : (hessian f y).det ≠ 0) :
    (hessian (auxiliaryCentralPathObjective f y0 t) y).IsInvertible := by
  simpa [auxiliaryCentralPathObjective_hessian_eq] using
    (hessian_isInvertible_of_det_ne_zero hHy : (hessian f y).IsInvertible)

namespace AuxiliaryCentralPathNewtonDecrement

/-- Source-facing notation for the Newton decrement `λ_{ψ(t; ·)}(y)` of the tilted objective,
read through the determinant-based Hessian bridge at `y`. -/
scoped notation:max "λψ[" f "; " y0 "; " t "; " y "](" hPos "; " hHy ")" =>
  newtonDecrement (auxiliaryCentralPathObjective f y0 t) y
    (auxiliaryCentralPathObjective_hessian_isPositive f y0 t y hPos)
    (auxiliaryCentralPathObjective_hessian_isInvertible f y0 t y hHy)

end AuxiliaryCentralPathNewtonDecrement

open scoped AuxiliaryCentralPathNewtonDecrement

/-- The notation `λψ[f; y₀; t; y](hPos; hHy)` is exactly the Chapter 5 Newton-decrement owner
applied to the tilted objective `ψ(t; ·)`. -/
@[simp] theorem auxiliaryCentralPathNewtonDecrement_eq_newtonDecrement
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ)
    (y : E) (hPos : (hessian f y).IsPositive) (hHy : (hessian f y).det ≠ 0) :
    λψ[f; y0; t; y](hPos; hHy) =
      newtonDecrement (auxiliaryCentralPathObjective f y0 t) y
        (auxiliaryCentralPathObjective_hessian_isPositive f y0 t y hPos)
        (auxiliaryCentralPathObjective_hessian_isInvertible f y0 t y hHy) := by
  rfl

/-- Expanding `λψ[f; y₀; t; y](hPos; hHy)` through the tilted-objective Newton-decrement owner
gives the inverse-Hessian pairing formula for the shifted gradient of `ψ(t; ·)`. -/
@[simp] theorem auxiliaryCentralPathNewtonDecrement_def
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ)
    (y : E) (hPos : (hessian f y).IsPositive) (hHy : (hessian f y).det ≠ 0) :
    λψ[f; y0; t; y](hPos; hHy) =
      Real.sqrt
        (inner ℝ (∇ f y - (t : ℝ) • ∇ f (y0 : E))
          ((hessian f y).inverse (∇ f y - (t : ℝ) • ∇ f (y0 : E)))) := by
  simpa [auxiliaryCentralPathObjective_gradient_eq, auxiliaryCentralPathObjective_hessian_eq] using
    newtonDecrement_def (auxiliaryCentralPathObjective f y0 t) y
      (auxiliaryCentralPathObjective_hessian_isPositive f y0 t y hPos)
      (auxiliaryCentralPathObjective_hessian_isInvertible f y0 t y hHy)

/-- The source-facing tilted-objective Newton decrement also agrees with the determinant bridge
`HessianDualLocalNorm.ofDetNeZero` applied to the shifted gradient covector. -/
@[simp] theorem auxiliaryCentralPathNewtonDecrement_eq_ofDetNeZero
    {dom : Set E} (f : E → ℝ) (y0 : dom) (t : ℝ)
    (y : E) (hPos : (hessian f y).IsPositive) (hHy : (hessian f y).det ≠ 0) :
    λψ[f; y0; t; y](hPos; hHy) =
      HessianDualLocalNorm.ofDetNeZero f y hPos hHy
        ((toDual ℝ E) (∇ f y - (t : ℝ) • ∇ f (y0 : E))) := sorry

end

end
