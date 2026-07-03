import Mathlib
import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

/- Definition 5.0.10 lies in the chapter's directional differential-calculus domain.

Sampled owner declarations:
* mathlib `HasLineDerivAt`, the canonical owner for first directional derivatives along affine
  lines;
* mathlib `lineDeriv`, the totalized directional derivative operator corresponding to
  `t ↦ f (x + t • u)` at `t = 0`;
* mathlib `DifferentiableAt.lineDeriv_eq_fderiv` and `inner_gradient_left`, the primitive
  first-order bridge from directional derivatives to gradient pairings;
* `hessian` in `Chap01/Definition_1_4_16`, the chapter owner for the second Fréchet derivative of
  a real-valued function on a Hilbert space;
* `iteratedFDeriv`, the canonical multilinear owner for the third Fréchet derivative.

Source/core/bridge triage:
* source-facing: the directional slice `t ↦ f (x + t • u)` and its first, second, and third
  derivatives at `0`;
* core/canonical: `lineDeriv ℝ f x u` for the first derivative and `hessian f x` for the
  second-order quadratic form;
* bridge/view: the identification of the third directional derivative with
  `iteratedFDeriv ℝ 3 f x (fun _ ↦ u)` under `C³` regularity.

Primitive data:
* a function `f`;
* a base point `x`;
* a direction `u`.

Derived API:
* the source-facing slice `directionalSlice f x u`;
* the owner-level first directional derivative `lineDeriv ℝ f x u`;
* the Hessian quadratic form `inner ℝ u (hessian f x u)`;
* the Fréchet third-derivative bridge for smooth functions.

The slice itself remains source-facing, but the first- and second-order derived API should reuse
the canonical owners `lineDeriv` and `hessian` instead of repeating their raw formulas. -/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition 5.0.10: the directional slice of `f` at `x` along `u` is the univariate function
`t ↦ f (x + t • u)`, from which the first, second, and third directional derivatives at `x` in
the direction `u` are taken at `t = 0`. -/
def directionalSlice (f : E → ℝ) (x u : E) : ℝ → ℝ :=
  fun t ↦ f (x + t • u)

/-- Evaluating the directional slice gives the textbook formula `φ(x; t) = f (x + t u)`. -/
@[simp] theorem directionalSlice_apply (f : E → ℝ) (x u : E) (t : ℝ) :
    directionalSlice f x u t = f (x + t • u) := rfl

/- The textbook first directional derivative at `x` along `u` is the canonical owner
`lineDeriv ℝ f x u`, i.e. the derivative at `0` of the slice `t ↦ f (x + t • u)`. -/
recall lineDeriv

/-- The second directional derivative is the second iterated derivative at `0` of the directional
slice. -/
def secondDirectionalDerivative (f : E → ℝ) (x u : E) : ℝ :=
  iteratedDeriv 2 (directionalSlice f x u) 0

/-- The third directional derivative is the third iterated derivative at `0` of the directional
slice. -/
def thirdDirectionalDerivative (f : E → ℝ) (x u : E) : ℝ :=
  iteratedDeriv 3 (directionalSlice f x u) 0

/-- The third directional derivative is odd in the direction argument. -/
@[simp] theorem thirdDirectionalDerivative_neg (f : E → ℝ) (x u : E) :
    thirdDirectionalDerivative f x (-u) = -thirdDirectionalDerivative f x u := by
  rw [thirdDirectionalDerivative]
  have hs : directionalSlice f x (-u) = fun t ↦ directionalSlice f x u (-t) := by
    funext t
    simp [directionalSlice]
  rw [hs]
  calc
    iteratedDeriv 3 (fun t ↦ directionalSlice f x u (-t)) 0
      = (-1 : ℝ) ^ (3 : ℕ) * iteratedDeriv 3 (directionalSlice f x u) 0 := by
          simpa [smul_eq_mul] using
            (iteratedDeriv_comp_neg 3 (directionalSlice f x u) 0)
    _ = -thirdDirectionalDerivative f x u := by
      norm_num [thirdDirectionalDerivative]

/-- For a `C³` function, the third directional derivative is the third Fréchet derivative of `f`
evaluated on the triple `(u, u, u)`. -/
-- Proof sketch: differentiate the slice three times and rewrite the result as evaluation of the
-- canonical trilinear map `iteratedFDeriv ℝ 3 f x` on the constant tuple `u`.
theorem thirdDirectionalDerivative_eq_iteratedFDeriv
    {f : E → ℝ} {x u : E} (hf : ContDiffAt ℝ 3 f x) :
    thirdDirectionalDerivative f x u = iteratedFDeriv ℝ 3 f x (fun _ ↦ u) := sorry

section Hilbert

variable [InnerProductSpace ℝ E] [CompleteSpace E]

/- Under differentiability, the textbook gradient pairing formula for the directional derivative is
the direct combination of the canonical bridge lemmas `DifferentiableAt.lineDeriv_eq_fderiv` and
`inner_gradient_left`. -/
recall DifferentiableAt.lineDeriv_eq_fderiv
recall inner_gradient_left

/-- If `f` is differentiable at `x` and its gradient is differentiable at `x`, then the second
directional derivative equals the Hessian quadratic form in the direction `u`. -/
-- Proof sketch: apply the chain rule twice to the directional slice and identify the derivative of
-- the gradient with the Hessian operator `fderiv ℝ (∇ f) x`.
theorem secondDirectionalDerivative_eq_hessian_quadratic_form
    {f : E → ℝ} {x u : E} (hf : DifferentiableAt ℝ f x)
    (hgrad : DifferentiableAt ℝ (∇ f) x) :
    secondDirectionalDerivative f x u = inner ℝ u (hessian f x u) := sorry

end Hilbert

end
