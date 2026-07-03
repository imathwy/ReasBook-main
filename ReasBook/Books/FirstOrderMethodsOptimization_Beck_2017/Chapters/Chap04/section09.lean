

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_4_9 (from Chap04) -/
open InnerProductSpace

noncomputable section

/- Proposition 4.9 is `source-facing`: it computes the conjugate of the hinge loss on `ℝ`.
The `core/canonical` owner abstractions already live upstream as `extendedIndicator` in
Chapter 2 and `conjugate_function` in Definition 4.1. This file therefore keeps only the
hinge-loss integrand and the scalar specialization of that owner conjugate via `toDualMap ℝ ℝ`.
The primitive data here is just the hinge-loss function; the conjugacy formula is derived API. -/

/-- The hinge-loss example `x ↦ max (1 - x, 0)`, viewed as an `EReal`-valued function. -/
def hinge_loss : ℝ → EReal :=
  fun x ↦ (max (1 - x) 0 : EReal)

/-- Evaluating `hinge_loss` at `x` returns `max (1 - x, 0)` as an extended real number. -/
@[simp] theorem hinge_loss_apply (x : ℝ) :
    hinge_loss x = (max (1 - x) 0 : EReal) :=
  rfl

-- Proof sketch: analyze the supremum in
-- `conjugate_function hinge_loss (InnerProductSpace.toDualMap ℝ ℝ y)` piecewise in `x`.
-- The affine branch on `(-∞, 1]` has slope `1 + y`, the branch on `[1, ∞)` has slope `y`, so a
-- finite maximizer exists exactly for `y ∈ [-1, 0]`, where the value at `x = 1` is `y`.
/-- Proposition 4.9: the convex conjugate of the hinge loss `x ↦ max (1 - x, 0)`, expressed via
the Chapter 4 owner `conjugate_function` on `ℝ` using `toDualMap ℝ ℝ`, is the affine function
`y` plus the extended-real-valued indicator of the interval `[-1, 0]`. -/
theorem hinge_loss_conjugate_eq (y : ℝ) :
    conjugate_function hinge_loss (toDualMap ℝ ℝ y) =
      (y : EReal) + extendedIndicator (Set.Icc (-1 : ℝ) 0) y := sorry

/-! ### Theorem_4_9 (from Chap04) -/
noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.9 is `source-facing` in the chapter infimal-convolution/conjugacy calculus. Its
ambient notions are already owned upstream by the project declarations
`is_convex_function`, `infimal_convolution`, and `conjugate_function`. The textbook right-hand
side `(h₁^* + h₂^*)^*` starts from a function on the dual space `E*`, so the canonical
`bridge/view` back to the primal space is the bidual identification
`Module.evalEquiv ℝ E : E ≃ₗ[ℝ] E**`. This file therefore states the theorem through that
owner-level bridge instead of expanding it as a raw lambda along `Module.Dual.eval ℝ E`, and
reuses the chapter owners directly instead of repeating parallel local copies. -/

recall is_convex_function
recall infimal_convolution
recall conjugate_function

-- Proof sketch: apply the chapter formula for the conjugate of an infimal convolution to obtain
-- `(h₁ □ h₂)* = h₁* + h₂*`. The infimal-convolution convexity theorem gives convexity of
-- `h₁ □ h₂`, and the hypothesis that it is real-valued forces the needed properness/closedness
-- in the finite-dimensional chapter setting. The conjugate of the dual-space sum `h₁* + h₂*`
-- then lives on the bidual `E**`, and `Module.evalEquiv ℝ E` transports that canonical owner
-- expression back to the primal space.
/-- Theorem 4.9: if `h₁` is a convex extended-real-valued function, `h₂` is a real-valued convex
function, and the infimal convolution `h₁ □ h₂` is real-valued, then `h₁ □ h₂` equals the
conjugate of the dual-space sum `h₁^* + h₂^*`, transported back to the primal space by the
canonical bidual equivalence `Module.evalEquiv ℝ E`. In this owner-level rendering of
`h₁ \square h₂ = (h₁^* + h₂^*)^*`, the properness that appears in textbook hypotheses is derived
from the everywhere-finite infimal-convolution assumption, so it is not kept as separate public
data. The explicit `Module.Dual.eval` lambda form is demoted to a derived companion rewrite. -/
theorem infimal_convolution_eq_dual_conjugate_of_sum_conjugates
    (h₁ : E → EReal) (h₂ : E → ℝ) (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : ConvexOn ℝ Set.univ h₂)
    (hreal :
      ∀ x, ∃ r : ℝ, (h₁ □ fun z ↦ (h₂ z : EReal)) x = (r : EReal)) :
    (h₁ □ fun x ↦ (h₂ x : EReal)) =
      conjugate_function
        (conjugate_function h₁ + conjugate_function (fun z ↦ (h₂ z : EReal))) ∘
          Module.evalEquiv ℝ E := sorry

/-- Companion rewrite of Theorem 4.9 in the explicit `Module.Dual.eval` presentation. -/
theorem infimal_convolution_eq_dual_conjugate_of_sum_conjugates_apply
    (h₁ : E → EReal) (h₂ : E → ℝ) (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : ConvexOn ℝ Set.univ h₂)
    (hreal :
      ∀ x, ∃ r : ℝ, (h₁ □ fun z ↦ (h₂ z : EReal)) x = (r : EReal)) :
    (h₁ □ fun x ↦ (h₂ x : EReal)) =
      fun x ↦
        conjugate_function
          (conjugate_function h₁ + conjugate_function (fun z ↦ (h₂ z : EReal)))
          (Module.Dual.eval ℝ E x) := by
  simpa [Function.comp] using
    infimal_convolution_eq_dual_conjugate_of_sum_conjugates
      h₁ h₂ hh₁_convex hh₂_convex hreal

end
