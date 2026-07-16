import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_8
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 4.23 is `source-facing`: it states the textbook formula
`h₁ + h₂ = (h₁^* □ h₂^*)^*` for a proper closed convex extended-real-valued function plus an
everywhere-finite convex perturbation. The `core/canonical` owners are already upstream:
Chapter 2's `IsProperExtendedRealFunction`, `is_convex_function`, and `infimal_convolution`,
Mathlib's `LowerSemicontinuous`, and Chapter 4's `conjugate_function` and
`biconjugate_function`. The explicit infimal-convolution/conjugate formula is therefore the main
source-facing declaration here, while the pure owner-form biconjugation equality is only a thin
companion view.

Primitive data: the functions `h₁`, `h₂` and the source hypotheses `hh₁_closed`,
`hh₁_convex`, `hh₂_convex`; the source-facing conjugate-of-sum formula also uses
`hh₁_proper`, following the upstream owner theorem `conjugate_function_add_eq_infimal_convolution`.
Derived API: the explicit conjugate/infimal-convolution identity and its owner-form
biconjugation companion. Properness is essential only for the first source-facing identity because
closed convexity alone still allows improper `EReal`-valued functions with `⊥` values, for which
the conjugate-of-sum formula can fail; the companion biconjugation equality itself is governed by
the owner theorem `biconjugate_function_eq_self_of_closed_convex` and therefore depends only on
closedness and convexity of the summed function. -/
recall IsProperExtendedRealFunction
recall is_convex_function
recall infimal_convolution
recall conjugate_function
recall biconjugate_function

-- Proof sketch: let `f := fun x ↦ h₁ x + (h₂ x : EReal)`. Because `h₂` is real-valued convex on
-- the whole space, it is continuous and hence lower semicontinuous in the finite-dimensional
-- setting, so `f` is again closed and convex. Apply the chapter-owner biconjugation theorem to
-- `f`, then rewrite `f*` using the preceding source-facing conjugate-of-sum theorem
-- `conjugate_function_add_eq_infimal_convolution`.
/-- Proposition 4.23: if `h₁` is a proper closed convex extended-real-valued function and `h₂` is a
real-valued convex function on the whole space, then the pointwise sum `h₁ + h₂` equals the
primal-side conjugate of the infimal convolution `h₁^* □ h₂^*`. This is the source-facing chapter
rendering of the textbook identity `h₁ + h₂ = (h₁^* □ h₂^*)^*`. -/
theorem proper_closed_convex_add_real_convex_eq_conjugate_infimal_convolution
    (h₁ : E → EReal) (h₂ : E → ℝ)
    (hh₁_proper : IsProperExtendedRealFunction h₁)
    (hh₁_closed : LowerSemicontinuous h₁)
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : ConvexOn ℝ Set.univ h₂) :
    (fun x ↦ h₁ x + (h₂ x : EReal)) =
      fun x ↦
        conjugate_function
          (conjugate_function h₁ □ conjugate_function (fun z ↦ (h₂ z : EReal)))
          (Module.Dual.eval ℝ E x) := sorry

-- Proof sketch: apply the chapter biconjugation theorem directly to the sum
-- `fun x ↦ h₁ x + (h₂ x : EReal)`. This is the owner-form companion to the explicit
-- source-facing formula in `proper_closed_convex_add_real_convex_eq_conjugate_infimal_convolution`.
/-- Proposition 4.23 in pure owner form: the sum `h₁ + h₂`, viewed as an `EReal`-valued function,
equals its biconjugate. -/
theorem proper_closed_convex_add_real_convex_eq_biconjugate
    (h₁ : E → EReal) (h₂ : E → ℝ)
    (hh₁_closed : LowerSemicontinuous h₁)
    (hh₁_convex : is_convex_function h₁)
    (hh₂_convex : ConvexOn ℝ Set.univ h₂) :
    (fun x ↦ h₁ x + (h₂ x : EReal)) = biconjugate_function (fun x ↦ h₁ x + (h₂ x : EReal)) :=
  sorry

end
