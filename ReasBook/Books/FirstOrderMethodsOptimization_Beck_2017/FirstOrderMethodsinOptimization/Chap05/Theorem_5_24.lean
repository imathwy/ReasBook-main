import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Definition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 5.24 is `source-facing` for the first-order characterization of strong convexity. The
extended-real convex-analysis owners it uses are already upstream: `effective_domain` and
`IsProperExtendedRealFunction` from Definition 2.5, `is_convex_function` from Definition 2.6, and
`subdifferential` from Definition 3.2. This file keeps only the new strong-convexity predicates
and equivalence theorem built on top of those owners. -/

recall subdifferential

/-- The first-order lower quadratic support inequality for an extended-real-valued convex
function. This is the source clause (ii), written with dual pairings `g (y - x)` instead of the
Euclidean inner-product notation. -/
def subgradient_quadratic_lower_bound (f : E → EReal) (σ : ℝ) : Prop :=
  ∀ x : E, ∀ g ∈ subdifferential f x, ∀ y ∈ effective_domain f,
    f y ≥ f x + ((g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) : ℝ) : EReal)

-- Proof sketch: unfold `subgradient_quadratic_lower_bound`; this is definitional equality.
/-- Unfolding `subgradient_quadratic_lower_bound` gives exactly the displayed quadratic
subgradient lower bound. -/
@[simp] theorem subgradient_quadratic_lower_bound_iff
    {f : E → EReal} {σ : ℝ} :
    subgradient_quadratic_lower_bound f σ ↔
      ∀ x : E, ∀ g ∈ subdifferential f x, ∀ y ∈ effective_domain f,
        f y ≥ f x + ((g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) : ℝ) : EReal) := sorry

/-- The strong monotonicity inequality for the subdifferential of an extended-real-valued convex
function. This is the source clause (iii), written in dual-pairing form. -/
def subdifferential_strong_monotonicity (f : E → EReal) (σ : ℝ) : Prop :=
  ∀ x y : E, ∀ gₓ ∈ subdifferential f x, ∀ gᵧ ∈ subdifferential f y,
    σ * ‖x - y‖ ^ (2 : ℕ) ≤ (gₓ - gᵧ) (x - y)

-- Proof sketch: unfold `subdifferential_strong_monotonicity`; this is definitional equality.
/-- Unfolding `subdifferential_strong_monotonicity` gives exactly the displayed strong
monotonicity inequality for pairs of subgradients. -/
@[simp] theorem subdifferential_strong_monotonicity_iff
    {f : E → EReal} {σ : ℝ} :
    subdifferential_strong_monotonicity f σ ↔
      ∀ x y : E, ∀ gₓ ∈ subdifferential f x, ∀ gᵧ ∈ subdifferential f y,
        σ * ‖x - y‖ ^ (2 : ℕ) ≤ (gₓ - gᵧ) (x - y) := sorry

-- Proof sketch: use the canonical owner-level strong-convexity statement
-- `StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)` for clause (i). For
-- `(i) → (iii)`, apply the strong-convexity support inequality at `x` and `y` and add the two
-- resulting estimates. For `(iii) → (ii)`, restrict `f` to segments from `x` toward relative-
-- interior perturbations of `y`, use the one-dimensional subgradient selection formula from
-- Lemma 5.22 together with the line-segment principle from Lemma 5.23, and integrate the strong
-- monotonicity estimate. For `(ii) → (i)`, apply (ii) at interior convex-combination points along
-- perturbed segments and pass to the endpoint limit using lower semicontinuity of `f`.
/-- Theorem 5.24: for a proper closed convex extended-real-valued function and a fixed modulus
`σ > 0`, the following are equivalent: (i) the real-valued restriction of `f` to its effective
domain is `σ`-strongly convex, (ii) every subgradient gives the quadratic lower support model, and
(iii) the subdifferential is `σ`-strongly monotone. This is the canonical owner-level rendering of
the textbook first-order characterization of strong convexity. -/
theorem strongConvexOn_tfae_subgradient_quadratic_lower_bound_strong_monotonicity
    (f : E → EReal) (σ : ℝ) (hσ : 0 < σ) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) :
    List.TFAE
      [StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal),
        subgradient_quadratic_lower_bound f σ,
        subdifferential_strong_monotonicity f σ] := sorry

end
