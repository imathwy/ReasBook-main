import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Theorem_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.27 is `source-facing` in the Chapter 3 convex-analysis API. Its owner declarations
are already the project primitives `effective_domain`, `is_convex_function`, and the
continuous-dual bridge `strongDualSubdifferential`, together with mathlib's owner
`LipschitzOnWith`. The only extra ingredient from the textbook is the owner-level inclusion
`strongDualSubdifferential f x ⊆ closedBall 0 L`; no separate wrapper predicate is kept for that
one-off condition. -/
recall effective_domain
recall is_convex_function
recall strongDualSubdifferential

end

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable (f : E → EReal) (X : Set E) (L : NNReal)
variable (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) (hf_convex : is_convex_function f)

-- Proof sketch: for `x, y ∈ X`, use `hX_subset` and the interior-point existence theorem to choose
-- subgradients `gₓ ∈ ∂ f(x)` and `gᵧ ∈ ∂ f(y)`. Apply the subgradient inequalities in both
-- directions and bound the pairings by `ContinuousLinearMap.le_opNorm`, using `hbound` to control
-- the norms of `gₓ` and `gᵧ`; this gives the two one-sided estimates needed for
-- `LipschitzOnWith L (fun x ↦ (f x).toReal) X`.
/-- Theorem 3.27 (1): if `f` never takes the value `-∞` on its effective domain and every
subgradient at a point of `X` has norm at most `L`, then the finite-valued restriction
`x ↦ (f x).toReal` is `L`-Lipschitz on `X`. -/
theorem lipschitzOnWith_toReal_of_subdifferential_norm_le_on
    (hX_subset : X ⊆ interior (effective_domain f))
    (hbound : ∀ ⦃x : E⦄, x ∈ X →
      strongDualSubdifferential f x ⊆ closedBall (0 : StrongDual ℝ E) L) :
    LipschitzOnWith L (fun x ↦ (f x).toReal) X := sorry

-- Proof sketch: the implication from bounded subgradients to Lipschitz continuity is part (1).
-- Conversely, assume `LipschitzOnWith L (fun x ↦ (f x).toReal) X`, fix `x ∈ X` and
-- `g ∈ ∂ f(x)`, and use `hX_open` to choose a small segment `x + εu ⊆ X` in a unit direction `u`
-- that realizes the dual norm of `g`. Combining the subgradient inequality with the Lipschitz
-- bound along that segment yields `g u ≤ L`, hence `‖g‖ ≤ L`.
/-- Theorem 3.27 (2): if `X` is open, then the finite-valued restriction
`x ↦ (f x).toReal` is `L`-Lipschitz on `X` if and only if every subgradient at a point of `X` has
norm at most `L`, provided `f` never takes the value `-∞` on its effective domain and
`X ⊆ effective_domain f`. -/
theorem lipschitzOnWith_toReal_iff_subdifferential_norm_le_on_of_isOpen
    (hX_open : IsOpen X) (hX_subset : X ⊆ effective_domain f) :
    LipschitzOnWith L (fun x ↦ (f x).toReal) X ↔
      ∀ ⦃x : E⦄, x ∈ X →
        strongDualSubdifferential f x ⊆ closedBall (0 : StrongDual ℝ E) L := sorry

end
