

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_27 (from Chap03) -/
/- Proposition 3.27 is recall-only in the Chapter 3 subdifferential-calculus API. The primary
mathematical domain is the weak max rule for subdifferentials of pointwise suprema. In this
domain, the owner abstraction is the Chapter 3 owner set `subdifferential`; the active-index family
`{i : ι // f i x = ⨆ j, f j x}` is derived data, and the convex-hull inclusion is the canonical
source-facing statement. Sampling the nearby owner declarations:

* `directional_derivative_iSup_eq_iSup_active_indices` in `Theorem_3_9` identifies the active
  indices for pointwise suprema.
* `subdifferential_pointwise_max_eq_convexHull_iUnion_active_subdifferential` in
  `Theorem_3_22` is the stronger equality under finite-family convexity/interior hypotheses.
* `convexHull_iUnion_active_subdifferential_subset_subdifferential_iSup` in `Theorem_3_23` is the
  weak inclusion with the exact source-facing semantics of Proposition 3.27.

This file therefore reuses the owner theorem from `Theorem_3_23` directly and introduces no
parallel local wrapper. -/
recall convexHull_iUnion_active_subdifferential_subset_subdifferential_iSup

/-! ### Theorem_3_27 (from Chap03) -/
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
