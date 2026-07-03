

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_4_5 (from Chap04) -/
universe u

open InnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 4.5 is `source-facing`. Its owner abstractions already exist upstream:
`extendedIndicator` in Chapter 2, `conjugate_function` in Definition 4.1, and the distance-based
potential in Example 2.5 as `euclidean_distance_potential`. This file therefore keeps only the
Fenchel-conjugacy identity specialized to that canonical project data, viewing the real-valued
distance potential as `EReal`-valued for conjugacy. -/

-- Proof sketch: rewrite `euclidean_distance_potential C` as the supremum over `c ∈ C` of the
-- affine functions `x ↦ ⟪x, c⟫ - 1/2 ‖c‖²`, identify the Euclidean pairing with the dual pairing
-- through `toDualMap`, and then compute the conjugate by splitting into the cases `y ∈ C` and
-- `y ∉ C`.
/-- Proposition 4.5: for a nonempty closed convex set `C` in a Euclidean space, the conjugate of
`x ↦ 1/2 ‖x‖² - 1/2 d(x, C)²`, expressed through the Chapter 2 owner
`euclidean_distance_potential`, is `y ↦ 1/2 ‖y‖² + δ_C(y)`. -/
theorem conjugate_function_quadratic_distance_eq_half_squared_norm_add_extendedIndicator
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    (fun y ↦ conjugate_function (fun x ↦ (euclidean_distance_potential C x : EReal))
      ↑(toDualMap ℝ E y)) =
      fun y ↦ (((1 / 2 : ℝ) * ‖y‖ ^ 2 : ℝ) : EReal) + extendedIndicator C y := sorry

end

/-! ### Theorem_4_5 (from Chap04) -/
noncomputable section

/- Theorem 4.5 is `source-facing`: it identifies the scalar conjugate of `x ↦ exp x`.
The `core/canonical` owner abstraction is the chapter Fenchel conjugate `conjugate_function` from
Definition 4.1, specialized to `ℝ` through `InnerProductSpace.toDualMap`. There is no additional
primitive data here beyond that owner specialization. -/

-- Proof sketch: for `y < 0`, send `x → -∞` to make `x * y - exp x` tend to `+∞`, so the supremum
-- is `⊤`. For `y = 0`, the supremum is `0`, approached as `x → -∞`. For `y > 0`, differentiate
-- `x ↦ x * y - exp x`, identify the unique critical point `x = log y`, and evaluate there to get
-- `y * log y - y`. Since `Real.log 0 = 0`, the same formula covers the case `y = 0`.
/-- Theorem 4.5: the conjugate of `x ↦ exp x` is `y log y - y` for `y ≥ 0`, and `⊤` for `y < 0`.
The convention `0 log 0 = 0` is encoded by `Real.log 0 = 0`. -/
theorem exp_conjugate_function_eq
    (y : ℝ) :
    conjugate_function (fun x : ℝ ↦ (Real.exp x : EReal)) (InnerProductSpace.toDualMap ℝ ℝ y) =
      if 0 ≤ y then ((y * Real.log y - y : ℝ) : EReal) else ⊤ := sorry
