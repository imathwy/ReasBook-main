

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_4_15 (from Chap04) -/
open Matrix
open scoped BigOperators

noncomputable section

/- Proposition 4.15 is `source-facing`: the textbook barrier on `ℝ^n` is the finite separable sum
of the scalar Chapter 4 owner `negative_log_barrier`. The `core/canonical` Fenchel owner is
`conjugate_function`, and the relevant `bridge/view` owner is
`conjugate_function_separable_sum_eq_sum_conjugate_function`. The positive-orthant description is
therefore derived API, expressed through Chapter 1's canonical `positiveOrthant`. The finite-sum
formula itself is more naturally owned at the general finite-product level and then specialized
back to `ℝ^n`. -/

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

-- Proof sketch: each summand is `-log (x i)` for `x i > 0` and `⊤` otherwise. Thus the finite sum
-- is finite exactly when every coordinate is positive, and on that positive orthant it collapses
-- to `-∑ i, log (x i)`.
/-- The finite separable sum of the scalar negative-log barrier is the textbook barrier:
`-∑ i, log (x i)` on the positive orthant and `∞` outside it. Specializing to `ι = Fin n`
recovers the usual formula on `ℝ^n_{++}`. -/
theorem sum_negative_log_barrier_apply (x : E) :
    (∑ i, negative_log_barrier (x i)) =
      if ∀ i, 0 < x i then ((-∑ i, Real.log (x i) : ℝ) : EReal) else ⊤ := sorry

end

section

variable {n : ℕ}

local notation "E" => Fin n → ℝ

-- Proof sketch: apply the Chapter 4 bridge
-- `conjugate_function_separable_sum_eq_sum_conjugate_function` to the separable sum
-- `x ↦ ∑ i, negative_log_barrier (x i)` and the coordinate dual family
-- `i ↦ LinearMap.toSpanSingleton ℝ ℝ (y i)`. Then use Proposition 4.8 coordinatewise. If every
-- `y i < 0`, the scalar conjugates sum to `-n - ∑ i, log (-y i)`; if some `y i ≥ 0`, one scalar
-- conjugate is `⊤`, so the whole sum is `⊤`.
/-- Proposition 4.15: the Fenchel conjugate of the separable sum of the scalar negative-log
barrier, equivalently by [sum_negative_log_barrier_apply] the textbook barrier
`x ↦ -∑ i, log (x i)` on `positiveOrthant n` and `∞` outside, is `-n - ∑ i, log (-y i)` on the
negative orthant and `∞` otherwise. The dual argument is expressed through the Euclidean pairing
`dotProductEquiv`. -/
theorem sum_negative_log_barrier_conjugate_eq
    (y : E) :
    conjugate_function (fun x : E ↦ ∑ i, negative_log_barrier (x i))
      (dotProductEquiv ℝ (Fin n) y) =
      if ∀ i : Fin n, y i < 0 then
        ((-(n : ℝ) - ∑ i : Fin n, Real.log (-y i) : ℝ) : EReal)
      else ⊤ := sorry

end

/-! ### Theorem_4_15 (from Chap04) -/
universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.15 is `source-facing` in the Chapter 4 conjugacy API. Its primitive data are the
owner predicates `IsProperExtendedRealFunction` and `is_convex_function`, while the conjugate is
the Chapter 4 owner `conjugate_function` on the dual space from Definition 4.1. -/

-- Proof sketch: choose `x₀ ∈ effective_domain f` from properness. Then `(y x₀ : EReal) - f x₀`
-- is finite for every dual vector `y`, so `conjugate_function f y` is never `⊥` because it
-- dominates this affine value. For finiteness at some dual vector, choose a point of the effective
-- domain with a subgradient and use the subgradient inequality to bound the supremum defining the
-- conjugate above.
/-- Theorem 4.15: properness of conjugate functions. In the finite-dimensional real normed-space
setting of the chapter, the conjugate of a proper convex extended-real-valued function is proper.
-/
theorem isProperExtendedRealFunction_conjugate_function
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    (hconvex : is_convex_function f) :
    IsProperExtendedRealFunction (conjugate_function f) := sorry

end
