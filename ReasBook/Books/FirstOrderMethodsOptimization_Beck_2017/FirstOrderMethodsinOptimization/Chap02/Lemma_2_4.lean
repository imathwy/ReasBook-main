import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: expand `support_function`; for `α ≥ 0`, move the scalar through the dual pairing
-- and then through the supremum over the nonempty image set.
/-- Lemma 2.4 (1): (a) the support function is positively homogeneous in the dual variable:
for a nonempty set `C` and `α ≥ 0`, one has `σ_C (α y) = α σ_C (y)`. -/
theorem support_function_nonneg_smul_dual
    (C : Set E) (hC : C.Nonempty) (y : Module.Dual ℝ E) {α : ℝ} (hα : 0 ≤ α) :
    support_function C (α • y) = (α : EReal) * support_function C y := sorry

-- Proof sketch: expand `support_function`; for each `x ∈ C`, linearity gives
-- `(y₁ + y₂) x = y₁ x + y₂ x`, and taking suprema over the same set yields the usual
-- subadditivity inequality; for `C = ∅`, both sides reduce to `⊥`-valued expressions in `EReal`.
/-- Lemma 2.4 (2): (b) the support function is subadditive on the dual space:
for any set `C`, `σ_C (y₁ + y₂) ≤ σ_C (y₁) + σ_C (y₂)`. -/
theorem support_function_add_le
    (C : Set E) (y₁ y₂ : Module.Dual ℝ E) :
    support_function C (y₁ + y₂) ≤ support_function C y₁ + support_function C y₂ := sorry

-- Proof sketch: rewrite `α • C` as the image of `C` under `x ↦ α • x`, expand
-- `support_function`, and use `y (α • x) = α * y x` with `α ≥ 0` to pull the scalar outside the
-- supremum.
/-- Lemma 2.4 (3): (c) scaling the set by a nonnegative scalar scales its support function by the
same scalar. -/
theorem support_function_smul_set
    (C : Set E) (hC : C.Nonempty) (y : Module.Dual ℝ E) {α : ℝ} (hα : 0 ≤ α) :
    support_function (α • C) y = (α : EReal) * support_function C y := sorry

-- Proof sketch: rewrite `A + B` as the Minkowski sum of pointwise additions, expand the defining
-- supremum, use `y (a + b) = y a + y b`, and separate the supremum over pairs into the sum of the
-- two one-variable suprema; if either set is empty, both sides are `⊥` by the definition of
-- `support_function` and `EReal.add_bot`/`EReal.bot_add`.
/-- Lemma 2.4 (4): (d) the support function of a Minkowski sum equals the sum of the support
functions. -/
theorem support_function_minkowski_sum
    (A B : Set E) (y : Module.Dual ℝ E) :
    support_function (A + B) y = support_function A y + support_function B y := sorry

end
