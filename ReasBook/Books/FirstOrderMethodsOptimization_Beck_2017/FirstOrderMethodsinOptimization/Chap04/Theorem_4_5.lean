import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

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
