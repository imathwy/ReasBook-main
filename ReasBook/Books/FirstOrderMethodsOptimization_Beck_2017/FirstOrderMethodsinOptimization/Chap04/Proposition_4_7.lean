import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Proposition 4.7 is `source-facing` in the chapter Fenchel-conjugacy API. The `core/canonical`
owner is Definition 4.1's `conjugate_function`, so this file keeps only the two positive-scaling
calculus identities from equations (4.14a) and (4.14b). -/

-- Proof sketch: expand the defining supremum of `conjugate_function`. For `α > 0`, rewrite
-- `y x - α f x` as `α * (((1 / α) • y) x - f x)`, then pull the positive scalar `(α : EReal)`
-- through the supremum.
/-- Proposition 4.7 (1): equation (4.14a). Scaling an extended-real-valued function by a positive
real scalar scales its conjugate by the same scalar and rescales the dual argument by `(1 / α)`,
the Lean form of `y / α`. -/
theorem conjugate_function_pos_real_mul
    (f : E → EReal) (α : ℝ) (hα : 0 < α) :
    conjugate_function (fun x ↦ (α : EReal) * f x) =
      fun y ↦ (α : EReal) * conjugate_function f ((1 / α) • y) := sorry

-- Proof sketch: expand the defining supremum of `conjugate_function` and substitute
-- `u = (1 / α) • x`, equivalently `x = α • u`. Because `α > 0`, this change of variables is a
-- bijection of `E`, and the supremum becomes `(α : EReal)` times the defining supremum of
-- `conjugate_function f`.
/-- Proposition 4.7 (2): equation (4.14b). For a positive real scalar `α`, the conjugate of
`x ↦ α f ((1 / α) • x)` is `y ↦ α f*(y)`. -/
theorem conjugate_function_pos_real_precomp_inv_smul
    (f : E → EReal) (α : ℝ) (hα : 0 < α) :
    conjugate_function (fun x ↦ (α : EReal) * f ((1 / α) • x)) =
      fun y ↦ (α : EReal) * conjugate_function f y := sorry

end
