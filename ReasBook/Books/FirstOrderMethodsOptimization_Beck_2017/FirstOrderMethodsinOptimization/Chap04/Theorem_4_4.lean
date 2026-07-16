import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {V : Type u} {E : Type v}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup E] [Module ℝ E]

/- Theorem 4.4 is `source-facing` in the chapter conjugacy API. Its primitive owner is
`conjugate_function` from Definition 4.1, while the inverse transpose in the textbook formula is
the canonical mathlib dual equivalence `A.dualMap.symm`. -/

-- Proof sketch: expand the conjugate by its defining supremum, make the change of variables
-- `z = A (x - a)` so that `x = A.symm z + a`, and rewrite the pairing term by the dual pullback
-- identity `A.dualMap φ x = φ (A x)`. The remaining affine constants factor out of the supremum,
-- leaving the conjugate of `f` evaluated at `A.dualMap.symm (y - b)`.
/-- Theorem 4.4: for `g(x) = f (A (x - a)) + ⟨b, x⟩ + c`, the conjugate of `g` at `y` is the
conjugate of `f` at the inverse transpose pullback `A.dualMap.symm (y - b)`, shifted by the affine
term `(y a) - c - (b a)`. This is the item's formula (4.13) in the chapter owner notation. -/
theorem conjugate_function_affine_change_of_variables
    (f : E → EReal) (A : V ≃ₗ[ℝ] E) (a : V) (b y : Module.Dual ℝ V) (c : ℝ) :
    conjugate_function (fun x : V ↦ f (A (x - a)) + (b x : EReal) + (c : EReal)) y =
      conjugate_function f (A.dualMap.symm (y - b)) +
        ((y a - c - b a : ℝ) : EReal) := sorry

end
