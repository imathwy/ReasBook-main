

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_4_7 (from Chap04) -/
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

/-! ### Theorem_4_7 (from Chap04) -/
universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Theorem 4.7 is `source-facing` in the chapter conjugacy calculus. The `core/canonical` owner
declarations already live upstream in the project: Chapter 2 owns `infimal_convolution`, while
Definition 4.1 owns `conjugate_function`. This file therefore keeps only the source theorem
statement and reuses those owners directly.

In the textbook, `h₁` and `h₂` are proper. For this `EReal` conjugacy identity, the only part of
properness used by the owner-level formula is that neither function ever takes the value `⊥`; the
nonempty-effective-domain part is redundant here. -/
recall infimal_convolution
recall conjugate_function

-- Proof sketch: unfold the definitions of `conjugate_function` and `infimal_convolution`, rewrite
-- the supremum over `x` and infimum over `u` as a supremum over decompositions `x = u + v`, and
-- separate the resulting affine expression into the sum of the two independent suprema defining
-- `conjugate_function h₁` and `conjugate_function h₂`.
/-- Theorem 4.7: if `h₁` and `h₂` never take the value `⊥`, then the conjugate of their infimal
convolution equals the pointwise sum of the conjugates. This is the owner-form rendering of the
textbook proper-case formula, with the redundant nonempty-domain part of properness removed. -/
theorem conjugate_function_infimal_convolution_eq_add
    (h₁ h₂ : E → EReal) (h₁_ne_bot : ∀ x, h₁ x ≠ ⊥) (h₂_ne_bot : ∀ x, h₂ x ≠ ⊥) :
    conjugate_function (h₁ □ h₂) = conjugate_function h₁ + conjugate_function h₂ :=
  sorry

end
