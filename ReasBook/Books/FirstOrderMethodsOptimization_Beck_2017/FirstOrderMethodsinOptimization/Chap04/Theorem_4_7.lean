import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_8
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

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
