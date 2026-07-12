import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- This exercise uses the canonical `Group` owner from `Mathlib.Algebra.Group.Defs`; the two
-- textbook equalities are the derived group lemmas `inv_mul_cancel` and `mul_inv_cancel`.

section Exercise78

universe u

variable {G : Type u} [Group G]

/- Exercise 7.8 (1): in the universal covering group proof, the equality `x⁻¹ * x = \widetilde e`
is the canonical left-inverse identity, with the textbook identity element `\widetilde e`
represented in Lean by `1`. -/
recall inv_mul_cancel (x : G) : x⁻¹ * x = 1

/- Exercise 7.8 (2): in the universal covering group proof, the equality `x * x⁻¹ = \widetilde e`
is the canonical right-inverse identity, with the textbook identity element `\widetilde e`
represented in Lean by `1`. -/
recall mul_inv_cancel (x : G) : x * x⁻¹ = 1

end Exercise78
