import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Proposition 1.8 is recall-only: the textbook statement that the Euclidean norm is self-dual is
exactly the specialization of the owner theorem `LinearIsometryEquiv.norm_map` to the canonical
Fréchet-Riesz equivalence `InnerProductSpace.toDual ℝ E : E ≃ₗᵢ⋆[ℝ] StrongDual ℝ E`, whose
canonical hypothesis is completeness of the inner-product space. -/
#check (InnerProductSpace.toDual ℝ E).norm_map

end
