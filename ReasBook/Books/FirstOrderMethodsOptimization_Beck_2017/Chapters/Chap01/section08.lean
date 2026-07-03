import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_8 (from Chap01) -/
/- Definition 1.8: an inner product on a real vector space is the canonical source-facing mathlib
data `InnerProductSpace.Core`; specialized to `ℝ`, this encodes the textbook symmetry, linearity,
and positive-definiteness axioms for the pairing. -/
recall InnerProductSpace.Core

/- The canonical bridge from this source-facing core data to the ambient owner abstraction
`InnerProductSpace` is `InnerProductSpace.ofCore`. -/
recall InnerProductSpace.ofCore

/-! ### Proposition_1_8 (from Chap01) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Proposition 1.8 is recall-only: the textbook statement that the Euclidean norm is self-dual is
exactly the specialization of the owner theorem `LinearIsometryEquiv.norm_map` to the canonical
Fréchet-Riesz equivalence `InnerProductSpace.toDual ℝ E : E ≃ₗᵢ⋆[ℝ] StrongDual ℝ E`, whose
canonical hypothesis is completeness of the inner-product space. -/
#check (InnerProductSpace.toDual ℝ E).norm_map

end
