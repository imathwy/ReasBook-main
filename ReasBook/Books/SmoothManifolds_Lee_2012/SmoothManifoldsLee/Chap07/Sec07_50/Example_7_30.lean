import Mathlib.LinearAlgebra.UnitaryGroup

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall via `lean_leansearch`: the canonical matrix owner is
-- `Matrix.specialUnitaryGroup`, and the ambient `U(n) ↪ GL(n, ℂ)` owner is
-- `Matrix.UnitaryGroup.embeddingGL`.

/- Example 7.30 (The Special Unitary Group): the textbook identity
`SU(n) = U(n) ∩ SL(n, ℂ)` is exactly the canonical membership theorem for
`Matrix.specialUnitaryGroup`. Together with the canonical embedding
`Matrix.UnitaryGroup.embeddingGL` of `U(n)` into `GL(n, ℂ)`, this is the source-facing
matrix-group API for the special unitary group used in the surrounding Chapter 7 discussion. -/
#check Matrix.specialUnitaryGroup
#check Matrix.mem_specialUnitaryGroup_iff
#check Matrix.UnitaryGroup.embeddingGL
