import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: the canonical owner for the textbook unitary group `U(n)` is
-- `Matrix.unitaryGroup (Fin n) ℂ`. The semantic recall hits verified before finalizing this item
-- were `Matrix.conjTranspose_mul`, `Matrix.mem_unitaryGroup_iff'`, and
-- `Matrix.UnitaryGroup.embeddingGL`.

/- Example 7.29 (The Unitary Group): the textbook `U(n)` is the canonical matrix-group owner
`Matrix.unitaryGroup (Fin n) ℂ`. The adjoint-reversal identity `(A * B)ᴴ = Bᴴ * Aᴴ` is
`Matrix.conjTranspose_mul`, the defining characterization `Aᴴ * A = 1` is
`Matrix.mem_unitaryGroup_iff'`, and the subgroup view inside `GL(n, ℂ)` is provided by
`Matrix.UnitaryGroup.embeddingGL`. -/
#check Matrix.conjTranspose_mul
#check Matrix.unitaryGroup
#check Matrix.mem_unitaryGroup_iff'
#check Matrix.UnitaryGroup.embeddingGL
