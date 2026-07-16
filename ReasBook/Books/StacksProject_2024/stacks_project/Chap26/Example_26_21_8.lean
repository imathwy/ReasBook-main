import Mathlib
import StacksProject_2024.stacks_project.Chap26.Example_26_20_7

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.Proj.isSeparated` as the
-- canonical owner-level separatedness result for projective spectra.

noncomputable section

open AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
section ProjectiveLine

variable (k : Type u) [Field k]

/-- Example 26.21.8: for the standard `Proj` model of `P^1_k`, the canonical structure morphism
`projectiveLineToSpec k` is separated. This is the projective-spectrum formalization of the
textbook statement that `\mathbf{P}^1_k -> \operatorname{Spec}(k)` is separated. -/
@[stacks 01KQ]
theorem projectiveLine_isSeparated :
    IsSeparated (projectiveLineToSpec k) := sorry

end ProjectiveLine
