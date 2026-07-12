import StacksProject_2024.Chap32.Lemma_32_22_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Remark 32.22.5: in Situation 32.22.1, Lemmas 32.22.2, 32.22.3, and 32.22.4
identify quasi-separated finite-type schemes over `S = lim_i S_i` with the approximation
inverse systems produced from diagrams of the form (32.22.2.1).  In particular, applying
Lemma 32.22.4 to `𝟙 X` in both directions says that two such limit descriptions of the same
`X` are canonically isomorphic after restricting to a common tail of the directed system.

The local Lean owner for the nontrivial part of this remark is Lemma 32.22.4, whose conclusion
provides a descended morphism of inverse systems over a common tail and uniqueness after further
shrinking. -/
#check InverseSystemMorphismOverBase

end AlgebraicGeometry
