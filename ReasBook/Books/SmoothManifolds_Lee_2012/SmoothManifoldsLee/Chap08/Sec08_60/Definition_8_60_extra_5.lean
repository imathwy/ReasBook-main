import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: no `lean_leansearch`-style MCP tool was available in this runner, so this
-- item is matched directly against `Mathlib.Geometry.Manifold.GroupLieAlgebra`.

/-
Definition 8.60-extra-5: the canonical mathlib owner for the Lie algebra `Lie(G)` of a Lie group
is `GroupLieAlgebra I G`. It is modeled by the tangent space at the identity, while
`mulInvariantVectorField` sends an element of `GroupLieAlgebra I G` to the corresponding smooth
left-invariant vector field on `G`; `mpullback_mulInvariantVectorField` and
`contMDiff_mulInvariantVectorField` record the left-invariance and smoothness of that field.
-/
recall GroupLieAlgebra
recall mulInvariantVectorField
recall mpullback_mulInvariantVectorField
recall contMDiff_mulInvariantVectorField
