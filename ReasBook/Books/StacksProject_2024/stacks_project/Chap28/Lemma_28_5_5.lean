import StacksProject_2024.stacks_project.Chap05.Definition_5_9_1
import StacksProject_2024.stacks_project.Chap28.Lemma_28_5_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced the canonical Noetherian-space instance
-- `AlgebraicGeometry.IsNoetherian.noetherianSpace`, while local project precedent provides the
-- topological owner `TopologicalSpace.LocallyNoetherianSpace` in `Chap05/Definition_5_9_1.lean`.
-- This item therefore needs only the locally Noetherian bridge as a new theorem, with the global
-- Noetherian clause recorded by direct recall.

/-- Lemma 28.5.5 (1): a locally Noetherian scheme has a locally Noetherian underlying topological
space. -/
@[stacks 01OZ]
theorem IsLocallyNoetherian.locallyNoetherianSpace (X : Scheme.{u}) [IsLocallyNoetherian X] :
    TopologicalSpace.LocallyNoetherianSpace X := sorry

attribute [instance 100] IsLocallyNoetherian.locallyNoetherianSpace

/- Lemma 28.5.5 (2): the Noetherian clause is already the canonical instance
`AlgebraicGeometry.IsNoetherian.noetherianSpace`. -/
#check AlgebraicGeometry.IsNoetherian.noetherianSpace

end AlgebraicGeometry
