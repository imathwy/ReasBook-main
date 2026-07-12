import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` found the exact mathlib instance
`AlgebraicGeometry.quasiCompact_of_noetherianSpace_source`. Since a Noetherian scheme already has
the canonical topological instance `AlgebraicGeometry.IsNoetherian.noetherianSpace`, the source
statement is a pure canonical recall and does not need a local wrapper. -/

/- Lemma 28.5.8: any morphism of schemes `f : X ⟶ Y` with `X` Noetherian is quasi-compact. This is
exactly the canonical instance `AlgebraicGeometry.quasiCompact_of_noetherianSpace_source`,
specialized through `AlgebraicGeometry.IsNoetherian.noetherianSpace`. -/
recall AlgebraicGeometry.quasiCompact_of_noetherianSpace_source

end AlgebraicGeometry
