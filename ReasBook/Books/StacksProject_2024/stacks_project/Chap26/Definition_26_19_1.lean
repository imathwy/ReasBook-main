import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Semantic recall: `lean_leansearch` recovered the canonical scheme-morphism owner
`QuasiCompact`, and nearby Chapter 26 files already use that owner for quasi-compact morphisms.
This item is therefore a pure canonical recall block. -/

/- Definition 26.19.1: a morphism of schemes is quasi-compact via the canonical morphism property
`QuasiCompact`, i.e. when the underlying map of topological spaces is quasi-compact. -/
recall AlgebraicGeometry.QuasiCompact

/- Companion recall: the source topological characterization is the canonical theorem
`AlgebraicGeometry.quasiCompact_iff_spectral`, identifying quasi-compactness of a scheme morphism
with spectrality of the underlying map on topological spaces. -/
recall AlgebraicGeometry.quasiCompact_iff_spectral
