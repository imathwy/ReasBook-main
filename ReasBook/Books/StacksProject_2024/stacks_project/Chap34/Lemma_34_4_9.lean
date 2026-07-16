import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap34.Definition_34_4_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `Definition_34_4_8` packages the three site structures in the source lemma as
-- the canonical small étale topology together with the induced affine Grothendieck topologies.

/- Lemma 34.4.9: this is a pure canonical recall. After Definition 34.4.8, the structures
`S_{\acute{e}tale}`, `(\textit{Aff}/S)_{\acute{e}tale}`, and `S_{affine, \acute{e}tale}` are
already represented by the Grothendieck topologies `S.smallEtaleTopology`,
`bigAffineEtaleTopology S`, and `smallAffineEtaleTopology S`. -/
recall smallEtaleTopology (S : Scheme.{u}) :
    CategoryTheory.GrothendieckTopology S.Etale

recall bigAffineEtaleTopology (S : Scheme.{u}) :
    CategoryTheory.GrothendieckTopology S.AffineOver

recall smallAffineEtaleTopology (S : Scheme.{u}) :
    CategoryTheory.GrothendieckTopology S.smallAffineEtaleSite

end AlgebraicGeometry.Scheme
