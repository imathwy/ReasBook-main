import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_25_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` found the lower-level `Proj` basic-open/global-section
-- layer, especially `Proj.fromOfGlobalSections`, `Proj.fromOfGlobalSections_preimage_basicOpen`,
-- and `Proj.pullbackAwayιIso`; the exact twisting sheaves, multiplication maps, and comparison
-- isomorphisms used in this remark are not yet packaged as dependency-closed concrete data in the
-- current project.

/- Remark 28.28.4: with the assumptions and notation of Lemma 28.28.3, write the displayed
comparison isomorphism as `\theta_\mathcal F`.  The isomorphism
`f^*\mathcal O_Y(n) \to \mathcal L^{\otimes n}` from Lemma 28.28.2 is
`\theta_{\mathcal L^{\otimes n}}`.  Pulling back the multiplication map
`\widetilde M \otimes_{\mathcal O_Y} \mathcal O_Y(n) \to \widetilde{M(n)}` to `X`, and using the
identification `M(n) = \Gamma_*(X, \mathcal L, \mathcal F \otimes \mathcal L^{\otimes n})`, gives a
commutative square whose lower horizontal arrow is the identity on
`\mathcal F \otimes \mathcal L^{\otimes n}`.

The checked recall surface exposes the graded global-section and twisted-section owners, the
generic `Proj` construction, and the sheaf-module pullback functor.  The local preceding items
record the ample invertible setup, but this remark does not import them as formal parameters because
the source-facing twisting sheaves `\mathcal O_Y(n)`, the Constructions 27.10.1.5 multiplication
maps for associated sheaves of graded modules, the comparison isomorphisms `\theta`, and the
pulled-back square are not yet concrete declarations.  This item is therefore recorded as a labeled
recall block rather than as a theorem over arbitrary replacement data. -/
#check AlgebraicGeometry.RingedSpace.gradedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedGlobalSectionsDegree
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedTwistedGlobalSectionsDegree
#check AlgebraicGeometry.Proj
#check AlgebraicGeometry.Proj.basicOpen
#check AlgebraicGeometry.Proj.fromOfGlobalSections
#check AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen
#check AlgebraicGeometry.Proj.pullbackAwayιIso
#check AlgebraicGeometry.Scheme.Modules.pullback

end AlgebraicGeometry.Scheme.Modules
