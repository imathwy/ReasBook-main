import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap31.Lemma_31_31_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

-- Semantic recall / owner check:
-- `lean_leansearch` surfaced the absolute projective-spectrum owner `AlgebraicGeometry.Proj`,
-- but no relative `Proj_S` construction with quotient-by-degree-submodule functoriality. Local
-- Chapter 31 precedent for Lemmas 31.31.1 and 31.31.4 records the same missing owner and uses the
-- available `RelativeProjPresentation` abstraction, together with the Chapter 28 finite type
-- quasi-coherent subobject theorem. The extra condition in this item is the support-disjointness
-- of the quotient degree piece, whose current owner is the module-sheaf support API.

/- Lemma 31.31.5: let `S` be a quasi-compact and quasi-separated scheme, let `\mathcal A` be a
quasi-coherent graded `\mathcal O_S`-algebra, let
`p : X = \underline{\mathrm{Proj}}_S(\mathcal A) \to S` be the relative `Proj`, let
`i : Z \to X` be a closed subscheme, and let `U \subset S` be an open. If `p` is quasi-compact,
`i` is of finite presentation, `U \cap p(i(Z)) = \emptyset`, `U` is quasi-compact, and every
graded piece `\mathcal A_n` is a finite type `\mathcal O_S`-module, then there exists `d > 0`
and a quasi-coherent finite type submodule `\mathcal F \subset \mathcal A_d` such that
`Z = \underline{\mathrm{Proj}}_S(\mathcal A / \mathcal F\mathcal A)` and the support of
`\mathcal A_d / \mathcal F` is disjoint from `U`.

The current project has the source proof ingredients below, but still lacks the relative-`Proj`
quotient owner needed to state the equality
`Z = \underline{\mathrm{Proj}}_S(\mathcal A / \mathcal F\mathcal A)` without introducing a fake
local wrapper. -/
recall RelativeProjPresentation
recall AlgebraicGeometry.closedImmersion_locallyOfFinitePresentation_iff_idealSheaf_isFiniteType
recall finiteTypeQuasiCoherentSubobjects_isDirectedColimit
recall AlgebraicGeometry.moduleSupport

end AlgebraicGeometry.Scheme.Hom
