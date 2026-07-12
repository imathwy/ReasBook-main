import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap28.Lemma_28_22_3
import StacksProject_2024.Chap29.Lemma_29_21_7
import StacksProject_2024.Chap31.Lemma_31_30_6
import StacksProject_2024.Chap31.Lemma_31_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

-- Semantic recall / owner check:
-- `lean_leansearch` surfaced the ambient closed-subscheme / ideal-sheaf owners
-- `AlgebraicGeometry.Scheme.IdealSheafData.subscheme` and
-- `AlgebraicGeometry.IsClosedImmersion.instSubschemeι`, while local Chapter 28/29/31 inspection
-- verified the available source ingredients `RelativeProjPresentation`,
-- `closedImmersion_locallyOfFinitePresentation_iff_idealSheaf_isFiniteType`, and
-- `finiteTypeQuasiCoherentSubobjects_isDirectedColimit`.
-- The current environment still has no owner relating a finite type degree-`d` submodule
-- `\mathcal F \subset \mathcal A_d` to the quotient relative `Proj`
-- `\underline{\mathrm{Proj}}_S(\mathcal A / \mathcal F \mathcal A)`, so this item is kept as a
-- labeled recall-only block rather than introducing an unlinked local wrapper for that missing
-- quotient-relative-`Proj` construction.

/- Lemma 31.31.4: let `S` be a quasi-compact and quasi-separated scheme, let `\mathcal A` be a
quasi-coherent graded `\mathcal O_S`-algebra, let
`p : X = \underline{\mathrm{Proj}}_S(\mathcal A) \to S` be the relative `Proj`, and let
`i : Z \to X` be a closed subscheme. If `p` is quasi-compact and `i` is of finite presentation,
then there exists a degree `d > 0` and a quasi-coherent finite type
`\mathcal O_S`-submodule `\mathcal F \subset \mathcal A_d` such that
`Z = \underline{\mathrm{Proj}}_S(\mathcal A / \mathcal F \mathcal A)`.

In the current project, the source proof ingredients are already recorded separately by the local
relative-`Proj` presentation owner, the closed-immersion ideal-sheaf finite-presentation criterion,
and the qcqs directed-colimit theorem for finite type quasi-coherent subobjects; the quotient
relative-`Proj` owner needed for the exact source statement is not yet available. -/
recall RelativeProjPresentation
recall AlgebraicGeometry.closedImmersion_locallyOfFinitePresentation_iff_idealSheaf_isFiniteType
recall finiteTypeQuasiCoherentSubobjects_isDirectedColimit

end AlgebraicGeometry.Scheme.Hom
