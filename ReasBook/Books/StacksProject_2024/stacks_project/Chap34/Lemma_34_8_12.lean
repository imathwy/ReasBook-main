import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap34.Definition_34_8_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme

/- Semantic recall: `lean_leansearch` surfaced the general `GrothendieckTopology` and
`Precoverage` site owners, and local Chapter 34 precedent in `Definition_34_8_11` represents
`(\textit{Aff}/S)_{ph}` by `Scheme.bigAffinePhTopology S` on the affine-over category
`S.AffineOver`. -/

/- Lemma 34.8.12: for a scheme `S`, the affine `ph` site `(\textit{Aff}/S)_{ph}` is the
Grothendieck topology `bigAffinePhTopology S` on the category of affine schemes over `S`. -/
recall bigAffinePhTopology (S : Scheme.{u}) : GrothendieckTopology S.AffineOver

end Scheme
end AlgebraicGeometry
