import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap29.Lemma_29_31_3

open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced affine cotangent/conormal ingredients such as
  `Ideal.Cotangent` and `Ideal.cotangentToQuotientSquare`;
- local project inspection found the scheme-side owner
  `AlgebraicGeometry.immersionConormalSheaf` in `Chap29/Lemma_29_31_3.lean`.

This item is therefore `core/canonical`: the source-facing conormal sheaf of an immersion is
already owned by the project-level declaration `immersionConormalSheaf`, so this file should stay
as a recall block rather than introducing a duplicate alias.
-/

/- Definition 29.31.1: Let `i : Z ⟶ X` be an immersion. The conormal sheaf `\mathcal{C}_{Z/X}` of
`Z` in `X`, or the conormal sheaf of `i`, is formalized in this project by
`immersionConormalSheaf i`. -/
recall immersionConormalSheaf

end AlgebraicGeometry
