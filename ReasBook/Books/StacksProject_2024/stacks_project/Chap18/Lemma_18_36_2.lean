import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [LocallySmall.{max u v} C]
variable (p : GrothendieckTopology.Point.{max u v} J)

/- Domain-style sampling:
- primary domain: points of a Grothendieck topology and their stalk functors on abelian sheaves
  and presheaves;
- sampled owner declarations:
  `GrothendieckTopology.Point.sheafFiber`,
  `GrothendieckTopology.Point.presheafFiber`,
  `GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso`,
  `ExactFunctor.of`;
- source/core/bridge triage:
  `source-facing`: the three clauses of Lemma 18.36.2 about stalk exactness and the
    sheafification comparison for abelian-group-valued sheaves and presheaves;
  `core/canonical`: the owner point `p` together with the canonical stalk functors
    `p.sheafFiber`, `p.presheafFiber`, the comparison
    `p.presheafToSheafCompSheafFiberIso AddCommGrpCat`, and the bundled exact functors
    `ExactFunctor.of p.sheafFiber` and `ExactFunctor.of p.presheafFiber`;
  `bridge/view`: the componentwise textbook comparison for a single presheaf, obtained from the
    owner natural isomorphism.
- primitive data: the site `J`, the point `p`, and the abelian sheaf/presheaf under consideration;
- derived API: the exactness packaging and the sheafification-to-stalk comparison. -/

section Exactness

/- Lemma 18.36.2 (1): for a point `p` of a site `𝒞`, the stalk functor on abelian sheaves
`Ab(𝒞) ⥤ Ab`, namely `ℱ ↦ ℱ_p`, is exact. This is the canonical bundled exact functor
`ExactFunctor.of p.sheafFiber` specialized to `AddCommGrpCat`. -/
#check
  (ExactFunctor.of p.sheafFiber :
    Sheaf J AddCommGrpCat ⥤ₑ AddCommGrpCat)

/- The second clause of the lemma says that the stalk functor on presheaves of abelian groups is
exact; this is the canonical bundled exact functor `ExactFunctor.of p.presheafFiber`. -/
#check
  (ExactFunctor.of p.presheafFiber :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ₑ AddCommGrpCat)

end Exactness

section Sheafification

variable [HasWeakSheafify J AddCommGrpCat]

/- The third clause says that for an abelian-group-valued presheaf `ℱ`, the stalk of `ℱ` agrees
canonically with the stalk of its sheafification. The displayed owner comparison is the natural
isomorphism from the stalk of the sheafification to the original presheaf stalk; if the source
prefers the opposite orientation, that textbook map is the inverse component. -/
#check
  (p.presheafToSheafCompSheafFiberIso AddCommGrpCat :
    presheafToSheaf J AddCommGrpCat ⋙ p.sheafFiber ≅ p.presheafFiber)

end Sheafification

end CategoryTheory
